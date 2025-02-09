/*
 * Copyright (c) godot-rust; Bromeon and contributors.
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use crate::builtin::{Callable, GString, Variant};
use crate::classes::object::ConnectFlags;
use crate::obj::{bounds, Bounds, Gd, GodotClass, WithBaseField};
use crate::registry::functional::{AsFunc, ParamTuple, TypedSignal};
use crate::{meta, sys};

/// Type-state builder for customizing signal connections.
///
/// Allows a high degree of customization for connecting signals, while maintaining complete type safety.
///
/// # Builder stages
///
/// The builder API has a well-defined flow and is separated in stages. In each stage, you have certain builder methods available that you can
/// or must call, before advancing to the next stage. Check the instructions.
///
/// ## Stage 1 (required)
/// Choose one:
/// - [`function`][Self::function]: Connect a global/associated function or a closure.
/// - [`object_self`][Self::object_self]: If you want to connect a method (in stage 2), running on the same object as the signal.
/// - [`object`][Self::object]: If you want to connect a method, running on a separate object.
///
/// ## Stage 2 (conditional)
/// Required iff `object_self` or `object` was called in stage 2.
/// - [`method_mut`][Self::method_mut]: Connect a `&mut self` method.
///
/// ## Stage 3
/// All these methods are optional, and they can be combined.
/// - [`sync`][Self::sync]: If the signal connection should be callable across threads.  \
///   Requires `Send` + `Sync` bounds on the provided function/method, and is only available for the `experimental-threads` Cargo feature.
/// - [`name`][Self::name]: Name of the `Callable` (for debug purposes).  \
///   If not specified, the Rust function name is used. This is typically a good default, but not very readable for closures.
/// - [`flags`][Self::flags]: Provide one or multiple [`ConnectFlags`][crate::classes::object::ConnectFlags], possibly combined with bitwise OR.
///
/// ## Final stage
/// - [`done`][Self::done]: Finalize the connection. Consumes the builder and registers the signal with Godot.
///
#[must_use]
pub struct ConnectBuilder<'a, CSig: GodotClass, CRcv, Ps, GodotFn> {
    parent_sig: &'a mut TypedSignal<'a, CSig, Ps>,
    data: BuilderData,

    // Type-state data.
    receiver_obj: CRcv,
    godot_fn: GodotFn,
}

impl<'a, CSig: WithBaseField, Ps: ParamTuple> ConnectBuilder<'a, CSig, (), Ps, ()> {
    pub(super) fn new(parent_sig: &'a mut TypedSignal<'a, CSig, Ps>) -> Self {
        ConnectBuilder {
            parent_sig,
            data: BuilderData::default(),
            godot_fn: (),
            receiver_obj: (),
        }
    }

    /// **Stage 1:** global/associated function or closure.
    pub fn function<F>(
        self,
        mut function: F,
    ) -> ConnectBuilder<
        'a,
        /* CSig = */ CSig,
        /* CRcv = */ (),
        /* Ps = */ Ps,
        /* GodotFn= */ impl FnMut(&[&Variant]) -> Result<Variant, ()> + 'static,
    >
    where
        F: AsFunc<(), Ps>,
    {
        let godot_fn = move |variant_args: &[&Variant]| -> Result<Variant, ()> {
            let args = Ps::from_variant_array(variant_args);
            function.call((), args);

            Ok(Variant::nil())
        };

        let mut data = self.data;
        data.callable_name = Some(sys::short_type_name::<F>().into());

        ConnectBuilder {
            parent_sig: self.parent_sig,
            data,
            godot_fn,
            receiver_obj: (),
        }
    }

    pub fn object_self(self) -> ConnectBuilder<'a, CSig, Gd<CSig>, Ps, ()> {
        let receiver_obj: Gd<CSig> = self.parent_sig.receiver_object();

        ConnectBuilder {
            parent_sig: self.parent_sig,
            data: self.data,
            godot_fn: (),
            receiver_obj,
        }
    }

    pub fn object<C: GodotClass>(self, object: Gd<C>) -> ConnectBuilder<'a, CSig, Gd<C>, Ps, ()> {
        ConnectBuilder {
            parent_sig: self.parent_sig,
            data: self.data,
            godot_fn: (),
            receiver_obj: object,
        }
    }
}

impl<'a, CSig: WithBaseField, CRcv: GodotClass, Ps: ParamTuple>
    ConnectBuilder<'a, CSig, Gd<CRcv>, Ps, ()>
{
    /// **Stage 2:** method taking `&mut self`.
    pub fn method_mut<F>(
        self,
        mut method_with_mut_self: F,
    ) -> ConnectBuilder<
        'a,
        /* CSig = */ CSig,
        /* CRcv: again reset to unit type, after object has been captured in closure. */
        (),
        /* Ps = */ Ps,
        /* GodotFn = */ impl FnMut(&[&Variant]) -> Result<Variant, ()>,
    >
    where
        CRcv: GodotClass + Bounds<Declarer = bounds::DeclUser>,
        for<'c> F: AsFunc<&'c mut CRcv, Ps>,
    {
        let mut gd: Gd<CRcv> = self.receiver_obj;

        let godot_fn = move |variant_args: &[&Variant]| -> Result<Variant, ()> {
            let args = Ps::from_variant_array(variant_args);
            let mut guard = gd.bind_mut();
            let instance = &mut *guard;
            method_with_mut_self.call(instance, args);

            Ok(Variant::nil())
        };

        let mut data = self.data;
        data.callable_name = Some(sys::short_type_name::<F>().into());

        ConnectBuilder {
            parent_sig: self.parent_sig,
            data,
            godot_fn,
            receiver_obj: (),
        }
    }
}

impl<'a, CSig, CRcv, Ps, GodotFn> ConnectBuilder<'a, CSig, CRcv, Ps, GodotFn>
where
    CSig: WithBaseField,
    Ps: ParamTuple,
    GodotFn: FnMut(&[&Variant]) -> Result<Variant, ()> + 'static,
{
    #[cfg(feature = "experimental-threads")]
    pub fn sync(
        self,
    ) -> ConnectBuilder<
        'a,
        /* CSig = */ CSig,
        /* CRcv = */ CRcv,
        /* Ps = */ Ps,
        /* GodotFn = */ impl FnMut(&[&Variant]) -> Result<Variant, ()>,
    >
    where
        // Why both Send+Sync: closure can not only impact another thread (Sync), but it's also possible to share such Callables across threads
        // (Send) or even call them from multiple threads (Sync). We don't differentiate the fine-grained needs, it's either thread-safe or not.
        GodotFn: Send + Sync,
    {
        let Self {
            parent_sig,
            mut data,
            receiver_obj,
            godot_fn,
        } = self;

        assert!(
            data.sync_callable.is_none(),
            "sync() called twice on the same builder."
        );

        let dummy_fn =
            |_variants: &[&Variant]| panic!("sync() closure should have been replaced by now.");

        data.sync_callable = Some(Callable::from_sync_fn(data.callable_name_ref(), godot_fn));

        ConnectBuilder {
            parent_sig,
            data,
            godot_fn: dummy_fn,
            receiver_obj,
        }
    }

    /// Name of the `Callable`, mostly used for debugging.
    ///
    /// If not provided, the Rust type name of the function/method is used.
    pub fn name(mut self, name: impl meta::AsArg<GString>) -> Self {
        assert!(
            self.data.callable_name.is_none(),
            "name() called twice on the same builder."
        );

        meta::arg_into_owned!(name);
        self.data.callable_name = Some(name);
        self
    }

    /// Add one or multiple flags to the connection, possibly combined with `|` operator.
    pub fn flags(mut self, flags: ConnectFlags) -> Self {
        assert!(
            self.data.connect_flags.is_none(),
            "flags() called twice on the same builder."
        );

        self.data.connect_flags = Some(flags);
        self
    }

    pub fn done(self) {
        let Self {
            parent_sig,
            data,
            godot_fn,
            receiver_obj: _,
        } = self;

        let callable_name = data.callable_name_ref();

        // If sync() was previously called, use the already-existing callable, otherwise construct a local one now.
        #[cfg(feature = "experimental-threads")]
        let callable = match data.sync_callable {
            Some(sync_callable) => sync_callable,
            None => Callable::from_local_fn(callable_name, godot_fn),
        };

        #[cfg(not(feature = "experimental-threads"))]
        let callable = Callable::from_local_fn(callable_name, godot_fn);

        parent_sig.connect_untyped(&callable, data.connect_flags);
    }
}

// ----------------------------------------------------------------------------------------------------------------------------------------------

/// Gathers all the non-typestate data, so that the builder can easily transfer it without manually moving each field.
#[derive(Default)]
struct BuilderData {
    /// User-specified name; if not provided, the Rust RTTI type name of the function is used.
    callable_name: Option<GString>,

    /// Godot connection flags.
    connect_flags: Option<ConnectFlags>,

    /// If [`sync()`][ConnectBuilder::sync] was called, then this already contains the populated closure.
    #[cfg(feature = "experimental-threads")]
    sync_callable: Option<Callable>,
}

impl BuilderData {
    fn callable_name_ref(&self) -> &GString {
        self.callable_name
            .as_ref()
            .expect("Signal connect name not set; this is a bug.")
    }
}
