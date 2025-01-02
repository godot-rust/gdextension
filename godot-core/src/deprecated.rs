/*
 * Copyright (c) godot-rust; Bromeon and contributors.
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

// ----------------------------------------------------------------------------------------------------------------------------------------------
// Compatibility

// Code generated by Rust derive macros cannot cause any deprecation warnings, due to questionable "feature"
// https://github.com/rust-lang/rust/pull/58994. Fortunately, an extra layer of indirection solves most problems: we generate a declarative
// macro that itself isn't deprecated, but _its_ expansion is. Since the expansion happens in a later step, the warning is emitted.

// Usage example.
//
// 1. Declare a const fn which describes the deprecation warning.
//
//     #[deprecated = "#[base] is no longer needed; Base<T> is recognized directly. \n\
//             More information on https://github.com/godot-rust/gdext/pull/577."]
//     pub const fn base_attribute() {}
//
// 2. At the place of usage, use the `emit_deprecated_warning!` macro to emit the warning. This can be generated by codegen, as well.
//
//     #[cfg(feature = "custom-godot")]
//     __deprecated::emit_deprecated_warning!(feature_custom_godot);

#[macro_export]
macro_rules! emit_deprecated_warning {
    ($warning_fn:ident) => {
        const _: () = $crate::__deprecated::$warning_fn();
    };
}

use crate::classes;
pub use crate::emit_deprecated_warning;
use crate::obj::{EngineBitfield, EngineEnum};
// ----------------------------------------------------------------------------------------------------------------------------------------------
// Library-side deprecations

#[deprecated = "\nThe attribute key #[init(val = ...)] replaces #[init(default = ...)].\n\
	More information on https://github.com/godot-rust/gdext/pull/844"]
pub const fn init_default() {}

#[deprecated = "\nThe attribute key #[class(editor_plugin)] is now implied by #[class(base = EditorPlugin)]. It is ignored.\n\
	More information on https://github.com/godot-rust/gdext/pull/884"]
pub const fn class_editor_plugin() {}

#[deprecated = "\nThe attribute key #[class(hidden)] has been renamed to #[class(internal)], following Godot terminology.\n\
    More information on https://github.com/godot-rust/gdext/pull/884"]
pub const fn class_hidden() {}

#[deprecated = "\nThe attribute key #[gdextension(entry_point)] has been renamed to #[gdextension(entry_symbol)], for consistency \
    with the configuration key in the .gdextension file.\n\
    More information on https://github.com/godot-rust/gdext/pull/959"]
pub const fn gdextension_entry_point() {}

// ----------------------------------------------------------------------------------------------------------------------------------------------
// Manual fills

// Note: this may cause import ambiguities for trait methods, however those are considered "minor changes" in Rust SemVer (which means
// patch bump for 0.x), in contrast to removing a trait impl. See https://doc.rust-lang.org/cargo/reference/semver.html#item-new and
// https://github.com/rust-lang/rfcs/blob/master/text/1105-api-evolution.md#minor-change-implementing-any-non-fundamental-trait.
impl EngineEnum for classes::object::ConnectFlags {
    fn try_from_ord(ord: i32) -> Option<Self> {
        <Self as EngineBitfield>::try_from_ord(ord as u64)
    }

    fn ord(self) -> i32 {
        <Self as EngineBitfield>::ord(self) as i32
    }

    fn as_str(&self) -> &'static str {
        match *self {
            Self::DEFERRED => "DEFERRED",
            Self::PERSIST => "PERSIST",
            Self::ONE_SHOT => "ONE_SHOT",
            Self::REFERENCE_COUNTED => "REFERENCE_COUNTED",
            _ => "",
        }
    }

    fn godot_name(&self) -> &'static str {
        match *self {
            Self::DEFERRED => "CONNECT_DEFERRED",
            Self::PERSIST => "CONNECT_PERSIST",
            Self::ONE_SHOT => "CONNECT_ONE_SHOT",
            Self::REFERENCE_COUNTED => "CONNECT_REFERENCE_COUNTED",
            _ => self.as_str(),
        }
    }
}

// ----------------------------------------------------------------------------------------------------------------------------------------------
// Godot-side deprecations

// This is a Godot-side deprecation. Since it's the only way in Godot 4.1, we keep compatibility for now.
#[cfg_attr(
    since_api = "4.2",
    deprecated = "\nUse #[export(range = (radians_as_degrees))] and not #[export(range = (radians))].\n\
	More information on https://github.com/godotengine/godot/pull/82195."
)]
pub const fn export_range_radians() {}
