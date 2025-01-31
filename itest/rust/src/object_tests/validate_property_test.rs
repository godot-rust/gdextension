/*
 * Copyright (c) godot-rust; Bromeon and contributors.
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use godot::builtin::{Array, Dictionary, StringName};
use godot::classes::IObject;
use godot::global::PropertyUsageFlags;
use godot::meta::PropertyInfo;
use godot::obj::NewAlloc;
use godot::register::{godot_api, GodotClass};
use godot::test::itest;

#[derive(GodotClass)]
#[class(base = Object, init)]
pub struct ValidatePropertyTest {
    #[export]
    my_var: i64,
}

#[godot_api]
impl IObject for ValidatePropertyTest {
    fn validate_property(&self, property: &mut PropertyInfo) {
        if property.property_name.to_string() == "my_var" {
            property.usage = PropertyUsageFlags::NO_EDITOR;
            property.property_name = StringName::from("SuperNewTestPropertyName");
        }
    }
}

#[itest]
fn validate_property_test() {
    let obj = ValidatePropertyTest::new_alloc();
    let properties: Array<Dictionary> = obj.get_property_list();

    for property in properties.iter_shared() {
        if property
            .get("name")
            .map(|v| v.to_string() == "SuperNewTestPropertyName")
            .unwrap_or(false)
        {
            let Some(usage) = property.get("usage").map(|v| v.to::<PropertyUsageFlags>()) else {
                continue;
            };
            assert_eq!(usage, PropertyUsageFlags::NO_EDITOR);
            obj.free();
            return;
        }
    }

    panic!("Test failed – unable to find validated property.");
}
