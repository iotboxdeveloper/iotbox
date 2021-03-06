module app_B4_HomeModeApp

open IoTBottomUp as base

open cap_location
open cap_ovenMode


one sig app_B4_HomeModeApp extends IoTApp {
  
  no_value : one cap_location_attr_mode_val,
  
  state : one cap_state,
  
  location : one cap_location,
  
  oven : one cap_ovenMode,
} {
  rules = r
}



one sig cap_state extends Capability {} {
  attributes = cap_state_attr
}
abstract sig cap_state_attr extends Attribute {}


one sig cap_state_attr_mode extends cap_state_attr {} {
  values = cap_state_attr_mode_val
}

abstract sig cap_state_attr_mode_val extends AttrValue {}
one sig cap_state_attr_mode_val_Home extends cap_state_attr_mode_val {}



// application rules base class

abstract sig r extends Rule {}

one sig r0 extends r {}{
  triggers   = r0_trig
  conditions = r0_cond
  commands   = r0_comm
}

abstract sig r0_trig extends Trigger {}

one sig r0_trig0 extends r0_trig {} {
  capabilities = app_B4_HomeModeApp.location
  attribute    = cap_location_attr_mode
  no value
}


abstract sig r0_cond extends Condition {}

one sig r0_cond0 extends r0_cond {} {
  capabilities = app_B4_HomeModeApp.location
  attribute    = cap_location_attr_mode
  value        = cap_location_attr_mode_val_Home
}

abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_B4_HomeModeApp.oven
  attribute = cap_ovenMode_attr_ovenMode
  value = cap_ovenMode_attr_ovenMode_val_grill
}



