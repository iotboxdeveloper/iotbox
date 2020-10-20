module app_DoubleTapModeChange

open IoTBottomUp as base

open cap_userInput
open cap_location
open cap_switch


one sig app_DoubleTapModeChange extends IoTApp {
  
  sendPushMessage : one cap_userInput,
  
  no_value : one cap_location_attr_mode_val,
  
  state : one cap_state,
  
  downMode : one cap_location_attr_mode_val,
  
  upMode : one cap_location_attr_mode_val,
  
  location : one cap_location,
  
  master : one cap_switch,
} {
  rules = r
}


one sig cap_userInput_attr_sendPushMessage extends cap_userInput_attr {}
{
    values = cap_userInput_attr_sendPushMessage_val
} 
abstract sig cap_userInput_attr_sendPushMessage_val extends cap_userInput_attr_value_val {}

one sig cap_state extends Capability {} {
  attributes = cap_state_attr
}
abstract sig cap_state_attr extends Attribute {}



one sig cap_state_attr_modeStartTime extends cap_state_attr{} {
  values = cap_state_attr_modeStartTime_val
}

abstract sig cap_state_attr_modeStartTime_val extends AttrValue {}

// application rules base class

abstract sig r extends Rule {}

one sig r0 extends r {}{
  triggers   = r0_trig
  conditions = r0_cond
  commands   = r0_comm
}

abstract sig r0_trig extends Trigger {}

one sig r0_trig0 extends r0_trig {} {
  capabilities = app_DoubleTapModeChange.master
  attribute    = cap_switch_attr_switch
  no value
}


abstract sig r0_cond extends Condition {}

one sig r0_cond0 extends r0_cond {} {
  capabilities = app_DoubleTapModeChange.master
  attribute    = cap_switch_attr_switch
  value        = cap_switch_attr_switch_val_on
}
one sig r0_cond1 extends r0_cond {} {
  capabilities = app_DoubleTapModeChange.location
  attribute    = cap_location_attr_mode
  value        = cap_location_attr_mode_val_Away
}
one sig r0_cond2 extends r0_cond {} {
  capabilities = app_DoubleTapModeChange.master
  attribute    = cap_switch_attr_switch
  value        = cap_switch_attr_switch_val
}

abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_DoubleTapModeChange.location
  attribute = cap_location_attr_mode
  value        = cap_location_attr_mode_val_Home
}


one sig r2 extends r {}{
  triggers   = r2_trig
  conditions = r2_cond
  commands   = r2_comm
}

abstract sig r2_trig extends Trigger {}

one sig r2_trig0 extends r2_trig {} {
  capabilities = app_DoubleTapModeChange.master
  attribute    = cap_switch_attr_switch
  no value
}


abstract sig r2_cond extends Condition {}

one sig r2_cond0 extends r2_cond {} {
  capabilities = app_DoubleTapModeChange.master
  attribute    = cap_switch_attr_switch
  value        = cap_switch_attr_switch_val - cap_switch_attr_switch_val_on
}
one sig r2_cond1 extends r2_cond {} {
  capabilities = app_DoubleTapModeChange.master
  attribute    = cap_switch_attr_switch
  value        = cap_switch_attr_switch_val_off
}
one sig r2_cond2 extends r2_cond {} {
  capabilities = app_DoubleTapModeChange.location
  attribute    = cap_location_attr_mode
  value        = cap_location_attr_mode_val_Away
}
one sig r2_cond3 extends r2_cond {} {
  capabilities = app_DoubleTapModeChange.master
  attribute    = cap_switch_attr_switch
  value        = cap_switch_attr_switch_val
}

abstract sig r2_comm extends Command {}

one sig r2_comm0 extends r2_comm {} {
  capability   = app_DoubleTapModeChange.location
  attribute = cap_location_attr_mode
  value        = cap_location_attr_mode_val_Home
}


