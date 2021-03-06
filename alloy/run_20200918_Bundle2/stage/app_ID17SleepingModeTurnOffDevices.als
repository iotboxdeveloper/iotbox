module app_ID17SleepingModeTurnOffDevices

open IoTBottomUp as base

open cap_location
open cap_switch


one sig app_ID17SleepingModeTurnOffDevices extends IoTApp {
  
  theSwitches : set cap_switch,
  
  no_value : one cap_location_attr_mode_val,
  
  state : one cap_state,
  
  location : one cap_location,
} {
  rules = r
}



one sig cap_state extends Capability {} {
  attributes = cap_state_attr
}
abstract sig cap_state_attr extends Attribute {}


one sig cap_state_attr_switchesTurnedOff extends cap_state_attr {} {
  values = cap_state_attr_switchesTurnedOff_val
}

abstract sig cap_state_attr_switchesTurnedOff_val extends AttrValue {}
one sig cap_state_attr_switchesTurnedOff_val_true extends cap_state_attr_switchesTurnedOff_val {}

one sig cap_state_attr_runIn extends cap_state_attr {} {
  values = cap_state_attr_runIn_val
}

abstract sig cap_state_attr_runIn_val extends AttrValue {}
one sig cap_state_attr_runIn_val_on extends cap_state_attr_runIn_val {}
one sig cap_state_attr_runIn_val_off extends cap_state_attr_runIn_val {}



// application rules base class

abstract sig r extends Rule {}

one sig r0 extends r {}{
  triggers   = r0_trig
  conditions = r0_cond
  commands   = r0_comm
}

abstract sig r0_trig extends Trigger {}

one sig r0_trig0 extends r0_trig {} {
  capabilities = app_ID17SleepingModeTurnOffDevices.location
  attribute    = cap_location_attr_mode
  no value
}


abstract sig r0_cond extends Condition {}


abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_ID17SleepingModeTurnOffDevices.state
  attribute = cap_state_attr_switchesTurnedOff
  value = cap_state_attr_switchesTurnedOff_val_true
}

one sig r1 extends r {}{
  triggers   = r1_trig
  conditions = r1_cond
  commands   = r1_comm
}

abstract sig r1_trig extends Trigger {}

one sig r1_trig0 extends r1_trig {} {
  capabilities = app_ID17SleepingModeTurnOffDevices.location
  attribute    = cap_location_attr_mode
  no value
}


abstract sig r1_cond extends Condition {}


abstract sig r1_comm extends Command {}

one sig r1_comm0 extends r1_comm {} {
  capability   = app_ID17SleepingModeTurnOffDevices.state
  attribute = cap_state_attr_runIn
  value = cap_state_attr_runIn_val_on
}



