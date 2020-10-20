module app_ID13SwitchOnSetHomeMode

open IoTBottomUp as base

open cap_location
open cap_switch


one sig app_ID13SwitchOnSetHomeMode extends IoTApp {
  
  mySwitch : set cap_switch,
  
  location : one cap_location,
} {
  rules = r
}







// application rules base class

abstract sig r extends Rule {}

one sig r0 extends r {}{
  triggers   = r0_trig
  conditions = r0_cond
  commands   = r0_comm
}

abstract sig r0_trig extends Trigger {}

one sig r0_trig0 extends r0_trig {} {
  capabilities = app_ID13SwitchOnSetHomeMode.mySwitch
  attribute    = cap_switch_attr_switch
  value        = cap_switch_attr_switch_val_on
}


abstract sig r0_cond extends Condition {}


abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_ID13SwitchOnSetHomeMode.location
  attribute = cap_location_attr_mode
  value = cap_location_attr_mode_val_Home
}

one sig r1 extends r {}{
  triggers   = r1_trig
  conditions = r1_cond
  commands   = r1_comm
}

abstract sig r1_trig extends Trigger {}

one sig r1_trig0 extends r1_trig {} {
  capabilities = app_ID13SwitchOnSetHomeMode.mySwitch
  attribute    = cap_switch_attr_switch
  value        = cap_switch_attr_switch_val_on
}


abstract sig r1_cond extends Condition {}


abstract sig r1_comm extends Command {}

one sig r1_comm0 extends r1_comm {} {
  capability   = app_ID13SwitchOnSetHomeMode.location
  attribute = cap_location_attr_mode
  value = cap_location_attr_mode_val_Home
}



