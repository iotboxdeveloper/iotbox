module app_ID16SleepingModeChange

open IoTBottomUp as base

open cap_location
open cap_switch


one sig app_ID16SleepingModeChange extends IoTApp {
  
  theSwitch : one cap_switch,
  
  location : one cap_location,
  
  Home_Day : one cap_location_attr_mode_val,
  
  Away_Day : one cap_location_attr_mode_val,
  
  Home_Night : one cap_location_attr_mode_val,
  
  Away_Night : one cap_location_attr_mode_val,
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
  capabilities = app_ID16SleepingModeChange.theSwitch
  attribute    = cap_switch_attr_switch
  value        = cap_switch_attr_switch_val_off
}


abstract sig r0_cond extends Condition {}


abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_ID16SleepingModeChange.location
  attribute = cap_location_attr_mode
  value        = app_ID16SleepingModeChange.Away_Day
}

one sig r1 extends r {}{
  triggers   = r1_trig
  conditions = r1_cond
  commands   = r1_comm
}

abstract sig r1_trig extends Trigger {}

one sig r1_trig0 extends r1_trig {} {
  capabilities = app_ID16SleepingModeChange.theSwitch
  attribute    = cap_switch_attr_switch
  value        = cap_switch_attr_switch_val_on
}


abstract sig r1_cond extends Condition {}


abstract sig r1_comm extends Command {}

one sig r1_comm0 extends r1_comm {} {
  capability   = app_ID16SleepingModeChange.location
  attribute = cap_location_attr_mode
  value        = app_ID16SleepingModeChange.Home_Day
}

one sig r2 extends r {}{
  triggers   = r2_trig
  conditions = r2_cond
  commands   = r2_comm
}

abstract sig r2_trig extends Trigger {}

one sig r2_trig0 extends r2_trig {} {
  capabilities = app_ID16SleepingModeChange.theSwitch
  attribute    = cap_switch_attr_switch
  value        = cap_switch_attr_switch_val_off
}


abstract sig r2_cond extends Condition {}


abstract sig r2_comm extends Command {}

one sig r2_comm0 extends r2_comm {} {
  capability   = app_ID16SleepingModeChange.location
  attribute = cap_location_attr_mode
  value        = app_ID16SleepingModeChange.Away_Night
}

one sig r3 extends r {}{
  triggers   = r3_trig
  conditions = r3_cond
  commands   = r3_comm
}

abstract sig r3_trig extends Trigger {}

one sig r3_trig0 extends r3_trig {} {
  capabilities = app_ID16SleepingModeChange.theSwitch
  attribute    = cap_switch_attr_switch
  value        = cap_switch_attr_switch_val_on
}


abstract sig r3_cond extends Condition {}


abstract sig r3_comm extends Command {}

one sig r3_comm0 extends r3_comm {} {
  capability   = app_ID16SleepingModeChange.location
  attribute = cap_location_attr_mode
  value        = app_ID16SleepingModeChange.Home_Night
}



