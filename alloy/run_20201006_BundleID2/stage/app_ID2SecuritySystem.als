module app_ID2SecuritySystem

open IoTBottomUp as base

open cap_lock
open cap_switch
open cap_presenceSensor


one sig app_ID2SecuritySystem extends IoTApp {
  
  presence : one cap_presenceSensor,
  
  state : one cap_state,
  
  lock1 : some cap_lock,
  
  switches : some cap_switch,
} {
  rules = r
}



one sig cap_state extends Capability {} {
  attributes = cap_state_attr
}
abstract sig cap_state_attr extends Attribute {}


one sig cap_state_attr_runIn extends cap_state_attr {} {
  values = cap_state_attr_runIn_val
}

abstract sig cap_state_attr_runIn_val extends AttrValue {}
one sig cap_state_attr_runIn_val_on extends cap_state_attr_runIn_val {}
one sig cap_state_attr_runIn_val_off extends cap_state_attr_runIn_val {}



// application rules base class

abstract sig r extends Rule {}

one sig r0 extends r {}{
  no triggers
  conditions = r0_cond
  commands   = r0_comm
}




abstract sig r0_cond extends Condition {}

one sig r0_cond0 extends r0_cond {} {
  capabilities = app_ID2SecuritySystem.state
  attribute    = cap_state_attr_runIn
  value        = cap_state_attr_runIn_val_on
}

abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_ID2SecuritySystem.switches
  attribute = cap_switch_attr_switch
  value = cap_switch_attr_switch_val_off
}

one sig r1 extends r {}{
  triggers   = r1_trig
  conditions = r1_cond
  commands   = r1_comm
}

abstract sig r1_trig extends Trigger {}

one sig r1_trig0 extends r1_trig {} {
  capabilities = app_ID2SecuritySystem.presence
  attribute    = cap_presenceSensor_attr_presence
  no value
}


abstract sig r1_cond extends Condition {}

one sig r1_cond0 extends r1_cond {} {
  capabilities = app_ID2SecuritySystem.lock1
  attribute    = cap_lock_attr_lock
  value        = cap_lock_attr_lock_val_unlocked
}
one sig r1_cond1 extends r1_cond {} {
  capabilities = app_ID2SecuritySystem.presence
  attribute    = cap_presenceSensor_attr_presence
  value        = cap_presenceSensor_attr_presence_val_present
}

abstract sig r1_comm extends Command {}

one sig r1_comm0 extends r1_comm {} {
  capability   = app_ID2SecuritySystem.lock1
  attribute = cap_lock_attr_lock
  value = cap_lock_attr_lock_val_unlock
}

one sig r2 extends r {}{
  triggers   = r2_trig
  conditions = r2_cond
  commands   = r2_comm
}

abstract sig r2_trig extends Trigger {}

one sig r2_trig0 extends r2_trig {} {
  capabilities = app_ID2SecuritySystem.presence
  attribute    = cap_presenceSensor_attr_presence
  no value
}


abstract sig r2_cond extends Condition {}

one sig r2_cond0 extends r2_cond {} {
  capabilities = app_ID2SecuritySystem.presence
  attribute    = cap_presenceSensor_attr_presence
  value        = cap_presenceSensor_attr_presence_val_not_present
}

abstract sig r2_comm extends Command {}

one sig r2_comm0 extends r2_comm {} {
  capability   = app_ID2SecuritySystem.state
  attribute = cap_state_attr_runIn
  value = cap_state_attr_runIn_val_on
}



