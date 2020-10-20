module app_ID6TurnOnSwitchNotHome_Safe

open IoTBottomUp as base

open cap_switchLevel
open cap_lock
open cap_presenceSensor


one sig app_ID6TurnOnSwitchNotHome_Safe extends IoTApp {
  
  myswitch : one cap_switchLevel,
  
  state : one cap_state,
  
  thelock : one cap_lock,
  
  person : one cap_presenceSensor,
} {
  rules = r
}



one sig cap_state extends Capability {} {
  attributes = cap_state_attr
}
abstract sig cap_state_attr extends Attribute {}


one sig cap_state_attr_attack extends cap_state_attr {} {
  values = cap_state_attr_attack_val
}

abstract sig cap_state_attr_attack_val extends AttrValue {}
one sig cap_state_attr_attack_val_true extends cap_state_attr_attack_val {}
one sig cap_state_attr_attack_val_false extends cap_state_attr_attack_val {}

one sig cap_state_attr_state_home extends cap_state_attr {} {
  values = cap_state_attr_state_home_val
}

abstract sig cap_state_attr_state_home_val extends AttrValue {}
one sig cap_state_attr_state_home_val_false extends cap_state_attr_state_home_val {}
one sig cap_state_attr_state_home_val_true extends cap_state_attr_state_home_val {}



// application rules base class

abstract sig r extends Rule {}

one sig r0 extends r {}{
  triggers   = r0_trig
  conditions = r0_cond
  commands   = r0_comm
}

abstract sig r0_trig extends Trigger {}

one sig r0_trig0 extends r0_trig {} {
  capabilities = app_ID6TurnOnSwitchNotHome_Safe.person
  attribute    = cap_presenceSensor_attr_presence
  no value
}


abstract sig r0_cond extends Condition {}

one sig r0_cond0 extends r0_cond {} {
  capabilities = app_ID6TurnOnSwitchNotHome_Safe.person
  attribute    = cap_presenceSensor_attr_presence
  value        = cap_presenceSensor_attr_presence_val_not_present
}

abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_ID6TurnOnSwitchNotHome_Safe.state
  attribute = cap_state_attr_state_home
  value = cap_state_attr_state_home_val_false
}
one sig r0_comm1 extends r0_comm {} {
  capability   = app_ID6TurnOnSwitchNotHome_Safe.state
  attribute = cap_state_attr_attack
  value = cap_state_attr_attack_val_true
}
one sig r0_comm2 extends r0_comm {} {
  capability   = app_ID6TurnOnSwitchNotHome_Safe.myswitch
  attribute = cap_switchLevel_attr_level
  value = cap_switchLevel_attr_level_val0
}


one sig r1 extends r {}{
  triggers   = r1_trig
  conditions = r1_cond
  commands   = r1_comm
}

abstract sig r1_trig extends Trigger {}

one sig r1_trig0 extends r1_trig {} {
  capabilities = app_ID6TurnOnSwitchNotHome_Safe.person
  attribute    = cap_presenceSensor_attr_presence
  no value
}


abstract sig r1_cond extends Condition {}

one sig r1_cond0 extends r1_cond {} {
  capabilities = app_ID6TurnOnSwitchNotHome_Safe.person
  attribute    = cap_presenceSensor_attr_presence
  value        = cap_presenceSensor_attr_presence_val - cap_presenceSensor_attr_presence_val_not_present
}

abstract sig r1_comm extends Command {}

one sig r1_comm0 extends r1_comm {} {
  capability   = app_ID6TurnOnSwitchNotHome_Safe.myswitch
  attribute = cap_switchLevel_attr_level
  value = cap_switchLevel_attr_level_val0
}
one sig r1_comm1 extends r1_comm {} {
  capability   = app_ID6TurnOnSwitchNotHome_Safe.state
  attribute = cap_state_attr_state_home
  value = cap_state_attr_state_home_val_true
}
one sig r1_comm2 extends r1_comm {} {
  capability   = app_ID6TurnOnSwitchNotHome_Safe.state
  attribute = cap_state_attr_attack
  value = cap_state_attr_attack_val_false
}



