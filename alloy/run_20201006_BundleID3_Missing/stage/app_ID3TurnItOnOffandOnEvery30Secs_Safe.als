module app_ID3TurnItOnOffandOnEvery30Secs_Safe

open IoTBottomUp as base

open cap_switch
open cap_contactSensor


one sig app_ID3TurnItOnOffandOnEvery30Secs_Safe extends IoTApp {
  
  contact1 : one cap_contactSensor,
  
  switch1 : one cap_switch,
  
  state : one cap_state,
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
  capabilities = app_ID3TurnItOnOffandOnEvery30Secs_Safe.state
  attribute    = cap_state_attr_runIn
  value        = cap_state_attr_runIn_val_on
}

abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_ID3TurnItOnOffandOnEvery30Secs_Safe.switch1
  attribute = cap_switch_attr_switch
  value = cap_switch_attr_switch_val_off
}


