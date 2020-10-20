module app_ImprovedPowerAllowance

open IoTBottomUp as base

open cap_switch


one sig app_ImprovedPowerAllowance extends IoTApp {
  
  theSwitch : one cap_switch,
  
  state : one cap_state,
} {
  rules = r
}



one sig cap_state extends Capability {} {
  attributes = cap_state_attr
}
abstract sig cap_state_attr extends Attribute {}




// application rules base class

abstract sig r extends Rule {}

one sig r0 extends r {}{
  triggers   = r0_trig
  conditions = r0_cond
  commands   = r0_comm
}

abstract sig r0_trig extends Trigger {}

one sig r0_trig0 extends r0_trig {} {
  capabilities = app_ImprovedPowerAllowance.theSwitch
  attribute    = cap_switch_attr_switch
  value        = cap_switch_attr_switch_val_on
}


abstract sig r0_cond extends Condition {}


abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_ImprovedPowerAllowance.theSwitch
  attribute = cap_switch_attr_switch
  value = cap_switch_attr_switch_val_off
}







