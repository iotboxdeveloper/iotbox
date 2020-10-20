module app_SecurityNightLight

open IoTBottomUp as base

open cap_motionSensor
open cap_switch


one sig app_SecurityNightLight extends IoTApp {
  
  motion1 : one cap_motionSensor,
  
  state : one cap_state,
  
  switches : some cap_switch,
} {
  rules = r
}



one sig cap_state extends Capability {} {
  attributes = cap_state_attr
}
abstract sig cap_state_attr extends Attribute {}


one sig cap_state_attr_modeStarted extends cap_state_attr {} {
  values = cap_state_attr_modeStarted_val
}

abstract sig cap_state_attr_modeStarted_val extends AttrValue {}
one sig cap_state_attr_modeStarted_val_true extends cap_state_attr_modeStarted_val {}
one sig cap_state_attr_modeStarted_val_false extends cap_state_attr_modeStarted_val {}

one sig cap_state_attr_motionStarted extends cap_state_attr {} {
  values = cap_state_attr_motionStarted_val
}

abstract sig cap_state_attr_motionStarted_val extends AttrValue {}
one sig cap_state_attr_motionStarted_val_true extends cap_state_attr_motionStarted_val {}
one sig cap_state_attr_motionStarted_val_false extends cap_state_attr_motionStarted_val {}


one sig cap_state_attr_thingsOn extends cap_state_attr {} {
  values = cap_state_attr_thingsOn_val
}

abstract sig cap_state_attr_thingsOn_val extends AttrValue {}
one sig cap_state_attr_thingsOn_val_false extends cap_state_attr_thingsOn_val {}
one sig cap_state_attr_thingsOn_val_true extends cap_state_attr_thingsOn_val {}



// application rules base class

abstract sig r extends Rule {}

one sig r0 extends r {}{
  triggers   = r0_trig
  conditions = r0_cond
  commands   = r0_comm
}

abstract sig r0_trig extends Trigger {}

one sig r0_trig0 extends r0_trig {} {
  capabilities = app_SecurityNightLight.motion1
  attribute    = cap_motionSensor_attr_motion
  no value
}


abstract sig r0_cond extends Condition {}

one sig r0_cond0 extends r0_cond {} {
  capabilities = app_SecurityNightLight.motion1
  attribute    = cap_motionSensor_attr_motion
  value        = cap_motionSensor_attr_motion_val_inactive
}
one sig r0_cond1 extends r0_cond {} {
  capabilities = app_SecurityNightLight.motion1
  attribute    = cap_motionSensor_attr_motion
  value        = cap_motionSensor_attr_motion_val - cap_motionSensor_attr_motion_val_active
}

abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
capability   = app_SecurityNightLight.state
  attribute = cap_state_attr_motionStarted
  value = cap_state_attr_motionStarted_val_false
}

one sig r1 extends r {}{
  triggers   = r1_trig
  conditions = r1_cond
  commands   = r1_comm
}

abstract sig r1_trig extends Trigger {}

one sig r1_trig0 extends r1_trig {} {
  capabilities = app_SecurityNightLight.motion1
  attribute    = cap_motionSensor_attr_motion
  no value
}


abstract sig r1_cond extends Condition {}

one sig r1_cond0 extends r1_cond {} {
  capabilities = app_SecurityNightLight.motion1
  attribute    = cap_motionSensor_attr_motion
  value        = cap_motionSensor_attr_motion_val_active
}

abstract sig r1_comm extends Command {}

one sig r1_comm0 extends r1_comm {} {
  capability   = app_SecurityNightLight.state
  attribute = cap_state_attr_motionStarted
  value = cap_state_attr_motionStarted_val_true
}


one sig r3 extends r {}{
  triggers   = r3_trig
  conditions = r3_cond
  commands   = r3_comm
}

abstract sig r3_trig extends Trigger {}

one sig r3_trig0 extends r3_trig {} {
  capabilities = app_SecurityNightLight.motion1
  attribute    = cap_motionSensor_attr_motion
  no value
}


abstract sig r3_cond extends Condition {}

one sig r3_cond0 extends r3_cond {} {
  capabilities = app_SecurityNightLight.motion1
  attribute    = cap_motionSensor_attr_motion
  value        = cap_motionSensor_attr_motion_val_active
}

abstract sig r3_comm extends Command {}

one sig r3_comm0 extends r3_comm {} {
  capability   = app_SecurityNightLight.state
  attribute = cap_state_attr_thingsOn
  value = cap_state_attr_thingsOn_val_true
}
one sig r3_comm1 extends r3_comm {} {
  capability   = app_SecurityNightLight.switches
  attribute = cap_switch_attr_switch
  value = cap_switch_attr_switch_val_on
}







