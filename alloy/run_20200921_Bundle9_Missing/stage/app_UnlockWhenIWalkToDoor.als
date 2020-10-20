module app_UnlockWhenIWalkToDoor

open IoTBottomUp as base

open cap_motionSensor
open cap_location
open cap_lock
open cap_presenceSensor


one sig app_UnlockWhenIWalkToDoor extends IoTApp {
  
  state : one cap_state,
  
  location : one cap_location,
  
  targetmode : one cap_location_attr_mode_val,
  
  presence1 : some cap_presenceSensor,
  
  motion1 : lone cap_motionSensor,
  
  lock1 : some cap_lock,
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
one sig cap_state_attr_mode_val_targetmode extends cap_state_attr_mode_val {}



// application rules base class

abstract sig r extends Rule {}

one sig r0 extends r {}{
  triggers   = r0_trig
  conditions = r0_cond
  commands   = r0_comm
}

abstract sig r0_trig extends Trigger {}

one sig r0_trig0 extends r0_trig {} {
  capabilities = app_UnlockWhenIWalkToDoor.motion1
  attribute    = cap_motionSensor_attr_motion
  no value
}


abstract sig r0_cond extends Condition {}

one sig r0_cond0 extends r0_cond {} {
  capabilities = app_UnlockWhenIWalkToDoor.motion1
  attribute    = cap_motionSensor_attr_motion
  value        = cap_motionSensor_attr_motion_val_active
}

abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_UnlockWhenIWalkToDoor.lock1
  attribute = cap_lock_attr_lock
  value = cap_lock_attr_lock_val_unlock
}
one sig r0_comm1 extends r0_comm {} {
  capability   = app_UnlockWhenIWalkToDoor.location
  attribute = cap_location_attr_mode
  value        = app_UnlockWhenIWalkToDoor.targetmode
}



