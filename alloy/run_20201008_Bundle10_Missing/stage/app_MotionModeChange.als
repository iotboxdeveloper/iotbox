module app_MotionModeChange

open IoTBottomUp as base
open cap_runIn
open cap_now

open cap_motionSensor
open cap_switch
open cap_location

open cap_userInput

one sig app_MotionModeChange extends IoTApp {
  location : one cap_location,
  
  motionSensors : one cap_motionSensor,
  
  switches : some cap_switch,
  

  
  state : one cap_state,

  newMode : one cap_location_attr_mode_val,
} {
  rules = r

}


one sig cap_state extends cap_runIn {} {
  attributes = cap_state_attr + cap_runIn_attr
}
abstract sig cap_state_attr extends Attribute {}


one sig cap_state_attr_modeStartTime extends cap_state_attr {} {
  values = cap_state_attr_modeStartTime_val
}

abstract sig cap_state_attr_modeStartTime_val extends AttrValue {}
one sig cap_state_attr_modeStartTime_val_0 extends cap_state_attr_modeStartTime_val {}



abstract sig r extends Rule {}

one sig r0 extends r {}{
  triggers   = r0_trig
  conditions = r0_cond
  commands   = r0_comm
}

abstract sig r0_trig extends Trigger {}

one sig r0_trig0 extends r0_trig {} {
  capabilities = app_MotionModeChange.motionSensors
  attribute    = cap_motionSensor_attr_motion
  value        = cap_motionSensor_attr_motion_val_active
}


abstract sig r0_cond extends Condition {}

one sig r0_cond0 extends r0_cond {} {
  capabilities = app_MotionModeChange.location
  attribute    = cap_location_attr_mode
  value        = cap_location_attr_mode_val - cap_location_attr_mode_val_Home
}

abstract sig r0_comm extends Command {}


one sig r0_comm1 extends r0_comm {} {
  capability   = app_MotionModeChange.switches
  attribute    = cap_switch_attr_switch
  value        = cap_switch_attr_switch_val_on
}




