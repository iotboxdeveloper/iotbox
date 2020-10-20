module app_B5_App1

open IoTBottomUp as base

open cap_motionSensor
open cap_switch


one sig app_B5_App1 extends IoTApp {
  
  motion1 : one cap_motionSensor,
  
  bulb : some cap_switch,
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
  capabilities = app_B5_App1.motion1
  attribute    = cap_motionSensor_attr_motion
  no value
}


abstract sig r0_cond extends Condition {}

one sig r0_cond0 extends r0_cond {} {
  capabilities = app_B5_App1.motion1
  attribute    = cap_motionSensor_attr_motion
  value        = cap_motionSensor_attr_motion_val_active
}

abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_B5_App1.bulb
  attribute = cap_switch_attr_switch
  value = cap_switch_attr_switch_val_on
}



