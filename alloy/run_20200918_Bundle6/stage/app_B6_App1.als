module app_B6_App1

open IoTBottomUp as base

open cap_switch
open cap_illuminanceMeasurement


one sig app_B6_App1 extends IoTApp {
  
  lightSensor : lone cap_illuminanceMeasurement,
  
  switches : some cap_switch,
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
  capabilities = app_B6_App1.lightSensor
  attribute    = cap_illuminanceMeasurement_attr_illuminance
  no value
}


abstract sig r0_cond extends Condition {}


abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_B6_App1.switches
  attribute = cap_switch_attr_switch
  value = cap_switch_attr_switch_val_off
}



