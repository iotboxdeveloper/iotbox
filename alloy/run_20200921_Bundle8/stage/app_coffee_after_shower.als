module app_coffee_after_shower

open IoTBottomUp as base

open cap_switch
open cap_relativeHumidityMeasurement


one sig app_coffee_after_shower extends IoTApp {
  
  coffee : one cap_switch,
  
  bathroom : one cap_relativeHumidityMeasurement,
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
  capabilities = app_coffee_after_shower.bathroom
  attribute    = cap_relativeHumidityMeasurement_attr_humidity
  no value
}


abstract sig r0_cond extends Condition {}


abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_coffee_after_shower.coffee
  attribute = cap_switch_attr_switch
  value = cap_switch_attr_switch_val_on
}



