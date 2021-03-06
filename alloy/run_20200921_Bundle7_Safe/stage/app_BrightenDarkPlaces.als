module app_BrightenDarkPlaces

open IoTBottomUp as base

open cap_switch
open cap_illuminanceMeasurement
open cap_contactSensor


one sig app_BrightenDarkPlaces extends IoTApp {
  
  contact1 : one cap_contactSensor,
  
  switch1 : one cap_switch,
  
  luminance1 : one cap_illuminanceMeasurement,
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
  capabilities = app_BrightenDarkPlaces.contact1
  attribute    = cap_contactSensor_attr_contact
  value        = cap_contactSensor_attr_contact_val_open
}


abstract sig r0_cond extends Condition {}


abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_BrightenDarkPlaces.switch1
  attribute = cap_switch_attr_switch
  value = cap_switch_attr_switch_val_on
}



