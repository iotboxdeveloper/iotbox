module app_ID7ConflictTimeandPresenceSensor

open IoTBottomUp as base

open cap_switch
open cap_presenceSensor


one sig app_ID7ConflictTimeandPresenceSensor extends IoTApp {
  
  person : some cap_presenceSensor,
  
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
  capabilities = app_ID7ConflictTimeandPresenceSensor.person
  attribute    = cap_presenceSensor_attr_presence
  no value
}


abstract sig r0_cond extends Condition {}

one sig r0_cond0 extends r0_cond {} {
  capabilities = app_ID7ConflictTimeandPresenceSensor.person
  attribute    = cap_presenceSensor_attr_presence
  value        = cap_presenceSensor_attr_presence_val_not_present
}

abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_ID7ConflictTimeandPresenceSensor.switches
  attribute = cap_switch_attr_switch
  value = cap_switch_attr_switch_val_off
}

one sig r1 extends r {}{
  no triggers
  conditions = r1_cond
  commands   = r1_comm
}




abstract sig r1_cond extends Condition {}


abstract sig r1_comm extends Command {}

one sig r1_comm0 extends r1_comm {} {
  capability   = app_ID7ConflictTimeandPresenceSensor.switches
  attribute = cap_switch_attr_switch
  value = cap_switch_attr_switch_val_off
}

one sig r2 extends r {}{
  no triggers
  conditions = r2_cond
  commands   = r2_comm
}




abstract sig r2_cond extends Condition {}


abstract sig r2_comm extends Command {}

one sig r2_comm0 extends r2_comm {} {
  capability   = app_ID7ConflictTimeandPresenceSensor.switches
  attribute = cap_switch_attr_switch
  value = cap_switch_attr_switch_val_on
}

one sig r3 extends r {}{
  triggers   = r3_trig
  conditions = r3_cond
  commands   = r3_comm
}

abstract sig r3_trig extends Trigger {}

one sig r3_trig0 extends r3_trig {} {
  capabilities = app_ID7ConflictTimeandPresenceSensor.person
  attribute    = cap_presenceSensor_attr_presence
  no value
}


abstract sig r3_cond extends Condition {}

one sig r3_cond0 extends r3_cond {} {
  capabilities = app_ID7ConflictTimeandPresenceSensor.person
  attribute    = cap_presenceSensor_attr_presence
  value        = cap_presenceSensor_attr_presence_val - cap_presenceSensor_attr_presence_val_not_present
}

abstract sig r3_comm extends Command {}

one sig r3_comm0 extends r3_comm {} {
  capability   = app_ID7ConflictTimeandPresenceSensor.switches
  attribute = cap_switch_attr_switch
  value = cap_switch_attr_switch_val_on
}



