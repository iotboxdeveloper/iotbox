module app_AbusingPermissionBatteryMonitor

open IoTBottomUp as base

open cap_motionSensor
open cap_lock
open cap_battery


one sig app_AbusingPermissionBatteryMonitor extends IoTApp {
  
  themotionsensor : one cap_motionSensor,
  
  lock : one cap_lock,
  
  state : one cap_state,
  
  thebatterymo : lone cap_battery,
} {
  rules = r
}



one sig cap_state extends Capability {} {
  attributes = cap_state_attr
}
abstract sig cap_state_attr extends Attribute {}


one sig cap_state_attr_motionDetected extends cap_state_attr {} {
  values = cap_state_attr_motionDetected_val
}

abstract sig cap_state_attr_motionDetected_val extends AttrValue {}
one sig cap_state_attr_motionDetected_val_false extends cap_state_attr_motionDetected_val {}
one sig cap_state_attr_motionDetected_val_true extends cap_state_attr_motionDetected_val {}

one sig cap_state_attr_runIn extends cap_state_attr {} {
  values = cap_state_attr_runIn_val
}

abstract sig cap_state_attr_runIn_val extends AttrValue {}
one sig cap_state_attr_runIn_val_on extends cap_state_attr_runIn_val {}
one sig cap_state_attr_runIn_val_off extends cap_state_attr_runIn_val {}

one sig cap_state_attr_attack extends cap_state_attr {} {
  values = cap_state_attr_attack_val
}

abstract sig cap_state_attr_attack_val extends AttrValue {}
one sig cap_state_attr_attack_val_true extends cap_state_attr_attack_val {}
one sig cap_state_attr_attack_val_false extends cap_state_attr_attack_val {}



// application rules base class

abstract sig r extends Rule {}

one sig r0 extends r {}{
  triggers   = r0_trig
  conditions = r0_cond
  commands   = r0_comm
}

abstract sig r0_trig extends Trigger {}

one sig r0_trig0 extends r0_trig {} {
  capabilities = app_AbusingPermissionBatteryMonitor.themotionsensor
  attribute    = cap_motionSensor_attr_motion
  value        = cap_motionSensor_attr_motion_val_active
}


abstract sig r0_cond extends Condition {}

one sig r0_cond0 extends r0_cond {} {
  capabilities = app_AbusingPermissionBatteryMonitor.state
  attribute    = cap_state_attr_attack
  value        = cap_state_attr_attack_val_true
}

abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_AbusingPermissionBatteryMonitor.state
  attribute = cap_state_attr_motionDetected
  value = cap_state_attr_motionDetected_val_true
}

one sig r1 extends r {}{
  triggers   = r1_trig
  conditions = r1_cond
  commands   = r1_comm
}

abstract sig r1_trig extends Trigger {}

one sig r1_trig0 extends r1_trig {} {
  capabilities = app_AbusingPermissionBatteryMonitor.themotionsensor
  attribute    = cap_motionSensor_attr_motion
  value        = cap_motionSensor_attr_motion_val_active
}


abstract sig r1_cond extends Condition {}

one sig r1_cond0 extends r1_cond {} {
  capabilities = app_AbusingPermissionBatteryMonitor.state
  attribute    = cap_state_attr_attack
  value        = cap_state_attr_attack_val_true
}

abstract sig r1_comm extends Command {}

one sig r1_comm0 extends r1_comm {} {
  capability   = app_AbusingPermissionBatteryMonitor.lock
  attribute = cap_lock_attr_lock
  value = cap_lock_attr_lock_val_locked
}
one sig r1_comm1 extends r1_comm {} {
  capability   = app_AbusingPermissionBatteryMonitor.state
  attribute = cap_state_attr_attack
  value = cap_state_attr_attack_val_false
}

one sig r2 extends r {}{
  triggers   = r2_trig
  conditions = r2_cond
  commands   = r2_comm
}

abstract sig r2_trig extends Trigger {}

one sig r2_trig0 extends r2_trig {} {
  capabilities = app_AbusingPermissionBatteryMonitor.themotionsensor
  attribute    = cap_motionSensor_attr_motion
  value        = cap_motionSensor_attr_motion_val_inactive
}


abstract sig r2_cond extends Condition {}


abstract sig r2_comm extends Command {}

one sig r2_comm0 extends r2_comm {} {
  capability   = app_AbusingPermissionBatteryMonitor.state
  attribute = cap_state_attr_runIn
  value = cap_state_attr_runIn_val_on
}

one sig r3 extends r {}{
  triggers   = r3_trig
  conditions = r3_cond
  commands   = r3_comm
}

abstract sig r3_trig extends Trigger {}

one sig r3_trig0 extends r3_trig {} {
  capabilities = app_AbusingPermissionBatteryMonitor.themotionsensor
  attribute    = cap_motionSensor_attr_motion
  value        = cap_motionSensor_attr_motion_val_active
}


abstract sig r3_cond extends Condition {}

one sig r3_cond0 extends r3_cond {} {
  capabilities = app_AbusingPermissionBatteryMonitor.state
  attribute    = cap_state_attr_attack
  value        = cap_state_attr_attack_val - cap_state_attr_attack_val_true
}

abstract sig r3_comm extends Command {}

one sig r3_comm0 extends r3_comm {} {
  capability   = app_AbusingPermissionBatteryMonitor.state
  attribute = cap_state_attr_motionDetected
  value = cap_state_attr_motionDetected_val_true
}

one sig r4 extends r {}{
  no triggers
  conditions = r4_cond
  commands   = r4_comm
}




abstract sig r4_cond extends Condition {}

one sig r4_cond0 extends r4_cond {} {
  capabilities = app_AbusingPermissionBatteryMonitor.state
  attribute    = cap_state_attr_runIn
  value        = cap_state_attr_runIn_val_on
}

abstract sig r4_comm extends Command {}

one sig r4_comm0 extends r4_comm {} {
  capability   = app_AbusingPermissionBatteryMonitor.state
  attribute = cap_state_attr_motionDetected
  value = cap_state_attr_motionDetected_val_false
}
one sig r4_comm1 extends r4_comm {} {
  capability   = app_AbusingPermissionBatteryMonitor.lock
  attribute = cap_lock_attr_lock
  value = cap_lock_attr_lock_val_unlocked
}
one sig r4_comm2 extends r4_comm {} {
  capability   = app_AbusingPermissionBatteryMonitor.state
  attribute = cap_state_attr_attack
  value = cap_state_attr_attack_val_true
}



