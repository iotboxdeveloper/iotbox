module app_ID12AlarmSoundsTurnOnLights_Safe

open IoTBottomUp as base

open cap_lock
open cap_alarm
open cap_switch
open cap_smokeDetector


one sig app_ID12AlarmSoundsTurnOnLights_Safe extends IoTApp {
  
  smoke : one cap_smokeDetector,
  
  lock : one cap_lock,
  
  mySwitch : set cap_switch,
  
  alarm : one cap_alarm,
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
  capabilities = app_ID12AlarmSoundsTurnOnLights_Safe.smoke
  attribute    = cap_smokeDetector_attr_smoke
  no value
}


abstract sig r0_cond extends Condition {}

one sig r0_cond0 extends r0_cond {} {
  capabilities = app_ID12AlarmSoundsTurnOnLights_Safe.smoke
  attribute    = cap_smokeDetector_attr_smoke
  value        = cap_smokeDetector_attr_smoke_val - cap_smokeDetector_attr_smoke_val_detected
}
one sig r0_cond1 extends r0_cond {} {
  capabilities = app_ID12AlarmSoundsTurnOnLights_Safe.smoke
  attribute    = cap_smokeDetector_attr_smoke
  value        = cap_smokeDetector_attr_smoke_val_clear
}

abstract sig r0_comm extends Command {}

one sig r0_comm0 extends r0_comm {} {
  capability   = app_ID12AlarmSoundsTurnOnLights_Safe.alarm
  attribute = cap_alarm_attr_alarm
  value = cap_alarm_attr_alarm_val_off
}

one sig r1 extends r {}{
  triggers   = r1_trig
  conditions = r1_cond
  commands   = r1_comm
}

abstract sig r1_trig extends Trigger {}

one sig r1_trig0 extends r1_trig {} {
  capabilities = app_ID12AlarmSoundsTurnOnLights_Safe.smoke
  attribute    = cap_smokeDetector_attr_smoke
  no value
}


abstract sig r1_cond extends Condition {}

one sig r1_cond0 extends r1_cond {} {
  capabilities = app_ID12AlarmSoundsTurnOnLights_Safe.smoke
  attribute    = cap_smokeDetector_attr_smoke
  value        = cap_smokeDetector_attr_smoke_val_detected
}

abstract sig r1_comm extends Command {}

one sig r1_comm0 extends r1_comm {} {
  capability   = app_ID12AlarmSoundsTurnOnLights_Safe.alarm
  attribute = cap_alarm_attr_alarm
  value = cap_alarm_attr_alarm_val_strobe
}
one sig r1_comm1 extends r1_comm {} {
  capability   = app_ID12AlarmSoundsTurnOnLights_Safe.mySwitch
  attribute = cap_switch_attr_switch
  value = cap_switch_attr_switch_val_on
}
one sig r1_comm2 extends r1_comm {} {
  capability   = app_ID12AlarmSoundsTurnOnLights_Safe.lock
  attribute = cap_lock_attr_lock
  value = cap_lock_attr_lock_val_unlock
}



