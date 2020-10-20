module assertions
open IoTBottomUp as base
open cap_fanSpeed
open cap_robotCleanerMovement
open cap_momentary
open cap_button
open cap_runIn
open cap_motionSensor
open cap_powerMeter
open cap_switchLevel
open cap_ovenMode
open cap_presenceSensor
open cap_mediaInputSource
open cap_powerSource
open cap_userInput
open cap_dishwasherMode
open cap_rapidCooling
open cap_ovenSetpoint
open cap_switch
open cap_alarm
open cap_location
open cap_thermostatCoolingSetpoint
open cap_valve
open cap_infraredLevel
open cap_odorSensor
open cap_mediaPlaybackShuffle
open cap_now
open cap_contactSensor
open cap_battery
open cap_temperatureMeasurement
open cap_audioVolume
open cap_waterSensor
open cap_thermostatHeatingSetpoint
open cap_lock
open cap_soundSensor
open cap_filterStatus
open cap_energyMeter
open cap_mediaPlaybackRepeat
open cap_illuminanceMeasurement
open cap_robotCleanerCleaningMode
open cap_tvChannel
open cap_accelerationSensor
open cap_signalStrength
open cap_dustSensor
open cap_robotCleanerTurboMode
open cap_app
open cap_carbonMonoxideDetector
open cap_formaldehydeMeasurement
open cap_voltageMeasurement
open cap_carbonDioxideMeasurement
open cap_airQualitySensor
open cap_washerOperatingState
open cap_carbonMonoxideMeasurement
open cap_relativeHumidityMeasurement
open cap_refrigerationSetpoint
open cap_equivalentCarbonDioxideMeasurement
open cap_tamperAlert
open cap_ultravioletIndex
open cap_tone
open cap_colorTemperature
open cap_windowShade
open cap_thermostatMode
open cap_threeAxis
open cap_imageCapture
open cap_thermostatOperatingState
open cap_thermostat
open cap_colorControl
open cap_dryerOperatingState
open cap_thermostatFanMode
open cap_thermostatSetpoint
open cap_musicPlayer
open cap_mediaPlayback
open cap_airConditionerMode
open cap_garageDoorControl
open cap_doorControl
open cap_audioMute
open cap_dishwasherOperatingState
open cap_ovenOperatingState
open cap_washerMode
open cap_dryerMode
open cap_smokeDetector
open cap_activityLightingMode
open app_BrightenDarkPlaces
open app_coffee_after_shower
open app_WholeHouseFan
open app_GoodNight
open app_MotionModeChange
open app_LockDoorWhenHomeModeSet
open app_LightFollowsMeIfThereIsNoLight
open app_AbusingPermissionBatteryMonitor

assert P__0 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__0
// P__0:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__1 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__1
// P__1:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__2 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__2
// P__2:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__3 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__3
// P__3:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__4 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__4
// P__4:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__5 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__5
// P__5:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__6 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__6
// P__6:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_state_attr_home,cap_state_attr_home_val_true


assert P__7 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__7
// P__7:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__8 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__8
// P__8:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__9 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__9
// P__9:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__10 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__10
// P__10:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__11 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__11
// P__11:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__12 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__12
// P__12:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__13 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__13
// P__13:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__14 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__14
// P__14:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__15 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__15
// P__15:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__16 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__16
// P__16:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__17 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__17
// P__17:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__18 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__18
// P__18:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__19 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__19
// P__19:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__20 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_open
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__20
// P__20:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__21 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__21
// P__21:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__22 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__22
// P__22:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__23 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__23
// P__23:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__24 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__24
// P__24:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__25 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__25
// P__25:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__26 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__26
// P__26:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__27 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__27
// P__27:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_state_attr_home,cap_state_attr_home_val_true


assert P__28 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__28
// P__28:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__29 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__29
// P__29:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__30 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__30
// P__30:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__31 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__31
// P__31:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__32 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__32
// P__32:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__33 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__33
// P__33:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__34 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__34
// P__34:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__35 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__35
// P__35:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__36 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__36
// P__36:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__37 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__37
// P__37:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__38 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__38
// P__38:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__39 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__39
// P__39:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__40 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__40
// P__40:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__41 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_contactSensor_attr_contact
    action.value     = cap_contactSensor_attr_contact_val_closed
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__41
// P__41:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__42 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__42
// P__42:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__43 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__43
// P__43:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__44 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__44
// P__44:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__45 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__45
// P__45:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__46 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__46
// P__46:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__47 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__47
// P__47:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__48 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__48
// P__48:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_state_attr_home,cap_state_attr_home_val_true


assert P__49 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__49
// P__49:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__50 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__50
// P__50:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__51 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__51
// P__51:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__52 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__52
// P__52:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__53 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__53
// P__53:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__54 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__54
// P__54:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__55 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__55
// P__55:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__56 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__56
// P__56:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__57 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__57
// P__57:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__58 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__58
// P__58:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__59 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__59
// P__59:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__60 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__60
// P__60:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__61 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__61
// P__61:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__62 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__62
// P__62:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__63 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__63
// P__63:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__64 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__64
// P__64:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__65 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__65
// P__65:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__66 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__66
// P__66:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__67 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__67
// P__67:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__68 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__68
// P__68:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__69 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__69
// P__69:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_state_attr_home,cap_state_attr_home_val_true


assert P__70 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__70
// P__70:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__71 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__71
// P__71:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__72 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__72
// P__72:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__73 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__73
// P__73:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__74 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__74
// P__74:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__75 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__75
// P__75:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__76 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__76
// P__76:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__77 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__77
// P__77:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__78 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__78
// P__78:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__79 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__79
// P__79:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__80 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__80
// P__80:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__81 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__81
// P__81:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__82 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__82
// P__82:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__83 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__83
// P__83:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__84 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__84
// P__84:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__85 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__85
// P__85:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__86 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__86
// P__86:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__87 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__87
// P__87:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__88 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__88
// P__88:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__89 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__89
// P__89:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__90 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__90
// P__90:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_state_attr_home,cap_state_attr_home_val_true


assert P__91 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__91
// P__91:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__92 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__92
// P__92:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__93 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__93
// P__93:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__94 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__94
// P__94:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__95 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__95
// P__95:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__96 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__96
// P__96:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__97 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__97
// P__97:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__98 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__98
// P__98:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__99 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__99
// P__99:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__100 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__100
// P__100:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__101 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__101
// P__101:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__102 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__102
// P__102:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__103 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__103
// P__103:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__104 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_relativeHumidityMeasurement_attr_humidity
    action.value     = cap_relativeHumidityMeasurement_attr_humidity_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__104
// P__104:cap_relativeHumidityMeasurement_attr_humidity,cap_relativeHumidityMeasurement_attr_humidity_val0,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__105 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__105
// P__105:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__106 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__106
// P__106:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__107 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__107
// P__107:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__108 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__108
// P__108:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__109 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__109
// P__109:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__110 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__110
// P__110:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__111 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__111
// P__111:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_state_attr_home,cap_state_attr_home_val_true


assert P__112 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__112
// P__112:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__113 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__113
// P__113:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__114 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__114
// P__114:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__115 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__115
// P__115:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__116 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__116
// P__116:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__117 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__117
// P__117:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__118 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__118
// P__118:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__119 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__119
// P__119:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__120 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__120
// P__120:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__121 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__121
// P__121:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__122 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__122
// P__122:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__123 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__123
// P__123:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__124 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__124
// P__124:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__125 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_high
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__125
// P__125:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_high,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__126 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__126
// P__126:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__127 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__127
// P__127:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__128 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__128
// P__128:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__129 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__129
// P__129:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__130 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__130
// P__130:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__131 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__131
// P__131:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__132 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__132
// P__132:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_state_attr_home,cap_state_attr_home_val_true


assert P__133 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__133
// P__133:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__134 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__134
// P__134:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__135 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__135
// P__135:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__136 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__136
// P__136:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__137 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__137
// P__137:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__138 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__138
// P__138:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__139 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__139
// P__139:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__140 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__140
// P__140:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__141 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__141
// P__141:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__142 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__142
// P__142:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__143 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__143
// P__143:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__144 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__144
// P__144:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__145 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__145
// P__145:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__146 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_eco
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__146
// P__146:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_eco,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__147 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__147
// P__147:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__148 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__148
// P__148:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__149 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__149
// P__149:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__150 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__150
// P__150:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__151 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__151
// P__151:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__152 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__152
// P__152:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__153 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__153
// P__153:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_state_attr_home,cap_state_attr_home_val_true


assert P__154 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__154
// P__154:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__155 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__155
// P__155:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__156 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__156
// P__156:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__157 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__157
// P__157:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__158 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__158
// P__158:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__159 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__159
// P__159:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__160 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__160
// P__160:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__161 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__161
// P__161:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__162 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__162
// P__162:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__163 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__163
// P__163:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__164 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__164
// P__164:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__165 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__165
// P__165:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__166 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__166
// P__166:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__167 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_med
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__167
// P__167:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_med,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__168 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__168
// P__168:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__169 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__169
// P__169:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__170 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__170
// P__170:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__171 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__171
// P__171:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__172 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__172
// P__172:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__173 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__173
// P__173:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__174 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__174
// P__174:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_state_attr_home,cap_state_attr_home_val_true


assert P__175 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__175
// P__175:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__176 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__176
// P__176:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__177 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__177
// P__177:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__178 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__178
// P__178:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__179 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__179
// P__179:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__180 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__180
// P__180:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__181 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__181
// P__181:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__182 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__182
// P__182:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__183 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__183
// P__183:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__184 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__184
// P__184:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__185 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__185
// P__185:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__186 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__186
// P__186:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__187 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__187
// P__187:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__188 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_cool
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__188
// P__188:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_cool,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__189 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__189
// P__189:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__190 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__190
// P__190:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__191 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__191
// P__191:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__192 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__192
// P__192:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__193 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__193
// P__193:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__194 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__194
// P__194:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__195 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__195
// P__195:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_state_attr_home,cap_state_attr_home_val_true


assert P__196 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__196
// P__196:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__197 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__197
// P__197:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__198 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__198
// P__198:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__199 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__199
// P__199:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__200 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__200
// P__200:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__201 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__201
// P__201:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__202 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__202
// P__202:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__203 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__203
// P__203:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__204 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__204
// P__204:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__205 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__205
// P__205:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__206 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__206
// P__206:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__207 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__207
// P__207:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__208 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__208
// P__208:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__209 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_thermostatMode_attr_thermostatMode
    action.value     = cap_thermostatMode_attr_thermostatMode_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__209
// P__209:cap_thermostatMode_attr_thermostatMode,cap_thermostatMode_attr_thermostatMode_val_off,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__210 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__210
// P__210:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__211 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__211
// P__211:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__212 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__212
// P__212:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__213 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__213
// P__213:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__214 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__214
// P__214:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__215 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__215
// P__215:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__216 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__216
// P__216:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_state_attr_home,cap_state_attr_home_val_true


assert P__217 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__217
// P__217:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__218 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__218
// P__218:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__219 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__219
// P__219:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__220 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__220
// P__220:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__221 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__221
// P__221:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__222 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__222
// P__222:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__223 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__223
// P__223:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__224 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__224
// P__224:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__225 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__225
// P__225:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__226 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__226
// P__226:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__227 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__227
// P__227:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__228 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__228
// P__228:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__229 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__229
// P__229:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__230 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_temperatureMeasurement_attr_temperature
    action.value     = cap_temperatureMeasurement_attr_temperature_val_low
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__230
// P__230:cap_temperatureMeasurement_attr_temperature,cap_temperatureMeasurement_attr_temperature_val_low,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__231 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__231
// P__231:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__232 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__232
// P__232:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__233 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__233
// P__233:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__234 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__234
// P__234:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__235 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__235
// P__235:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__236 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__236
// P__236:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__237 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__237
// P__237:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_state_attr_home,cap_state_attr_home_val_true


assert P__238 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__238
// P__238:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__239 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__239
// P__239:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__240 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__240
// P__240:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__241 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__241
// P__241:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__242 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__242
// P__242:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__243 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__243
// P__243:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__244 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__244
// P__244:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__245 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__245
// P__245:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__246 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__246
// P__246:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__247 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__247
// P__247:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__248 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__248
// P__248:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__249 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__249
// P__249:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__250 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__250
// P__250:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__251 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_active
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__251
// P__251:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__252 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__252
// P__252:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__253 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__253
// P__253:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__254 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__254
// P__254:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__255 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__255
// P__255:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__256 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__256
// P__256:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__257 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__257
// P__257:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__258 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__258
// P__258:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_state_attr_home,cap_state_attr_home_val_true


assert P__259 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__259
// P__259:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__260 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__260
// P__260:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__261 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__261
// P__261:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__262 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__262
// P__262:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__263 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__263
// P__263:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__264 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__264
// P__264:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__265 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__265
// P__265:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__266 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__266
// P__266:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__267 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__267
// P__267:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__268 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__268
// P__268:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__269 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__269
// P__269:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__270 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__270
// P__270:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__271 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__271
// P__271:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__272 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_motionSensor_attr_motion
    action.value     = cap_motionSensor_attr_motion_val_inactive
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__272
// P__272:cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__273 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__273
// P__273:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__274 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__274
// P__274:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__275 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__275
// P__275:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__276 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__276
// P__276:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__277 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__277
// P__277:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__278 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__278
// P__278:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__279 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__279
// P__279:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_state_attr_home,cap_state_attr_home_val_true


assert P__280 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__280
// P__280:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__281 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__281
// P__281:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__282 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__282
// P__282:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__283 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__283
// P__283:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__284 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__284
// P__284:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__285 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__285
// P__285:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__286 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__286
// P__286:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__287 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__287
// P__287:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__288 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__288
// P__288:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__289 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__289
// P__289:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__290 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__290
// P__290:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__291 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__291
// P__291:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__292 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__292
// P__292:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__293 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_locked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__293
// P__293:cap_lock_attr_lock,cap_lock_attr_lock_val_locked,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__294 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__294
// P__294:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__295 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__295
// P__295:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__296 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__296
// P__296:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__297 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__297
// P__297:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__298 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__298
// P__298:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__299 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__299
// P__299:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__300 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__300
// P__300:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_state_attr_home,cap_state_attr_home_val_true


assert P__301 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__301
// P__301:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__302 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__302
// P__302:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__303 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__303
// P__303:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__304 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__304
// P__304:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__305 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__305
// P__305:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__306 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__306
// P__306:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__307 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__307
// P__307:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__308 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__308
// P__308:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__309 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__309
// P__309:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__310 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__310
// P__310:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__311 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__311
// P__311:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__312 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__312
// P__312:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__313 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__313
// P__313:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__314 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked_with_timeout
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__314
// P__314:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__315 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__315
// P__315:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__316 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__316
// P__316:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__317 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__317
// P__317:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__318 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__318
// P__318:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__319 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__319
// P__319:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__320 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__320
// P__320:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__321 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__321
// P__321:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_state_attr_home,cap_state_attr_home_val_true


assert P__322 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__322
// P__322:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__323 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__323
// P__323:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__324 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__324
// P__324:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__325 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__325
// P__325:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__326 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__326
// P__326:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__327 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__327
// P__327:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__328 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__328
// P__328:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__329 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__329
// P__329:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__330 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__330
// P__330:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__331 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__331
// P__331:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__332 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__332
// P__332:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__333 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__333
// P__333:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__334 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__334
// P__334:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__335 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_on
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__335
// P__335:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__336 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__336
// P__336:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__337 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__337
// P__337:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__338 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__338
// P__338:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__339 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__339
// P__339:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__340 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__340
// P__340:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__341 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__341
// P__341:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__342 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__342
// P__342:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_state_attr_home,cap_state_attr_home_val_true


assert P__343 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__343
// P__343:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__344 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__344
// P__344:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__345 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__345
// P__345:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__346 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__346
// P__346:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__347 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__347
// P__347:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__348 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__348
// P__348:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__349 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__349
// P__349:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__350 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__350
// P__350:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__351 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__351
// P__351:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__352 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__352
// P__352:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__353 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__353
// P__353:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__354 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__354
// P__354:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__355 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__355
// P__355:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__356 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_runIn_attr_runIn
    action.value     = cap_runIn_attr_runIn_val_off
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__356
// P__356:cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__357 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__357
// P__357:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__358 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__358
// P__358:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__359 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__359
// P__359:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__360 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__360
// P__360:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__361 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__361
// P__361:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__362 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__362
// P__362:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__363 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__363
// P__363:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_state_attr_home,cap_state_attr_home_val_true


assert P__364 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__364
// P__364:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__365 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__365
// P__365:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__366 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__366
// P__366:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__367 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__367
// P__367:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__368 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__368
// P__368:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__369 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__369
// P__369:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__370 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__370
// P__370:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__371 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__371
// P__371:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__372 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__372
// P__372:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__373 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__373
// P__373:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__374 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__374
// P__374:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__375 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__375
// P__375:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__376 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__376
// P__376:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__377 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = cap_illuminanceMeasurement_attr_illuminance_val0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__377
// P__377:cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__378 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__378
// P__378:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__379 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__379
// P__379:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__380 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__380
// P__380:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__381 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__381
// P__381:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__382 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__382
// P__382:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__383 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__383
// P__383:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__384 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__384
// P__384:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_state_attr_home,cap_state_attr_home_val_true


assert P__385 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__385
// P__385:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__386 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__386
// P__386:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__387 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__387
// P__387:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__388 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__388
// P__388:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__389 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__389
// P__389:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__390 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__390
// P__390:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__391 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__391
// P__391:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__392 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__392
// P__392:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__393 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__393
// P__393:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__394 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__394
// P__394:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__395 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__395
// P__395:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__396 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__396
// P__396:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__397 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__397
// P__397:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__398 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_0
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__398
// P__398:cap_illuminanceMeasurement_attr_illuminance,range_0,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__399 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__399
// P__399:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__400 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__400
// P__400:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__401 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__401
// P__401:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__402 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__402
// P__402:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__403 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__403
// P__403:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__404 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__404
// P__404:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__405 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__405
// P__405:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_state_attr_home,cap_state_attr_home_val_true


assert P__406 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__406
// P__406:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__407 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__407
// P__407:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__408 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__408
// P__408:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__409 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__409
// P__409:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__410 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__410
// P__410:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__411 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__411
// P__411:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__412 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__412
// P__412:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__413 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__413
// P__413:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__414 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__414
// P__414:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__415 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__415
// P__415:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__416 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__416
// P__416:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__417 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__417
// P__417:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__418 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__418
// P__418:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__419 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_illuminanceMeasurement_attr_illuminance
    action.value     = range_1
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__419
// P__419:cap_illuminanceMeasurement_attr_illuminance,range_1,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false


assert P__420 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_on
            }
        )
        }
    }) 
  }
}
check P__420
// P__420:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_switch_attr_switch,cap_switch_attr_switch_val_on


assert P__421 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_switch_attr_switch
            action'.value     = cap_switch_attr_switch_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_switch_attr_switch
                action''.value     = cap_switch_attr_switch_val_off
            }
        )
        }
    }) 
  }
}
check P__421
// P__421:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_switch_attr_switch,cap_switch_attr_switch_val_off


assert P__422 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_true
            }
        )
        }
    }) 
  }
}
check P__422
// P__422:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_true


assert P__423 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_fanRunning
            action'.value     = cap_state_attr_fanRunning_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_fanRunning
                action''.value     = cap_state_attr_fanRunning_val_false
            }
        )
        }
    }) 
  }
}
check P__423
// P__423:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_state_attr_fanRunning,cap_state_attr_fanRunning_val_false


assert P__424 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = app_MotionModeChange.newMode
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_MotionModeChange.newMode
            }
        )
        }
    }) 
  }
}
check P__424
// P__424:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_location_attr_mode,app_MotionModeChange.newMode


assert P__425 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Home
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Home
            }
        )
        }
    }) 
  }
}
check P__425
// P__425:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__426 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_home
            action'.value     = cap_state_attr_home_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_home
                action''.value     = cap_state_attr_home_val_true
            }
        )
        }
    }) 
  }
}
check P__426
// P__426:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_state_attr_home,cap_state_attr_home_val_true


assert P__427 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_locked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_locked
            }
        )
        }
    }) 
  }
}
check P__427
// P__427:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_lock_attr_lock,cap_lock_attr_lock_val_locked


assert P__428 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked_with_timeout
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked_with_timeout
            }
        )
        }
    }) 
  }
}
check P__428
// P__428:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked_with_timeout


assert P__429 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__429
// P__429:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_on


assert P__430 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_runIn_attr_runIn
            action'.value     = cap_runIn_attr_runIn_val_off
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_runIn_attr_runIn
                action''.value     = cap_runIn_attr_runIn_val_off
            }
        )
        }
    }) 
  }
}
check P__430
// P__430:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_runIn_attr_runIn,cap_runIn_attr_runIn_val_off


assert P__431 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_inactive
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_inactive
            }
        )
        }
    }) 
  }
}
check P__431
// P__431:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_inactive


assert P__432 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_motionSensor_attr_motion
            action'.value     = cap_motionSensor_attr_motion_val_active
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_motionSensor_attr_motion
                action''.value     = cap_motionSensor_attr_motion_val_active
            }
        )
        }
    }) 
  }
}
check P__432
// P__432:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_motionSensor_attr_motion,cap_motionSensor_attr_motion_val_active


assert P__433 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_0
            }
        )
        }
    }) 
  }
}
check P__433
// P__433:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_illuminanceMeasurement_attr_illuminance,range_0


assert P__434 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = cap_illuminanceMeasurement_attr_illuminance_val0
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = cap_illuminanceMeasurement_attr_illuminance_val0
            }
        )
        }
    }) 
  }
}
check P__434
// P__434:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_illuminanceMeasurement_attr_illuminance,cap_illuminanceMeasurement_attr_illuminance_val0


assert P__435 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_illuminanceMeasurement_attr_illuminance
            action'.value     = range_1
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_illuminanceMeasurement_attr_illuminance
                action''.value     = range_1
            }
        )
        }
    }) 
  }
}
check P__435
// P__435:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_illuminanceMeasurement_attr_illuminance,range_1


assert P__436 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_true
            }
        )
        }
    }) 
  }
}
check P__436
// P__436:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_true


assert P__437 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_lock_attr_lock
            action'.value     = cap_lock_attr_lock_val_unlocked
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_lock_attr_lock
                action''.value     = cap_lock_attr_lock_val_unlocked
            }
        )
        }
    }) 
  }
}
check P__437
// P__437:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked


assert P__438 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_attack
            action'.value     = cap_state_attr_attack_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_attack
                action''.value     = cap_state_attr_attack_val_false
            }
        )
        }
    }) 
  }
}
check P__438
// P__438:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_state_attr_attack,cap_state_attr_attack_val_false


assert P__439 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_runIn
            action'.value     = cap_state_attr_runIn_val_on
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_runIn
                action''.value     = cap_state_attr_runIn_val_on
            }
        )
        }
    }) 
  }
}
check P__439
// P__439:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__440 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_lock_attr_lock
    action.value     = cap_lock_attr_lock_val_unlocked
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_state_attr_motionDetected
            action'.value     = cap_state_attr_motionDetected_val_false
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_motionDetected
                action''.value     = cap_state_attr_motionDetected_val_false
            }
        )
        }
    }) 
  }
}
check P__440
// P__440:cap_lock_attr_lock,cap_lock_attr_lock_val_unlocked,cap_state_attr_motionDetected,cap_state_attr_motionDetected_val_false

