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
open app_ID17SleepingModeTurnOffDevices
open app_ID16SleepingModeChange

assert P__0 {
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
            action'.attribute = cap_state_attr_switchesTurnedOff
            action'.value     = cap_state_attr_switchesTurnedOff_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_switchesTurnedOff
                action''.value     = cap_state_attr_switchesTurnedOff_val_true
            }
        )
        }
    }) 
  }
}
check P__0
// P__0:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_state_attr_switchesTurnedOff,cap_state_attr_switchesTurnedOff_val_true


assert P__1 {
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
check P__1
// P__1:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__2 {
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
            action'.value     = app_ID16SleepingModeChange.Home_Day
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_ID16SleepingModeChange.Home_Day
            }
        )
        }
    }) 
  }
}
check P__2
// P__2:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_location_attr_mode,app_ID16SleepingModeChange.Home_Day


assert P__3 {
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
            action'.value     = app_ID16SleepingModeChange.Home_Night
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_ID16SleepingModeChange.Home_Night
            }
        )
        }
    }) 
  }
}
check P__3
// P__3:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_location_attr_mode,app_ID16SleepingModeChange.Home_Night


assert P__4 {
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
            action'.value     = app_ID16SleepingModeChange.Away_Night
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_ID16SleepingModeChange.Away_Night
            }
        )
        }
    }) 
  }
}
check P__4
// P__4:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_location_attr_mode,app_ID16SleepingModeChange.Away_Night


assert P__5 {
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
            action'.value     = app_ID16SleepingModeChange.Away_Day
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_ID16SleepingModeChange.Away_Day
            }
        )
        }
    }) 
  }
}
check P__5
// P__5:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_location_attr_mode,app_ID16SleepingModeChange.Away_Day


assert P__6 {
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
check P__6
// P__6:cap_switch_attr_switch,cap_switch_attr_switch_val_on,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__7 {
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
            action'.attribute = cap_state_attr_switchesTurnedOff
            action'.value     = cap_state_attr_switchesTurnedOff_val_true
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_state_attr_switchesTurnedOff
                action''.value     = cap_state_attr_switchesTurnedOff_val_true
            }
        )
        }
    }) 
  }
}
check P__7
// P__7:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_state_attr_switchesTurnedOff,cap_state_attr_switchesTurnedOff_val_true


assert P__8 {
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
check P__8
// P__8:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__9 {
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
            action'.value     = app_ID16SleepingModeChange.Home_Day
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_ID16SleepingModeChange.Home_Day
            }
        )
        }
    }) 
  }
}
check P__9
// P__9:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_location_attr_mode,app_ID16SleepingModeChange.Home_Day


assert P__10 {
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
            action'.value     = app_ID16SleepingModeChange.Home_Night
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_ID16SleepingModeChange.Home_Night
            }
        )
        }
    }) 
  }
}
check P__10
// P__10:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_location_attr_mode,app_ID16SleepingModeChange.Home_Night


assert P__11 {
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
            action'.value     = app_ID16SleepingModeChange.Away_Night
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_ID16SleepingModeChange.Away_Night
            }
        )
        }
    }) 
  }
}
check P__11
// P__11:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_location_attr_mode,app_ID16SleepingModeChange.Away_Night


assert P__12 {
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
            action'.value     = app_ID16SleepingModeChange.Away_Day
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = app_ID16SleepingModeChange.Away_Day
            }
        )
        }
    }) 
  }
}
check P__12
// P__12:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_location_attr_mode,app_ID16SleepingModeChange.Away_Day


assert P__13 {
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
check P__13
// P__13:cap_switch_attr_switch,cap_switch_attr_switch_val_off,cap_location_attr_mode,cap_location_attr_mode_val_Home

