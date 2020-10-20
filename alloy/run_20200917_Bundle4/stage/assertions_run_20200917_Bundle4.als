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
open app_B4_HomeModeApp
open app_B4_OpenDoorWhenSmokeDetected
open app_B4_MaliciousApp

assert P__0 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_grill
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_grill
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_grill
            }
        )
        }
    }) 
  }
}
check P__0
// P__0:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill


assert P__1 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_grill
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_defrosting
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_defrosting
            }
        )
        }
    }) 
  }
}
check P__1
// P__1:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting


assert P__2 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_grill
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_momentary_attr_momentary
            action'.value     = cap_momentary_attr_momentary_val_push
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_momentary_attr_momentary
                action''.value     = cap_momentary_attr_momentary_val_push
            }
        )
        }
    }) 
  }
}
check P__2
// P__2:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill,cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push


assert P__3 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_grill
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_closed
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_closed
            }
        )
        }
    }) 
  }
}
check P__3
// P__3:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed


assert P__4 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_grill
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_open
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_open
            }
        )
        }
    }) 
  }
}
check P__4
// P__4:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open


assert P__5 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_grill
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
check P__5
// P__5:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__6 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_grill
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
// P__6:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__7 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_grill
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Away
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Away
            }
        )
        }
    }) 
  }
}
check P__7
// P__7:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill,cap_location_attr_mode,cap_location_attr_mode_val_Away


assert P__8 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_grill
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_not_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_not_present
            }
        )
        }
    }) 
  }
}
check P__8
// P__8:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present


assert P__9 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_grill
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_present
            }
        )
        }
    }) 
  }
}
check P__9
// P__9:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present


assert P__10 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_defrosting
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_grill
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_grill
            }
        )
        }
    }) 
  }
}
check P__10
// P__10:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill


assert P__11 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_defrosting
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_defrosting
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_defrosting
            }
        )
        }
    }) 
  }
}
check P__11
// P__11:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting


assert P__12 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_defrosting
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_momentary_attr_momentary
            action'.value     = cap_momentary_attr_momentary_val_push
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_momentary_attr_momentary
                action''.value     = cap_momentary_attr_momentary_val_push
            }
        )
        }
    }) 
  }
}
check P__12
// P__12:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting,cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push


assert P__13 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_defrosting
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_closed
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_closed
            }
        )
        }
    }) 
  }
}
check P__13
// P__13:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed


assert P__14 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_defrosting
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_open
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_open
            }
        )
        }
    }) 
  }
}
check P__14
// P__14:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open


assert P__15 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_defrosting
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
check P__15
// P__15:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__16 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_defrosting
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
check P__16
// P__16:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__17 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_defrosting
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Away
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Away
            }
        )
        }
    }) 
  }
}
check P__17
// P__17:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting,cap_location_attr_mode,cap_location_attr_mode_val_Away


assert P__18 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_defrosting
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_not_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_not_present
            }
        )
        }
    }) 
  }
}
check P__18
// P__18:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present


assert P__19 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_ovenMode_attr_ovenMode
    action.value     = cap_ovenMode_attr_ovenMode_val_defrosting
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_present
            }
        )
        }
    }) 
  }
}
check P__19
// P__19:cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present


assert P__20 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_momentary_attr_momentary
    action.value     = cap_momentary_attr_momentary_val_push
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_grill
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_grill
            }
        )
        }
    }) 
  }
}
check P__20
// P__20:cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill


assert P__21 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_momentary_attr_momentary
    action.value     = cap_momentary_attr_momentary_val_push
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_defrosting
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_defrosting
            }
        )
        }
    }) 
  }
}
check P__21
// P__21:cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting


assert P__22 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_momentary_attr_momentary
    action.value     = cap_momentary_attr_momentary_val_push
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_momentary_attr_momentary
            action'.value     = cap_momentary_attr_momentary_val_push
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_momentary_attr_momentary
                action''.value     = cap_momentary_attr_momentary_val_push
            }
        )
        }
    }) 
  }
}
check P__22
// P__22:cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push,cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push


assert P__23 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_momentary_attr_momentary
    action.value     = cap_momentary_attr_momentary_val_push
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_closed
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_closed
            }
        )
        }
    }) 
  }
}
check P__23
// P__23:cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed


assert P__24 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_momentary_attr_momentary
    action.value     = cap_momentary_attr_momentary_val_push
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_open
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_open
            }
        )
        }
    }) 
  }
}
check P__24
// P__24:cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open


assert P__25 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_momentary_attr_momentary
    action.value     = cap_momentary_attr_momentary_val_push
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
check P__25
// P__25:cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__26 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_momentary_attr_momentary
    action.value     = cap_momentary_attr_momentary_val_push
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
// P__26:cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__27 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_momentary_attr_momentary
    action.value     = cap_momentary_attr_momentary_val_push
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Away
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Away
            }
        )
        }
    }) 
  }
}
check P__27
// P__27:cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push,cap_location_attr_mode,cap_location_attr_mode_val_Away


assert P__28 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_momentary_attr_momentary
    action.value     = cap_momentary_attr_momentary_val_push
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_not_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_not_present
            }
        )
        }
    }) 
  }
}
check P__28
// P__28:cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present


assert P__29 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_momentary_attr_momentary
    action.value     = cap_momentary_attr_momentary_val_push
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_present
            }
        )
        }
    }) 
  }
}
check P__29
// P__29:cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present


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
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_grill
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_grill
            }
        )
        }
    }) 
  }
}
check P__30
// P__30:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill


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
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_defrosting
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_defrosting
            }
        )
        }
    }) 
  }
}
check P__31
// P__31:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting


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
            action'.attribute = cap_momentary_attr_momentary
            action'.value     = cap_momentary_attr_momentary_val_push
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_momentary_attr_momentary
                action''.value     = cap_momentary_attr_momentary_val_push
            }
        )
        }
    }) 
  }
}
check P__32
// P__32:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push


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
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_closed
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_closed
            }
        )
        }
    }) 
  }
}
check P__33
// P__33:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed


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
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_open
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_open
            }
        )
        }
    }) 
  }
}
check P__34
// P__34:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open


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
check P__35
// P__35:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_state_attr_runIn,cap_state_attr_runIn_val_on


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
check P__36
// P__36:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_location_attr_mode,cap_location_attr_mode_val_Home


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
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Away
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Away
            }
        )
        }
    }) 
  }
}
check P__37
// P__37:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_location_attr_mode,cap_location_attr_mode_val_Away


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
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_not_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_not_present
            }
        )
        }
    }) 
  }
}
check P__38
// P__38:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present


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
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_present
            }
        )
        }
    }) 
  }
}
check P__39
// P__39:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present


assert P__40 {
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
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_grill
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_grill
            }
        )
        }
    }) 
  }
}
check P__40
// P__40:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill


assert P__41 {
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
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_defrosting
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_defrosting
            }
        )
        }
    }) 
  }
}
check P__41
// P__41:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting


assert P__42 {
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
            action'.attribute = cap_momentary_attr_momentary
            action'.value     = cap_momentary_attr_momentary_val_push
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_momentary_attr_momentary
                action''.value     = cap_momentary_attr_momentary_val_push
            }
        )
        }
    }) 
  }
}
check P__42
// P__42:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push


assert P__43 {
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
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_closed
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_closed
            }
        )
        }
    }) 
  }
}
check P__43
// P__43:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed


assert P__44 {
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
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_open
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_open
            }
        )
        }
    }) 
  }
}
check P__44
// P__44:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open


assert P__45 {
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
check P__45
// P__45:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__46 {
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
check P__46
// P__46:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__47 {
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
            action'.value     = cap_location_attr_mode_val_Away
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Away
            }
        )
        }
    }) 
  }
}
check P__47
// P__47:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_location_attr_mode,cap_location_attr_mode_val_Away


assert P__48 {
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
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_not_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_not_present
            }
        )
        }
    }) 
  }
}
check P__48
// P__48:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present


assert P__49 {
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
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_present
            }
        )
        }
    }) 
  }
}
check P__49
// P__49:cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present


assert P__50 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = app_OpenDoorWhenSmokeDetected.detected
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_grill
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_grill
            }
        )
        }
    }) 
  }
}
check P__50
// P__50:cap_smokeDetector_attr_smoke,app_OpenDoorWhenSmokeDetected.detected,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill


assert P__51 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = app_OpenDoorWhenSmokeDetected.detected
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_defrosting
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_defrosting
            }
        )
        }
    }) 
  }
}
check P__51
// P__51:cap_smokeDetector_attr_smoke,app_OpenDoorWhenSmokeDetected.detected,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting


assert P__52 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = app_OpenDoorWhenSmokeDetected.detected
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_momentary_attr_momentary
            action'.value     = cap_momentary_attr_momentary_val_push
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_momentary_attr_momentary
                action''.value     = cap_momentary_attr_momentary_val_push
            }
        )
        }
    }) 
  }
}
check P__52
// P__52:cap_smokeDetector_attr_smoke,app_OpenDoorWhenSmokeDetected.detected,cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push


assert P__53 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = app_OpenDoorWhenSmokeDetected.detected
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_closed
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_closed
            }
        )
        }
    }) 
  }
}
check P__53
// P__53:cap_smokeDetector_attr_smoke,app_OpenDoorWhenSmokeDetected.detected,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed


assert P__54 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = app_OpenDoorWhenSmokeDetected.detected
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_open
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_open
            }
        )
        }
    }) 
  }
}
check P__54
// P__54:cap_smokeDetector_attr_smoke,app_OpenDoorWhenSmokeDetected.detected,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open


assert P__55 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = app_OpenDoorWhenSmokeDetected.detected
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
check P__55
// P__55:cap_smokeDetector_attr_smoke,app_OpenDoorWhenSmokeDetected.detected,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__56 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = app_OpenDoorWhenSmokeDetected.detected
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
check P__56
// P__56:cap_smokeDetector_attr_smoke,app_OpenDoorWhenSmokeDetected.detected,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__57 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = app_OpenDoorWhenSmokeDetected.detected
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Away
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Away
            }
        )
        }
    }) 
  }
}
check P__57
// P__57:cap_smokeDetector_attr_smoke,app_OpenDoorWhenSmokeDetected.detected,cap_location_attr_mode,cap_location_attr_mode_val_Away


assert P__58 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = app_OpenDoorWhenSmokeDetected.detected
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_not_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_not_present
            }
        )
        }
    }) 
  }
}
check P__58
// P__58:cap_smokeDetector_attr_smoke,app_OpenDoorWhenSmokeDetected.detected,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present


assert P__59 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = app_OpenDoorWhenSmokeDetected.detected
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_present
            }
        )
        }
    }) 
  }
}
check P__59
// P__59:cap_smokeDetector_attr_smoke,app_OpenDoorWhenSmokeDetected.detected,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present


assert P__60 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = cap_smokeDetector_attr_smoke_val_tested
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_grill
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_grill
            }
        )
        }
    }) 
  }
}
check P__60
// P__60:cap_smokeDetector_attr_smoke,cap_smokeDetector_attr_smoke_val_tested,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill


assert P__61 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = cap_smokeDetector_attr_smoke_val_tested
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_defrosting
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_defrosting
            }
        )
        }
    }) 
  }
}
check P__61
// P__61:cap_smokeDetector_attr_smoke,cap_smokeDetector_attr_smoke_val_tested,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting


assert P__62 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = cap_smokeDetector_attr_smoke_val_tested
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_momentary_attr_momentary
            action'.value     = cap_momentary_attr_momentary_val_push
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_momentary_attr_momentary
                action''.value     = cap_momentary_attr_momentary_val_push
            }
        )
        }
    }) 
  }
}
check P__62
// P__62:cap_smokeDetector_attr_smoke,cap_smokeDetector_attr_smoke_val_tested,cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push


assert P__63 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = cap_smokeDetector_attr_smoke_val_tested
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_closed
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_closed
            }
        )
        }
    }) 
  }
}
check P__63
// P__63:cap_smokeDetector_attr_smoke,cap_smokeDetector_attr_smoke_val_tested,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed


assert P__64 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = cap_smokeDetector_attr_smoke_val_tested
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_open
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_open
            }
        )
        }
    }) 
  }
}
check P__64
// P__64:cap_smokeDetector_attr_smoke,cap_smokeDetector_attr_smoke_val_tested,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open


assert P__65 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = cap_smokeDetector_attr_smoke_val_tested
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
check P__65
// P__65:cap_smokeDetector_attr_smoke,cap_smokeDetector_attr_smoke_val_tested,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__66 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = cap_smokeDetector_attr_smoke_val_tested
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
check P__66
// P__66:cap_smokeDetector_attr_smoke,cap_smokeDetector_attr_smoke_val_tested,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__67 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = cap_smokeDetector_attr_smoke_val_tested
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Away
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Away
            }
        )
        }
    }) 
  }
}
check P__67
// P__67:cap_smokeDetector_attr_smoke,cap_smokeDetector_attr_smoke_val_tested,cap_location_attr_mode,cap_location_attr_mode_val_Away


assert P__68 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = cap_smokeDetector_attr_smoke_val_tested
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_not_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_not_present
            }
        )
        }
    }) 
  }
}
check P__68
// P__68:cap_smokeDetector_attr_smoke,cap_smokeDetector_attr_smoke_val_tested,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present


assert P__69 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_smokeDetector_attr_smoke
    action.value     = cap_smokeDetector_attr_smoke_val_tested
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_present
            }
        )
        }
    }) 
  }
}
check P__69
// P__69:cap_smokeDetector_attr_smoke,cap_smokeDetector_attr_smoke_val_tested,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present


assert P__70 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_not_present
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_grill
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_grill
            }
        )
        }
    }) 
  }
}
check P__70
// P__70:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill


assert P__71 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_not_present
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_defrosting
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_defrosting
            }
        )
        }
    }) 
  }
}
check P__71
// P__71:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting


assert P__72 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_not_present
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_momentary_attr_momentary
            action'.value     = cap_momentary_attr_momentary_val_push
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_momentary_attr_momentary
                action''.value     = cap_momentary_attr_momentary_val_push
            }
        )
        }
    }) 
  }
}
check P__72
// P__72:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present,cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push


assert P__73 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_not_present
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_closed
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_closed
            }
        )
        }
    }) 
  }
}
check P__73
// P__73:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed


assert P__74 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_not_present
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_open
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_open
            }
        )
        }
    }) 
  }
}
check P__74
// P__74:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open


assert P__75 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_not_present
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
check P__75
// P__75:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__76 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_not_present
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
check P__76
// P__76:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__77 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_not_present
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Away
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Away
            }
        )
        }
    }) 
  }
}
check P__77
// P__77:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present,cap_location_attr_mode,cap_location_attr_mode_val_Away


assert P__78 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_not_present
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_not_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_not_present
            }
        )
        }
    }) 
  }
}
check P__78
// P__78:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present


assert P__79 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_not_present
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_present
            }
        )
        }
    }) 
  }
}
check P__79
// P__79:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present


assert P__80 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_present
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_grill
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_grill
            }
        )
        }
    }) 
  }
}
check P__80
// P__80:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_grill


assert P__81 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_present
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_ovenMode_attr_ovenMode
            action'.value     = cap_ovenMode_attr_ovenMode_val_defrosting
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_ovenMode_attr_ovenMode
                action''.value     = cap_ovenMode_attr_ovenMode_val_defrosting
            }
        )
        }
    }) 
  }
}
check P__81
// P__81:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present,cap_ovenMode_attr_ovenMode,cap_ovenMode_attr_ovenMode_val_defrosting


assert P__82 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_present
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_momentary_attr_momentary
            action'.value     = cap_momentary_attr_momentary_val_push
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_momentary_attr_momentary
                action''.value     = cap_momentary_attr_momentary_val_push
            }
        )
        }
    }) 
  }
}
check P__82
// P__82:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present,cap_momentary_attr_momentary,cap_momentary_attr_momentary_val_push


assert P__83 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_present
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_closed
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_closed
            }
        )
        }
    }) 
  }
}
check P__83
// P__83:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_closed


assert P__84 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_present
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_contactSensor_attr_contact
            action'.value     = cap_contactSensor_attr_contact_val_open
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_contactSensor_attr_contact
                action''.value     = cap_contactSensor_attr_contact_val_open
            }
        )
        }
    }) 
  }
}
check P__84
// P__84:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present,cap_contactSensor_attr_contact,cap_contactSensor_attr_contact_val_open


assert P__85 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_present
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
check P__85
// P__85:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present,cap_state_attr_runIn,cap_state_attr_runIn_val_on


assert P__86 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_present
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
check P__86
// P__86:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present,cap_location_attr_mode,cap_location_attr_mode_val_Home


assert P__87 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_present
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_location_attr_mode
            action'.value     = cap_location_attr_mode_val_Away
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_location_attr_mode
                action''.value     = cap_location_attr_mode_val_Away
            }
        )
        }
    }) 
  }
}
check P__87
// P__87:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present,cap_location_attr_mode,cap_location_attr_mode_val_Away


assert P__88 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_present
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_not_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_not_present
            }
        )
        }
    }) 
  }
}
check P__88
// P__88:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_not_present


assert P__89 {
  // there is no situation where C occurs (e.g. the switch is automatically off)
  no r : IoTApp.rules, action : r.commands {
    action.attribute = cap_presenceSensor_attr_presence
    action.value     = cap_presenceSensor_attr_presence_val_present
    (some predecessor : r.*(~connected), action' : predecessor.triggers {
    // caused by some causal path of events
    // where it is not a path that has X
    // e.g. X=(have some event that is not NIGHT mode, and is not preceded by NIGHT mode)
        not {
        (
        {
            action'.attribute = cap_presenceSensor_attr_presence
            action'.value     = cap_presenceSensor_attr_presence_val_present
        }
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers {
                action''.attribute = cap_presenceSensor_attr_presence
                action''.value     = cap_presenceSensor_attr_presence_val_present
            }
        )
        }
    }) 
  }
}
check P__89
// P__89:cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present,cap_presenceSensor_attr_presence,cap_presenceSensor_attr_presence_val_present

