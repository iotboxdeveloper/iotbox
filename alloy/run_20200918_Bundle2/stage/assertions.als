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
open app_ID16SleepingModeChange
open app_ID17SleepingModeTurnOffDevices

assert P__0 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Day 
    }) 
  }
}


assert P__1 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__2 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Day 
    }) 
  }
}


assert P__3 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Home 
    }) 
  }
}


assert P__4 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Night 
    }) 
  }
}


assert P__5 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Away 
    }) 
  }
}


assert P__6 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__7 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Night 
    }) 
  }
}


assert P__8 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_off 
    }) 
  }
}


assert P__9 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_on 
    }) 
  }
}


assert P__10 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_state_attr_switchesTurnedOff
      event.value     = cap_state_attr_switchesTurnedOff_val_true 
    }) 
  }
}


assert P__11 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Day 
    }) 
  }
}


assert P__12 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__13 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Day 
    }) 
  }
}


assert P__14 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Home 
    }) 
  }
}


assert P__15 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Night 
    }) 
  }
}


assert P__16 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Away 
    }) 
  }
}


assert P__17 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__18 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Night 
    }) 
  }
}


assert P__19 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_off 
    }) 
  }
}


assert P__20 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_on 
    }) 
  }
}


assert P__21 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_state_attr_switchesTurnedOff
      event.value     = cap_state_attr_switchesTurnedOff_val_true 
    }) 
  }
}


assert P__22 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Day 
    }) 
  }
}


assert P__23 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__24 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Day 
    }) 
  }
}


assert P__25 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Home 
    }) 
  }
}


assert P__26 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Night 
    }) 
  }
}


assert P__27 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Away 
    }) 
  }
}


assert P__28 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__29 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Night 
    }) 
  }
}


assert P__30 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_off 
    }) 
  }
}


assert P__31 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_on 
    }) 
  }
}


assert P__32 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_state_attr_switchesTurnedOff
      event.value     = cap_state_attr_switchesTurnedOff_val_true 
    }) 
  }
}


assert P__33 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Day 
    }) 
  }
}


assert P__34 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__35 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Day 
    }) 
  }
}


assert P__36 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Home 
    }) 
  }
}


assert P__37 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Night 
    }) 
  }
}


assert P__38 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Away 
    }) 
  }
}


assert P__39 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__40 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Night 
    }) 
  }
}


assert P__41 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_off 
    }) 
  }
}


assert P__42 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_on 
    }) 
  }
}


assert P__43 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_state_attr_switchesTurnedOff
      event.value     = cap_state_attr_switchesTurnedOff_val_true 
    }) 
  }
}


assert P__44 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Day 
    }) 
  }
}


assert P__45 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__46 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Day 
    }) 
  }
}


assert P__47 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Home 
    }) 
  }
}


assert P__48 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Night 
    }) 
  }
}


assert P__49 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Away 
    }) 
  }
}


assert P__50 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__51 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Night 
    }) 
  }
}


assert P__52 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_off 
    }) 
  }
}


assert P__53 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_on 
    }) 
  }
}


assert P__54 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_state_attr_switchesTurnedOff
      event.value     = cap_state_attr_switchesTurnedOff_val_true 
    }) 
  }
}


assert P__55 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Day 
    }) 
  }
}


assert P__56 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__57 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Day 
    }) 
  }
}


assert P__58 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Home 
    }) 
  }
}


assert P__59 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Night 
    }) 
  }
}


assert P__60 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Away 
    }) 
  }
}


assert P__61 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__62 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Night 
    }) 
  }
}


assert P__63 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_off 
    }) 
  }
}


assert P__64 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_on 
    }) 
  }
}


assert P__65 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_state_attr_switchesTurnedOff
      event.value     = cap_state_attr_switchesTurnedOff_val_true 
    }) 
  }
}


assert P__66 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Day 
    }) 
  }
}


assert P__67 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__68 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Day 
    }) 
  }
}


assert P__69 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Home 
    }) 
  }
}


assert P__70 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Night 
    }) 
  }
}


assert P__71 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Away 
    }) 
  }
}


assert P__72 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__73 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Night 
    }) 
  }
}


assert P__74 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_off 
    }) 
  }
}


assert P__75 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_on 
    }) 
  }
}


assert P__76 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_state_attr_switchesTurnedOff
      event.value     = cap_state_attr_switchesTurnedOff_val_true 
    }) 
  }
}


assert P__77 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Day 
    }) 
  }
}


assert P__78 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__79 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Day 
    }) 
  }
}


assert P__80 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Home 
    }) 
  }
}


assert P__81 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Night 
    }) 
  }
}


assert P__82 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Away 
    }) 
  }
}


assert P__83 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__84 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Night 
    }) 
  }
}


assert P__85 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_off 
    }) 
  }
}


assert P__86 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_on 
    }) 
  }
}


assert P__87 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_state_attr_switchesTurnedOff
      event.value     = cap_state_attr_switchesTurnedOff_val_true 
    }) 
  }
}


assert P__88 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Day 
    }) 
  }
}


assert P__89 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__90 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Day 
    }) 
  }
}


assert P__91 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Home 
    }) 
  }
}


assert P__92 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Night 
    }) 
  }
}


assert P__93 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Away 
    }) 
  }
}


assert P__94 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__95 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Night 
    }) 
  }
}


assert P__96 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_off 
    }) 
  }
}


assert P__97 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_on 
    }) 
  }
}


assert P__98 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_state_attr_switchesTurnedOff
      event.value     = cap_state_attr_switchesTurnedOff_val_true 
    }) 
  }
}


assert P__99 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Day 
    }) 
  }
}


assert P__100 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__101 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Day 
    }) 
  }
}


assert P__102 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Home 
    }) 
  }
}


assert P__103 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Away_Night 
    }) 
  }
}


assert P__104 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Away 
    }) 
  }
}


assert P__105 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = app_ID16SleepingModeChange.Home_Night 
    }) 
  }
}


assert P__106 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_location_attr_mode
      event.value     = cap_location_attr_mode_val_Night 
    }) 
  }
}


assert P__107 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_off 
    }) 
  }
}


assert P__108 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_switch_attr_switch
      event.value     = cap_switch_attr_switch_val_on 
    }) 
  }
}


assert P__109 {
  no r : IoTApp.rules, action : r.commands {
    // 
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_on

    (some predecessor : r.*(~connected), event : predecessor.triggers {
      
      event.attribute = cap_state_attr_switchesTurnedOff
      event.value     = cap_state_attr_switchesTurnedOff_val_true 
    }) 
  }
}

