module IoTGraphModel

open IoTBottomUp as base
open IoTChannel  as chan

open cap_runIn
open cap_lock
open cap_switch
open cap_temperatureMeasurement
open cap_presenceSensor
open cap_motionSensor
open cap_location
open cap_contactSensor
open cap_smokeDetector
open cap_alarm
open cap_doorControl

open app_IlluminatedResponsetoUnexpectedVisitors

pred connected_runIn[r,r' : Rule] {
  no r'.triggers
  some comm : r.commands, cond : r'.conditions {
    (cond.attribute  = cap_runIn_attr_runIn)
    (cond.value      = cap_runIn_attr_runIn_val_on)
    (comm.capability = cond.capabilities)
    (comm.attribute  = cond.attribute)
    (comm.value      = cond.value)
  }
}

pred connected_caps[comm : Command, trig : Trigger] {
  (some comm.capability & trig.capabilities)
  (comm.attribute = trig.attribute)
  (comm.value in trig.value) or (no trig.value)
}

pred connected_chan[comm : Command, trig : Trigger] {
  some c : Channel {
    some (comm.capability   & c.actuators)
    some (trig.capabilities & c.sensors)
  }
}

pred are_indirect[r,r' : Rule] {
  are_connected[r,r']
  no comm : r.commands, trig : r'.triggers {
    connected_caps[comm, trig]
  }
}

pred are_connected[r,r' : Rule] {
  (some comm : r.commands, trig : r'.triggers {
    connected_caps[comm, trig] or connected_chan[comm, trig]
  }) or (connected_runIn[r,r'])
  all comm : r.commands, cond : r'.conditions {
    ((some comm.capability & cond.capabilities) and (comm.attribute = cond.attribute)) => {
      (comm.value in cond.value)
    }
  }
}

pred are_siblings[r,r' : Rule] {
  (no r.triggers) or (no r'.triggers) or (some t : r.triggers, t' : r'.triggers {
    (t.attribute = t'.attribute)
    (some t.value & t'.value) or (no t.value) or (no t'.value)
  })
  all c : r.conditions, c' : r'.conditions {
    ((some c.capabilities & c'.capabilities) and (c.attribute = c'.attribute))
      => (some c.value & c'.value)
  }
}

fact {
  all r,r' : Rule {
    (r' in r.connected) <=> are_connected[r,r']
    (r' in r.siblings)  <=> are_siblings[r,r']
    (r' in r.indirect)  <=> are_indirect[r,r']
    (r' in r.scheduled) <=> connected_runIn[r,r']
  }
}


// P5: DON'T turn off The living room’s bulb WHEN someone is at home
assert P5 {
  no r : IoTApp.rules, action : r.commands {
    // "DON'T turn off The living room’s bulb..."
    action.attribute = cap_switch_attr_switch
    action.value     = cap_switch_attr_switch_val_off

    (some predecessor : r.*(~connected), action' : predecessor.commands {
      // ...when someone is at home
      action'.attribute = cap_location_attr_mode
      action'.value     = cap_location_attr_mode_val_Home 
    }) 
    or
    (some predecessor : r.*(~connected), event : predecessor.triggers {
      // ...or if motion is active 
      event.attribute = cap_motionSensor_attr_motion
      event.value     = cap_motionSensor_attr_motion_val_active
    }) 
    or 
    (some predecessor : r.*(~connected), event : predecessor.triggers {
      // ...or if the user no present
      event.attribute = cap_presenceSensor_attr_presence
      event.value     = cap_presenceSensor_attr_presence_val_present
    })
  }
}




check P5

