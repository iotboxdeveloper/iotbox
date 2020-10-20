
// filename: cap_thermostatOperatingState.als
module cap_thermostatOperatingState
open IoTBottomUp
one sig cap_thermostatOperatingState extends Capability {}
{
    attributes = cap_thermostatOperatingState_attr
}
abstract sig cap_thermostatOperatingState_attr extends Attribute {}
one sig cap_thermostatOperatingState_attr_thermostatOperatingState extends cap_thermostatOperatingState_attr {}
{
    values = cap_thermostatOperatingState_attr_thermostatOperatingState_val
} 
abstract sig cap_thermostatOperatingState_attr_thermostatOperatingState_val extends AttrValue {}
one sig cap_thermostatOperatingState_attr_thermostatOperatingState_val_cooling extends cap_thermostatOperatingState_attr_thermostatOperatingState_val {}
one sig cap_thermostatOperatingState_attr_thermostatOperatingState_val_fan_only extends cap_thermostatOperatingState_attr_thermostatOperatingState_val {}
one sig cap_thermostatOperatingState_attr_thermostatOperatingState_val_heating extends cap_thermostatOperatingState_attr_thermostatOperatingState_val {}
one sig cap_thermostatOperatingState_attr_thermostatOperatingState_val_idle extends cap_thermostatOperatingState_attr_thermostatOperatingState_val {}
one sig cap_thermostatOperatingState_attr_thermostatOperatingState_val_pending_cool extends cap_thermostatOperatingState_attr_thermostatOperatingState_val {}
one sig cap_thermostatOperatingState_attr_thermostatOperatingState_val_pending_heat extends cap_thermostatOperatingState_attr_thermostatOperatingState_val {}
one sig cap_thermostatOperatingState_attr_thermostatOperatingState_val_vent_economizer extends cap_thermostatOperatingState_attr_thermostatOperatingState_val {}
