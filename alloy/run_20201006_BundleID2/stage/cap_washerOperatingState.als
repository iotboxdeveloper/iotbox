
// filename: cap_washerOperatingState.als
module cap_washerOperatingState
open IoTBottomUp
one sig cap_washerOperatingState extends Capability {}
{
    attributes = cap_washerOperatingState_attr
}
abstract sig cap_washerOperatingState_attr extends Attribute {}
one sig cap_washerOperatingState_attr_machineState extends cap_washerOperatingState_attr {}
{
    values = cap_washerOperatingState_attr_machineState_val
} 
abstract sig cap_washerOperatingState_attr_machineState_val extends AttrValue {}
one sig cap_washerOperatingState_attr_machineState_val_pause extends cap_washerOperatingState_attr_machineState_val {}
one sig cap_washerOperatingState_attr_machineState_val_run extends cap_washerOperatingState_attr_machineState_val {}
one sig cap_washerOperatingState_attr_machineState_val_stop extends cap_washerOperatingState_attr_machineState_val {}
one sig cap_washerOperatingState_attr_supportedMachineStates extends cap_washerOperatingState_attr {}
{
    values = cap_washerOperatingState_attr_supportedMachineStates_val
} 
abstract sig cap_washerOperatingState_attr_supportedMachineStates_val extends AttrValue {}
one sig cap_washerOperatingState_attr_washerJobState extends cap_washerOperatingState_attr {}
{
    values = cap_washerOperatingState_attr_washerJobState_val
} 
abstract sig cap_washerOperatingState_attr_washerJobState_val extends AttrValue {}
one sig cap_washerOperatingState_attr_washerJobState_val_airWash extends cap_washerOperatingState_attr_washerJobState_val {}
one sig cap_washerOperatingState_attr_washerJobState_val_cooling extends cap_washerOperatingState_attr_washerJobState_val {}
one sig cap_washerOperatingState_attr_washerJobState_val_delayWash extends cap_washerOperatingState_attr_washerJobState_val {}
one sig cap_washerOperatingState_attr_washerJobState_val_drying extends cap_washerOperatingState_attr_washerJobState_val {}
one sig cap_washerOperatingState_attr_washerJobState_val_finish extends cap_washerOperatingState_attr_washerJobState_val {}
one sig cap_washerOperatingState_attr_washerJobState_val_none extends cap_washerOperatingState_attr_washerJobState_val {}
one sig cap_washerOperatingState_attr_washerJobState_val_preWash extends cap_washerOperatingState_attr_washerJobState_val {}
one sig cap_washerOperatingState_attr_washerJobState_val_rinse extends cap_washerOperatingState_attr_washerJobState_val {}
one sig cap_washerOperatingState_attr_washerJobState_val_spin extends cap_washerOperatingState_attr_washerJobState_val {}
one sig cap_washerOperatingState_attr_washerJobState_val_wash extends cap_washerOperatingState_attr_washerJobState_val {}
one sig cap_washerOperatingState_attr_washerJobState_val_weightSensing extends cap_washerOperatingState_attr_washerJobState_val {}
one sig cap_washerOperatingState_attr_washerJobState_val_wrinklePrevent extends cap_washerOperatingState_attr_washerJobState_val {}
one sig cap_washerOperatingState_attr_completionTime extends cap_washerOperatingState_attr {}
{
    values = cap_washerOperatingState_attr_completionTime_val
} 
abstract sig cap_washerOperatingState_attr_completionTime_val extends AttrValue {}