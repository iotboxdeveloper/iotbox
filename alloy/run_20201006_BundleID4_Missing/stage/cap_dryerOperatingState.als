
// filename: cap_dryerOperatingState.als
module cap_dryerOperatingState
open IoTBottomUp
one sig cap_dryerOperatingState extends Capability {}
{
    attributes = cap_dryerOperatingState_attr
}
abstract sig cap_dryerOperatingState_attr extends Attribute {}
one sig cap_dryerOperatingState_attr_machineState extends cap_dryerOperatingState_attr {}
{
    values = cap_dryerOperatingState_attr_machineState_val
} 
abstract sig cap_dryerOperatingState_attr_machineState_val extends AttrValue {}
one sig cap_dryerOperatingState_attr_machineState_val_pause extends cap_dryerOperatingState_attr_machineState_val {}
one sig cap_dryerOperatingState_attr_machineState_val_run extends cap_dryerOperatingState_attr_machineState_val {}
one sig cap_dryerOperatingState_attr_machineState_val_stop extends cap_dryerOperatingState_attr_machineState_val {}
one sig cap_dryerOperatingState_attr_supportedMachineStates extends cap_dryerOperatingState_attr {}
{
    values = cap_dryerOperatingState_attr_supportedMachineStates_val
} 
abstract sig cap_dryerOperatingState_attr_supportedMachineStates_val extends AttrValue {}
one sig cap_dryerOperatingState_attr_dryerJobState extends cap_dryerOperatingState_attr {}
{
    values = cap_dryerOperatingState_attr_dryerJobState_val
} 
abstract sig cap_dryerOperatingState_attr_dryerJobState_val extends AttrValue {}
one sig cap_dryerOperatingState_attr_dryerJobState_val_cooling extends cap_dryerOperatingState_attr_dryerJobState_val {}
one sig cap_dryerOperatingState_attr_dryerJobState_val_delayWash extends cap_dryerOperatingState_attr_dryerJobState_val {}
one sig cap_dryerOperatingState_attr_dryerJobState_val_drying extends cap_dryerOperatingState_attr_dryerJobState_val {}
one sig cap_dryerOperatingState_attr_dryerJobState_val_finished extends cap_dryerOperatingState_attr_dryerJobState_val {}
one sig cap_dryerOperatingState_attr_dryerJobState_val_none extends cap_dryerOperatingState_attr_dryerJobState_val {}
one sig cap_dryerOperatingState_attr_dryerJobState_val_weightSensing extends cap_dryerOperatingState_attr_dryerJobState_val {}
one sig cap_dryerOperatingState_attr_dryerJobState_val_wrinklePrevent extends cap_dryerOperatingState_attr_dryerJobState_val {}
one sig cap_dryerOperatingState_attr_completionTime extends cap_dryerOperatingState_attr {}
{
    values = cap_dryerOperatingState_attr_completionTime_val
} 
abstract sig cap_dryerOperatingState_attr_completionTime_val extends AttrValue {}