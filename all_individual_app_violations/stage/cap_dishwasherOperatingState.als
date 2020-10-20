
// filename: cap_dishwasherOperatingState.als
module cap_dishwasherOperatingState
open IoTBottomUp
one sig cap_dishwasherOperatingState extends Capability {}
{
    attributes = cap_dishwasherOperatingState_attr
}
abstract sig cap_dishwasherOperatingState_attr extends Attribute {}
one sig cap_dishwasherOperatingState_attr_machineState extends cap_dishwasherOperatingState_attr {}
{
    values = cap_dishwasherOperatingState_attr_machineState_val
} 
abstract sig cap_dishwasherOperatingState_attr_machineState_val extends AttrValue {}
one sig cap_dishwasherOperatingState_attr_machineState_val_pause extends cap_dishwasherOperatingState_attr_machineState_val {}
one sig cap_dishwasherOperatingState_attr_machineState_val_run extends cap_dishwasherOperatingState_attr_machineState_val {}
one sig cap_dishwasherOperatingState_attr_machineState_val_stop extends cap_dishwasherOperatingState_attr_machineState_val {}
one sig cap_dishwasherOperatingState_attr_supportedMachineStates extends cap_dishwasherOperatingState_attr {}
{
    values = cap_dishwasherOperatingState_attr_supportedMachineStates_val
} 
abstract sig cap_dishwasherOperatingState_attr_supportedMachineStates_val extends AttrValue {}
one sig cap_dishwasherOperatingState_attr_dishwasherJobState extends cap_dishwasherOperatingState_attr {}
{
    values = cap_dishwasherOperatingState_attr_dishwasherJobState_val
} 
abstract sig cap_dishwasherOperatingState_attr_dishwasherJobState_val extends AttrValue {}
one sig cap_dishwasherOperatingState_attr_dishwasherJobState_val_airwash extends cap_dishwasherOperatingState_attr_dishwasherJobState_val {}
one sig cap_dishwasherOperatingState_attr_dishwasherJobState_val_cooling extends cap_dishwasherOperatingState_attr_dishwasherJobState_val {}
one sig cap_dishwasherOperatingState_attr_dishwasherJobState_val_drying extends cap_dishwasherOperatingState_attr_dishwasherJobState_val {}
one sig cap_dishwasherOperatingState_attr_dishwasherJobState_val_finish extends cap_dishwasherOperatingState_attr_dishwasherJobState_val {}
one sig cap_dishwasherOperatingState_attr_dishwasherJobState_val_preDrain extends cap_dishwasherOperatingState_attr_dishwasherJobState_val {}
one sig cap_dishwasherOperatingState_attr_dishwasherJobState_val_prewash extends cap_dishwasherOperatingState_attr_dishwasherJobState_val {}
one sig cap_dishwasherOperatingState_attr_dishwasherJobState_val_rinse extends cap_dishwasherOperatingState_attr_dishwasherJobState_val {}
one sig cap_dishwasherOperatingState_attr_dishwasherJobState_val_spin extends cap_dishwasherOperatingState_attr_dishwasherJobState_val {}
one sig cap_dishwasherOperatingState_attr_dishwasherJobState_val_unknown extends cap_dishwasherOperatingState_attr_dishwasherJobState_val {}
one sig cap_dishwasherOperatingState_attr_dishwasherJobState_val_wash extends cap_dishwasherOperatingState_attr_dishwasherJobState_val {}
one sig cap_dishwasherOperatingState_attr_dishwasherJobState_val_wrinklePrevent extends cap_dishwasherOperatingState_attr_dishwasherJobState_val {}
one sig cap_dishwasherOperatingState_attr_completionTime extends cap_dishwasherOperatingState_attr {}
{
    values = cap_dishwasherOperatingState_attr_completionTime_val
} 
abstract sig cap_dishwasherOperatingState_attr_completionTime_val extends AttrValue {}
