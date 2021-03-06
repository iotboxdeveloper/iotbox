
// filename: cap_mediaInputSource.als
module cap_mediaInputSource
open IoTBottomUp
one sig cap_mediaInputSource extends Capability {}
{
    attributes = cap_mediaInputSource_attr
}
abstract sig cap_mediaInputSource_attr extends Attribute {}
one sig cap_mediaInputSource_attr_inputSource extends cap_mediaInputSource_attr {}
{
    values = cap_mediaInputSource_attr_inputSource_val
} 
abstract sig cap_mediaInputSource_attr_inputSource_val extends AttrValue {}
one sig cap_mediaInputSource_attr_inputSource_val_AM extends cap_mediaInputSource_attr_inputSource_val {}
one sig cap_mediaInputSource_attr_inputSource_val_CD extends cap_mediaInputSource_attr_inputSource_val {}
one sig cap_mediaInputSource_attr_inputSource_val_FM extends cap_mediaInputSource_attr_inputSource_val {}
one sig cap_mediaInputSource_attr_inputSource_val_HDMI extends cap_mediaInputSource_attr_inputSource_val {}
one sig cap_mediaInputSource_attr_inputSource_val_HDMI2 extends cap_mediaInputSource_attr_inputSource_val {}
one sig cap_mediaInputSource_attr_inputSource_val_USB extends cap_mediaInputSource_attr_inputSource_val {}
one sig cap_mediaInputSource_attr_inputSource_val_YouTube extends cap_mediaInputSource_attr_inputSource_val {}
one sig cap_mediaInputSource_attr_inputSource_val_aux extends cap_mediaInputSource_attr_inputSource_val {}
one sig cap_mediaInputSource_attr_inputSource_val_bluetooth extends cap_mediaInputSource_attr_inputSource_val {}
one sig cap_mediaInputSource_attr_inputSource_val_digital extends cap_mediaInputSource_attr_inputSource_val {}
one sig cap_mediaInputSource_attr_inputSource_val_melon extends cap_mediaInputSource_attr_inputSource_val {}
one sig cap_mediaInputSource_attr_inputSource_val_wifi extends cap_mediaInputSource_attr_inputSource_val {}
one sig cap_mediaInputSource_attr_supportedInputSources extends cap_mediaInputSource_attr {}
{
    values = cap_mediaInputSource_attr_supportedInputSources_val
} 
abstract sig cap_mediaInputSource_attr_supportedInputSources_val extends AttrValue {}
