# generator of traces
import os

import random

import sys, ipdb, traceback
from IPython import embed

from utils import world_utils
# from utils.world_utils import read_caps, read_files_in_directory, guess_cap_name_from_attribute, \
#     read_caps_from_app_files, get_rules_from_app_files, capabilities_we_care_about, fill_state_variables_possible_values, \
#     guess_app_name_from_rule, append_app_name_to_state, fill_missing_vals, derive_interesting_events, read_channel_connection


# Like this this:
# python3 world.py ~/eclipse-workspace/IOTCOM-github/FormalAnalyzer/out/run_20200921_Bundle2_Safe/stage/ 20 5

def info(type, value, tb):
    traceback.print_exception(type, value, tb)
    ipdb.pm()

sys.excepthook = info

# parse apps
directory_with_apps = sys.argv[1]
number_of_traces_to_have = int(sys.argv[2])

model_physical = sys.argv[3].startswith('t')
if len(sys.argv) >= 5:
    iteration = sys.argv[4]

fs = os.listdir(directory_with_apps)

cap_files, app_files = world_utils.read_files_in_directory(fs)


cap_names_to_attrs, attr_possible_values = world_utils.read_caps(cap_files)

world_utils.read_caps_from_app_files(cap_names_to_attrs, attr_possible_values, app_files)


channels = world_utils.read_channel_connection()
rule_names = world_utils.get_rules_from_app_files(app_files, attr_possible_values)

capabilities_in_home = world_utils.capabilities_we_care_about(rule_names)

interesting_events = world_utils.derive_interesting_events(rule_names, attr_possible_values)

## in each app


# state attrs
# state stuff do not appear in the caps file
# but need to figure out their names and possible values
# rmb to prefix the app name to the name of the state
world_utils.fill_state_variables_possible_values(rule_names, attr_possible_values)

world_utils.fill_missing_vals(rule_names, attr_possible_values)

# generate set of interesting events
## interesting events are events that pass a check
## or negate a check 
### i.e., we generate events based on triggers, conditions, and commands
### for each trigger and condition, we generate 2 event. 1 which enables the trigger/condition, 1 negating it


def reset_state():

    # model of smarthome
    ## state(valuations: Valuations, time_i, finallys : set[Event], globallys: Valuations, current: Event)
    #
    # let's start with this:
    ## state(mappings : Valuations, time_i, finallys : set[Event, current : Event)
    ## valuations : attr -> one val
    ## time_i : index/integer
    state = {'eventuallys': [], 'mappings': {}}
    # at time 0, assign random val to each attr
    for attr in attr_possible_values.keys():
        if len(attr_possible_values[attr]) == 0:
            continue
        if '_runIn' in attr:
            state['mappings'][attr] = 'false'
        else:
            state['mappings'][attr] = random.choice(attr_possible_values[attr])

    return state





# events are (??, attr, vals ) <- TODO apps may share the same device. how to account for this?
# ?? : capability type
# are we working with a simplifying assumption that all caps bind to the same device
# e.g. any app using a switch is bound to the same switch
## TODO this depends on the evaluation bundles

# note that





def conditions_met(state):
    rules_with_met_conditions = []
    condition_objects = {}
    for rule_name, r in rule_names.items():
        rule_condition_met_count = 0
        for condition_name, condition in r['condition'].items():
            # check if individual condition is met

            ## link capability to app_specific_cap 'app_ID16SleepingModeChange.theSwitch'
            rule_cap = world_utils.guess_cap_name_from_attribute(condition['attribute'])

            rule_attr = condition['attribute']
            expected_rule_attr = condition['value']

            if 'cap_state_attr' in rule_attr:
                app_name = world_utils.guess_app_name_from_rule(rule_name)
                rule_attr = world_utils.append_app_name_to_state(app_name, condition)

            if 'cap_location_attr_mode' in rule_attr:
                # special case mode comparisons.
                # Home should be equal to cap_location_attr_mode_val_Home
                new_expected_rule_attr = []
                for expected_attr in expected_rule_attr:
                    new_expected_rule_attr.append(expected_attr)
                    if expected_attr.lower().endswith('home'):
                        new_expected_rule_attr.append( 'cap_location_attr_mode_val_Home')
                    elif expected_attr.lower().endswith('away'):
                        new_expected_rule_attr.append('cap_location_attr_mode_val_Away')

                if state['mappings'][rule_attr] in new_expected_rule_attr or state['mappings'][
                        rule_attr] in new_expected_rule_attr:
                    rule_condition_met_count += 1

            elif state['mappings'][rule_attr] in expected_rule_attr or state['mappings'][rule_attr] in expected_rule_attr:
                rule_condition_met_count += 1
            elif condition['attribute'] in state['mappings'] and (state['mappings'][condition['attribute']] in expected_rule_attr or \
                    state['mappings'][condition['attribute']] in expected_rule_attr):
                rule_condition_met_count += 1
        if rule_condition_met_count == len(r['condition']):
            rules_with_met_conditions.append(rule_name)
            condition_objects[rule_name] = []
            for condition in r['condition'].values():
                condition_objects[rule_name].append(condition)

    print('conditions met', rules_with_met_conditions)
    return rules_with_met_conditions, condition_objects


def triggered_rules(state, event, execution_log):
    rules_triggered = []

    # some rules have no triggers and conditions, need to throttle them
    ignore_always_triggerable = random.randint(0, 100) < 80

    for rule_name, r in rule_names.items():
        if len(r['trigger']) == 0 and len(r['condition']) == 0 and ignore_always_triggerable:
            continue

        if len(r['trigger']) > 0 :
            for trigger_name, trigger in r['trigger'].items():
                if event['attribute'] == trigger['attribute'] and \
                        (trigger['value'] is None or event['value'] in trigger['value']):
                    rules_triggered.append(rule_name)
        else:  # rules without triggers. These are always enabled
            rules_triggered.append(rule_name)

    if len(rules_triggered) > 0:
        execution_log['trigger_condition_commands'].append(event['attribute'] + '__' + event['value'])
    return rules_triggered





# property_to_check = ('cap_momentary_attr_momentary', 'cap_momentary_attr_momentary_val_push', 'cap_presenceSensor_attr_presence', 'cap_presenceSensor_attr_presence_val_not_present')

# create trace of num_events events
num_events = 300
fname = [fpath_part for fpath_part in sys.argv[1].split('/') if 'Bundle' in fpath_part][0]

if len(sys.argv) >= 5:
    fname += iteration

def create_trace():
    def add_eventuallys(state, triggered, conditions, rule_names, condition_objects):
        rules_applied = set(triggered) & set(conditions)
        for rule_applied in rules_applied:
            r = rule_names[rule_applied]
            for command_name, command in r['command'].items():
                state['eventuallys'].append({'attribute': command['attribute'], 'value': command['value'][0]})
                print('\tadding to eventuallys', state['eventuallys'][-1])
                print('\t\tfrom', rule_applied, command_name)

                automated_executed_rules.append(command['attribute'] + '__' + command['value'][0])

            # print('eventuallys', 'sz=', len(state['eventuallys']))
            # print(state['eventuallys'][:5])

            for condition in condition_objects[rule_applied]:
                if 'runIn' in condition['attribute']:
                    # need to change state related to this attribute
                    # print('\t applied ', condition['attribute'])
                    state[condition['attribute']] = False


    def apply_event_to_state(state, event, is_auto=False):
        # just make the state change
        state['mappings'][event['attribute']] = event['value']


        if not is_auto:
            executed_events.append(event['attribute'] + '__' + event['value'])
        else:
            executed_events.append(event['attribute'] + '__' + event['value'] + "_auto")

    def transmit_info_through_channels(state, event, channels, cap_names_to_attrs, attr_possible_values,
                                       capabilities_in_home):
        # change state mappings based on the sensors in the event
        capability_from_event = world_utils.guess_cap_name_from_attribute(event['attribute'])
        if not model_physical:
            return
        new_events= []
        # has channels?
        for channel_name, channel in channels.items():
            if capability_from_event not in channel['actuators']:
                continue
            # pick a attr of the sensors
            sensors_affected = channel['sensors']

            attrs_affected = [attr for sensor in sensors_affected for attr in cap_names_to_attrs[sensor] if
                              sensor in capabilities_in_home]

            for attr_affected in attrs_affected:
                possible_values = list(attr_possible_values[attr_affected])
                if len(possible_values) == 0:
                    print(attr_affected, 'has no values?')
                    continue
                new_event = {'attribute': attr_affected, 'value': random.choice(possible_values)}
                print('\ttransmission through channel', 'from:', event['value'], 'to', new_event['value'], ' through',
                      channel_name, ' sensors=', sensors_affected)

                # do physical channel changes occur immediately? or through eventuallys
                # state['eventuallys'].append({'attribute': new_event['attribute'], 'value': new_event['value'][0]})
                # or
                apply_event_to_state(state, new_event, is_auto=False)
                new_events.append(new_event)
        return new_events
    #
    def execute_event(state, event, execution_log, is_auto=False, allow_physical=True):
        previous_conditions, _ = conditions_met(state) # for bookkeeping. Used to determine if any conditions changed

        apply_event_to_state(state, event, is_auto)
        if allow_physical:
            channel_new_events = transmit_info_through_channels(state, event, channels, cap_names_to_attrs, attr_possible_values,
                                       capabilities_in_home)
        else:
            channel_new_events = []
        triggered = triggered_rules(state, event, execution_log)
        for channel_new_event in channel_new_events:
            channel_triggered_rules = triggered_rules(state, channel_new_event, execution_log)
            for new_rule in channel_triggered_rules:
                if new_rule not in triggered:
                    triggered.append(new_rule)


        # print('\ttriggered', triggered)
        conditions, condition_objects = conditions_met(state)

        if len(set(conditions) - set(previous_conditions)) > 0:
            new_conditions_met = set(conditions) - set(previous_conditions)
            # this event caused a change
            execution_log['trigger_condition_commands'].append(event['attribute'] + '__' + event['value'])

        # print('\tconditions', conditions)
        add_eventuallys(state, triggered, conditions, rule_names, condition_objects)

    state = reset_state()

    automated_executed_rules = []
    executed_events = []
    trigger_condition_commands = []
    execution_log = {'trigger_condition_commands': trigger_condition_commands, 'executed_events': executed_events}
    num_commands = 0
    # at the start of each time
    for i in range(num_events):
        print('i=', i)

        # generate event based on interesting_events
        is_auto = False
        event = None
        if len(state['eventuallys']) > 0 and random.randint(0, 100) < 50:
            event = state['eventuallys'].pop(0)
            print('\ttaking from eventuallys', event)
            num_commands += 1

            # set variables for bookkeeping. 
            execution_log['trigger_condition_commands'].append(event['attribute'] + '__' + event['value'])
            is_auto = True

        if event is None:
            event = random.choice(interesting_events)

        print('\tevent=', event)
        if isinstance(event['value'], list):
            raise Exception("shit")
        # execute
        execute_event(state, event, execution_log, is_auto)

        # if event['value'] == 'cap_state_attr_runIn_val_on':
        #     embed()

        # check property
        if is_auto:
            pass
            # if event['attribute'] in [property_to_check[0], property_to_check[2]]:
            #     if state['mappings'][property_to_check[0]] == property_to_check[1] and  state['mappings'][property_to_check[2]] == property_to_check[3]:
            #         print('failed property!')
            #         # failed_property = True
            # break
        if num_commands >= 10:
            print('reached 10 events')
            break
    print('command count', num_commands)
    # exhaust the eventuallys
    print('clearing pending events')
    total_to_clear = len(state['eventuallys'])
    # embed()
    while len(state['eventuallys']) > 0:
        event = state['eventuallys'].pop(0)
        print('event', 'at i =', i, ' (after event generation) event=', event)
        # execute
        execute_event(state, event, execution_log,is_auto=True, allow_physical=False)

        # if event['attribute'] in [property_to_check[0], property_to_check[2]]:
        #     if state['mappings'][property_to_check[0]] == property_to_check[1] and state['mappings'][property_to_check[2]] == \
        #             property_to_check[3]:
        # print('failed property!')
        # failed_property = True
        # break

        i += 1

        if i >= total_to_clear * 0.5:
            print('\tremaing : ', len(state['eventuallys']))
            break

    # embed()
    print('====done====')
    # print(automated_executed_rules)
    print('executed events:')
    print(executed_events)
    print('number of autos', len([event for event in executed_events if 'auto' in event]))
    print('number of executed', len(executed_events))
    print('number of trigger_condition_commands', len(trigger_condition_commands))
    print('executed interesting events')
    print(trigger_condition_commands)



    return executed_events, trigger_condition_commands


sequences_of_events = []
sequences_of_interesting_events = []
for i in range(number_of_traces_to_have):
    one_sequence_of_events, one_sequence_of_only_interesting = create_trace()
    sequences_of_events.append(one_sequence_of_events)
    sequences_of_interesting_events.append(one_sequence_of_only_interesting)


with open('trace_' + fname + '.txt', 'w+') as outfile:
    for executed_events in sequences_of_events:
        outfile.write('<START> ') # DSM needs this weird thing
        for event in executed_events:
            outfile.write(event + ' ')
        outfile.write('<END> \n')

with open('trace_rule_events_' + fname + '.txt', 'w+') as outfile:
    for executed_events in sequences_of_interesting_events:
        outfile.write('<START> ') # DSM needs this weird thing
        for event in executed_events:
            outfile.write(event + ' ')
        outfile.write('<END> \n')


if True:  # failed_property
    pass

print()
print('written to ', 'trace_' + fname + '.txt')
print()
print()

embed()
