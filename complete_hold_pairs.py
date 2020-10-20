import os

import random

import sys, ipdb, traceback
from IPython import embed

from utils import world_utils

# from utils.world_utils import read_caps, read_files_in_directory, guess_cap_name_from_attribute, \
#     read_caps_from_app_files, get_rules_from_app_files, capabilities_we_care_about, fill_state_variables_possible_values, \
#     guess_app_name_from_rule, append_app_name_to_state, fill_missing_vals, derive_interesting_events, read_channel_connection


# python3 complete_hold_pairs.py ~/eclipse-workspace/IOTCOM-github/FormalAnalyzer/out/run_20200921_Bundle1_Safe/stage/
# then mv the assertions_* file into the stage directory

def info(type, value, tb):
    traceback.print_exception(type, value, tb)
    ipdb.pm()
sys.excepthook = info

# parse apps
fs = os.listdir(sys.argv[1])

pairs_file = sys.argv[1] + '/holdPairs.txt'

# read
pairs = []
with open(pairs_file) as infile:
    for line in infile:
        line = line.strip()
        try:
            command_attr, command_value, event_attr, event_value = line.split(',')
            pairs.append((command_attr, command_value, event_attr, event_value))
        except:
            continue

cap_files, app_files = world_utils.read_files_in_directory(fs)

cap_names_to_attrs, attr_possible_values = world_utils.read_caps(cap_files)

world_utils.read_caps_from_app_files(cap_names_to_attrs, attr_possible_values, app_files)

channels = world_utils.read_channel_connection()
rule_names = world_utils.get_rules_from_app_files(app_files, attr_possible_values)

capabilities_in_home = world_utils.capabilities_we_care_about(rule_names)

interesting_events = world_utils.derive_interesting_events(rule_names, attr_possible_values)
command_events = world_utils.derive_interesting_events(rule_names, attr_possible_values, ["commands_only", 'permit_all'])


# from hold pairs
# we know the command, and the root interesting_event
#
# From the root, traverse to the command,
# the path completes the holdPairs
#

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



def apply_event_to_state(state, event, is_auto=False):
    # just make the state change
    state['mappings'][event['attribute']] = event['value']

def transmit_info_through_channels(state, event, channels, cap_names_to_attrs, attr_possible_values,
                                   capabilities_in_home):
    # change state mappings based on the sensors in the event
    capability_from_event = world_utils.guess_cap_name_from_attribute(event['attribute'])

    new_events = []
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
            new_events.append(new_event)
            print('\ttransmission through channel', 'from:', event['value'], 'to', new_event['value'],
                  ' through',
                  channel_name, ' sensors=', sensors_affected)
            apply_event_to_state(state, new_event, is_auto=False)
    return new_events


def triggered_rules(state, event, execution_log):
    rules_triggered = []
    for rule_name, r in rule_names.items():
        if len(r['trigger']) > 0 :
            for trigger_name, trigger in r['trigger'].items():
                if event['attribute'] == trigger['attribute'] and \
                        (trigger['value'] is None or event['value'] in trigger['value']):
                    rules_triggered.append(rule_name)
        else:  # rules without triggers. These are always enabled
            rules_triggered.append(rule_name)

    # do the same for all sensors affected by the physical channels
    new_events = transmit_info_through_channels(state, event, channels, cap_names_to_attrs, attr_possible_values,
                                   capabilities_in_home)
    for new_event in new_events:
        for rule_name, r in rule_names.items():
            if len(r['trigger']) > 0 :
                for trigger_name, trigger in r['trigger'].items():
                    if new_event['attribute'] == trigger['attribute'] and \
                            (trigger['value'] is None or new_event['value'] in trigger['value']):
                        rules_triggered.append(rule_name)
            else:  # rules without triggers. These are always enabled
                rules_triggered.append(rule_name)

    return rules_triggered


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
            if state['mappings'][rule_attr] in expected_rule_attr or state['mappings'][rule_attr] in expected_rule_attr:
                rule_condition_met_count += 1
        if rule_condition_met_count == len(r['condition']):
            rules_with_met_conditions.append(rule_name)
            condition_objects[rule_name] = []
            for condition in r['condition'].values():
                condition_objects[rule_name].append(condition)

    # invoke state changes
    transmit_info_through_channels(state, event, channels, cap_names_to_attrs, attr_possible_values,
                                       capabilities_in_home)
    # do it again
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
            if state['mappings'][rule_attr] in expected_rule_attr or state['mappings'][rule_attr] in expected_rule_attr:
                rule_condition_met_count += 1
        if rule_condition_met_count == len(r['condition']):
            rules_with_met_conditions.append(rule_name)
            condition_objects[rule_name] = []
            for condition in r['condition'].values():
                condition_objects[rule_name].append(condition)


    return rules_with_met_conditions, condition_objects


def r_with_conditions_touched(event):
    touched = set()
    for rule_name, r in rule_names.items():
        for condition_name, condition in r['condition'].items():
            if condition['attribute'] == event['attribute']:
                touched.add(rule_name)

    state = {'mappings': {}}
    transmit_info_through_channels(state, event, channels, cap_names_to_attrs, attr_possible_values,
                                               capabilities_in_home)

    for rule_name, r in rule_names.items():
        for condition_name, condition in r['condition'].items():
            for key in state['mappings'].keys():
                # print('comparing ', state['mappings'][key], 'with ', condition['attribute'])
                if key == condition['attribute']:
                    touched.add(rule_name)

    # vacuously touched (no conditions)
    for rule_name, r in rule_names.items():
        if len(r['condition']) == 0:
            touched.add(rule_name)

    return touched


def execute_event(state, event, execution_log, is_auto=False):
    apply_event_to_state(state, event, is_auto)
    transmit_info_through_channels(state, event, channels, cap_names_to_attrs, attr_possible_values,
                                   capabilities_in_home)
    triggered = triggered_rules(state, event, execution_log)
    # print('\ttriggered', triggered)



def apply_rule_and_get_triggered_rules(rule_applied):
    all_triggered = set()
    all_condition_touched = set()
    for command_name, command in rule_applied['command'].items():

        event = {'attribute': command['attribute'], 'value': command['value'][0]}

        apply_event_to_state(state, event, True)


        r_triggered = triggered_rules(state, event, {})
        all_triggered.update(r_triggered)

        touched_conditions = r_with_conditions_touched(event)
        all_condition_touched.update(touched_conditions)





    return all_triggered, all_condition_touched


# find commands that can trigger anytime without cause
# sometimes there are such commands in the models
spontaneuous_occuring_commands = set()
for command_event in command_events:

    for rule in rule_names.values():
        for command in rule['command'].values():
            if command['value'][0] == command_event['value']:
                # take the first trigger if there is
                if len(rule['trigger']) > 0:
                    trigg = list(rule['trigger'].values())[0]

                    interesting_event = {'attribute': trigg['attribute'],
                                         'value': trigg['value'][0] if trigg['value'] is not None else None}

                elif len(rule['condition']) > 0:
                    cond = list(rule['condition'].values())[0]

                    interesting_event = {'attribute': cond['attribute'],
                                         'value': cond['value'][0] if cond['value'] is not None else None}
                else:
                    print('nothing to go with...')
                    spontaneuous_occuring_commands.add((command_event['attribute'], command_event['value']))
                    break





# construct the traversal
paths = []


for pair in pairs:

    print('=====starting with new pair=====')
    command_attr, command_value, event_attr, event_value = pair
    print('commands:', command_attr, command_value)
    print('event:', event_attr, event_value)

    state = reset_state()
    starting_rules = set()

    # traverse for one pair
    # first find the starting rule
    for rule_name, rule in rule_names.items():
        match_trigger = False
        for trigger_name, trigger in rule['trigger'].items():
            if trigger['attribute'] == event_attr and (
                    trigger['value'] is None or event_value == 'null' or event_value in trigger['value']):
                match_trigger = True

        match_condition = False
        for _, condition in rule['condition'].items():
            if condition['attribute'] == event_attr and (
                    condition['value'] is None or event_value == 'null' or event_value in condition['value']):
                match_condition = True

        if match_trigger or match_condition:
            starting_rules.add(rule_name)

    if starting_rules is None:
        # weird....
        continue

    print('found rule', starting_rules)
    # apply rule
    reached_command = False


    queue = []
    for starting_rule in starting_rules:
        starting_path = []
        # add all triggers and conditions
        for _, trigger in rule_names[starting_rule]['trigger'].items():
            starting_path.append((trigger['attribute'], trigger['value'][0] if trigger['value'] is not None else None ))

        for _, condition in rule_names[starting_rule]['condition'].items():
            if condition['value'] is not None and 'range_' in condition['value'][0]:
                continue
            starting_path.append(('cond:' + condition['attribute'], condition['value'][0] if condition['value'] is not None else None))

        queue.append((starting_rule, starting_path))

    while  len(queue) > 0:
        current_rule_name, path = queue.pop(0)   # queue -> bfs
        rule_applied = rule_names[current_rule_name]
        print('\tcurrent item : ', current_rule_name, path )

        # terminating condition
        for _, command in rule_applied['command'].items():
            if command['attribute'] == command_attr and command_value in command['value']:
                reached_command = True
                path.append((command_attr, command_value))

                paths.append(path)
                break

        # if reached_command:
        #     break
        if reached_command and len(path) > 3:  # 3
            # probably a bit too much
            break


        all_triggered, r_conditions = apply_rule_and_get_triggered_rules(rule_applied)

        next_rules = set(all_triggered) & set(r_conditions)

        print('\t trigger=', all_triggered)
        print('\t conditions=', r_conditions)
        print()
        print('next_rules', next_rules)
        print()

        for next_rule in next_rules:
            next_path = path.copy()
            # next_path.append(next_rule)
            for _, trigger in rule_names[next_rule]['trigger'].items():
                next_path.append((trigger['attribute'], trigger['value'][0] if trigger['value'] is not None else None))

            for _, condition in rule_names[next_rule]['condition'].items():
                if condition['value'] is not None and 'range_' in condition['value'][0]:
                    next_path.append(('cond:' + condition['attribute'], None))
                    continue
                next_path.append(('cond:' + condition['attribute'], condition['value'][0] if condition['value'] is not None else None))

            queue.append((next_rule, next_path))


    print(reached_command)
    if not reached_command:
        # physical channels?
        print()
        raise Exception('missing path...')


new_pairs_file = sys.argv[1] + '/newHoldPairs.txt'
print(paths)


with open(new_pairs_file, 'w+') as outfile:
    # format: command_attr, command_value, event_attr, event_value, event_attr, event_value, ...
    for path in paths:
        # all possible paths, including shorter ones
        for i in range(0, len(path) - 1):
            if path[i][0].startswith('cond:') and 'runIn' not in path[i][0]:  # we only start paths with triggers
                continue

            command_attr, command_value = path[-1]
            line = command_attr + ',' + command_value + ','

            for event_attr, event_value in path[i:-1]:
                line += event_attr + ',' + ((event_value + ',') if event_value is not None else 'null' + ',')

            outfile.write(line)
            outfile.write('\n')

    for event in spontaneuous_occuring_commands:
        line = event[0] + ',' + event[1] + ','
        outfile.write(line)
        outfile.write('\n')

print()
print()
print('written to', new_pairs_file)
print()
#

embed()

