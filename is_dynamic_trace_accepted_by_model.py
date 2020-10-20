"""
inputs: 1) pairs of (command, interesting_event)
        2) traces file

This forms the rules using the pairs.
    command near interesting_event

i.e. for all interesting_event near the command
we check that a trace has the interesting_event occuring within N events before or after the command
If not, we reject the trace

python3 is_dynamic_trace_accepted_by_model.py ~/eclipse-workspace/IOTCOM-github/FormalAnalyzer/out/run_20200921_Bundle2_Safe/stage/newHoldPairs.txt bundle_2_new/input.txt trace_run_20200921_Bundle2_Safe.txt 120  120
"""
import sys
from IPython import embed

import sys, ipdb, traceback


def info(type, value, tb):
    traceback.print_exception(type, value, tb)
    ipdb.pm()


sys.excepthook = info

pairs_file = sys.argv[1]
traces_file = sys.argv[2]
static_traces_file = sys.argv[3]

RANGE_TO_INSPECT = int(sys.argv[4])
try:
    RANGE_TO_LOOK_FOR_MISSING_EVENTS = int(sys.argv[5])
except:
    RANGE_TO_LOOK_FOR_MISSING_EVENTS = RANGE_TO_INSPECT

# read
pairs = []
with open(pairs_file) as infile:
    for line in infile:
        line = line.strip()
        line_components = line.split(',')
        # print(line_components)
        command_attr, command_value = line_components[:2]

        context = []
        for i in range(2, len(line_components) - 1, 2):
            event_attr = line_components[i]
            event_value = line_components[i + 1]

            context.append((event_attr, event_value))
        pairs.append((command_attr, command_value, context))

traces = []
with open(traces_file) as infile:
    for line in infile:
        trace = []

        next_event_is_auto = False
        auto_event_to_match = None
        for event in line.split():
            if event == '<START>' or event == '<END>':
                continue
            if '_auto_' in event and  'location' not in event:

                if '_' + event.split('_auto_')[1] in trace[-1]:
                    # print('matched ', event, 'to ', trace[-1])
                    last_event = trace[-1]
                    last_event = last_event + '_auto'
                    trace[-1] = last_event
                else:
                    # next event has auto
                    next_event_is_auto = True
                    auto_event_to_match = event.split('_auto_')[1]

            elif '_auto_' in event and 'location' in event:
                if 'location_mode_change_' in event:
                    event = 'location_mode_change_' + event.split('location_mode_change_')[1] + '_auto'
                    trace.append(event)
                else:
                    # event = 'location_mode_change_' + '' + '_auto'
                    # trace.append(event)
                    if event.split('_auto_')[1] in trace[-1]:
                        last_event = trace[-1]
                        last_event = last_event + '_auto'
                        trace[-1] = last_event

            else:
                if next_event_is_auto and '_' + auto_event_to_match in event:
                    next_event_is_auto = False
                    auto_event_to_match = None

                    trace.append(event + '_auto')
                elif next_event_is_auto:

                    # evidently, not the next event!!!
                    # traverse back and pick the most recent event that matches
                    for j in range(1, len(trace)):
                        if '_' + auto_event_to_match in trace[-1 * j]:
                            next_event_is_auto = False
                            auto_event_to_match = None
                            # print('setting to none2', next_event_is_auto)

                            trace[-1 * j] = trace[-1 * j] + '_auto'
                            break

                else:
                    trace.append(event)
        traces.append(trace)



def vocab_match(pairs, traces):
    pair_values = [(attr,value) for attr, value, context in pairs]
    pair_values.extend([(event_attr, event_value)  for attr, value, context in pairs for event_attr, event_value in context if event_value != 'null'])

    vocab_pair_values = set([(attr, pair_value) if 'cond:' not in attr else (attr.split('cond:')[1],pair_value) for attr, pair_value in pair_values])

    trace_vocab = set([event if 'auto' not in event else event.split('_auto')[0] for one_trace in traces for event in one_trace])

    # print(trace_vocab)
    result = {}
    # try to find mapping of trace_vocab to vocab_pair_values
    for word in trace_vocab:
        if len(word) < 2:
            continue

        suffix = word.split('_')[-1]

        # print('word', word)

        for attr, value in vocab_pair_values:
            value = value.replace('.', '_').replace('(', '_').replace(')', '_') # deal with some weirdness related to bundle 2's modes
            add_mapping_if_enough_parts_match(attr, result, suffix, value, word)
        if word not in result:
            # print('missing ', word)
            result[word] = 'noise'
    return result


def add_mapping_if_enough_parts_match(attr, result, suffix, value, word):
    if (suffix in value.split('_')[-1] and '_' + suffix in value) or \
            ('departed' in suffix and 'not_present' in value) or \
            ('arrived' in suffix and 'val_present' in value):

        word_parts = word.split('_')[:-1]  # other than the last part, should have another part match
        if any(['_' + word_part.lower() in value.lower() for word_part in word_parts if len(word_part) > 1]):
            result[word] = attr + '__' + value

            # print('assign', word, 'to', value)


vocab_map = vocab_match(pairs,traces )

missing_mappings = set([key for key in vocab_map.keys() if vocab_map[key] == 'noise'])

# sometimes, the pairs file doesn't have any the necessary events. match the missing stuff to static events
static_traces = []
with open(static_traces_file) as infile:
    for line in infile:
        for event in line.split():
            if '__' not in event:
                continue
            attr, value = event.split('__')

            for missing_event in missing_mappings:
                suffix = missing_event.split('_')[-1]

                add_mapping_if_enough_parts_match(attr, vocab_map, suffix, value, missing_event)




# print(vocab_map)
# embed()

# trace conversion!
new_traces = []
for trace in traces:
    new_trace= []
    for event  in trace:
        if event.endswith('_auto'):
            new_event = vocab_map[event.split('_auto')[0]]

            if new_event == 'noise':
                continue
            new_event += '_auto'

            # if new_event == 'cap_motionSensor_attr_motion__cap_motionSensor_attr_motion_val_active_auto':
            #     embed()
        else:
            new_event = vocab_map[event]

        # if
        new_trace.append(new_event)

    new_traces.append(new_trace)

traces = new_traces

# process
# 'likely' invariants
commands_required_events = {}
for command_attr, command_value, context in pairs:
    if command_attr + "__" + command_value not in commands_required_events:
        commands_required_events[command_attr + "__" + command_value] = []

    path = []
    for event_attr, event_value in context:
        path.append(event_attr + '__' + event_value)
    commands_required_events[command_attr + "__" + command_value].append(path)

# debugging print
# for command, possible_paths in commands_required_events.items():
#     print('command', command, ' requires one of ')
#     for path in possible_paths:
#         print('\t\t', path)

# embed()
# debug

commands_without_requirements = set()
rejects = 0
accepts = 0

num_accepts_because_no_command_requirements = 0

unexplained = []

rejects_caused_by_missing = 0
matter_of_distance = []
missing_event = []


def is_trace_accepted(trace):
    global rejects_caused_by_missing
    # a trace is accepted if
    # for all commands
    # there is one event nearby that explains it
    positions_of_commands = []
    for i, event in enumerate(trace):
        if '_auto' in event:  # is a command
            positions_of_commands.append(i)
    # print(positions_of_commands)
    all_explaned = True
    if len(positions_of_commands) > 0:
        all_explaned = is_every_command_explained(trace, positions_of_commands)

    if not all_explaned:
        # print('not all explained')
        return False

    any_missing_event = detect_missing_action(trace)
    if any_missing_event:
        rejects_caused_by_missing += 1
        # print('some event missing')
        # print('in trace= ', trace)
        # embed()
        return False

    return True


def detect_missing_action(trace):
    global matter_of_distance
    # iterate up the list of events

    #
    position_of_explanations_of_action = {}
    expected_actions = {}
    for i, event in enumerate(trace):

        # if < 0, its a cooldown, do not allow it to resurface immediately
        expected_actions = {key: value + 1 if value < 0 else value for key, value in expected_actions.items() if
                            value != 0}
        expected_actions = {key: value for key, value in expected_actions.items() if value != 0}

        #
        if event.split('_auto')[0] in expected_actions and expected_actions[event.split('_auto')[0]] > 0:
            # print('resolved', event, 'at i =', i, ' its expiry was at', expected_actions[event.split('_auto')[0]])

            expected_actions[event.split('_auto')[0]] = -1 * RANGE_TO_INSPECT

        # detect if any expected event has expired
        for action, expiry in expected_actions.items():
            if expiry > 0 and expiry < i:
                # expired
                # print('missing', action, 'expected at expiry=', expiry, 'but is at', (i + trace[i:].index(action + '_auto')) if (action + '_auto') in trace[i:] else ' not in trace at all')
                if (action + '_auto') in trace[i:]:
                    matter_of_distance.append((i + trace[i:].index(action + '_auto')))
                missing_event.append(action)
                # embed()
                # raise Exception()
                return True

        for command_attr_value in commands_required_events.keys():
            if command_attr_value not in position_of_explanations_of_action:
                position_of_explanations_of_action[command_attr_value] = {}
            # check if any command is now explained from the traces
            # these form the expected actions
            # we expect these actions in the next 10? events in the trace
            # otherwise we consider them as missing

            explained, satisfied_path, witness = is_command_explained(
                command_attr_value, i + 1, position_of_explanations_of_action[command_attr_value], trace,
                require_explicit_condition_match=True)
            if explained:

                if command_attr_value not in expected_actions:
                    # print('expecting', command_attr_value, 'when i=', i + 1 + RANGE_TO_LOOK_FOR_MISSING_EVENTS)
                    # print('\t satisfied path', satisfied_path)
                    # print('\t\tseemingly triggered by i =', i + 1, ', event=', event)
                    # print('\t\twitness=', witness)
                    expected_actions[command_attr_value] = i + 1 + RANGE_TO_LOOK_FOR_MISSING_EVENTS

    return False


def is_every_command_explained(trace, positions_of_commands):
    position_of_explanations = {}

    for position_of_commands in positions_of_commands:

        # prevent weird errors due to undefined initial conditions:
        if position_of_commands < 15:
            continue

        command = trace[position_of_commands]

        # e.g. 'cap_switch_attr_switch__cap_switch_attr_switch_val_off_auto'
        # all of these assumes that command_value is enough to identify a command
        command_attr_value = command.split('_auto')[0]

        # debugging, bookkeeping
        unexplained.append(command_attr_value)

        explained, satisfied_path, _ = is_command_explained(command_attr_value, position_of_commands,
                                                            position_of_explanations,
                                                            trace)
        # print('position', position_of_commands, 'explained=', explained, 'command_attr_value',command_attr_value )
        if not explained:  # one command unexplained -> not every command is explained!
            return False
    return True


# require_explicit_condition_match -> TRUE if trying to figure out what events MUST occur
def is_command_explained(command_attr_value, position_of_commands, position_of_explanations, trace,
                         require_explicit_condition_match=False):
    # print('checking', command_attr_value)
    # if command_attr_value == 'cap_location_attr_mode__cap_location_attr_mode_val_Home':
        # print("checking cap_location_attr_mode__cap_location_attr_mode_val_Home against", trace[:position_of_commands])
        # print('requiring ', commands_required_events[command_attr_value])
    explained = False
    if command_attr_value in commands_required_events:
        if command_attr_value not in position_of_explanations:
            position_of_explanations[command_attr_value] = []

        min_position = max(0, position_of_commands - RANGE_TO_INSPECT)
        max_position = min(len(trace), position_of_commands)

        # print(commands_required_events[command_attr_value])
        for possible_path in commands_required_events[command_attr_value]:
            # print('testing against path', possible_path)
            position_of_explanations[command_attr_value] = []

            j = 0

            # for debugging
            possible_path_witness = {}

            # just compare strings
            string_to_match, check_negation, j = get_string_to_check(possible_path, j)

            # print('matching for ', string_to_match, check_negation, j )
            if string_to_match is None and len(check_negation) == 0:
                # in this case, we are done.
                # This path exists, and we are happy
                explained = True
                break
            elif string_to_match is None and len(check_negation) > 0:
                # corner case. When no triggers, but some condition

                explained = detect_when_no_direct_match_but_has_conditions(check_negation, explained, max_position,
                                                                           min_position,
                                                                           require_explicit_condition_match, trace)

                # if not explained:
                #     print('unexplained?')
                #
                break  # always break cos nothing to match. In this case, explained = False (from its initial assignment)

            state_for_tracking_negated = {}
            # print('will search betw', min_position,  max_position)
            for i, event in enumerate(trace[min_position: max_position]):
                # check if any of check_negation has been negated
                for condition_event in check_negation:
                    #   check condition's attribute                 not exact match
                    if condition_event.split("__")[0] in event and condition_event not in event:
                        # is negation then
                        if condition_event not in condition_event:  # but if at some point it is true, then its possible
                            state_for_tracking_negated[condition_event] = True

                    elif condition_event in event:  # if its a match, restore. Or at some point it is true
                        state_for_tracking_negated[condition_event] = False
                        break

                # check if all conditions are explicitly met. This is used for only require_explicit_condition_match
                if require_explicit_condition_match:
                    all_conditions_met = True
                    for condition_event in check_negation:
                        if condition_event not in state_for_tracking_negated or state_for_tracking_negated[
                            condition_event]:
                            all_conditions_met = False

                else:
                    all_conditions_met = None

                # print('i', i, ' event', event)
                # print('string_to_match', string_to_match)
                # print(state_for_tracking_negated)
                if string_to_match in event and (min_position + i) not in position_of_explanations[command_attr_value]:

                    if any([item for _, item in state_for_tracking_negated.items()]):
                        # print('cannot match as negated condition detected')
                        pass
                    else:
                        if require_explicit_condition_match:
                            if not all_conditions_met:
                                # print('continuing due to missing condition. cannot advance to next clause yet')
                                continue

                        # print('oh my')
                        position_of_explanations[command_attr_value].append(min_position + i)
                        possible_path_witness[string_to_match] = min_position + i
                        # print('adding witness')

                        string_to_match, check_negation, j = get_string_to_check(possible_path, j)
                        # print('matching for ', string_to_match, check_negation, j)
                        if string_to_match is None:
                            # in this case, we are done.
                            # This path exists, and we are happy

                            # check if any conditions neglected
                            explained = detect_when_no_direct_match_but_has_conditions(check_negation, explained,
                                                                                       max_position,
                                                                                       min_position,
                                                                                       require_explicit_condition_match,
                                                                                       trace)
                            # explained = True
                            break

            if explained:  # as long as one path has explained the command, move to the next command
                break
            # if 'auto' in event and command in event:
            #   explained = False # if explained was true, its used to explain this event
    else:
        commands_without_requirements.add(command_value)  # no required events
        explained = False  # not in commands_required_events -> nothing should be able to trigger it
        # print('reject as we dont know what its context looks like. Its missing')
        # embed()
        possible_path = []
        possible_path_witness = {}
    return explained, possible_path, possible_path_witness


def detect_when_no_direct_match_but_has_conditions(check_negation, explained, max_position, min_position,
                                                   require_explicit_condition_match, trace):
    state_for_tracking_negated = {}
    for condition_event in check_negation:
        for i, event in enumerate(trace[min_position: max_position]):

            #   check condition's attribute                 not exact match
            if condition_event.split("__")[0] in event and condition_event not in event:
                # is negation then
                if condition_event not in condition_event:
                    state_for_tracking_negated[condition_event] = True

            elif condition_event in event:  # if its a match, restore
                state_for_tracking_negated[condition_event] = False
                # kinda done?
                break
    if not require_explicit_condition_match:
        if not any([item for _, item in state_for_tracking_negated.items()]):
            explained = True
    else:
        # need all events in check_negation to be False
        all_conditions_met = True
        for condition_event in check_negation:
            if condition_event not in state_for_tracking_negated or state_for_tracking_negated[condition_event]:
                all_conditions_met = False
        if all_conditions_met:
            # print('1')
            explained = True
    return explained


def get_string_to_check(possible_path, j):
    if j >= len(possible_path):
        return None, [], j

    required_event = possible_path[j]
    string_to_check = required_event if not required_event.endswith('null') else required_event.split('__')[0]

    check_negation = []

    if 'cond:' in string_to_check:
        check_negation.append(string_to_check.split('cond:')[1])
        string_to_check = None
    j += 1
    if j >= len(possible_path):
        # return None, check_negation, j
        return string_to_check, check_negation, j

    next_event = possible_path[j]
    while 'cond:' in next_event:
        check_negation.append(next_event.split('cond:')[1])

        j += 1
        if j < len(possible_path):
            next_event = possible_path[j]
        else:
            return string_to_check, check_negation, j

    return string_to_check, check_negation, j


for num, trace in enumerate(traces):
    accepted = is_trace_accepted(trace)

    if not accepted:
        # print('reject trace', num)
        # print()
        rejects += 1
    else:
        # print('accept')
        # print()
        # embed()
        accepts += 1

# print('done')
# print('length of traces', len(traces))
# print('commands_without_requirements', commands_without_requirements)
#
#
# print('rejects', rejects)
# print('accepts', accepts)
#

# # print('missing_event', missing_event)
#
# # embed()


print(accepts / (rejects + accepts))
