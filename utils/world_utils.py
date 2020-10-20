import random
import sys


def read_channel_connection():
    channels = {}
    with open(sys.argv[1] +'/' + 'IoTChannel.als') as infile:
        for line in infile:
            if 'extends Channel' in line:
                channel_name = line.split('one sig ')[1].split(' extends Channel')[0]
                channels[channel_name] = {}
            elif 'sensors' in line and '=' in line:
                sensors = line.split('= ')[1].split('+')
                sensors = [sensor.strip() for sensor in sensors]

                channels[channel_name]['sensors'] = sensors

            elif 'actuators' in line and '='  in line:
                actuators = line.split('= ')[1].split('+')
                actuators = [actuator.strip() for actuator in actuators]

                channels[channel_name]['actuators'] = actuators
    return channels



def read_caps(cap_files):
    cap_names_to_attrs = {}
    attr_possible_values = {}
    # in each cap file
    for cap_file in cap_files:
        with open(sys.argv[1] +'/' + cap_file) as infile:
            for line in infile:
                # print(line)
                ##  identify cap_name
                if 'extends Capability' in line:
                    cap_name = line.split('sig ')[1].split(' extends Capability')[0]
                    cap_names_to_attrs[cap_name] = []

                extract_attr_and_vals_from_line(attr_possible_values, cap_names_to_attrs, line)
    return cap_names_to_attrs, attr_possible_values




def read_files_in_directory(fs):
    cap_files = []
    app_files = []
    for f in fs:
        if 'app_' in f:
            app_files.append(f)
        elif 'cap_' in f:
            cap_files.append(f)

    return cap_files, app_files


def extract_attr_and_vals_from_line(attr_possible_values, cap_names_to_attrs, line):
    ## identify attribute
    ### typically looks like 'cap_button_attr_numberOfButtons'
    if 'cap_state_attr_' in line:
        return
    if ' extends cap_' in line and ('_attr ' in line or '_attr{}' in line):
        attr_name = line.split('one sig ')[1].split(' extends ')[0]

        # guess cap_name from the attr_name
        cap_name = guess_cap_name_from_attribute(attr_name)
        cap_names_to_attrs[cap_name].append(attr_name)
        attr_possible_values[attr_name] = []
    ## identify val for each attribute
    if 'one sig cap_' in line and '_val' in line and ' extends cap_' in line and '_val' in line.split('extends')[1]:
        ### 'one sig cap_button_attr_button_val_pushed extends cap_button_attr_button_val {}'
        value_names = line.split('one sig ')[1].split(' extends cap_')[0]

        for value_name in value_names.split(','):
            value_name = value_name.strip()

            # guess attr_name
            if '_boolval_' in value_name:  # weird corner case
                attr_name = value_name.split('_boolval_')[0]
            elif any(['val' + str(i) in value_name for i in range(0, 9)]):
                attr_name = value_name.split('val')[0]
            else:
                attr_name = value_name.split('val_')[
                    0]  # there are a bunch of weird corner cases here: val0, boolval, ...
            if attr_name.endswith('_'):
                attr_name = attr_name[:-1]
            attr_possible_values[attr_name].append(value_name)


def guess_cap_name_from_attribute(attr_name):
    cap_name = attr_name.split('_attr')[0]
    return cap_name


def read_caps_from_app_files(cap_names_to_attrs, attr_possible_values, app_files):
    # there could be new attrs introduced by the apps
    # in each cap file
    for app_file in app_files:
        with open(sys.argv[1] +'/' + app_file) as infile:
            for line in infile:
                extract_attr_and_vals_from_line(attr_possible_values, cap_names_to_attrs, line)


def interpret_value(attribute, value, attr_possible_values):
    # value can be a list
    if ',' in value:
        return [item.strip() for item in value.split(',')]
    if '-' in value: # set difference

        possibilities = get_possible_values(attr_possible_values, attribute, value)

        for attr_val in value.split('-')[1:]:
            attr_val = attr_val.strip()

            # sometimes, modes are like App1.Home, App2.AWAY...
            if 'cap_location_attr_mode' in attribute and '.' in attr_val: # some app-defined mode
                attr_val = attr_val.split('.')[1]
                attr_val = 'cap_location_attr_mode_val_' + attr_val

            # print(possibilities)
            if attr_val in possibilities:
                possibilities.remove(attr_val)
            else:
                print('missing attrval=', attr_val, 'among possible values of ', attribute)

        return list(possibilities)
    return [value]


def get_possible_values(attr_possible_values, attribute, value, create_negation_for_boolean = True):
    if attribute in attr_possible_values:
        possibilities = set(attr_possible_values[attribute])  # clone
    elif create_negation_for_boolean and 'cap_state' in attribute and value.endswith('_true'):  # if its boolean state value

        possibilities = set([value.split()[-1].replace('_true', '_false'), value.split()[-1]])
    elif create_negation_for_boolean and 'cap_state' in attribute and value.endswith('_true'):
        possibilities = set([value.split()[-1].replace('_false', '_true'), value.split()[-1]])
    else:
        print('no such attribute', attribute, 'will return empty')
        possibilities = set() # returning empty..
    return possibilities


def get_rules_from_app_files(app_files, attr_possible_values):
    rule_names = {}
    for app_file in app_files:
        ## parse each rule
        with open(sys.argv[1] + '/' + app_file) as infile:
            in_rule = False
            in_trigger = False
            in_condition = False
            in_command = False

            rule_name = None
            for line in infile:
                # strip comments
                line = line.split('//')[0]
                # print(line)

                # extensions, e.g. new Modes "Home_Day" etc...
                # TODO
                if 'one sig ' in line and ('extends r ' in line or 'extends r{}' in line):
                    # rule_name should be something like r1, r2, r3 ...
                    rule_name = app_file.split('.als')[0] + '_' + line.split('one sig ')[1].split(' extends')[0]
                    rule_names[rule_name] = {'trigger': {}, 'condition': {}, 'command': {}}
                    in_rule = True

                if 'one sig ' in line and ' extends ' in line and '_trig ' in line:
                    in_trigger = True
                    in_condition = False
                    in_command = False
                    trigger_name = line.split('one sig ')[1].split(' extends')[0]
                    rule_names[rule_name]['trigger'][trigger_name] = {}

                if in_trigger and 'capabilities' in line:
                    rule_names[rule_name]['trigger'][trigger_name]['capabilities'] = line.split('= ')[1].strip()
                if in_trigger and 'attribute' in line:
                    rule_names[rule_name]['trigger'][trigger_name]['attribute'] = line.split('= ')[1].strip()
                if in_trigger and 'value' in line:
                    if 'no value' in line:
                        rule_names[rule_name]['trigger'][trigger_name]['value'] = None
                    else:
                        attribute = rule_names[rule_name]['trigger'][trigger_name]['attribute']
                        rule_names[rule_name]['trigger'][trigger_name]['value'] = interpret_value(
                            attribute, line.split('= ')[1].strip(), attr_possible_values)

                if 'one sig ' in line and ' extends ' in line and '_cond ' in line:
                    in_condition = True
                    in_trigger = False
                    in_command = False
                    condition_name = line.split('one sig ')[1].split(' extends')[0]
                    rule_names[rule_name]['condition'][condition_name] = {}

                if in_condition and 'capability' in line:
                    rule_names[rule_name]['condition'][condition_name]['capability'] = line.split('= ')[1].strip()
                if in_condition and 'attribute' in line:
                    rule_names[rule_name]['condition'][condition_name]['attribute'] = line.split('= ')[1].strip()
                if in_condition and 'value' in line:
                    if 'no value' in line:
                        rule_names[rule_name]['condition'][condition_name]['value'] = None
                    else:
                        attribute = rule_names[rule_name]['condition'][condition_name]['attribute']
                        rule_names[rule_name]['condition'][condition_name]['value'] = interpret_value(attribute, line.split('= ')[1].strip(), attr_possible_values)

                if 'one sig ' in line and ' extends ' in line and '_comm ' in line:
                    in_command = True
                    in_trigger = False
                    in_condition = False
                    command_name = line.split('one sig ')[1].split(' extends')[0]
                    rule_names[rule_name]['command'][command_name] = {}

                if in_command and 'capability' in line:
                    rule_names[rule_name]['command'][command_name]['capability'] = line.split('= ')[1].strip()
                if in_command and 'attribute' in line:
                    rule_names[rule_name]['command'][command_name]['attribute'] = line.split('= ')[1].strip()
                if in_command and 'value' in line:
                    rule_names[rule_name]['command'][command_name]['value'] = [line.split('= ')[1].strip()]

    return rule_names




def capabilities_we_care_about(rule_names):
    result = set()
    for rule_name, rule in rule_names.items():
        for thing_type in ['trigger', 'condition', 'command']:
            for thing_name, thing in rule[thing_type].items():
                cap = guess_cap_name_from_attribute(thing['attribute'])
                result.add(cap)

    return result




def fill_state_variables_possible_values(rule_names, attr_possible_values):
    for rule_name, r in rule_names.items():

        app_name = guess_app_name_from_rule(rule_name)

        for trigger_name, trigger in r['trigger'].items():
            if 'cap_state_attr_' in trigger['attribute']:
                if append_app_name_to_state(app_name, trigger) not in attr_possible_values:
                    attr_possible_values[append_app_name_to_state(app_name, trigger)] = []

                attr_possible_values[append_app_name_to_state(app_name, trigger)].append(trigger['value'][0])

        for command_name, command in r['command'].items():
            if 'cap_state_attr_' in command['attribute']:
                if append_app_name_to_state(app_name, command) not in attr_possible_values:
                    attr_possible_values[append_app_name_to_state(app_name, command)] = []

                attr_possible_values[append_app_name_to_state(app_name, command)].append(command['value'][0])

        for condition_name, condition in r['condition'].items():
            if 'cap_state_attr_' in condition['attribute']:
                if append_app_name_to_state(app_name, condition) not in attr_possible_values:
                    attr_possible_values[append_app_name_to_state(app_name, condition)] = []

                attr_possible_values[append_app_name_to_state(app_name, condition)].append(condition['value'][0])


def guess_app_name_from_rule(rule_name):
    if 'app_r' not in rule_name:  # handle this anme differently otherwise "_r" will break the text too early
        app_name = rule_name.split('_r')[0]
    else:
        app_name = 'app_' + rule_name.split('app_')[1].split('_r')[0]
    return app_name


def append_app_name_to_state(app_name, thing_with_attribute_key):
    return app_name + thing_with_attribute_key['attribute']


def fill_missing_vals(rule_names, attr_possible_values):
    """
    For stupid things like app_ID16SleepingModeChange.Home_Day.
    HOme_Day isn't defined in the caps file
    :param rule_names:
    :param attr_possible_values:
    :return:
    """
    for rule_name, r in rule_names.items():

        if 'app_r' not in rule_name:  # handle this anme differently otherwise "_r" will break the text too early
            app_name = rule_name.split('_r')[0]
        else:
            app_name = 'app_' + rule_name.split('app_')[1].split('_r')[0]

        for trigger_name, trigger in r['trigger'].items():
            if 'cap_state_attr_' in trigger['attribute']:
                continue

            trigger_values = trigger['value']
            if trigger_values is not None:
                for trigger_value in trigger_values:
                    if trigger_value is not None and 'cap_location_attr_mode' in trigger_value and '.' in trigger_value: # deal with new app-defined modes (e.g. appX_blahblah_Night_Away
                        trigger_value = trigger_value.split('.')[1]

                    if trigger_value not in attr_possible_values[trigger['attribute']] and trigger_value is not None:
                        print('adding missing val for attr', 'attribute=', trigger['attribute'], 'value=', trigger_value)
                        attr_possible_values[trigger['attribute']].append(trigger_value)


        for command_name, command in r['command'].items():
            if 'cap_state_attr_' in command['attribute']:
                continue

            command_value = command['value'][0]
            if 'cap_location_attr_mode' in command_value:
                if '.' in command_value:
                    print('what runs this??')
                    command_value = command_value.split('.')[1]
                elif 'cap_location_attr_mode_val_' in command_value:
                    command_value = command_value.split('cap_location_attr_mode_val_')[1]

            if command_value not in attr_possible_values[command['attribute']]:
                print('adding missing val for attr', 'attribute=', command['attribute'], 'value=', command_value)
                attr_possible_values[command['attribute']].append(command_value)

        for condition_name, condition in r['condition'].items():
            if 'cap_state_attr_' in condition['attribute']:
                continue

            if len(condition['value']) > 0:
                condition_value = condition['value'][0]

                if 'cap_location_attr_mode' in condition_value:
                    condition_value = condition_value.split('.')[1] if '.' in condition_value else condition_value
                if condition_value not in attr_possible_values[condition['attribute']]:
                    print('missing val for attr', 'attribute=', condition['attribute'], 'value=', condition_value)

                    attr_possible_values[condition['attribute']].append(condition['value'][0])


def derive_interesting_events(rule_names, attr_possible_values, additional_filter=None):
    """

    :param rule_names:
    :param attr_possible_values:
    :param additional_filter:  currentonly None or ["commands_only", "permit_all"]
    :return:
    """

    # config for filtering stuff
    permit_all = additional_filter is not None and 'permit_all' in additional_filter

    #

    interesting_events = []
    for rule_name, rule in rule_names.items():
        if 'app_r' not in rule_name:  # handle this anme differently otherwise "_r" will break the text too early
            app_name = rule_name.split('_r')[0]
        else:
            app_name = 'app_' + rule_name.split('app_')[1].split('_r')[0]

        if additional_filter is None or "commands_only" not in additional_filter:
            for trigger_name, trigger in rule['trigger'].items():
                if 'cap_state_attr_' in trigger['attribute'] and not permit_all:  # state variable
                    continue  # state variables are not 'events' for us to create

                if 'cap_location_attr_mode' in trigger['attribute'] and not permit_all:
                    continue  # the mode can't randomly change

                if trigger['value'] is not None:
                    event = {'attribute': trigger['attribute'], 'value': trigger['value'][0]}
                    interesting_events.append(event)
                elif trigger['value'] is None:
                    # pick a random value
                    # the trigger can be triggered by any change in this attribute
                    trigger_attribute = trigger['attribute']
                    other_values = sorted(list(attr_possible_values[trigger_attribute]))
                    if len(other_values) > 0:
                        another_value = other_values[0] # random.choice(other_values)
                        event = {'attribute': trigger_attribute, 'value': another_value}
                        interesting_events.append(event)


                if trigger['value'] is not None:
                    # create second event, which has different value from the first
                    trigger_attribute = trigger['attribute']

                    other_values = sorted(list(attr_possible_values[trigger_attribute]))

                    if trigger['value'][0] in other_values:
                        other_values.remove(trigger['value'][0])
                 
                    else:
                        print('odd:', 'missing value', trigger['value'][0] )

                    if len(other_values) > 0:
                        another_value = other_values[0] # random.choice(other_values)
                        event2 = {'attribute': trigger_attribute, 'value': another_value}
                        interesting_events.append(event2)


        for command_name, command in rule['command'].items():
            if 'cap_state_attr_' in command['attribute'] and not permit_all:  # state variable
                continue # state variables are not 'events' for us to create
            if 'cap_location_attr_mode' in command['attribute'] and not permit_all:  # state variable
                continue  # the mode can't randomly change

            event = {'attribute': command['attribute'], 'value': command['value'][0]}
            interesting_events.append(event)

            command_attribute = command['attribute']

            other_values = sorted(list(get_possible_values(attr_possible_values, command_attribute, command['value'][0], False)))

            if command['value'][0] in other_values:
                other_values.remove(command['value'][0])

            if len(other_values) > 0:
                another_value = other_values[0] # random.choice(other_values)
                event2 = {'attribute': command_attribute, 'value': another_value}
                interesting_events.append(event2)

        if additional_filter is None or "commands_only" not in additional_filter:
            for condition_name, condition in rule['condition'].items():
                if 'cap_state_attr_' in condition['attribute']:  # state variable
                    continue  # state variables are not 'events' for us to create
                if 'cap_location_attr_mode' in condition['attribute']:  # state variable
                    continue  # the mode can't randomly change

                condition_attribute = condition['attribute']
                try:
                    other_values = sorted(list(attr_possible_values[condition_attribute]))
                except KeyError:
                    other_values = []
                if len(condition['value']) > 0:

                    event = {'attribute': condition['attribute'], 'value': condition['value'][0]}
                    interesting_events.append(event)

                    if condition['value'][0] in other_values:
                        other_values.remove(condition['value'][0])

                if len(other_values) > 0:
                    another_value = other_values[0] # random.choice(other_values)
                    event2 = {'attribute': condition_attribute, 'value': another_value}
                    interesting_events.append(event2)
    return interesting_events

