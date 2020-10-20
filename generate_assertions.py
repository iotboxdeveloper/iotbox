import os

import random

import sys, ipdb, traceback
from IPython import embed



from utils import world_utils


# from utils.world_utils import read_caps, read_files_in_directory, guess_cap_name_from_attribute, \
#     read_caps_from_app_files, get_rules_from_app_files, capabilities_we_care_about, fill_state_variables_possible_values, \
#     guess_app_name_from_rule, append_app_name_to_state, fill_missing_vals, derive_interesting_events, read_channel_connection


# python3 generate_assertions.py ~/eclipse-workspace/IOTCOM-github/FormalAnalyzer/out/run_20200921_Bundle1_Safe/stage/
# REMEMBER: then mv the assertions_* file into the stage directory

def info(type, value, tb):
    traceback.print_exception(type, value, tb)
    ipdb.pm()


sys.excepthook = info

# parse apps
fs = os.listdir(sys.argv[1])

cap_files, app_files = world_utils.read_files_in_directory(fs)

# number_of_traces_to_have = int(sys.argv[2])

cap_names_to_attrs, attr_possible_values = world_utils.read_caps(cap_files)

world_utils.read_caps_from_app_files(cap_names_to_attrs, attr_possible_values, app_files)

channels = world_utils.read_channel_connection()
rule_names = world_utils.get_rules_from_app_files(app_files, attr_possible_values)

capabilities_in_home = world_utils.capabilities_we_care_about(rule_names)

interesting_events = world_utils.derive_interesting_events(rule_names, attr_possible_values)

# state attrs
# state stuff do not appear in the caps file
# but need to figure out their names and possible values
# rmb to prefix the app name to the name of the state
world_utils.fill_state_variables_possible_values(rule_names, attr_possible_values)

world_utils.fill_missing_vals(rule_names, attr_possible_values)

interesting_events = world_utils.derive_interesting_events(rule_names, attr_possible_values, ['permit_all'])

command_events = world_utils.derive_interesting_events(rule_names, attr_possible_values, ["commands_only", 'permit_all'])



# find all commands
# the idea is to find all the triggers leading to these commands.



# pairs of (event, command) for all interesting events and commands. (Note that "interesting" is different from world.py's definition of interesting)

# create assertions for all of them.
# if (X1, command) is model-checked and the assertion holds (i.e no counterexamples),
# that's a rule X1 -> command.
# we find all of these Xses, such that we can say:
#  (X1 v X2 v X3 v ... v Xn) -> command

### hmmmm, I think the template is wrong. We want to check a different property.
### if we want to find x -> c (c always preceded by x). find cases when c ^ ~x.
### in other words, a counterexample shows c ^ !x.
### such a property to produce this counterexample is (!c and x)
### we are satisfied only after expanding (X1 v X2 V... ) that the command is always explained.
### need to express in terms of "no X". e.g "no (rule such that (c and not x ))"

pairs = []
pairs_already_stored = set()
first_interesting_event_for_command = {}

for command_event in command_events:
    if command_event['value'] in first_interesting_event_for_command :
        continue
    for rule in rule_names.values():
        for command in rule['command'].values():
            if command['value'][0] == command_event['value']:
                # take the first trigger if there is
                if len(rule['trigger']) > 0:
                    trigg = list(rule['trigger'].values())[0]
                   
                    interesting_event = {'attribute': trigg['attribute'], 'value': trigg['value'][0] if trigg['value'] is not None else None}

                elif len(rule['condition']) > 0 :
                    cond = list(rule['condition'].values())[0]
                   
                    interesting_event = {'attribute': cond['attribute'], 'value': cond['value'][0] if cond['value'] is not None else None}
                else:
                    print('nothing to go with...')
                    break

                first_interesting_event_for_command[command['value'][0]] = (interesting_event, command_event)
                pairs.append((interesting_event, command_event))
                break
        if command_event['value'] in first_interesting_event_for_command :
            break

# embed()

#### remember to sync with update_assertions
template = """
assert P__{i} {{
  // if {comm_value} occurs 
  no r : IoTApp.rules, action : r.commands {{
    action.attribute = {comm_attr}
    action.value     = {comm_value}
    (some predecessor : r.*(~connected), action' : predecessor.triggers, cond: predecessor.conditions {{
    // it is caused by {interesting_attr}
    // 
    // e.g. check that all events on the paths e.g. is an event that is not NIGHT mode, and is not preceded by NIGHT mode
        not {{
        (
        {{
            action'.attribute = {interesting_attr}
            {value_match}
            
        }}
        ) 
        or
        (
            some predecessor' : predecessor.*(~connected), action'' : predecessor'.triggers, cond'' : predecessor'.conditions {{
                predecessor != r
                action''.attribute = {interesting_attr}
                {value_match2}
                
            }}
        )
        // P__{i}_insert_more_here
        }}
    }}) 
  }}
}}
"""

assertions = []
for i, pair in enumerate(pairs):
    if pair[0]['value'] is not None:
        value_match = "(no action'.value and cond.attribute = action'.attribute and cond.value = " + \
                      pair[0]['value'] + ") or action'.value     = " + pair[0]['value']
        value_match2 = "(no action''.value and cond''.attribute = action''.attribute and cond''.value = " + \
                       pair[0]['value'] + ") or action''.value     = " + pair[0]['value']
    else:
        value_match = "(no action'.value)"
        value_match2 = "(no action''.value) "

    assertion = template.format(**{
        'i': i,
        'comm_attr': pair[1]['attribute'],
        'comm_value': pair[1]['value'],
        'interesting_attr': pair[0]['attribute'],
        'interesting_value': pair[0]['value'],

        'value_match': value_match,
        'value_match2': value_match2
    })

    assertions.append(assertion)

fname = [fpath_part for fpath_part in sys.argv[1].split('/') if 'Bundle' in fpath_part][0]

with open('assertions_' + fname + '.als', 'w+') as outfile:
    outfile.write("module assertions\n")
    outfile.write("open IoTBottomUp as base\n")
    outfile.write("open IoTChannel as chan\n")
    for cap_file in cap_files:
        outfile.write("open " + cap_file.split('.')[0] + "\n")
    for app_file in app_files:
        outfile.write("open " + app_file.split('.')[0] + "\n")

    outfile.write("""
    pred connected_runIn[r,r' : Rule] {
      no r'.triggers
      some comm : r.commands, cond : r'.conditions {
        (cond.attribute  = cap_runIn_attr_runIn)
        (cond.value      = cap_runIn_attr_runIn_val_on)
        (comm.capability = cond.capabilities)
        (comm.attribute  = cond.attribute)
        (comm.value      = cond.value)
      }
    }
    
    pred connected_caps[comm : Command, trig : Trigger] {
      (some comm.capability & trig.capabilities)
      (comm.attribute = trig.attribute)
      (comm.value in trig.value) or (no trig.value)
    }
    
    pred connected_chan[comm : Command, trig : Trigger] {
      some c : Channel {
        some (comm.capability   & c.actuators)
        some (trig.capabilities & c.sensors)
      }
    }
    
    pred are_indirect[r,r' : Rule] {
      are_connected[r,r']
      no comm : r.commands, trig : r'.triggers {
        connected_caps[comm, trig]
      }
    }
    
    pred are_connected[r,r' : Rule] {
      (some comm : r.commands, trig : r'.triggers {
        connected_caps[comm, trig] or connected_chan[comm, trig]
      }) or (connected_runIn[r,r'])
      all comm : r.commands, cond : r'.conditions {
        ((some comm.capability & cond.capabilities) and (comm.attribute = cond.attribute)) => {
          (comm.value in cond.value)
        }
      }
    }
    
    pred are_siblings[r,r' : Rule] {
      (no r.triggers) or (no r'.triggers) or (some t : r.triggers, t' : r'.triggers {
        (t.attribute = t'.attribute)
        (some t.value & t'.value) or (no t.value) or (no t'.value)
      })
      all c : r.conditions, c' : r'.conditions {
        ((some c.capabilities & c'.capabilities) and (c.attribute = c'.attribute))
          => (some c.value & c'.value)
      }
    }
    
    fact {
      all r,r' : Rule {
        (r' in r.connected) <=> are_connected[r,r']
        (r' in r.siblings)  <=> are_siblings[r,r']
        (r' in r.indirect)  <=> are_indirect[r,r']
        (r' in r.scheduled) <=> connected_runIn[r,r']
      }
    }
    
    """)

    for i, assertion in enumerate(assertions):
        outfile.write(assertion)
        outfile.write("check P__" + str(i) + "\n")
        
        command = pairs[i][1]
        interesting_event = pairs[i][0]

        command_attr = command['attribute']
        command_value = command['value']

        event_attr = interesting_event['attribute']
        event_value = interesting_event['value']

        outfile.write('// P__'+ str(i)  + ':' + command_attr+ "," + command_value
                      + ',' + event_attr + ',' + (event_value if event_value is not None else 'null') + '\n')
        outfile.write('// P__'+ str(i) + '_insert_metadata_here')
        outfile.write('\n')

print()
print('write to ', 'assertions_' + fname + '.als')
print()
print('probably you want to run: ')
print('cp', 'assertions_' + fname + '.als', sys.argv[1])
# while we are at it, generate the names of rules, triggers, conditions, commands used by the Alloy analyder
# need to link from the skolem bindings to the attribute names, value names

with open('link_from_alloy_skolem_to_attr_val_' + fname + '.txt', 'w+') as outfile:
    for rule_name, rule in rule_names.items():
        alloy_rule_name = rule_name.split('_r')[0] + '/r' + rule_name.split('_r')[1] + '$0'

        for trigger_name, trigger in rule['trigger'].items():
            # app_ID15CreateGeneralPropertyViolations/r0_trig0
            trigger_name = rule_name.split('_r')[0] + '/' + trigger_name + '$0'
            trigger_attribute = trigger['attribute']
            trigger_value = ','.join(trigger['value']) if trigger['value'] is not None else 'null'

            outfile.write(trigger_name + ',' +  trigger_attribute + ',' + trigger_value + '\n')

        for condition_name, condition in rule['condition'].items():
            # app_ID15CreateGeneralPropertyViolations/r0_trig0
            condition_name = rule_name.split('_r')[0] + '/' + condition_name + '$0'
            condition_attribute = condition['attribute']
            condition_value = ','.join(condition['value'])

            outfile.write(condition_name + ',' + condition_attribute + ',' + condition_value + '\n')

        for command_name, command in rule['command'].items():
            # app_ID15CreateGeneralPropertyViolations/r0_trig0
            command_name = rule_name.split('_r')[0] + '/' + command_name + '$0'
            command_attribute = command['attribute']
            command_value = ','.join(command['value'])

            outfile.write(command_name + ',' + command_attribute + ',' + command_value + '\n')



embed()


# property_to_check = ('cap_momentary_attr_momentary', 'cap_momentary_attr_momentary_val_push', 'cap_presenceSensor_attr_presence', 'cap_presenceSensor_attr_presence_val_not_present')

# # create trace of num_events events
# num_events = 300
# fname = [fpath_part for fpath_part in sys.argv[1].split('/') if 'Bundle' in fpath_part][0]
#
# if len(sys.argv) >= 4:
#     fname += sys.argv[3]

