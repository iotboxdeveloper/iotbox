import sys


# Run this after running the Java alloy stuff
# e.g. time java -jar build/libs/iotcom-sandbox-refine-1.0.0.jar ~/eclipse-workspace/IOTCOM-github/FormalAnalyzer/out/run_20200921_Bundle8_Safe/stage/ ~/repos/smartthings_control/link_from_alloy_skolem_to_attr_val_run_20200921_Bundle8_Safe.txt
# That gives us newAssertions.txt file
# Then run this like:
# python3 update_assertions.py ~/eclipse-workspace/IOTCOM-github/FormalAnalyzer/out/run_20200921_Bundle1_Safe/stage/assertions_run_20200921_Bundle1_Safe.als ~/eclipse-workspace/IOTCOM-github/FormalAnalyzer/out/run_20200921_Bundle1_Safe/stage/newAssertions.txt


original_assertions = sys.argv[1]
file_content = ""
with open(original_assertions) as infile:
    file_content = infile.read()

#####
# stuff for updating assertions. Assuming that the java file (SandBoxSolver) in iotcom for sandboxing stuff is already run. (built with /gradlew sandboxFatJar)
new_pairs_file = sys.argv[2]

new_things_to_add_for_command = {}
with open(new_pairs_file) as infile:
    lines = []
    for line in infile:
        if line not in lines:
            lines.append(line.strip())

    for line in lines:
        command, attr, val = line.split(',')
        if command not in new_things_to_add_for_command:
            new_things_to_add_for_command[command] = []
        new_things_to_add_for_command[command].append((attr, val))


#### remember to sync with generate_assertions
item_tempalte = """
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
        """
for command, tthings_to_add in new_things_to_add_for_command.items():
    for thing_to_add in tthings_to_add:
        attr, value = thing_to_add
        if value is not None and value.strip() != 'null':  # argh, stupid 'null' strings showed up somehow
            value_match = "(no action'.value and cond.attribute = action'.attribute and cond.value = " + value + \
                          ") or action'.value     = " + value
            value_match2 = "(no action''.value and cond''.attribute = action''.attribute and cond''.value = " + \
                           value + ") or action''.value     = " + value
        else:
            print('found null/None')
            value_match = "(no action'.value)"
            value_match2 = "(no action''.value) "

        alloy_assertion_part = item_tempalte.format(**{
            'interesting_attr': attr,
            'interesting_value': value,

            'value_match': value_match,
            'value_match2': value_match2
        })

        location_text_to_update = "// " + command + "_insert_more_here"

        location_metadata_to_update = '// ' + command + '_insert_metadata_here'

        alloy_assertion_part = 'or\n' + alloy_assertion_part + '\n        ' + location_text_to_update

        # '// P__' + str(i) + ':' + command_attr + "," + command_value
        # + ',' + event_attr + ',' + (event_value if event_value is not None else 'null') + '\n'
        metadata_update_part = '// ' + command + ':^,' + attr + ',' + value  \
                               + '\n' + location_metadata_to_update

        file_content = file_content.replace(location_text_to_update, alloy_assertion_part)
        file_content = file_content.replace(location_metadata_to_update, metadata_update_part)

# print(file_content)

import os
os.rename(original_assertions, original_assertions +'.bak')

with open(original_assertions, 'w') as outfile:
    outfile.write(file_content)

#####
