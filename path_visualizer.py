
import sys

new_hold_pairs_file = sys.argv[1]

desired_command_attributes = sys.argv[2].split(',')

desired_event_attributes = sys.argv[3].split(',')

template = """
digraph Automata {{
rankdir=LR
size="8,5"
node [shape=doublecircle]
CC{endnode}
node [shape=circle]
{lines}
}}
"""

line_template = """
CC{i} -> CC{j} [label={label}]
"""


with open(new_hold_pairs_file) as infile:
    for line_no, line in enumerate(infile):
        line = line.strip()

        line_components = line.split(',')
        command_attr, command_val = line_components[:2]

        has_desired_command_attribute = False
        for desired_command_attribute in desired_command_attributes:
            if desired_command_attribute.lower() in command_attr.lower() :
                has_desired_command_attribute = True
        if not has_desired_command_attribute:
            continue

        has_desired_event_attribute = False
        for desired_event_attribute in desired_event_attributes:
            if len(line_components) < 4 or len(line_components) >= 4 and desired_event_attribute.lower() in line_components[2].lower():
                has_desired_event_attribute = True
        if not has_desired_event_attribute:
            continue

        print('ok', line_no)
        context = []
        for i in range(2, len(line_components) - 1, 2):
            event_attr = line_components[i]
            event_value = line_components[i + 1]

            # if similar to previous one and is less specific, no need for it.
            # if event_value.endswith('_null') and event_attr == context[-1][0]:
            #     continue

            context.append((event_attr, event_value))

        lines = ""
        for i, (event_attr, event_val) in enumerate(context):
            drop_cond = event_attr.split('cond:')[1] if 'cond:' in event_attr else event_attr
            line = line_template.format(**{
                'i': i,
                'j': i + 1,
                'label': drop_cond + '_' + event_val.split('_')[-1]
            })
            lines += line

        line = line_template.format(**{
                'i': i + 1,
                'j': i + 2,
                'label': command_attr + '_' + command_val.split('_')[-1]
            })
        lines += line

        dot_file_content = template.format(**{
                'endnode': i + 2,
                'lines': lines
            })

        with open('inspect_path_' + str(line_no) + '.dot', 'w+') as outfile:
            outfile.write(dot_file_content)

        print('write to ', 'inspect_path_' + str(line_no) + '.dot')