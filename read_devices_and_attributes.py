import yaml
from collections import defaultdict


# this script gives us the commands for each device.
# i want to use this to instrument the code. i.e find calls to these sensitive APIs


devices = []
with open('devices_and_their_attributes.txt') as infile:
    s = ""
    for line in infile:
        # print(line)
        if ';;' in line:
            device = yaml.safe_load(s)
            if device is not None:
                devices.append(device)
            s = ""
            continue
        s += line



commands = defaultdict(set)
attributes = defaultdict(set)

for device in devices:
    # device['attributes']['command']
    print(device)
    for attribute in device['attributes'].keys():
        if attribute in ['schema', 'type', 'values']:
            continue
        attributes[device['id']].add(attribute)

        # if 'enumCommand' in device['attributes'][attribute]:
        #     for device_function in device['attributes'][attribute]['enumCommand']:
        #         commands[device['id']].add(device_function['command'])

    for command in device['commands'].keys():
        commands[device['id']].add(command)   


    # device['attributes']['value']

with open('device_attributes.txt', 'w+') as outfile:
    for device, attributes in attributes.items():
        for a in attributes:
            outfile.write(device + ',' + a)
            outfile.write('\n')

with open('device_commands.txt', 'w+') as outfile:
    for device, commands in commands.items():
        for a in commands:
            outfile.write(device + ',' + a)
            outfile.write('\n')


capability_attributes = {}
with open('capabilities_attributes_commands.txt') as infile:
    for line in infile:
        splitted = line.split("\t")
        capability = splitted[1]

        capability_attributes[capability] = []

        if len(splitted[2].strip()) == 0:
            continue


        if '[' not in splitted[2]:
            capability_attributes[capability].append(splitted[2].strip(' "'))

        # else:
        #     attributes = splitted[2].split("[")[1].rstrip('"]')
        #     for attribute in attributes.split(","):
        #         capability_attributes[capability].append(attribute.strip(' "'))

        else:
            capability_attributes[capability].append(splitted[2].split(' ')[0].strip('" '))

with open('capability_attributes.txt', 'w+') as outfile:
    for device, attributes in capability_attributes.items():
        for a in attributes:
            outfile.write(device + ',' + a)
            outfile.write('\n')


