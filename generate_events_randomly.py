# Requirements:
"pip3 install requests-html"
"pip3 install ipdb"
"pip3 install IPython"

# a "zzz" app is assumed to exist on smartthings. This app (assumed to be appear last in the list sorted alphabetically) is used to query for the simulation details.

# this script generates events

# config


from requests_html import HTMLSession
import requests 

from http.cookies import SimpleCookie

from IPython import embed
import sys, ipdb, traceback

def info(type, value, tb):
    traceback.print_exception(type, value, tb)
    ipdb.pm()

sys.excepthook = info

import sys


from github3 import login


cookie_str = sys.argv[1]
location = sys.argv[2]

# def init():
cookie = SimpleCookie()


cookie_str = sys.argv[1]

cookie.load(cookie_str)

time_matters = sys.argv[3].startswith('t') or sys.argv[3].startswith('T') 

current_time = None
if time_matters:

    def update_time(new_time_in_seconds_since_epoch):

        if not time_matters:
            return

        # gh token goes here
        token = '-----------------'
        gh = login(token = token)
        # gist id goes here
        gist = [g for g in gh.gists() if '<gist id>' in g.html_url ][0]

        files = {
            'time': { 
                'content': new_time_in_seconds_since_epoch if type(new_time_in_seconds_since_epoch) == str else str(new_time_in_seconds_since_epoch)
            }
        }

        gist.edit('', files)

        current_time = new_time_in_seconds_since_epoch
        return current_time


    from datetime import datetime, time, timezone, timedelta
    import pytz

    tz = pytz.timezone('US/Alaska')

    start = datetime.combine(datetime.now(), time.min)
    # minus an offset. The experiments are run in a different timezone from Alaska, where sometimes now < start, so we avoid this by making start even earlier. 
    start = start - timedelta(hours=8) 

    end = datetime.combine(datetime.now(), time.max)
    end = end + timedelta(hours=8)


    start_time = int(datetime.timestamp(tz.localize(start)))
    end_time = int(datetime.timestamp(tz.localize(end)))

    current_time = update_time(start_time)
    #current_time = get_current_time()



session = HTMLSession()
for item in cookie.items():
    session.cookies.set(*item)
a = session.get('https://graph.api.smartthings.com/ide/apps')

rows = a.html.find('#smartapp-table tr')
smartapps = []
for row in rows:
    for link in row.find('a'):
        if link.attrs['href'].startswith('/ide/app/editor/'):
            smartapps.append('https://graph.api.smartthings.com/' + link.attrs['href'])

            tmp_smartapp_id = link.attrs['href'].split('editor/')[1] # '12c162b8-997d-41ea-aefd-deff013bf9a8'
    for button in row.find('span'):
        if 'data-app' in button.attrs and button.attrs['data-location'] == location:
            smartapp_id = tmp_smartapp_id

# the last smartapp's id is used in this script. But, really, any smartapp can be used.
smartapp_page = session.get('https://graph.api.smartthings.com/ide/app/editor/' + smartapp_id)

print('obtaining csrf token next')
csrf = smartapp_page.html.find('meta[name="_csrf"]')[0].attrs['content']

locations = [option.attrs['value'] for option in smartapp_page.html.find('#location option')]

# pick last, but probably should depend on the user specifying something in the sys.argv


# location = locations[-1]
print('setting location')

data = {'id': smartapp_id, 'location': location, '_csrf': csrf}
print(data)
l = session.post('https://graph.api.smartthings.com/ide/app/setLocation', data = {'id': smartapp_id, 'location': location, '_csrf': csrf})

print('getting simulation settings')

l_json = l.json()
l_json['simulation']['settings']

settings = []

for section in l_json['simulation']['smartAppVersion']['preferences']['sections']:
    for body in section['body']:
        if 'type' not in body or not body['type'].startswith('capability.'):
            continue
        name = body['name']
        capability = body['type']
        is_multiple = body['multiple']
        settings.append({'name' : name, 'type' : capability, 'is_multiple': is_multiple})

# embed()

configuration_data = {
'id': smartapp_id, 'location': location, '_csrf': csrf
}

# sends the config of a virtual device. we just want the response of startSimulation
# this need to the match the smartapp's capabilities
# settings = [
#     {'name': 'presence', 'type': 'capability.presenceSensor'},  
#     # {'name': 'phone1', 'type': 'phone'}
# ]

for device in settings:

    configuration_data['settings.' + device['name'] + '.value'] = '_new0' if device['is_multiple'] else '_new'
    configuration_data['settings.' + device['name'] + '.type'] =  device['type']
    configuration_data['settings.' + device['name'] + '.readOnly'] = False
    configuration_data['settings.' + device['name'] + '.capabilities'] = ''

print('starting the simulation')

simulation_response = session.post('https://graph.api.smartthings.com/ide/app/startSimulation', data=configuration_data)

simulation_response_json = simulation_response.json()
if 'hub' not in simulation_response_json:
    print('failed!!')
    print(simulation_response.text)


hub = simulation_response_json['hub']

virtual_devices = {}

# HJ: using 'virtualDevices' gives us only the devices for the chosen smartapp
# for simulation_device in simulation_response_json['virtualDevices']:
#     device_network_id = simulation_device['deviceNetworkId'] 
#     label = simulation_device['label']
#     virtual_devices[label] = device_network_id

# but if we use 'devices', we can get all the devices.
virtual_devices = {device['id'] : device['deviceNetworkId'] for device in simulation_response_json['devices'] if device['virtual']}
virtual_devices_dni = set([device['deviceNetworkId'] for device in simulation_response_json['devices'] if device['virtual']])

# for key, value in simulation_response_json['simulation']['settings'].items():
#     virtual_devices[key] = value

simulation_devices = {} 
simulation_devices_id_to_dni = {} 
for device in simulation_response_json['devices']:
    device_network_id = device['deviceNetworkId']
    device_id = device['id']

    simulation_devices[device_network_id.lower()] = device_id
    simulation_devices_id_to_dni[device_id] = device_network_id.lower()


capability_to_virtual_device_dni = {}

capability_to_device_dni = {}
typeMap = simulation_response_json['typeMap']
for capability, device_ids in typeMap.items():
    for device_id in device_ids:

        if device_id not in virtual_devices:
        
            if capability not in capability_to_device_dni:
                capability_to_device_dni[capability] = []
            capability_to_device_dni[capability].append(simulation_devices_id_to_dni[device_id])

        else:        
            if capability not in capability_to_virtual_device_dni:
                capability_to_virtual_device_dni[capability] = []
            capability_to_virtual_device_dni[capability].append(virtual_devices[device_id])


# actions_of_device = {}
# for device, device_id in simulation_devices.items():
#   for tileMap in tilesMap[device_id]:
#       for state in tileMap['states']:
#           if state['action'] is None:
#               continue
#           if device_id not in actions_of_device:
#               actions_of_device[device_id] = set()
#           actions_of_device[device_id].add(state['action'])

actions_of_device = {}
for device_id, tileMaps in simulation_response_json['tilesMap'].items():
    for tileMap in tileMaps:
        for state in tileMap['states']:
            if state['action'] is None:
                continue
            if device_id not in actions_of_device:
                actions_of_device[device_id] = set()
            if any([c.isupper() for c in state['action']]):
                continue
            actions_of_device[device_id].add(state['action'])



measurements_of_virtual_devices = {}
for virtual_device in [ device for device in simulation_response_json['devices'] if device['virtual']]:
    dni = virtual_device['deviceNetworkId']
    measurements_of_virtual_devices[dni] = []
    for status in virtual_device['currentStates']:
        if status['rawDescription'] is not None:
            measurements_of_virtual_devices[dni].append(status['rawDescription'])
        elif status['name'] is not None and status['value'] is not None:
            measurements_of_virtual_devices[dni].append(status['name'] + ':' + status['value'])

    if len(measurements_of_virtual_devices[dni]) == 0:
        del measurements_of_virtual_devices[dni]
        for cap, v_devices in capability_to_virtual_device_dni.items():
            if dni in v_devices:
                v_devices.remove(dni)


# session, actions_of_device, simulation_devices, hub, csrf = init()
def generate_events(event_stream):
    global current_time
    execute_command_url = 'https://graph.api.smartthings.com/ide/app/executeCommand'

   

    for device, action in event_stream:

        if time_matters and random.randint(0, 100) > 92: 
            print('updating time')
            if end_time - current_time < 1800: # less than 1 hour
                current_time = start_time

            new_time = random.randint(current_time, current_time + 1800) # any time in the next 30 minutes 
            current_time = update_time(new_time)

        if device not in simulation_devices.keys():
            print("error: device not found:", device, 'skipping event')
            continue

        if device in virtual_devices_dni:
            print('goign to run ws', 'with action', action,' is it a str?', isinstance(action[0], str))

            if isinstance(action[0], str):
                if ':' in action[0]:
                    action = (action[0].split(":")[0], action[0].split(":")[1])             
                
                    asyncio.get_event_loop().run_until_complete(send_virtual_sensor_reading(action[0], action[1], device, hub))
                else:
                    asyncio.get_event_loop().run_until_complete(send_virtual_sensor_reading(action[0], None, device, hub))
                 
        else:
            print('running POST', device, action)
            l = session.post(execute_command_url, data={
                'id': simulation_devices[device],
                'command': action,
                '_csrf': csrf
            })
            print('recv', l.text)
        

def remove_smartapp(smartapp_id):
    remove_url = 'https://graph.api.smartthings.com/ide/app/stopSimulation'
    session.post(remove_url, data={
        'id': smartapp_id,  
        'location': location,
        '_csrf': csrf
    })


def get_current_time():
    # gist url and gist id goes here
    gist_url = 'https://gist.githubusercontent.com/<githubuser>/<gist id>/raw/<gist>/time'
    gist = [g for g in gh.gists() if '<gist id>' in g.html_url ][0]
    f = gist.files['time']

    page = requests.get(f.raw_url)
    return int(page.text)

    


import asyncio
import websockets

async def send_virtual_sensor_reading(message_type, message_value, device_network_id, hub):
    uri = "wss://ic-na01-useast1.connect.smartthings.com/device/" + hub
    async with websockets.connect(uri, ping_interval=20, ping_timeout=None) as websocket:
        # init
        q = await websocket.recv()
        print('first', q)
        if 'NULL' not in q:
            q= await websocket.recv()
            print('second', q)
        if '20000' not in q:
            q=await websocket.recv()
            print('third', q)

        print("done websocket init")

        if message_value is not None:
            print('> ', '{data: "' + message_type + ': ' + message_value + '", dni: "' + device_network_id + '", h: "' + hub + '"}')
            await websocket.send('{data: "' + message_type + ': ' + message_value + '", dni: "' + device_network_id + '", h: "' + hub + '"}')
        else:
            print('> ', '{data: "' + message_type  + '", dni: "' + device_network_id + '", h: "' + hub + '"}')
            await websocket.send('{data: "' + message_type + '", dni: "' + device_network_id + '", h: "' + hub + '"}')
            
        print('sent')
        # resp = await websocket.recv()
        # print(f"< {resp}")

        return True


def get_devices_for_capability(capability, capability_to_virtual_device_dni, capability_to_device_dni):
    devices = []

    if capability in capability_to_device_dni:
        for device_dni in capability_to_device_dni[capability]:
            devices.append(device_dni)

    if len(devices) > 0:

        # print('get_devices (only non-virtual): ', devices)
        return devices # favour non-virtual devices

    if capability in capability_to_virtual_device_dni:
        for virtual_device_dni in capability_to_virtual_device_dni[capability]:
            if virtual_device_dni in measurements_of_virtual_devices:
                devices.append(virtual_device_dni)

    # print('get_devices: ', devices)
    return devices


import random

def get_random_capability(capabilities):
    def is_acceptable_cap(cap):
        acceptables = ['capability.smokeDetector', 'capability.switch', 'capability.sensor', 'capability.lock', 'capability.illuminanceMeasurement', 'capability.accelerationSensor']
        return cap in acceptables
    return random.choice([cap for cap in capabilities if cap.startswith('cap') and is_acceptable_cap(cap)])

def get_random_value_of_measurement(measurement_type, capability):
    if 'capability.illuminanceMeasurementCapability' in capability or 'capability.illuminanceMeasurement' in capability or 'capability.accelerationSensor' in capability:
        return random.randint(0, 200)
    else:
        raise Exception("unsupported. args=" + measurement_type + " : " + capability)

print('constructing')


# construct
capabilities = [cap for cap in capability_to_device_dni.keys() if len(capability_to_device_dni[cap]) > 0]
capabilities.extend([cap for cap in  capability_to_virtual_device_dni.keys() if len(capability_to_virtual_device_dni[cap]) > 0])


def create_event_stream():
    num_events = random.randint(20, 40)
    event_stream = []
    for i in range(num_events):
        capability = get_random_capability(capabilities)
        
        print('capability ', capability)
        devices = get_devices_for_capability(capability, capability_to_virtual_device_dni, capability_to_device_dni)
        device = random.choice(devices)

        # pick action for device
        if simulation_devices[device] in actions_of_device:
            action = random.sample(actions_of_device[simulation_devices[device]], 1)

        elif device not in actions_of_device and device in measurements_of_virtual_devices:
            
            action_type = measurements_of_virtual_devices[device][0].split(':')[0]
            action_value = get_random_value_of_measurement(action_type, capability)
            action = (action_type, action_value)

     # event_stream = [('presence_sensor_a', 'arrived'), ('1adf', ('illuminance', '100'))]
        else:
            print('missing' , device)

        # map from 
        event_stream.append((device, action))
    return event_stream

event_stream = create_event_stream()

print("printing event_stream")    
print(event_stream)
# generate_events(event_stream)


def create_device(device_type, location_name):
    device_type_ids = {
        "Simulated Alarm" : "7cb4aa6c-7d54-4969-b08a-bb3d22e8122d",
        "Simulated Button" : "7085326a-05d3-4175-9c05-93c6904b5fef",
        "Simulated Color Control" : "9c78f10f-d71c-4bbd-a164-cfc6fc3729dc",
        "Simulated Contact Sensor" : "3237c3c4-7f74-4fd0-89db-9bbcf945feaa",
        "Simulated Device Preferences" : "3aeac427-f5c9-47b6-b9df-bca69b71f0d8",
        "Simulated Dimmable Bulb" : "b5f4bbe9-8282-4132-9799-2bbe99354366",
        "Simulated Dimmer Switch" : "504755f1-c94d-49f2-ace9-46d63284c719",
        "Simulated Garage Door Opener" : "5a476918-a33b-45cd-a274-6cf94611ba75",
        "Simulated Lock" : "8c438f30-9f29-45e2-ac8b-ed1bb7e7e3f3",
        "Simulated Minimote" : "2d629fba-7b73-432a-8a84-0c810a744be8",
        "Simulated Motion Sensor" : "853d865e-1d6c-4dcf-87a3-879b7757b9d7",
        "Simulated Presence Sensor" : "0d8244b9-e242-4e38-8f30-834b0753a239",
        "Simulated RGB Bulb" : "6512b733-2113-48cd-92cf-380ddb3fc1f5",
        "Simulated RGBW Bulb" : "5d237d4f-a0a7-4287-919a-42511176f0a5",
        "Simulated Refrigerator" : "e9ca772d-7f65-4809-9d49-2a87f8f3415e",
        "Simulated Refrigerator Door" : "58e1d183-435b-4c55-bc87-a8639e56b556",
        "Simulated Refrigerator Temperature Control" : "cd80202a-8922-4359-911a-94cde5d10c44",
        "Simulated Smoke Alarm" : "ac1759bd-cc1c-41ef-a770-ce0e6e86760c",
        "Simulated Switch" : "c5b2dbad-73cb-4e12-bf41-f08742e8e560",
        "Simulated Temperature Sensor" : "420a5067-a4b9-4858-bdc6-a088903e78b2",
        "Simulated Thermostat" : "9264f29a-4470-4332-b689-bc5cfe7c9bfc",
        "Simulated Water Sensor" : "fa6abb9e-b44e-4fbd-9820-76a2b56305a4",
        "Simulated Water Valve" : "1468389b-8fdd-484b-970e-9a85757617b7",
        "Simulated White Color Temperature Bulb" : "4cd363b8-abdc-4844-a1f6-f1edd97f7bac",
        "Simulated Window Shade" : "fd6e7d7e-4f9f-4dac-b5c7-1241eadeda81",
    }


    create_device_url = 'https://graph.api.smartthings.com/device/save'
    session.post(create_device_url, data={
        'id': smartapp_id,  
        'locationId': location,
        'zigbeeId': None,   
        'label': None,
        'name': "L_" + location_name + "_v_" + device_type.replace(" ","_").lower() + "_a",
        'deviceNetworkId': "L_" + location_name + "_v_" + device_type.replace(" ","_").lower() + "_a",  
        'type.id': device_type_ids[device_type],
        'handlerVersion': "LATEST_APPROVED",
        'hubId': None,
        'groupId': None,
        'create': 'create',
        '_csrf': csrf
    })

def install_app_in_location(smartapp_id, location):
    l = session.post('https://graph.api.smartthings.com/ide/app/setLocation', data = {'id': smartapp_id, 'location': location, '_csrf': csrf})
    return l

def assign_simulated_devices(smartapp_id):
    pass

print('end')

import time

def coordinate():

    print('waiting')
    time.sleep(3)

    with open('coordinator.txt', 'w') as outfile:
        outfile.write("done")     
        print('writing done')

# coordinate()


print('=== An IPython repl is opened. Run the following commands ===')
print("""for i in range(N):
   generate_events(create_event_stream()) 
   time.sleep(10)
   coordinate()""")
print('=== exit using exit() ===')
embed()
