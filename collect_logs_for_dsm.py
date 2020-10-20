# https://graph.api.smartthings.com/ide/logs


# ST.init({
#               url: '/ide/',
#               websocket: 'wss://ic-na01-useast1.connect.smartthings.com/',
#               client: 'a64a7052-82af-4709-9037-f972a5193cf1'
#           });

# register a64a7052-82af-4709-9037-f972a5193cf1

# logs -> 0 -> msg


## Collect logs from SmartThings Simulator's log.
##

from requests_html import HTMLSession

from http.cookies import SimpleCookie

from IPython import embed
import sys, ipdb, traceback

import pickle

def info(type, value, tb):
    traceback.print_exception(type, value, tb)
    ipdb.pm()


sys.excepthook = info

def write_trace():
    print('checking for events')
    if len(trace) > 0:
        print('will write')

        filenum = 0
        while os.path.exists('trace_' + sys.argv[3] + '.txt' + str(filenum)):
            filenum += 1
        with open('trace_' + sys.argv[3] + '.txt' + str(filenum), 'w+') as outfile:
            for i, tuple_event in enumerate(trace):
                event = tuple_event[0] + "__" + tuple_event[1].split()[0]
                outfile.write(event)
                if i != len(trace) - 1:
                    outfile.write(" ")
            outfile.write('\n')
        print('written')

        with open('resps_' + sys.argv[3] + '.txt' + str(filenum), 'wb') as outfile:
            pickle.dump(resps, outfile)
        print('written')
    trace.clear()

import sys

cookie_str = sys.argv[1]
location = sys.argv[2]

# def init():
cookie = SimpleCookie()

# cookie_str = '_hp2_id.2894297474=%7B%22userId%22%3A%221676578337305413%22%2C%22pageviewId%22%3A%229925373119943%22%2C%22sessionId%22%3A%228231688974056707%22%2C%22identity%22%3Anull%2C%22trackerVersion%22%3A%224.0%22%7D; JSESSIONID=58510E5697A720E662510006FD3CA539-n1; _JTKN=eyJraWQiOiI5dmtsOTkyYTE4ZmVNX045X2tuQ2I2dHh6Ri1LdnBwVkFNNTYtOFIwX21BIiwiYWxnIjoiUlMyNTYifQ.eyJwcmluY2lwYWwiOiJ1c2VyX3V1aWQ6YzNmOTM3NjMtYWY5MS0zZGUxLTRmZWQtY2I5ZTNiMjliMTQ4Iiwic2Ftc3VuZ19hY2NvdW50X2lkIjoicXB1b2dkc251aiIsInVzZXJfbmFtZSI6InVzZXJfdXVpZDpjM2Y5Mzc2My1hZjkxLTNkZTEtNGZlZC1jYjllM2IyOWIxNDgiLCJzY29wZSI6WyJ3OmN1c3RvbWNhcGFiaWxpdHkiLCJjb250cm9sbGVyOndlYnNzbyIsInI6Y3VzdG9tY2FwYWJpbGl0eSIsIm1vYmlsZSIsInI6Y2F0YWxvZyJdLCJmdWxsTmFtZSI6IkhvbmcgSmluIEthbmciLCJleHAiOjE1OTU4MjcxMTYsInV1aWQiOiJjM2Y5Mzc2My1hZjkxLTNkZTEtNGZlZC1jYjllM2IyOWIxNDgiLCJlbWFpbCI6Imthbmdob25namluQGdtYWlsLmNvbSIsImF1dGhvcml0aWVzIjpbIlJPTEVfREVWRUxPUEVSIiwiUk9MRV9VU0VSIl0sImNsaWVudF9pZCI6IjhmNGRiZTZkLTkwNjYtNGQwZS05OWQwLWRmMWFjN2U2OWE3ZSJ9.k9ar604HWb1yIodl37UJkm62kyQ9GOkJge_07Eoou84IQmDFKBptsVeYpRVhDRP4x-P16XLVlvFFC34wK8f1CMO5BEcVWI_kmiH_OwKuY3C5f2XEGOWxtuvVY-GFRg39efrx_pZxldKp22BWkiXKOOMPwe6UoQSWzvoo1K2yTLF249etFs4K1j6nAP_aWG0Q6x0Xs6qz9uGUG74on6lodfqxlpuUlbbjdSWXDs4yj2Iv5Uw6z9y4FRM6Y13V96ALpbshqZgXs7vpc1FWRAZs-b9maF6gBZTnjgEEWFIQXpXWT6nzYR10Bl0KSysH66c1Hsv9Mnz1XCs6FYsFSu48HA'

cookie_str = sys.argv[1]

cookie.load(cookie_str)

session = HTMLSession()
for item in cookie.items():
    session.cookies.set(*item)
a = session.get('https://graph.api.smartthings.com/ide/apps')

links = a.html.find('#smartapp-table tr a')
smartapps = []

smartapp_id = None

for link in links:
    if link.attrs['href'].startswith('/ide/app/editor/'):
        smartapps.append('https://graph.api.smartthings.com/' + link.attrs['href'])

        smartapp_id = link.attrs['href'].split('editor/')[1]  # '12c162b8-997d-41ea-aefd-deff013bf9a8'

if smartapp_id is None:
    print('cannot find smartapp id')
    print(links)
    raise Exception('cannot get smartapp id')

# the last smartapp's id is used in this script. But, really, any smartapp can be used.
smartapp_page = session.get('https://graph.api.smartthings.com/ide/app/editor/' + smartapp_id)

csrf = smartapp_page.html.find('meta[name="_csrf"]')[0].attrs['content']

locations = [option.attrs['value'] for option in smartapp_page.html.find('#location option')]

log_page = session.get('https://graph.api.smartthings.com/ide/logs')
websocket_page = log_page.text.split("ST.init")[1].split("websocket: ")[1].split(',')[0].strip("'")
client = log_page.text.split("ST.init")[1].split("client: ")[1].split("'")[1]

from IPython import embed

import asyncio
import websockets
import os

import json

# embed()

print(websocket_page)
print(client)

trace = []

resps = []

def coordinate_and_write():
    print('checking')
    # check if we should start a new trace
    done = False
    with open('coordinator.txt', 'r') as infile:
        
        for line in infile:
            if line.strip() == "done":
                done = True

    if done:
        write_trace()
        done = False
        with open('coordinator.txt', 'w') as outfile:
            outfile.write("no")

        print()
        print()
        print()

async def read_logs(websocket, client):
    print('connecting to ', websocket + 'client/' + client)

    next_to_ignore = None

    async with websockets.connect(websocket + 'client/' + client, ping_interval=20, ping_timeout=None) as websocket:
        # init

        # print('> ', 'register ' + client)
        # await websocket.send('register ' + client)

        print("done websocket init")

        print('sent. Ready for commands to be sent')

        while True:

           
            coordinate_and_write()
            resp = await websocket.recv()

            coordinate_and_write()
            # print(f"< {resp}")

            if '{' in resp:  # is json
                for one_line in resp.split('\n'):

                    resp_json = json.loads(one_line)

                    resps.append(resp_json)
                    if 'logs' in resp_json:
                        for log in resp_json['logs']:
                            device_description = ""
                            if 'msg' in log:
                                print('log: ', log['msg'])

                                # print('log -----', log.keys())
                                # if 'targets' in log:
                                #     targets = []
                                #     for target in log["targets"]:
                                #         targets.append(target["label"])

                                #         method = log['msg'].split("PUBLISHED ")[1]
                                #         sandbox_of_api_calls.add((target["label"], method))
                                if 'command was sent to' in log['msg']:
                                    device_description = log['msg'].split('command was sent to ')[1].strip()
                                    command_type = log['msg'].split('command was sent to ')[0].strip()


                                    if next_to_ignore is not None and next_to_ignore == command_type:
                                        pass #ignored 
                                        next_to_ignore = None
                                    else:
                                        trace.append((device_description, command_type))


                                if 'Invoking ' in log['msg'] and '*' in log['msg']:
                                    executed_code = log['msg'].split('*')[1]

                                    if '(' in executed_code: 
                                        # there will be a X command was sent to Y log later on, but it should be ignored since it refers to the same event
                                        # as this one.
                                        
                                        executed_command = executed_code.split('.')[1].split()[0].strip().strip('()')
                                        print('next to ignore', executed_command)
                                        # next_to_ignore = executed_command

                                        trace.append((device_description, 'auto_' + executed_command))
                                    else: # probably something like "location mode change", so we'll just accept the whole sting
                                        executed_command = executed_code.replace(' ', '_')                                    
                                        trace.append((device_description, 'auto_' + executed_command))
                                    


                    if 'event' in resp_json:
                        print('event:', resp_json['event']['description'])
                        # extract device id

                        if 'deviceId' in resp_json['event']:
                            device_id = resp_json['event']['deviceId']
                            # device_ndi = resp_json['event']['linkText']
                            print('  at device_id=', device_id)
                            # print('  which has ndi=', device_ndi)
                        else:
                            print('  no known device')

                        if 'eventSource' in resp_json['event'] and resp_json['event']['eventSource'] == "COMMAND":
                            if 'command was sent to ' in resp_json['event']['description']:
                                device_description = resp_json['event']['description'].split('command was sent to ')[1].strip()
                                command_type = resp_json['event']['description'].split('command was sent to ')[0].strip()

                                if next_to_ignore is not None and next_to_ignore == command_type:
                                    pass #ignored 
                                    next_to_ignore = None
                                else:
                                    trace.append((device_description, command_type))
                        elif 'eventType' in resp_json['event'] and resp_json['event']['eventType'] == "NOTIFICATION":
                            trace.append(("notification", resp_json['event']['description']))

                        elif 'eventType' in resp_json['event'] and resp_json['event'][
                                    'eventType'] == "LOCATION_MODE_CHANGE":
                            trace.append(("mode_change", resp_json['event']['rawDescription'].replace(' ', '_'))) 

            

try:
    asyncio.get_event_loop().run_until_complete(read_logs(websocket_page, client))
    asyncio.get_event_loop().run_forever()
except KeyboardInterrupt:
    pass

# print('trace: ', trace)

write_trace()


# on termination, always reset 
with open('coordinator.txt', 'w') as outfile:
    outfile.write("no")
