import sys


## strawman sandbox

allowed_calls = set()

# training. pass input.txt (same formatted file for DSM)
with open(sys.argv[1], 'r') as infile:
    for line in infile:
        events = line.split()
        allowed_calls.update([event for event in events if len(event) > 0])


# test file
outcomes = []
traces = []
with open(sys.argv[2], 'r') as infile:
    for line in infile:
        accepted = True
        events = line.split()

        traces.append(events)

        for event in events:
            if event not in allowed_calls:
                print('found suspicious call:', event)
                accepted = False
                break

        outcomes.append(accepted)


print(outcomes)

num_rejected = sum([1 for outcome in outcomes if outcome is False])
num_accepted = sum([1 for outcome in outcomes if outcome is True])

print('% rejected = ', num_rejected / (1.0 * num_accepted + num_rejected))
print('if computing unsafe traces, % rejected is the true positive rate. Otherwise, it is the false positive rate.')
print('total traces used to compute the above = ', len(traces))
