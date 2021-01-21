
# Introduction

In a nutshell, IoTBox tries to find all execution paths (across multiple apps) that reaches an action.
Using that, we can 'guess' if a given trace was produced from the same smart home or not.
e.g. if there are actions that cannot be explained by the executions paths that we identified, then it's a different smart home,
or if there are actions that we expect given an trace, but it's not present, then it's a different smart home.

This helps to defend the smart home against unexpected code changes (coming from a compromised, upstream version of the SmartThings app), or latent behavior that's executed through dynamic method invocation (e.g. GStrings).

Our project can analyse apps of SmartThings Classic and IFTTT, but our prototype that 'enforces' the policy only works for SmartThings classic.
The general idea of this project should be applicable to other models of IoT apps, but we focused our experiments on only these two platforms.
We work with apps that can be analysed by the IOTCOM project. If the scope of that project increases to allow apps of other platforms,
then they can be analysed by this project too.
These apps go into https://graph.api.smartthings.com/ide/apps.

This GitHub repository is the replication package, and the following sections provide instructions on replicating the results.

[Table II, III results](#obtaining-evaluation-results-table-ii-iii)

[Table I results](#rerunning-the-experiments-from-scratch)

[Description of other scripts](#description-of-scripts)

# Obtaining evaluation results (Table II, III)

These are the key findings.
To quickly reproduce the results in the paper, run `sh test.sh`. 
This will produce all the numbers required to check the results in Table II and III.

The Alloy assertions can be viewed in the `alloy/` directory.

# Rerunning the experiments from scratch
All the Alloy models we used are in the `alloy/` directory.

First, we generate the assertion for all actions for in one bundle.
One assertion is created for each action.
Run `python3 generate_assertions.py alloy/run_20200921_Bundle1_Safe/stage/`,
a file containing the assertion is created. This assertion is similar in its format to the security policies used by IOTCOM.

Copy the produced assertion file to the bundle
`cp assertions_run_20200921_Bundle1_Safe.als alloy/run_20200921_Bundle1_Safe/stage/`

Run the Alloy analyser to produce counterexamples for each assertion.
Note that the code was tested on Java 8.
`java -jar alloy/iotcom-sandbox-refine-1.0.0.jar  alloy/run_20200921_Bundle1_Safe/stage/ link_from_alloy_skolem_to_attr_val_run_20200921_Bundle1_Safe.txt`.
This jar file is a modified version of IOTCOM, which wraps over the execution of the Alloy Analyser.

Read the output of the above command carefully, it will indicate if there are counterexamples found. 
On the first run, it is likely to have found counterexamples.
Thus, update the assertion file to include the counterexamples:

`python3 update_assertions.py alloy/run_20200921_Bundle1_Safe/stage/assertions_run_20200921_Bundle1_Safe.als alloy/run_20200921_Bundle1_Safe/stage/newAssertions.txt`

and run the Alloy Analyser again:
`java -jar alloy/iotcom-sandbox-refine-1.0.0.jar  alloy/run_20200921_Bundle1_Safe/stage/ link_from_alloy_skolem_to_attr_val_run_20200921_Bundle1_Safe.txt`

Repeat the above 2 steps (`update assertion` and `java -jar alloy/iotcom-sandbox-refine-1.0.0.jar `) as many times as necessary,
until `java -jar alloy/iotcom-sandbox-refine-1.0.0.jar ` tells you that there are no longer any counter examples.
This indicates that we have found all the necessary information to find all paths.

Next, construct the paths
`python3 complete_hold_pairs.py alloy/run_20200921_Bundle1_Safe/stage/`.
The output of this script gives us the paths from each triggering event (from the output of `java -jar alloy/iotcom-sandbox-refine-1.0.0.jar`) to each action.



# Individual app violations (Table I)


The 4 cases discussed in Table I are given in individual_app_violations. We modify the Alloy files (bundle-01.*.als) produced by IOTCOM to remove the irrelevant assertions. These files can be opened in the Alloy Analyser GUI, then Execute > Check * from the GUI.


The total violations can be counted using `ls -la all_individual_app_violations/*xml | wc`.
These violations were found using IOTCOM (https://cse.unl.edu/~hbagheri/publications/2020ISSTA.pdf).

## Breakdown of violations
Our work is largely based on IOTCOM, which detects coordination threats and violations of safety properties.
Most of the 'false positive' violations come from the coordination threats, which suggests that these rules will need further refinement to be deployed in a smart home.

# Description of scripts

## Scripts related to exercising the SmartThings simulator
Run both scripts on different terminals.
First, run `generate_events_randomly` and wait for it to collect the necessary info, then run `collect_logs_for_dsm.py`. Follow the instructions printed by the `generate_events_randomly` script.

* collect_logs_for_dsm.py: <cookie_str> <location> <identifier to save file as>
* generate_events_randomly.py: <cookie_str> <location> <does time matter: T/F>
	Get <cookie_str> by navigating to the SmartThings IDE, and inspect the Network tab under developer tools. Copy the cookie and paste it in here. 
	<location> is the uuid that is produced under SmartThings. This is where the devices are located at.
	If the apps model time, <does time matter> is T. If no time-related function is used, then the simulator runs quite a little faster, and you can skip the time-related processing by indicating 'F'

## scripts for offline simulator
* world.py: <path to alloy stage> <number of sequences> <model physical channels?>
	e.g. `python3 world.py ~/eclipse-workspace/IOTCOM-github/FormalAnalyzer/out/run_20200921_Bundle2_Safe/stage/ 20 5 t`

	This creates the trace_run_* files you can find in static_traces/
	<model physical channels?> has to always be 't', 'f' is unsupported for the time being

## Scripts for forming the rules of the sandbox
* generate_assertions.py: creates an initial set of assertions
e.g. `python3 generate_assertions.py alloy/run_20200921_Bundle1_Safe/stage/`
After running, remember to check the created file and cp them into the stage directory
e.g. `cp assertions_run_20200921_Bundle1_Safe.als alloy/run_20200921_Bundle1_Safe/stage/`

* alloy/iotcom-sandbox-refine-1.0.0.jar runs our code, modified from IOTCOM, that runs Alloy
Note that this requires Java 8.

`time java -jar alloy/iotcom-sandbox-refine-1.0.0.jar  alloy/run_20200921_Bundle1_Safe/stage/ link_from_alloy_skolem_to_attr_val_run_20200921_Bundle1_Safe.txt`

* update_assertions.py: updates the assertion files with the new information (e.g. other events that trigger the action)
`python3 update_assertions.py alloy/run_20200921_Bundle1_Safe/stage/assertions_run_20200921_Bundle1_Safe.als alloy/run_20200921_Bundle1_Safe/stage/newAssertions.txt`

* complete_hold_pairs.py: Completes the paths based on the initial events. 
`python3 complete_hold_pairs.py alloy/run_20200921_Bundle1_Safe/stage/`

## Scripts to accept traces
* is_trace_accepted_by_model.py: compares the trace to the model, and prints out the percentage of traces that were accepted


## Script to visualize path
* python3 path_visualizer.py: produces a simple visualization of the paths that lead to a given action
e.g. `python3 path_visualizer.py alloy/run_20201008_Bundle10_Safe/stage/newHoldPairs.txt lock switch`
produces a visualization of path from a `switch` event to a `lock` event

