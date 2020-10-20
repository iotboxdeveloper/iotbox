echo "Hello."
echo "Let's begin."
echo "Running IoTBox evaluation..."

echo "1% is the threshold. If 99% is accepted, then the bundle is considered benign. Otherwise, it is considered malicious."
echo ""
echo "                             ............."
echo "=============================Static Traces=========================="
echo "                             ............."
echo "=============================For Table II =========================="
echo "                             .............."
echo "Running bundle 16 "
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20201006_BundleID9_Safe/stage/newHoldPairs.txt static_traces/trace_run_20201006_BundleID9_Safe.txt  50
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20201006_BundleID9_Safe/stage/newHoldPairs.txt static_traces/trace_run_20201006_BundleID9.txt  50

echo "========="
echo "Running bundle 15 "
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20201006_BundleID8_Safe/stage/newHoldPairs.txt static_traces/trace_run_20201006_BundleID8_Safe.txt  30
echo "% of unsafe traces (Missing) that are accepted (expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20201006_BundleID8_Safe/stage/newHoldPairs.txt static_traces/trace_run_20201006_BundleID8.txt  30

echo "========="
echo "Running bundle 9 "
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20201006_BundleID2_Safe/stage/newHoldPairs.txt static_traces/trace_run_20201006_BundleID2_Safe.txt 50 
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20201006_BundleID2_Safe/stage/newHoldPairs.txt static_traces/trace_run_20201006_BundleID2.txt 50 

echo "========="
echo "Running bundle 8 "
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20201006_BundleID1_Safe/stage/newHoldPairs.txt static_traces/trace_run_20201006_BundleID1_Safe.txt 75 
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20201006_BundleID1_Safe/stage/newHoldPairs.txt static_traces/trace_run_20201006_BundleID1.txt 75 

echo "========="
echo "Running bundle 13 "
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle9_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200921_Bundle9_Safe.txt 67 
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle9_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200921_Bundle9.txt 67
echo "% of unsafe traces (Missing) that are accepted (expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle9_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200921_Bundle9_Missing.txt 67


echo "========="
echo "Running bundle 12 "
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle8_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200921_Bundle8_Safe.txt 80  
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle8_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200921_Bundle8.txt 80  
echo "% of unsafe traces (Missing) that are  accepted(expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle8_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200921_Bundle8_Missing.txt 80  

echo "========="
echo "Running Bundle 10 (bundle 17 in the paper)"
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20201008_Bundle10_Safe/stage/newHoldPairs.txt static_traces/trace_run_20201008_Bundle10_Safe.txt  20 40
echo "% of unsafe traces (Missing) that are accepted (expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20201008_Bundle10_Safe/stage/newHoldPairs.txt static_traces/trace_run_20201008_Bundle10_Missing.txt  20 40


echo "========="
echo "Running bundle 7 "
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle7_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200921_Bundle7_Safe.txt 40 
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle7_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200921_Bundle7.txt 40 
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle7_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200921_Bundle7_Missing.txt 40 


echo "========="
echo "Running bundle 6 "
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle6_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200921_Bundle6_Safe.txt 40 
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle6_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200918_Bundle6.txt 40 

echo "========="
echo "Running bundle 5 "
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle5_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200921_Bundle5_Safe.txt 40 
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle5_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200917_Bundle5.txt 40 

echo "========="
echo "Running bundle 4 "
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle4_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200921_Bundle4_Safe.txt 100 
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle4_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200917_Bundle4.txt 100 

echo "========="
echo "Running bundle 3 "
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle3_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200921_Bundle3_Safe.txt 23 40
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle3_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200918_Bundle3.txt 23 40

echo "========="
echo "Running bundle 2 "
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle2_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200921_Bundle2_Safe.txt 25 
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle2_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200918_Bundle2.txt 25 

echo "========="
echo "Running bundle 1 "
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle1_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200921_Bundle1_Safe.txt 20 
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_trace_accepted_by_model.py alloy/run_20200921_Bundle1_Safe/stage/newHoldPairs.txt static_traces/trace_run_20200918_Bundle1.txt 20 

echo "                             .............."
echo "=============================Dynamic Traces=========================="
echo "                             .............."
echo "=============================For Table III=========================="
echo "                             .............."
echo "Running bundle 17, for dynamic traces"
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_dynamic_trace_accepted_by_model.py alloy/run_20201008_Bundle10_Safe/stage/newHoldPairs.txt dynamic_traces/bundle_10_random_new/input.txt static_traces/trace_run_20201008_Bundle10_Safe.txt  19
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_dynamic_trace_accepted_by_model.py alloy/run_20201008_Bundle10_Safe/stage/newHoldPairs.txt dynamic_traces/bundle_10_random_new_unsafe/input.txt static_traces/trace_run_20201008_Bundle10_Safe.txt  19

echo "========="
echo "Running bundle 16, for dynamic traces"
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_dynamic_trace_accepted_by_model.py alloy/run_20201006_BundleID9_Safe/stage/newHoldPairs.txt dynamic_traces/bundle_id9_new/input.txt  static_traces/trace_run_20201006_BundleID9_Safe.txt 40 
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_dynamic_trace_accepted_by_model.py alloy/run_20201006_BundleID9_Safe/stage/newHoldPairs.txt dynamic_traces/bundle_id9_new_test/input.txt  static_traces/trace_run_20201006_BundleID9_Safe.txt 40 

echo "========="
echo "Running bundle 8, for dynamic traces"
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_dynamic_trace_accepted_by_model.py alloy/run_20201006_BundleID1_Safe/stage/newHoldPairs.txt dynamic_traces/bundle_id1_new/input.txt static_traces/trace_run_20201006_BundleID1_Safe.txt 40  
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_dynamic_trace_accepted_by_model.py alloy/run_20201006_BundleID1_Safe/stage/newHoldPairs.txt dynamic_traces/bundle_id1_new_test/input.txt static_traces/trace_run_20201006_BundleID1_Safe.txt  40

echo "========="
echo "Running bundle 9, for dynamic traces"
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_dynamic_trace_accepted_by_model.py alloy/run_20201006_BundleID2_Safe/stage/newHoldPairs.txt dynamic_traces/bundle_id2_new/input.txt static_traces/trace_run_20201006_BundleID2_Safe.txt  60
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_dynamic_trace_accepted_by_model.py alloy/run_20201006_BundleID2_Safe/stage/newHoldPairs.txt dynamic_traces/bundle_id2_new_test/input.txt static_traces/trace_run_20201006_BundleID2_Safe.txt  60

echo "========="
echo "Running bundle 16, for dynamic traces"
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_dynamic_trace_accepted_by_model.py alloy/run_20201006_BundleID9_Safe/stage/newHoldPairs.txt dynamic_traces/bundle_id9_new/input.txt static_traces/trace_run_20201006_BundleID9_Safe.txt  40
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_dynamic_trace_accepted_by_model.py alloy/run_20201006_BundleID9_Safe/stage/newHoldPairs.txt dynamic_traces/bundle_id9_new_test/input.txt static_traces/trace_run_20201006_BundleID9_Safe.txt 40 

echo "========="
echo "Running bundle 1, for dynamic traces"
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_dynamic_trace_accepted_by_model.py alloy/run_20200921_Bundle1_Safe/stage/newHoldPairs.txt dynamic_traces/bundle_1_safe/input.txt static_traces/trace_run_20200921_Bundle1_Safe.txt 10 
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_dynamic_trace_accepted_by_model.py alloy/run_20200921_Bundle1_Safe/stage/newHoldPairs.txt dynamic_traces/bundle_1_unsafe/input.txt static_traces/trace_run_20200921_Bundle1_Safe.txt 10

echo "========="
echo "Running bundle 2, for dynamic traces"
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_dynamic_trace_accepted_by_model.py alloy/run_20200921_Bundle2_Safe/stage/newHoldPairs.txt dynamic_traces/bundle_2_new/input.txt static_traces/trace_run_20200921_Bundle2_Safe.txt 120 
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_dynamic_trace_accepted_by_model.py alloy/run_20200921_Bundle2_Safe/stage/newHoldPairs.txt dynamic_traces/bundle_2_new_test/input.txt static_traces/trace_run_20200921_Bundle2_Safe.txt 120 

echo "========="
echo "Running bundle 3, for dynamic traces"
echo "% of benign traces that are accepted (expected 1.0, 0.99)="
python3 is_dynamic_trace_accepted_by_model.py alloy/run_20200921_Bundle3_Safe/stage/newHoldPairs.txt dynamic_traces/bundle_3_safe/input.txt static_traces/trace_run_20200921_Bundle3_Safe.txt 43 
echo "% of unsafe traces that are accepted (expected <0.99)="
python3 is_dynamic_trace_accepted_by_model.py alloy/run_20200921_Bundle3_Safe/stage/newHoldPairs.txt dynamic_traces/bundle_3_unsafe/input.txt static_traces/trace_run_20200921_Bundle3_Safe.txt 43 

echo "=============================Done=========================="
