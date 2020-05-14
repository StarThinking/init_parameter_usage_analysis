#!/bin/bash

component_project=hdfs
classpath_path="/root/reconf_test_gen/$component_project/soot_path/classpath.txt"
procdir_path="/root/reconf_test_gen/$component_project/soot_path/proc_dir.txt"

java -cp build/libs/init_parameter_usage_analysis-1.0.jar ParameterUsageAnalysis $procdir_path $classpath_path
