# Component Parameter Analysis

Note that the .txt is filtered!

## Build
gradle build

## Use example:
org.apache.hadoop.hdfs.server.namenode.NameNode
org.apache.hadoop.hdfs.server.namenode.SecondaryNameNode
org.apache.hadoop.hdfs.server.datanode.DataNode
org.apache.hadoop.hdfs.qjournal.server.JournalNode
org.apache.hadoop.hdfs.server.balancer.Balancer
org.apache.hadoop.hdfs.server.mover.Mover

java -cp build/libs/component_parameter_analysis-1.0.jar ComponentAnalysis /root/hadoop-3.1.2-src/hadoop-hdfs-project/hadoop-hdfs/target/classes org.apache.hadoop.hdfs.server.namenode.NameNode
