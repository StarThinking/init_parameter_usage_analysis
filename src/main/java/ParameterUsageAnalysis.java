import soot.*;
import soot.jimple.*; 
import soot.jimple.AssignStmt;
import soot.jimple.IfStmt;
import soot.jimple.ThisRef;
import soot.options.Options;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.BlockGraph;
import soot.toolkits.graph.BriefBlockGraph;
import soot.toolkits.scalar.ArraySparseSet;
import soot.toolkits.scalar.FlowSet;
import soot.jimple.toolkits.callgraph.Targets;
import soot.jimple.toolkits.callgraph.Sources;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.*;
import soot.jimple.toolkits.annotation.callgraph.CallGraphGrapher;
import soot.tagkit.LineNumberTag;
import soot.jimple.internal.InvokeExprBox;
import soot.jimple.internal.RValueBox;
import soot.jimple.internal.*;

import soot.util.*;
import soot.Type;

import java.io.File;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.InputStreamReader;
import java.util.*;
import java.lang.Exception;

public class ParameterUsageAnalysis  {
    private static String confClassName = "org.apache.hadoop.conf.Configuration";
    private static CallGraph cg = null;
    private static List<String> procDirList = new ArrayList<String>();
    private static String classPath = ".";
    //private static String componentClass = "org.apache.hadoop.hdfs.server.namenode.NameNode";
    private static String componentClassName = "org.apache.hadoop.hdfs.server.namenode.SecondaryNameNode";

    private static List<String> configurationGetMethodNames = new ArrayList<String>();
    static {
        configurationGetMethodNames.add("getInt");
        configurationGetMethodNames.add("getInts");
        configurationGetMethodNames.add("getLong");
        configurationGetMethodNames.add("getLongBytes");
        configurationGetMethodNames.add("getFloat");
        configurationGetMethodNames.add("getDouble");
        configurationGetMethodNames.add("getBoolean");
        configurationGetMethodNames.add("getStorageSize");
        configurationGetMethodNames.add("getStrings");
        configurationGetMethodNames.add("getTimeDuration");
        configurationGetMethodNames.add("getRaw");
        configurationGetMethodNames.add("getEnum");
        configurationGetMethodNames.add("get");
    }

    private static void loadClassPath(String classPathPath) {
	try {
	    BufferedReader reader = new BufferedReader(new FileReader(classPathPath));
	    String buffer = "";
	    while ((buffer = reader.readLine()) != null) {
	        if (!buffer.equals("null"))
	            classPath += ":" + buffer;
            }
            reader.close();
	} catch(Exception e) {
 	    e.printStackTrace();
	}
    }
    
    private static void loadProcDirList(String procDirListPath) {
	try {
	    BufferedReader reader = new BufferedReader(new FileReader(procDirListPath));
	    String buffer = "";
	    while ((buffer = reader.readLine()) != null) {
	        if (!buffer.equals("null"))
	            procDirList.add(buffer);
            }
            reader.close();
	} catch(Exception e) {
 	    e.printStackTrace();
	}
    }

    public static void init() {
        Options.v().set_whole_program(true);  // process whole program
    	Options.v().set_allow_phantom_refs(true); // load phantom references
        Options.v().set_prepend_classpath(true); // prepend class path
        Options.v().set_src_prec(Options.src_prec_class); // process only .class files
        Options.v().set_process_dir(procDirList); // process all .class files in directory
    	Options.v().set_soot_classpath(classPath);
        Options.v().setPhaseOption("cg.spark", "on"); // use spark for call graph
    	Options.v().set_output_dir("/tmp/sootOutput"); // use spark for call graph
        Options.v().set_keep_line_number(true);
                   
        List<String> excludeList = new ArrayList<String>();
	excludeList.add("org.apache.hadoop.hbase.replication.regionserver.WALFileLengthProvider");	
	excludeList.add("org.apache.hadoop.hbase.hbtop.screen.top.TopScreenPresenter");	
	//excludeList.add("org.apache.hadoop.hbase.wal.*");
 	Options.v().set_no_bodies_for_excluded(true);	
	Options.v().set_exclude(excludeList);

        SootClass sootClass = Scene.v().loadClassAndSupport(componentClassName);
        sootClass.setApplicationClass();
        Scene.v().loadNecessaryClasses();
        CHATransformer.v().transform();
    	cg = Scene.v().getCallGraph();
    }
    
    private static final int levelThreshold = 5;

    private static void leveledPrint(String str, int level) {
        int l = 0;
        String tab = "";
        while (l < level) {
            tab += "\t";
            l ++;
        }
        System.out.println(tab + "(" + level + ") " + str);
    }

    private static void isLocalTransferred(InvokeExpr expr, List<Value> locals, int level) {
        for (int para_index = 0; para_index < expr.getArgCount(); para_index++) {
            ValueBox vb = expr.getArgBox(para_index);
            leveledPrint(para_index + " argument is " + vb, level);
            for (Value l : locals) {
                if(vb.getValue().equals(l)) {
                    leveledPrint("ARGUMENT_PASSING local value " + l + " is to be transferred as " + para_index + "th argument", level);
                }
            }
        }
        return;
    }

    private static int isConfMethod(SootMethod sootMethod, int level) {
        SootClass confClass = Scene.v().getSootClass(confClassName);
        SootClass declareClass = sootMethod.getDeclaringClass();
        String methodName = sootMethod.getName();
        if (declareClass.equals(confClass)) {
            //if (configurationGetMethodNames.contains(methodName)) {
            if (methodName.startsWith("get")) {
                leveledPrint("CONFIGURATION_GET_METHOD " + methodName, level);
                return 0;
            } else {
                return -1;
                //leveledPrint("CONFIGURATION_GET_METHOD " + methodName + " but NOT in list", level);
            }
        }
        return -1;
    }

    public static boolean goThrough(SootMethod sootMethod, int level) {
        leveledPrint("GO_THROUGH_BEGIN: " + sootMethod.getName(), level);
	Body body = null;
	try {
            body = sootMethod.getActiveBody();
        } catch (Exception e) {
            //System.out.println(e);
        }
        if (body == null) {
            leveledPrint("RETURN: body is null", level);
            return false;
        } 

        // go through each unit
	List<Value> localParaDefs = new ArrayList<Value>();
        List<Value> allLocals = new ArrayList<Value>();
        for (Local l : body.getLocals()) {
            leveledPrint("local: " + l, level);
            allLocals.add(l);
        }
        for (Unit unit : body.getUnits()) {
            leveledPrint("unit is " + unit, level);
            Boolean isReturnADef = false;
            if (isInvoke(unit)) {
                leveledPrint("INVOKE_UNIT", level);
                InvokeExpr expr = getInvokeExpr(unit);
                isLocalTransferred(expr, allLocals, level);
                SootMethod methodInvoked = expr.getMethod();
                if (level < levelThreshold) {
                    int tmp_ret = -1;
                    if ((tmp_ret = isConfMethod(methodInvoked, level)) >= 0) {
                        if (tmp_ret == 0) {
                            leveledPrint("RETURN: CONFIGURATION_GET_METHOD " + methodInvoked.getName(), level);
                            for (Value v : expr.getArgs()) {
                                leveledPrint("Parameter of ConfMethod: " + v, level);
                            }
                        }
                    } else {
                        isReturnADef = goThrough(methodInvoked, level+1);
                    }
                } else {
                    leveledPrint("SKIP: reach Level Threshold and skip jump into method " + methodInvoked.getName(), level);
                }

            }
            // AssignStmt
        }
	leveledPrint("RETURN: finish going through method " + sootMethod.getName(), level);
        // check if return value is one of local definitions
        return false;
    }

    public static void main(String[] args) {
	if (args.length != 2) {
	    System.out.println("Wrong arguments: [procDirListPath] [classPathPath]");
	    System.exit(-1);
	}
	String procDirListPath = args[0];
	String classPathPath = args[1];
        
	loadClassPath(classPathPath);
	loadProcDirList(procDirListPath);

        // init once and perform analysises for different functions
	int level = 0;
        ParameterUsageAnalysis.init();
        SootClass componentSootClass = Scene.v().getSootClass(componentClassName);
        /*for (SootMethod sm : componentSootClass.getMethods()) {
            if (sm.isConstructor()) {
                System.out.println(sm.getSubSignature());
                ParameterUsageAnalysis.goThrough(sm, level);
            }
        }*/
        //SootMethod initMethod = componentSootClass.getMethod("void <init>(org.apache.hadoop.conf.Configuration)");
        // SootMethod initMethod = componentSootClass.getMethod("void <init>(org.apache.hadoop.conf.Configuration)"); body is null
        SootMethod initMethod = componentSootClass.getMethod("void <init>(org.apache.hadoop.conf.Configuration,org.apache.hadoop.hdfs.server.namenode.SecondaryNameNode$CommandLineOpts)");
        ParameterUsageAnalysis.goThrough(initMethod, level);
    }

    public static boolean isInvoke(Unit q){
        if (q instanceof JInvokeStmt)
            return true;
        else if (q instanceof JAssignStmt)
            if ((((JAssignStmt)q).rightBox.getValue()) instanceof InvokeExpr)
                return true;
        return false;
    }

    public static InvokeExpr getInvokeExpr(Unit q){
        assert (q instanceof JInvokeStmt || q instanceof JAssignStmt);
        InvokeExpr ie;
        if (q instanceof JInvokeStmt)
            ie = ((JInvokeStmt)q).getInvokeExpr();
        else if (q instanceof JAssignStmt)
            ie = ((InvokeExpr)(((JAssignStmt)q).rightBox.getValue()));
        else
            ie = null;
        return ie;
    }
}








//SootMethod initMethod = componentSootClass.getMethod("org.apache.hadoop.hdfs.server.namenode.NameNode: void <init>(org.apache.hadoop.conf.Configuration)");
//List<Type> parameterTypes = new ArrayList<Type>();
//RefType firstType = RefType.v("org.apache.hadoop.conf.Configuration");
//parameterTypes.add(firstType);
//void <init>(org.apache.hadoop.conf.Configuration,org.apache.hadoop.hdfs.server.common.HdfsServerConstants$NamenodeRole)
