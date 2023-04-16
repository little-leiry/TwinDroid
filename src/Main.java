import analysis.*;
import graph.Graph;
import org.apache.commons.collections4.CollectionUtils;
import soot.*;

import soot.options.Options;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.CompleteBlockGraph;

import java.io.*;
import java.util.*;

import static java.lang.Thread.sleep;

public class Main {
    public static final String code_base_path_12 = "/data/disk_16t_2/leiry/android12_source/";
    public static final String dexCode_path_12 = code_base_path_12 + "DEX-12-framework/";
    public static final String dexCode_path_lite_12 = code_base_path_12 + "systemCode/";

    public static final String code_base_path_11 = "/data/disk_16t_2/leiry/android11_source/";
    public static final String dexCode_path_11 = code_base_path_11 + "DEX-11-framework/";
    public static final String dexCode_path_lite_11 = code_base_path_11 + "systemCode/";

    public static final String store_base_path_12 = "android12/";
    public static final String store_base_path_11 = "android11/";

    public static void main(String[] args) throws IOException, InterruptedException {
        long start, end;
        Utils.printPartingLine("+");
        String android_code_path = dexCode_path_12;
        if(android_code_path.contains("android11")){
            Analysis.store_base_path = "android11/";
        }
        System.out.println(Analysis.store_base_path);
        //Utils.pause();
        System.out.println("Loading (initialize) classes ...");
        start = System.currentTimeMillis();
        sootInitial_dex(android_code_path);
        System.out.println("Done.");
        //Utils.printPartingLine("+");
        System.out.println("Initializing interface & abstract classes information ...");
        Analysis.initializeInterfaceAndAbstractClassesInfo();
        System.out.println("Done.");
        end = System.currentTimeMillis();
        System.out.println("Initialization: " + Utils.ms2DHMS(start, end));
        Utils.printPartingLine("+");
        System.out.println("Stage 1: find target package settings ...");
        start = System.currentTimeMillis();
        AnalysisForParsingClass2.findTargetPackageSettings();
        end = System.currentTimeMillis();
        System.out.println("Stage 1: " + Utils.ms2DHMS(start, end));
        Analysis.clearCommonDataSet();
        //Utils.pause();
        Utils.printPartingLine("+");
        System.out.println("Stage 2: identify suspicious processing methods ...");
        start = System.currentTimeMillis();
        AnalysisForSystemClass2.identifySuspiciousMethods();
        end = System.currentTimeMillis();
        System.out.println("Stage 2: " + Utils.ms2DHMS(start, end));
        //test3();
    }

    private static void sootInitial_dex(String code_path) {
        soot.G.reset();
        // android.jar包位置
        Options.v().set_force_android_jar("lib/android31.jar");
        // 处理java则为Options.src_prec_java，处理jar包则为src_prec_J
        Options.v().set_src_prec(Options.src_prec_apk);
        // 该处测试用于apk，可注释
        Options.v().set_process_multiple_dex(true);
        // 以下不用管
        Options.v().set_process_dir(Collections.singletonList(code_path));
        Options.v().set_whole_program(true);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_output_format(Options.output_format_none);
        Options.v().ignore_resolution_errors();
        Scene.v().loadNecessaryClasses();
    }

    private static void sootInitial_java(String javaPath) {
        soot.G.reset();
        // android.jar包位置
        Options.v().set_force_android_jar("lib/android31.jar");
        Options.v().set_src_prec(Options.src_prec_class);
        // 以下不用管
        Options.v().set_process_dir(Collections.singletonList(javaPath));
        Options.v().set_whole_program(true);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_output_format(Options.output_format_none);
        Options.v().ignore_resolution_errors();
        Scene.v().loadNecessaryClasses();
    }


    /*public static void test1(){
        long start, end;
        start = System.currentTimeMillis();
        List<String > a = new ArrayList<>();
        a.add("1");
        String[] b = new String[1];
        b[0] = "2";
        for(String s : b){
            System.out.println(s);
        }
        a.toArray(b);
        for(String s : b){
            System.out.println(s);
        }
        end = System.currentTimeMillis();
        System.out.println(end-start);
    }

    // print body
    // given class name and method name
    public static void test2() {
        String[] className = {
                "android.content.pm.parsing.component.ParsedComponent",
                "android.content.pm.parsing.component.ParsedActivity",
                "android.content.pm.parsing.component.ParsedIntentInfo",
                "android.content.pm.parsing.component.ParsedService",
                "com.android.server.pm.permission.PermissionManagerService",
                "android.content.pm.parsing.component.ParsedInstrumentation",
                "com.android.server.pm.SharedUserSetting",
                "androidx.appcompat.widget.SuggestionsAdapter",
                "android.content.pm.parsing.ParsingPackageImpl",
                "com.android.server.pm.PackageManagerService",
                "com.android.server.pm.parsing.pkg.PackageImpl",
                "android.content.res.XmlBlock",
                "android.content.pm.parsing.ParsingPackage",
                "android.content.pm.parsing.PackageInfoWithoutStateUtils",
                "com.android.server.pm.parsing",
                "com.android.server.backup.UserBackupManagerService"
        };
        String[] methodName = {"revokeRuntimePermissionsIfGroupChanged", "<init>", "getActivities", "addActivity", "preparePackageLI", "newParser", "revokeRuntimePermissionsIfGroupChangedInternal",
        "generateWithComponents", "PackageParserLegacyCoreTest", "addPackage", "readFullBackupSchedule"};
        SootClass cls = Scene.v().getSootClassUnsafe(className[0]);
        for(SootMethod sm : cls.getMethods()){
            System.out.println("+++ " + sm);
            System.out.println("=== " + sm.retrieveActiveBody());
        }

        //System.out.println(cls.getInterfaces());
        //System.out.println(cls.getSuperclass());
        for(SootField sf : cls.getFields()){
            System.out.println(sf.getType());
            if(sf.getType() instanceof RefType){
                System.out.println("=== " + ((RefType) sf.getType()).getAnySubType());
            }
            Utils.pause();
        }
    }

    // print body
    // given method signature
    private static void test3() {
        String[] sigs = {
                "<com.android.server.pm.PackageManagerService: com.android.server.pm.PackageManagerService$PrepareResult preparePackageLI(com.android.server.pm.PackageManagerService$InstallArgs,com.android.server.pm.PackageManagerService$PackageInstalledInfo)>",
                "<com.android.server.pm.PackageManagerService: void assertPackageIsValid(com.android.server.pm.parsing.pkg.AndroidPackage,int,int)>",
                "<com.android.server.pm.ComponentResolver$ActivityIntentResolver: void addActivity(android.content.pm.parsing.component.ParsedActivity,java.lang.String,java.util.List)>",
                "<com.android.server.pm.ComponentResolver: void addReceiversLocked(com.android.server.pm.parsing.pkg.AndroidPackage,boolean)>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseSplitApplication(android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,int,int)>",
                "<android.content.pm.parsing.component.ParsedActivityUtils: android.content.pm.parsing.result.ParseResult parseActivityAlias(android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser,boolean,android.content.pm.parsing.result.ParseInput)>",
                "<android.content.pm.parsing.ParsingPackageImpl: void addMimeGroupsFromComponent(android.content.pm.parsing.component.ParsedComponent)>",
                "<android.content.pm.PackageParser: android.util.Pair parsePackageSplitNames(org.xmlpull.v1.XmlPullParser,android.util.AttributeSet)>",
                "<android.content.pm.parsing.ParsingPackageImpl: android.content.pm.parsing.ParsingPackageImpl addPreferredActivityFilter(java.lang.String,android.content.pm.parsing.component.ParsedIntentInfo)>",
                "<android.content.pm.parsing.component.ParsedActivityUtils: android.content.pm.parsing.result.ParseResult parseActivityOrAlias(android.content.pm.parsing.component.ParsedActivity,android.content.pm.parsing.ParsingPackage,java.lang.String,android.content.res.XmlResourceParser,android.content.res.Resources,android.content.res.TypedArray,boolean,boolean,boolean,android.content.pm.parsing.result.ParseInput,int,int,int)>",
                "<android.content.pm.parsing.component.ParsedActivity: java.lang.String getClassName()>",
                "<android.content.pm.parsing.ParsingPackageUtils: android.content.pm.parsing.result.ParseResult parseFeatureGroup(android.content.pm.parsing.result.ParseInput,android.content.pm.parsing.ParsingPackage,android.content.res.Resources,android.content.res.XmlResourceParser)>"
        };
        String methodSig = sigs[0];
        Body body = Utils.getBodyOfMethod(methodSig);
        SootClass cls = body.getMethod().getDeclaringClass();
        *//*for(SootField sf : cls.getFields()){
            System.out.println(sf.getSignature());
            System.out.println(sf.getSignature().split("<")[1].split(":")[0]);
        }
        Set<Value> null_vars = new HashSet<>();
        for(Unit u : body.getUnits()){
            if(u.toString().contains("virtualinvoke $r2.<com.android.server.pm.ComponentResolv")){
                Value base = Utils.getBaseOfInvokeExpr(Utils.getInvokeOfUnit(u));
                System.out.println(base.getType());
            }
        }*//*
        //System.out.println(null_vars);
        //System.out.println(body);
        //Log.logBody(body, store_base_path_12);
        //System.out.println(body);
        //List<Value> values = new ArrayList<>();

        CompleteBlockGraph cbg = new CompleteBlockGraph(body);
        System.out.println("Generate paths ... ");
        Graph.generatePathsFromBlock(cbg.getBlocks().get(215));
        System.out.println(Graph.path_num);
        System.out.println(Graph.paths.size());
        System.out.println(Graph.path);
        // Find the LCA.
        *//*List<Block> blocks = new ArrayList<>();
        blocks.add(cbg.getBlocks().get(78));
        blocks.add(cbg.getBlocks().get(81));
        blocks.add(cbg.getBlocks().get(84));
        blocks.add(cbg.getBlocks().get(87));
        blocks.add(cbg.getBlocks().get(90));
        blocks.add(cbg.getBlocks().get(93));
        blocks.add(cbg.getBlocks().get(96));
        blocks.add(cbg.getBlocks().get(255));
        blocks.add(cbg.getBlocks().get(257));
        blocks.add(cbg.getBlocks().get(259));*//*
        *//*blocks.add(cbg.getBlocks().get(93));
        blocks.add(cbg.getBlocks().get(96));
        blocks.add(cbg.getBlocks().get(102));
        blocks.add(cbg.getBlocks().get(115));
        blocks.add(cbg.getBlocks().get(129));
        blocks.add(cbg.getBlocks().get(142));
        blocks.add(cbg.getBlocks().get(163));
        blocks.add(cbg.getBlocks().get(184));
        blocks.add(cbg.getBlocks().get(197));
        blocks.add(cbg.getBlocks().get(209));*//*
        *//*System.out.println("Stupid: " + Graph.getLeastCommonAncestorOfBlocks(blocks));
        System.out.println("Smart: " + Graph.getLeastCommonAncestorOfBlocksSmart(blocks));*//*
        //Block block = cbg.getBlocks().get(71);
        //System.out.println(Graph.isTailBlockOfLoop(block));
        *//*Collection<ExceptionalBlockGraph.ExceptionDest> exceptionDests = cbg.getExceptionDests(block);
        System.out.println(exceptionDests.size());
        for(ExceptionalBlockGraph.ExceptionDest e : exceptionDests){
            System.out.println(e.getHandlerNode());
            System.out.println(e.getThrowables());
        }*//*

    }


    private static void test4() {
        List<String> a = new ArrayList<>();
        for(int i = 0; i<10; i++){
            a.add(Integer.toString(i));
        }
        System.out.println("=== " + a);
        List<String> b = new ArrayList<>();
        for(int i = 5; i>0; i--){
            b.add(Integer.toString(i-1));
        }
        System.out.println("=== " + b);
        System.out.println(CollectionUtils.disjunction(a, b));
    }

    public static void test5() throws IOException, InterruptedException {
        String framework_path = code_base_path_12+"frameworks";
        String packages_path = code_base_path_12+"packages";
        Utils.getJavaFiles(packages_path);
        //copyFile(new File("src/analysis.Log.java"), "Log_copy.java");
        //File f = new File("src/analysis.Log.java");
        //System.out.println(f.getParent());
        //createDir("/data/disk_16t_2/leiry/1/2/3");
    }*/
}

