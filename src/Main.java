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
}

