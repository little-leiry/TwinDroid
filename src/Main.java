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
    // Android 12's source code.
    public static final String code_base_path_12 = "/data/disk_16t_2/leiry/android12_source/";
    public static final String dexCode_path_12 = code_base_path_12 + "DEX-12-framework/";
    // Android 11's source code.
    public static final String code_base_path_11 = "/data/disk_16t_2/leiry/android11_source/";
    public static final String dexCode_path_11 = code_base_path_11 + "DEX-11-framework/";

    public static void main(String[] args) {
        long start, end;
        Utils.printPartingLine("+");
        int analyzed_android_version = 12;
        String android_code_path = initializeAnalysisSettings(analyzed_android_version);
        if(android_code_path == null){
            String msg = "Unsupported android version: " + analyzed_android_version;
            Utils.terminate(msg);
        }
        System.out.println("Currently analyzed android version: " + analyzed_android_version + "\nAndroid DEX code path: " +
                android_code_path + "\nAnalysis data storing path: " + Analysis.store_base_path);
        //Utils.pause();
        System.out.println("Loading (initializing) classes ...");
        start = System.currentTimeMillis();
        loadClasses_dex(android_code_path);
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
    }

    public static String initializeAnalysisSettings(int android_version){
        String android_code_path = null;
        switch (android_version){
            case 11:
                Analysis.store_base_path = "android11/";
                android_code_path = dexCode_path_11;
                break;
            case 12:
                Analysis.store_base_path = "android12/";
                android_code_path = dexCode_path_12;
                break;
        }
        return android_code_path;
    }

    public static void loadClasses_dex(String code_path) {
        soot.G.reset();
        // android.jar
        Options.v().set_force_android_jar("lib/android31.jar");
        Options.v().set_src_prec(Options.src_prec_apk);
        Options.v().set_process_multiple_dex(true);
        Options.v().set_process_dir(Collections.singletonList(code_path));
        Options.v().set_whole_program(true);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_output_format(Options.output_format_none);
        Options.v().ignore_resolution_errors();
        Scene.v().loadNecessaryClasses();
    }
}

