package analysis;

import soot.Body;
import soot.SootMethod;
import soot.toolkits.graph.CompleteBlockGraph;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

public class Log {
    public static PrintWriter analysis_pw;

    public static void logData(String file_path, String data){
        if(file_path == null || data == null) return;
        try {
            File file = new File(file_path);
            if(!file.getParentFile().exists()){
                file.getParentFile().mkdirs();
            }
            FileWriter fw = new FileWriter(file, true);
            BufferedWriter bw = new BufferedWriter(fw);
            bw.write(data);
            bw.newLine();
            bw.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public static void logBody(Body body, String store_base_path){
        if(body == null) return;
        SootMethod method = body.getMethod();
        int sig = method.getSignature().hashCode();
        String file_path = store_base_path + "methods/" + method.getName() + sig + ".txt";
        try {
            File file = new File(file_path);
            if(!file.getParentFile().exists()){
                file.getParentFile().mkdirs();
            }
            if(file.exists()) return; // Have been logged.
            PrintWriter out = new PrintWriter(file_path);
            out.println(body);
            out.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public static void logCBG(CompleteBlockGraph cbg, String store_base_path){
        if(cbg == null) return;
        SootMethod method = cbg.getBody().getMethod();
        int sig = method.getSignature().hashCode();
        String file_path = store_base_path + "methods/block_" + method.getName() + sig + ".txt";
        try {
            File file = new File(file_path);
            if(!file.getParentFile().exists()){
                file.getParentFile().mkdirs();
            }
            if(file.exists()) return;
            PrintWriter out = new PrintWriter(file_path);
            out.println(cbg);
            out.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }


    public static void deleteData(String file_path){
        if(file_path == null) return;
        try{
            File file = new File(file_path);
            if(!file.exists()) return;
            FileWriter fw = new FileWriter(file);
            fw.write("");
            fw.flush();
            fw.close();
        } catch (IOException e){
            e.printStackTrace();
        }
    }

    public static void delete(String file_path){
        if(file_path == null) return;
        File file = new File(file_path);
        if(!file.exists()) return;
        if(file.isFile()){
            file.delete();
        } else if (file.isDirectory()){
            File[] files = file.listFiles();
            for(File f : files){
                delete(f.getAbsolutePath());
            }
        }
    }

    public static List<String> readData(String file_path){
        if(file_path == null) return null;
        try {
            File file = new File(file_path);
            FileReader fr = new FileReader(file);
            BufferedReader br = new BufferedReader(fr);
            String line;
            List<String> data = new ArrayList<>();
            while((line = br.readLine()) != null){
                data.add(line);
            }
            return data;
        }catch (IOException e){
            e.printStackTrace();
        }
        return null;
    }

    public static void generatePrinterWriter(String file_name){
        try {
            FileWriter fw = new FileWriter(file_name, true);
            analysis_pw = new PrintWriter(fw);
        } catch (FileNotFoundException e) {
            throw new RuntimeException(e);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public static int getFileId(File file){
       long file_size = file.length();
        return (int) (file_size / 1048576 / 30);
    }

    public static String getFileId(String path){
        File file = new File(path);
        long file_size = file.length();
        return (int) (file_size / 1048576 / 30) + "";
    }
}
