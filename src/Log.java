import soot.Body;
import soot.SootMethod;
import soot.toolkits.graph.CompleteBlockGraph;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

public class Log {
    public static PrintWriter analysis_pw;

    static {

    }

    public static void logData(String file_path, String data){
        try {
            File file = new File(file_path);
            if(!file.exists()){
                file.createNewFile();
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

    public static void logBody(Body body){
        SootMethod method = body.getMethod();
        String subSig = method.getSubSignature();
        String file_path = "methods/" + subSig.split(" ")[1] + ".txt";
        try {
            File file = new File(file_path);
            if(file.exists()) return;
            PrintWriter out = new PrintWriter(file_path);
            out.println(body);
            out.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public static void logCBG(CompleteBlockGraph cbg){
        SootMethod method = cbg.getBody().getMethod();
        String subSig = method.getSubSignature();
        String file_path = "methods/block_" + subSig.split(" ")[1] + ".txt";
        try {
            File file = new File(file_path);
            if(file.exists()) return;
            PrintWriter out = new PrintWriter(file_path);
            out.println(cbg);
            out.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }


    public static void deleteData(String file_path){
        try{
            FileWriter fw = new FileWriter(file_path);
            fw.write("");
            fw.flush();
            fw.close();
        } catch (IOException e){
            e.printStackTrace();
        }
    }

    public static List<String> readData(String file_path){
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
}
