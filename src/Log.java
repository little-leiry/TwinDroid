import java.io.*;
import java.util.ArrayList;
import java.util.List;

public class Log {
    public static void logData(String file_path, String data){
        try {
            File file = new File(file_path);
            if(!file.exists()){
                file.createNewFile();
            }
            FileWriter fw = new FileWriter(file.getName(), true);
            BufferedWriter bw = new BufferedWriter(fw);
            bw.write(data);
            bw.newLine();
            bw.close();
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
}
