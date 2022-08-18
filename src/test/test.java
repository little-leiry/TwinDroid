package test;

import java.util.HashMap;
import java.util.Map;

public class test {
    public static void testSample() {
        String a = "test1";
        showString(a);
        String b = "test2";
        showString(b);
        Map<String, String > c = new HashMap<String, String>();
        c.put("aa", "1");
    }

    private static void showString(String s) {
        System.out.println("--- " + s);
    }
}
