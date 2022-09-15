import java.util.ArrayList;
import java.util.List;

public class SkipInfo {
    // skip_names: important names. These names are unlikely an element name.
    public static List<String> skip_names = new ArrayList<>();

    // skip_methods, skip_classes: important methods / classes. If a statement contains this kind of methods / classes, just skipping this statement.
    public static List<String> skip_methods = new ArrayList<>();
    public static List<String> skip_classes = new ArrayList<>();

    // no_analyzed_methods, no_analyzed_classes: these methods' / classes' functions have been known, no need to be analyzed.
    public static List<String> no_analyzed_classes = new ArrayList<>();
    public static List<String> no_analyzed_methods = new ArrayList<>();
}
