import soot.Body;
import soot.SootMethod;
import soot.Value;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.CompleteBlockGraph;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

public class Graph {
    public static List<Block> call_path = new ArrayList<>();
    public static List<List<Block>> call_paths = new ArrayList<>();

    // DFS
    // Get all call paths among blocks in a method.
    public static void generateCallPathsFromBlock(Block block){
        call_path.add(block);
        if(! block.getSuccs().isEmpty()) {
            for (Block b : block.getSuccs()) {
                generateCallPathsFromBlock(b);
            }
        } else {
            List<Block> call_path_copy = Utils.deepCopy(call_path);
            call_paths.add(call_path_copy);
        }
        call_path.remove(block);
    }
}
