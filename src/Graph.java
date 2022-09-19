import soot.toolkits.graph.Block;

import java.util.*;

public class Graph {
    public static List<Integer> path = new ArrayList<>();
    //public static Set<List<Integer>> call_paths = new HashSet<>();

    public static List<List<Integer>> paths = new ArrayList<>();

    // DFS
    // Get all call paths among blocks in a method.
    public static void generatePathsFromBlock(Block block){
        if(block == null){
            System.out.println("Null start block.");
            return;
        }
        int block_id = block.getIndexInMethod();
        path.add((Integer) block_id);
        List<Block> legal_successors = new ArrayList<>();
        // Ignore the loop in a call path.
        for(Block successor : block.getSuccs()){
            if(successor.getIndexInMethod() > block_id){
                legal_successors.add(successor);
            }
        }
        if(! legal_successors.isEmpty()) {
            for (Block successor : legal_successors) {
                generatePathsFromBlock(successor);
            }
        } else { // Search completely, generate a call path.
            //System.out.println("--- " + call_path);
            List<Integer> call_path_copy = Utils.deepCopy(path);
            paths.add(call_path_copy);
            System.out.println(paths.size());
        }

        path.remove((Integer) block_id); // Delete current block when it has been searched completely.
        //System.out.println(call_path);
    }
}
