import soot.toolkits.graph.Block;

import java.util.*;

import static java.lang.System.exit;

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
        Set<Block> legal_successors = new HashSet<>();
        // Make sure that the block ids in the pass are incremental.
        int flag_small = 1;
        for(Block successor : block.getSuccs()){
            if(successor.getIndexInMethod() > block_id){
                legal_successors.add(successor);
                flag_small = 0;
            } else if(block.getSuccs().size()==1){ // There is a loop in the path.
                for(Block ss : successor.getSuccs()){
                    if(ss.getIndexInMethod() > block_id){
                        legal_successors.add(ss);
                    }
                }
            }
        }
        if(flag_small == 1 && block.getSuccs().size() > 1){
            System.out.println("--- block id: " + block_id);
            for(Block b : block.getSuccs()){
                System.out.println(("--- success id: ") + b.getIndexInMethod());
            }
            exit(0);
        }
        if(!legal_successors.isEmpty()) {
            for (Block successor : legal_successors) {
                generatePathsFromBlock(successor);
            }
        } else { // Search completely, generate a call path.
            //System.out.println("--- " + call_path);
            List<Integer> call_path_copy = Utils.deepCopy(path);
            paths.add(call_path_copy);
        }

        path.remove((Integer) block_id); // Delete current block when it has been searched completely.
        //System.out.println(call_path);
    }
}
