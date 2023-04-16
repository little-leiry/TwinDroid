package graph;

import analysis.Utils;
import comparator.BlockComparator;
import soot.Unit;
import soot.jimple.IdentityStmt;
import soot.toolkits.graph.Block;
import org.apache.commons.collections4.CollectionUtils;

import java.util.*;

import static java.lang.System.exit;

public class Graph {
    public static List<Integer> path = new ArrayList<>();
    //public static Set<List<Integer>> call_paths = new HashSet<>();

    public static List<List<Integer>> paths = new ArrayList<>();

    public static int path_num = 0;
    public static int path_num_max = 1000000;

    public static boolean isExceptionBlock(Block block){
        if(block == null){
            return false;
        }
        for(Unit unit : block){
            if(unit instanceof IdentityStmt){
                if(unit.toString().contains("@caughtexception")){
                    return true;
                }
            }
        }
        return false;
    }
    public static boolean isTailBlockOfLoop(Block block){
        int block_id = block.getIndexInMethod();
        List<Block> succs_blocks = block.getSuccs();
        if(succs_blocks.size() == 1){
            Block succs_block = succs_blocks.get(0);
            if((succs_block.getIndexInMethod() < block_id) && !isExceptionBlock(succs_block)){
                return true;
            }
        } else if(succs_blocks.size() == 2){
            Block succs_block0 = succs_blocks.get(0);
            Block succs_block1 = succs_blocks.get(1);
            if(succs_block0.getIndexInMethod() < block_id && !isExceptionBlock(succs_block0)){
                if(succs_block1.getIndexInMethod() > block_id && isExceptionBlock(succs_block1)){
                    return true;
                }
            }
        }
        return false;
    }

    public static boolean arePreBlocksOfOneBlock(List<Block> blocks, Map<Block, List<Block>> blockToPreBlocks){
        //System.out.println("---: " + Utils.getBlockIds(blocks));
        /*for(Map.Entry<Block, List<Block>> entry : blockToPreBlocks.entrySet()){
            System.out.println("---: " + entry.getKey().getIndexInMethod() + "=>" + Utils.getBlockIds(entry.getValue()));
        }*/
        if(blocks == null || blocks.size() <= 1) return true;

        int flag = 0;
        for(List<Block> pre_blocks : blockToPreBlocks.values()){
            List<Block> intersection = new ArrayList<>(CollectionUtils.intersection(pre_blocks, blocks));
            if(intersection.size() > 0){
                if(intersection.size() != blocks.size()) {
                    return false;
                } else {
                    flag = 1;
                }
            }
        }
        if(flag == 1) {
            return true;
        }
        return false;
    }

    public static void addBlockAndPreBlocks(Map<Block, List<Block>> blockToPreblocks, Block block, List<Block> pre_blocks, int flag_orig){
        if(blockToPreblocks.isEmpty()){
            blockToPreblocks.put(block, pre_blocks);
        }else if(flag_orig == 1) {
            blockToPreblocks.put(block, pre_blocks);
        } else {
            // Judge whether this block is the pre-block of the existing block.
            int flag_existing = 0;
            for(Map.Entry<Block, List<Block>> entry : blockToPreblocks.entrySet()){
                List<Block> existing_pre_blocks = entry.getValue();
                if(existing_pre_blocks.contains(block)){
                    flag_existing = 1;
                    for(Block b : pre_blocks){
                        if(!existing_pre_blocks.contains(b)){
                            existing_pre_blocks.add(b);
                        }
                    }
                }
            }
            if(flag_existing == 0){
                blockToPreblocks.put(block, pre_blocks);
            }
        }
    }

    // If have common blocks, the tail block can be presented by the common blocks.
    // And the pre-blocks containing this tail block also can be presented by the common blocks.
    public static void adjustBlocks(Block tail_block, List<Block> blocks, List<Block> common_blocks, List<Block> orig_blocks,
                                                      Map<Block, List<Block>> blockToPreblocks) {
        blocks.remove(tail_block);
        int flag_present = 0;
        if(!CollectionUtils.intersection(common_blocks, orig_blocks).isEmpty()){
            flag_present = 1;
        }
        for(Map.Entry<Block, List<Block>> entry : blockToPreblocks.entrySet()) {
            List<Block> preBlocks = entry.getValue();
            if(flag_present == 1 && preBlocks.contains(tail_block)) {
                for(Block pb : preBlocks) {
                    if(blocks.contains(pb)) {
                        blocks.remove(pb);
                    }
                }
            }
            // The tail block and the common blocks cannot only present one block.
            if(!CollectionUtils.intersection(common_blocks, preBlocks).isEmpty()) {
                if(!preBlocks.contains(tail_block)) {
                    flag_present = 1;
                }
            }
        }
    }

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
            } else if(isTailBlockOfLoop(block)){ // There is a loop in the path.
                for(Block ss : successor.getSuccs()){
                    if(ss.getIndexInMethod() > block_id){
                        legal_successors.add(ss);
                    }
                }
            }
        }
        if(flag_small == 1 && block.getSuccs().size() > 1){ // All succs-blocks' IDs are smaller than the block's ID, and the number of succs-blocks is more than 1.
            if(block.getSuccs().get(1).getIndexInMethod() != block_id) {
                System.out.println("--- block id: " + block_id);
                for (Block b : block.getSuccs()) {
                    System.out.println(("--- success id: ") + b.getIndexInMethod());
                }
            }
        }
        if(!legal_successors.isEmpty()) {
            for (Block successor : legal_successors) {
                generatePathsFromBlock(successor);
            }
        } else { // Search completely, generate a call path.
            //System.out.println("--- " + call_path);
            List<Integer> call_path_copy = Utils.deepCopy(path);
            paths.add(call_path_copy);
            path_num += 1;
            if(path_num > path_num_max) {
                throw new RuntimeException("Path explosion! Currently generated path num: " + path_num);
            }
        }
        path.remove((Integer) block_id); // Delete current block when it has been searched completely.
        //System.out.println(call_path);
    }
    
    // Get the least common ancestor of blocks (including the block in the blocks).
    // Smart method:
    // 1) Get the biggest block, then get its ancestors;
    // 2) If the ancestors and the blocks have intersection, judge whether the intersection has the LCA;
    // 3) If it has, return the LCA.
    // 4) If the ancestors and the blocks don't have intersection, add ancestors to the blocks.
    // 5) Remove the biggest block, repeat;
    public static int getLeastCommonAncestorOfBlocksSmart(List<Block> blocks) {
        if(blocks == null || blocks.isEmpty()) return -1;

        if(blocks.size() == 1) {
            return blocks.get(0).getIndexInMethod();
        }

        List<Block> blocks_copy = Utils.deepCopy(blocks); // Avoid changing the original blocks.
        List<Block> orig_blocks = Utils.deepCopy(blocks_copy);
        Map<Block, List<Block>> blockToPreblocks = new HashMap<>();
        while (true) {
            // Sort the blocks according to their IDs.
            Collections.sort(blocks_copy, new BlockComparator());
            //System.out.println("=== Blocks: " + Utils.getBlockIds(blocks_copy));
            Block tail_block = blocks_copy.get(blocks_copy.size() - 1);
            int flag_orig = 0;
            if (orig_blocks.contains(tail_block)) {
                orig_blocks.remove(tail_block);
                flag_orig = 1;
            }
            int tail_block_id = tail_block.getIndexInMethod();
            //System.out.println("=== Tail block: " + tail_block_id);
            List<Block> pre_blocks = Utils.deepCopy(tail_block.getPreds());
            if(pre_blocks.contains(tail_block)){
                pre_blocks.remove(tail_block);
            }
            //System.out.println("=== Pre-blocks: " + Utils.getBlockIds(pre_blocks));
            List<Block> common_blocks = new ArrayList<>(CollectionUtils.intersection(blocks_copy, pre_blocks));
            //System.out.println("=== Common blocks: " + Utils.getBlockIds(common_blocks));
            if (!common_blocks.isEmpty()) {
                if(blocks_copy.size() == 2){
                    return blocks_copy.get(0).getIndexInMethod();
                }else if (orig_blocks.size() == 1) {
                    // blocks = tail block + original block + rest blocks.
                    // tail block is (1), original block is (2),
                    // if rest blocks are (1), original block is the lca.
                    Block ob = orig_blocks.get(0);
                    if (common_blocks.contains(ob)) {
                        List<Block> un_obs = new ArrayList<>(blocks_copy);
                        un_obs.remove(ob);
                        if (arePreBlocksOfOneBlock(un_obs, blockToPreblocks)) {
                            return ob.getIndexInMethod();
                        }
                    }
                } else if (orig_blocks.size() == 0){
                    // blocks = tail block + common blocks + rest blocks.
                    // if tail block is (1), common blocks are (2), and rest blocks are (1) or (2),
                    // common blocks have the lca.
                    if(arePreBlocksOfOneBlock(common_blocks, blockToPreblocks)){ // common blocks are (2)
                        List<Block> tailAndCommonBlocks = new ArrayList<>(common_blocks);
                        tailAndCommonBlocks.add(tail_block);
                        if(!arePreBlocksOfOneBlock(tailAndCommonBlocks, blockToPreblocks)) { // tail block is (1)
                            List<Block> un_cbs = new ArrayList<>(CollectionUtils.disjunction(blocks_copy, common_blocks));
                            //System.out.println("=== Un-common blocks: " + Utils.getBlockIds(un_cbs));
                            List<Block> un_tbs = new ArrayList<>(blocks_copy);
                            un_tbs.remove(tail_block);
                            //System.out.println("=== Un-tail blocks: " + Utils.getBlockIds(un_tbs));
                            if(arePreBlocksOfOneBlock(un_cbs, blockToPreblocks) || arePreBlocksOfOneBlock(un_tbs, blockToPreblocks)){ // rest blocks are (1) or (2)
                                Collections.sort(common_blocks, new BlockComparator());
                                return common_blocks.get(common_blocks.size() - 1).getIndexInMethod();
                            }
                        }
                    }
                }
            } else { // Add pre-blocks to the blocks.
                int flag_big = 1;
                for (Block b : pre_blocks) {
                    if (b.getIndexInMethod() < tail_block_id) { // Ensure the pre-block's is smaller than current block's id.
                        flag_big = 0;
                        if (!blocks_copy.contains(b)) {
                            blocks_copy.add(b);
                        }
                    }
                }
                if (flag_big == 1 && tail_block_id != 0) { // All pre-blocks' IDs are bigger that the block's ID, and this block is not the 0-block.
                    String msg = "Special block." + "\n---block id: " + tail_block_id;
                    Utils.terminate(msg);
                }
            }
            adjustBlocks(tail_block, blocks_copy, common_blocks, orig_blocks, blockToPreblocks);
            //System.out.println("=== Adjusted blocks: " + Utils.getBlockIds(blocks));
            addBlockAndPreBlocks(blockToPreblocks, tail_block, pre_blocks, flag_orig);
            /*for(Map.Entry<Block, List<Block>> entry : blockToPreblocks.entrySet()){
                System.out.println("### " + entry.getKey().getIndexInMethod() + "=>" + Utils.getBlockIds(entry.getValue()));
            }
            Utils.pause();*/
        }
    }



    // Stupid method:
    // 1) For each block, generate all the ancestors of it (BFS);
    // 2) For all ancestor lists, find the intersection of them;
    // 3) Return the biggest Block of the intersection.
    public static void getAncestorsOfBlock(Block block, List<Integer> ancestors){
        Queue<Block> pre_blocks = new LinkedList<>();
        pre_blocks.offer(block);
        while(!pre_blocks.isEmpty()){
            Block head_block = pre_blocks.poll();
            int head_block_id =head_block.getIndexInMethod();
            if(!ancestors.contains(head_block_id)) {
                ancestors.add(head_block_id);
            }
            int flag_big = 1;
            for(Block b : head_block.getPreds()){
                if(b.getIndexInMethod() < head_block_id){
                    flag_big = 0;
                    if(!pre_blocks.contains(b)) {
                        pre_blocks.offer(b);
                    }
                }
            }
            if(flag_big == 1 && head_block_id!=0){ // All pre-blocks' IDs are bigger that the block's ID, and this block is not the 0-block.
                Utils.printPartingLine("!");
                System.out.println("Special block.");
                System.out.println("---block id: " + head_block_id);
                Utils.printPartingLine("!");
                exit(0);
            }
            //System.out.println("Ancestors: " + ancestors);
            //analysis.Utils.pause();
        }
    }

    public static Integer getLeastCommonAncestorOfBlocks(List<Block> blocks){
        if(blocks == null || blocks.isEmpty()) return -1;

        if(blocks.size() == 1) {
            return blocks.get(0).getIndexInMethod();
        }

        List<Block> blocks_copy = Utils.deepCopy(blocks); // Avoid changing the original blocks.
        List<List<Integer>> pre_block_info = new ArrayList<>();
        for(Block block: blocks_copy){
            List<Integer> ancestors = new ArrayList<>();
            getAncestorsOfBlock(block, ancestors);
            //System.out.println("**** block_id " + block.getIndexInMethod() + ": " + ancestors);
            pre_block_info.add(ancestors);
            //System.out.println("#### " + pre_block_info);
        }
        List<Integer> common_blocks = pre_block_info.get(0);
        for (int i = 1; i < pre_block_info.size(); i++) {
            common_blocks = new ArrayList<>(CollectionUtils.intersection(common_blocks, pre_block_info.get(i)));
        }
        Collections.sort(common_blocks);
        return common_blocks.get(common_blocks.size() -1 );
    }
}
