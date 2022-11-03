package comparator;

import soot.ValueBox;
import soot.toolkits.graph.Block;

import java.util.Comparator;

public class BlockComparator implements Comparator<Block> {
    public int compare(Block b1, Block b2){
        int i1 = b1.getIndexInMethod();
        int i2 = b2.getIndexInMethod();
        if(i1 > i2){
            return 1;
        } else if(i1 == i2) {
            return 0;
        } else {
            return -1;
        }
    }
}
