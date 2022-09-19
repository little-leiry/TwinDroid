import java.util.Comparator;
import java.util.List;

public class ListComparator implements Comparator<List> {
    public int compare(List l1, List l2){
        if(l1.size() > l2.size()){
            return -1;
        } else if(l1.size() == l2.size()){
            return 0;
        } else {
            return 1;
        }
    }
}
