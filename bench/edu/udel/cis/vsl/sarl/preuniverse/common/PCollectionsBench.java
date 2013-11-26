package edu.udel.cis.vsl.sarl.preuniverse.common;
import org.pcollections.PVector;
import org.pcollections.TreePVector;

public class PCollectionsBench {

    /**
     * @author Mohammad Alsulmi (malsulmi)
     */
    public static void main(String[] args) {
        PVector<String> ve;
        int maxSize = (int) Math.pow(2, 28);
        for (int i = 1; i <= maxSize; i = i * 2) {
            ve = TreePVector.empty();
            int size = i;
            long stime = System.nanoTime();

            
            for (int j = 0; j < size; j++) {
                //String xx = Integer.toString(j);
                ve.plus(null);
            }
            long etime = System.nanoTime();

            double fTime = (etime - stime) / 1000000000.0;
            System.out.println(size+ "  "+fTime + " Sec");
        }
    }

}
