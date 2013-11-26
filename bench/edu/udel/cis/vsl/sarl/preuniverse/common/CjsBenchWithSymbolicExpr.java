package edu.udel.cis.vsl.sarl.preuniverse.common;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.IF.ExpressionFactory;
import edu.udel.cis.vsl.sarl.preuniverse.PreUniverses;
import edu.udel.cis.vsl.sarl.preuniverse.IF.FactorySystem;

public class CjsBenchWithSymbolicExpr {
	 /**
     * @author Mohammad Alsulmi (malsulmi)
     */
	public final static SymbolicUniverse universe = SARL.newIdealUniverse();
	public final static FactorySystem system = PreUniverses
			.newIdealFactorySystem();

	public final static SymbolicType integerType = universe.integerType();

	public final static ExpressionFactory expressionFactory = system
			.expressionFactory();


    public static void main(String[] args) {
      //  PersistentVector<SymbolicExpression> vector;
        SymbolicExpression element = universe.integer(1000);

        int maxSize = (int) Math.pow(2, 28);
        for (int i = 1; i <= maxSize; i = i * 2) {
        //	vector = Persistents.vector();
            int size = i;
            long stime = System.nanoTime();

            
            for (int j = 0; j < size; j++) {
          //      vector.plus(element);
            }
            long etime = System.nanoTime();

            double fTime = (etime - stime) / 1000000000.0;
            System.out.println(size+ "  "+fTime + " Sec");
        }
    }


}