package edu.udel.cis.vsl.sarl.IF;

import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.number.IF.Numbers;

public class SARLConstants {

	/**
	 * Used in a heuristic to determine when to use probabilistic methods to
	 * determine polynomial zero-ness. If the product of the number of variables
	 * and the total degree is greater than or equal to this number, the
	 * polynomial is considered too big to be expanded, and probabilistic
	 * techniques will be used instead (unless the probabilistic bound is 0).
	 */
	public final static IntegerNumber polyProbThreshold = Numbers.REAL_FACTORY
			.integer(100);
	
	
	

}
