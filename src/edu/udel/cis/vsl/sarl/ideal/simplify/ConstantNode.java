package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.math.BigInteger;
import java.util.Arrays;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;

/**
 * A constant node. This is a leaf node in the tree.
 * 
 * @author siegel
 */
class ConstantNode extends EvalNode {
	ConstantNode(Rat value) {
		this.value = value;
	}

	Rat evaluate() {
		return value;
	}

	@Override
	public int hashCode() {
		if (hashCode == -1) {
			BigInteger bigIntArray[] = { value.a, value.b };
			hashCode = 345
					* (Arrays.hashCode(bigIntArray)
							^ SymbolicOperator.CONCRETE.hashCode())
					+ parents.size();
		}
		return hashCode;
	}

	@Override
	public SymbolicOperator operator() {
		return SymbolicOperator.CONCRETE;
	}
}