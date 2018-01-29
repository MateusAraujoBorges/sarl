package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.math.BigInteger;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;

/**
 * A node representing a power operation: a base raised to some fixed power.
 * This node has one child, the base. The exponent is a constant number, so
 * a field in this node.
 * 
 * @author siegel
 */
class PowerNode extends EvalNode {
	private EvalNode base;
	private BigInteger exponent;

	PowerNode(EvalNode base, BigInteger exponent) {
		this.base = base;
		this.exponent = exponent;
		base.addParent(this);
	}

	Rat evaluate() {
		if (value == null) {
			value = new Rat(base.evaluate());
			value.power(exponent);
		}
		return clearOnCount();
	}

	@Override
	public int hashCode() {
		if (hashCode == -1) {
			hashCode = base.hashCode() ^ exponent.hashCode()
					^ SymbolicOperator.POWER.hashCode() + parents.size();
		}
		return hashCode;
	}

	@Override
	public SymbolicOperator operator() {
		return SymbolicOperator.POWER;
	}
}