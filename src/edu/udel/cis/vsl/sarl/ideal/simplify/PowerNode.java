package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.math.BigInteger;

/**
 * A node representing a power operation: a base raised to some fixed power.
 * This node has one child, the base. The exponent is a constant number, so a
 * field in this node.
 * 
 * @author siegel
 */
class PowerNode extends EvalNode {
	private EvalNode base;
	protected BigInteger exponent;

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
	public EvalNodeKind kind() {
		return EvalNodeKind.POW;
	}

	@Override
	public int isoCode() {
		if (isoCode == 0) {
			isoCode = base.isoCode;
			isoCode = isoCode ^ EvalNodeKind.POW.hashCode()
					^ (depth() * 179426339) ^ parents.size()
					^ exponent.hashCode();
		}
		return isoCode;
	}
}