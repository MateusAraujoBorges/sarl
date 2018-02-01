package edu.udel.cis.vsl.sarl.ideal.simplify;

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
	public EvalNodeKind kind() {
		return EvalNodeKind.CONST;
	}

	@Override
	public int isoCode() {
		if (isoCode == 0)
			isoCode = value.hashCode() ^ (parents.size() * 179424797)
					^ EvalNodeKind.CONST.hashCode();
		return isoCode;
	}
}