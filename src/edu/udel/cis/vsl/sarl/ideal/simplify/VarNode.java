package edu.udel.cis.vsl.sarl.ideal.simplify;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;

/**
 * A variable node. This is a leaf node in the tree.
 * 
 * @author siegel
 */
class VarNode extends EvalNode {
	/**
	 * Sets the value of this variable. This automatically nullifies all
	 * ancestor nodes of this node, since their values depend on this value.
	 * 
	 * @param value
	 *            the value to associate to this node
	 */
	public void setValue(Rat value) {
		this.value = value;
		for (EvalNode parent : getParents()) {
			parent.nullifyValue();
		}
	}

	@Override
	Rat evaluate() {
		return value;
	}

	@Override
	public int hashCode() {
		return 345 * SymbolicOperator.SYMBOLIC_CONSTANT.hashCode()
				+ parents.size();
	}

	// TODO: it's not necessarily a symbolic constant...
	@Override
	public SymbolicOperator operator() {
		return SymbolicOperator.SYMBOLIC_CONSTANT;
	}
}