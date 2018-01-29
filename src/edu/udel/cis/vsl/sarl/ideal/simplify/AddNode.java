package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.Arrays;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;

/**
 * A node representing the sum of its children.
 * 
 * @author siegel
 */
class AddNode extends EvalNode {
	private EvalNode[] children;

	private int depth = -1;

	private long numDescendants = -1;

	AddNode(EvalNode[] children) {
		assert children.length >= 1;
		this.children = children;
		for (EvalNode child : children)
			child.addParent(this);
	}

	@Override
	Rat evaluate() {
		if (value == null) {
			value = new Rat(children[0].evaluate());
			for (int i = 1; i < children.length; i++)
				value.add(children[i].evaluate());
		}
		return clearOnCount();
	}

	@Override
	int depth() {
		if (depth < 0) {
			int maxChildDepth = 0;

			for (EvalNode child : children) {
				int childDepth = child.depth();

				maxChildDepth = childDepth > maxChildDepth ? childDepth
						: maxChildDepth;
			}
			depth = 1 + maxChildDepth;
		}
		return depth;
	}

	@Override
	long numDescendants() {
		if (numDescendants < 0) {
			numDescendants = children.length;

			for (int i = 0; i < children.length; i++)
				numDescendants += children[i].numDescendants();
		}
		return numDescendants;
	}

	@Override
	public int hashCode() {
		if (hashCode == -1) {
			int[] childrenHashCodes = new int[children.length];

			for (int i = 0; i < children.length; i++)
				childrenHashCodes[i] = children[i].hashCode();
			hashCode = 1777773
					* (Arrays.hashCode(childrenHashCodes)
							^ SymbolicOperator.ADD.hashCode())
					+ parents.size();
		}
		return hashCode;
	}

	@Override
	public SymbolicOperator operator() {
		return SymbolicOperator.ADD;
	}

	@Override
	public int numChildren() {
		return children.length;
	}

	@Override
	public EvalNode[] getChildren() {
		return children;
	}
}