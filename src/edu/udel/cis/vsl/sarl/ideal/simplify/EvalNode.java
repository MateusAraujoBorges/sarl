package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.math.BigInteger;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;

/**
 * A node in the "tree" used to represent the polynomial. Leaf nodes are either
 * constants or variables. Non-leaf nodes represent either addition,
 * multiplication, or exponentiation. It's not really a tree, because we allow
 * sharing. So it's a DAG.
 * 
 * @author siegel
 *
 */
abstract class EvalNode {

	/**
	 * The cached result of evaluating this node.
	 */
	protected Rat value = null;

	/**
	 * The parent nodes of this node, i.e., all nodes in the tree that have this
	 * node as a child. (So, it isn't really a tree.)
	 */
	protected List<EvalNode> parents = new LinkedList<>();

	/**
	 * The number of times method {@link #evaluate()} has been called.
	 */
	protected int evalCount = 0;

	protected int hashCode = -1;

	/**
	 * Add the given node to the parent list of this node.
	 * 
	 * @param parent
	 *            the node to make a parent
	 */
	void addParent(EvalNode parent) {
		parents.add(parent);
	}

	/**
	 * Returns the set of parents.
	 * 
	 * @return the parents of this node
	 */
	Collection<EvalNode> getParents() {
		return parents;
	}

	void nullifyValue() {
		if (value != null) {
			value = null;
			for (EvalNode parent : parents)
				parent.nullifyValue();
		}
	}

	/**
	 * Computes the value of this node, a concrete rational number. Might return
	 * a cached value.
	 * 
	 * @return the result of evaluating this node
	 */
	abstract Rat evaluate();

	/**
	 * Increments the evaluation count; if that count then equals the number of
	 * parents of this node, sets the {@link #value} to {@code null} so the
	 * {@link BigInteger}s can be swept up by the garbage collector.
	 * 
	 * @return the {@link #value} in the pre-state (before possibly setting it
	 *         to {@code null})
	 */
	Rat clearOnCount() {
		evalCount++;
		if (evalCount == parents.size()) {
			Rat result = value;

			value = null;
			return result;
		} else {
			return value;
		}
	}

	int depth() {
		return 1;
	}

	long numDescendants() {
		return 1;
	}

	public int numChildren() {
		return 0;
	}
	
	// numDistinctChildren?

	public EvalNode[] getChildren() {
		return null;
	}

	public abstract SymbolicOperator operator();

	// @Override public boolean equals(Object object) {
	//
	// }

}