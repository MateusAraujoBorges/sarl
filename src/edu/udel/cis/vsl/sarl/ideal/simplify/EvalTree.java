package edu.udel.cis.vsl.sarl.ideal.simplify;

/**
 * A DAG (directed acyclic graph) representing a simple polynomial expression.
 * Nodes are either +, -, *, constant, or variable.
 * 
 * @author siegel
 *
 */
public class EvalTree {

	EvalNode root;

	/**
	 * Array of the nodes of this DAG by ID number.
	 */
	EvalNode[] nodes;

	public EvalTree(EvalNode root) {
		this.root = root;
	}

}
