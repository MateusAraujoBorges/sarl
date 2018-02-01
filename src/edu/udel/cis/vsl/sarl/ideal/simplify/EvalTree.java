package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.Stack;

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
	// EvalNode[] nodes;

	public EvalTree(EvalNode root) {
		this.root = root;
		// TODO: set IDs

		int idCounter = 0;
		Stack<EvalNode> dfsStack = new Stack<>();

		// traverse the tree to set IDs:
		dfsStack.push(root);
		while (!dfsStack.isEmpty()) {
			EvalNode node = dfsStack.pop();

			if (node.nodeId == -1) {
				node.nodeId = idCounter++;

				int numChildren = node.numChildren();
				EvalNode children[] = node.getChildren();

				for (int i = 0; i < numChildren; i++)
					if (children[i].nodeId == -1)
						dfsStack.push(children[i]);
			}
		}
	}

	@Override
	public int hashCode() {
		return root.isoCode;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof EvalTree) {
			EvalTree that = (EvalTree) obj;

			IsomorphismChecker checker = new IsomorphismChecker(this, that);

			return checker.areIsomophic();
		}
		return false;
	}
}
