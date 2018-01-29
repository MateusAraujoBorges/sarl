package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.Arrays;
import java.util.Comparator;
import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;

// need to create mapping between trees.
// create HashMap ... using object codes? arrays?
// create array of all nodes and put an index in each node.
// value can go outside or not

// invariant: if u->v is in map, then u and v have same operator,
// if they are constants they have the same value. They have the
// same hashCode. They have same number of incoming and outgoing edges.
// There exists of parent u0 of u and a parent v0 of v such that
// u0->v0. (Unless u and v are root nodes). map is injective.

// if the map is a bijection, is it an isomorphism?

// check u and v match. if not, return false
// let S = children of u, T = children of v.
// let S' be the matched children of u.
// Check map(s') in T for all s' in S'.
// Let T' be the matched children of v.
// Check match^-1(t') in S for all t' in T'.
// come up with matching for remainder --- if not possible, return false.
public class IsomorphicTreeComparator {

	EvalNode tree1;

	EvalNode tree2;

	Map<EvalNode, EvalNode> map1;

	Map<EvalNode, EvalNode> map2;

	public IsomorphicTreeComparator(EvalNode tree1, EvalNode tree2) {
		this.tree1 = tree1;
		this.tree2 = tree2;
	}

	private static boolean match(EvalNode u, EvalNode v) {
		SymbolicOperator op = u.operator();

		if (op != v.operator())
			return false;
		if (op == SymbolicOperator.CONCRETE) {
			Rat val1 = ((ConstantNode) u).value;

			if (!val1.equals(((ConstantNode) v).value))
				return false;
		}
		if (u.parents.size() != v.parents.size())
			return false;
		if (u.numChildren() != v.numChildren())
			return false;
		if (u.hashCode() != v.hashCode())
			return false;
		return true;
	}

	private static EvalNodeHashComparator comparator = new EvalNodeHashComparator();

	public static boolean isIsomophicTrees(EvalNode tree0, EvalNode tree1) {
		if (tree0.operator() != tree1.operator())
			return false;
		if (tree0.numDescendants() != tree1.numDescendants())
			return false;
		if (tree0.numChildren() != tree1.numChildren())
			return false;
		if (tree0.numChildren() == 0)
			return true;

		int numChildren = tree0.numChildren();
		EvalNode children0Copy[] = Arrays.copyOf(tree0.getChildren(),
				numChildren);
		EvalNode children1Copy[] = Arrays.copyOf(tree1.getChildren(),
				numChildren);

		Arrays.sort(children0Copy, comparator);
		Arrays.sort(children1Copy, comparator);

		boolean currLevelEq = Arrays.equals(children0Copy, children1Copy);

		if (!currLevelEq)
			return false;
		else
			for (int i = 0; i < numChildren; i++)
				if (!isIsomophicTrees(children0Copy[i], children0Copy[i]))
					return false;
		return true;
	}

	private static class EvalNodeHashComparator
			implements Comparator<EvalNode> {

		@Override
		public int compare(EvalNode o1, EvalNode o2) {
			return Integer.compare(o1.hashCode(), o2.hashCode());
		}

	}
}
