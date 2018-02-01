package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.sarl.ideal.simplify.EvalNode.EvalNodeKind;

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
public class IsomorphismChecker {

	EvalTree tree1;

	EvalTree tree2;

	Map<EvalNode, EvalNode> map1;

	Map<EvalNode, EvalNode> map2;

	public IsomorphismChecker(EvalTree tree1, EvalTree tree2) {
		this.tree1 = tree1;
		this.tree2 = tree2;
		this.map1 = new HashMap<>();
		this.map2 = new HashMap<>();
	}

	private static boolean match(EvalNode u, EvalNode v) {
		if (u.isoCode() != v.isoCode())
			return false;

		EvalNodeKind kind = u.kind();

		if (kind != v.kind())
			return false;
		if (kind == EvalNodeKind.CONST) {
			Rat val1 = ((ConstantNode) u).value;

			if (!val1.equals(((ConstantNode) v).value))
				return false;
		} else if (kind == EvalNodeKind.POW) {
			BigInteger exp = ((PowerNode) u).exponent;

			if (!exp.equals(((PowerNode) v).exponent))
				return false;
		}
		if (u.parents.size() != v.parents.size())
			return false;
		if (u.numChildren() != v.numChildren())
			return false;
		return true;
	}

	public boolean areIsomophic() {
		if (!match(tree1.root, tree2.root))
			return false;
		return iso(tree1.root, tree2.root);
	}

	/**
	 * pre-condition: match(n0, n1)
	 * 
	 * @param n0
	 * @param n1
	 * @return
	 */
	private boolean iso(EvalNode n0, EvalNode n1) {
		EvalNode[] children0 = n0.getChildren();
		EvalNode[] children1 = n1.getChildren();
		Set<EvalNode> set1 = new HashSet<>();
		int n = children0.length;

		for (int i = 0; i < n; i++)
			set1.add(children1[i]);
		for (int i = 0; i < n; i++) {
			EvalNode u = children0[i];
			EvalNode u_match = map1.get(u);

			if (u_match != null) {
				if (!set1.remove(u_match))
					return false;
			} else {
				boolean matched = false;

				for (int j = 0; j < n; j++) {
					EvalNode v = children1[j];

					if (!map2.containsKey(v) && match(u, v)) {
						map1.put(u, v);
						map2.put(v, u);
						if (!iso(u, v))
							return false;
						matched = true;
						set1.remove(v);
						break;
					}
				}
				if (!matched)
					return false;
			}
		}
		assert set1.isEmpty();
		return true;
	}

	/**
	 * <code>
	 * map1 : N0 -> N1
	 * map2 : N1 -> N0
	 * 
	 * iso(N0, N1) {
	 *   // some simple checks
	 *   // for each children that haven't had corresponded nodes. (f(n0) in children(N1), vice versa)
	 *   // pick candidate pairs based on isoCode();
	 *   // then do recursive checking.
	 * }
	 * </code>
	 */
}
