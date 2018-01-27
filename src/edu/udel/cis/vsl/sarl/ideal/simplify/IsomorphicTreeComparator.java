package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.Arrays;
import java.util.Comparator;

import edu.udel.cis.vsl.sarl.ideal.simplify.FastEvaluator3.EvalNode;

public class IsomorphicTreeComparator {

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
