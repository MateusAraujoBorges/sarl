package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.Arrays;

import edu.udel.cis.vsl.sarl.ideal.simplify.FastEvaluator3.EvalNode;

public class IsomorphicTreeComparator {

	public static boolean isIsomophicTrees(EvalNode tree0, EvalNode tree1) {
		if (tree0.operator() != tree1.operator())
			return false;
		if (tree0.numDescendants() != tree1.numDescendants())
			return false;
		if (tree0.numChildren() != tree1.numChildren())
			return false;
		if (tree0.numChildren() == 0)
			return true;

		int hashCodes0[] = new int[tree0.numChildren()];
		int hashCodes1[] = new int[hashCodes0.length];
		EvalNode children0[] = tree0.getChildren();
		EvalNode children1[] = tree1.getChildren();

		for (int i = 0; i < hashCodes0.length; i++) {
			hashCodes0[i] = children0[i].hashCode();
			hashCodes1[i] = children1[i].hashCode();
		}
		Arrays.sort(hashCodes0);
		Arrays.sort(hashCodes1);

		boolean currLevelEq = Arrays.equals(hashCodes0, hashCodes1);

		if (!currLevelEq)
			return false;
		else
			for (int i = 0; i < children0.length; i++)
				if (!isIsomophicTrees(children0[i], children1[i]))
					return false;
		return true;
	}
}
