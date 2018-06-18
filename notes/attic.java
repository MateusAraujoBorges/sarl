import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map.Entry;

import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.ideal.IF.RationalExpression;
import edu.udel.cis.vsl.sarl.ideal.simplify.InconsistentContextException;
import edu.udel.cis.vsl.sarl.util.Pair;
import edu.udel.cis.vsl.sarl.util.SingletonMap;

/**
	 * <p>
	 * Incorporates a new substitution into the {@link #subMap}. Updates the
	 * {@link #subMap} as needed in order to maintain its invariants.
	 * </p>
	 * 
	 * <p>
	 * Preconditions: (0) the invariants of the {@link #subMap} hold; (1) both
	 * expressions are non-null and have the same type; (2) the new substitution
	 * cannot introduce a cycle in the {@link #subMap}; (3) the substitution may
	 * not involve any {@link RationalExpression}s.
	 * </p>
	 * 
	 * <p>
	 * Postconditions: (0) the invariants of the {@link #subMap} hold; (1) all
	 * condition determined by the {@link #subMap} is the conjunction of the
	 * original condition and the equality {@code x}={@code y}.
	 * </p>
	 * 
	 * <p>
	 * Note that this method does not require that {@code x} and {@code y}
	 * satisfy all of the invariants of the {@link #subMap}. Instead, it does
	 * all of the work to modify that pair and modify other entries in the
	 * {@link #subMap} to guarantee that the invariants will hold in the
	 * post-state, assuming they held in the pre-state.
	 * </p>
	 * 
	 * <p>
	 * Inconsistency can be determined if the same key is mapped to two
	 * constants that are not equal.
	 * </p>
	 * 
	 * @param x
	 *            the expression to be replaced
	 * @param y
	 *            the expression that will be substituted for <code>x</code>
	 */
	private void addSubOld(SymbolicExpression x, SymbolicExpression y)
			throws InconsistentContextException {
		LinkedList<Pair<SymbolicExpression, SymbolicExpression>> workList = new LinkedList<>();

		workList.add(new Pair<>(x, y));
		while (!workList.isEmpty()) {
			Pair<SymbolicExpression, SymbolicExpression> pair = workList
					.removeFirst();

			pair.left = simplify(pair.left);
			pair.right = simplify(pair.right);
			standardizePair(pair);

			SymbolicExpression newKey = pair.left;

			if (newKey == null)
				continue; // a trivial substitution

			SymbolicExpression newValue = pair.right;
			SymbolicExpression oldValue = getSub(newKey);

			if (oldValue != null && oldValue.equals(newValue))
				continue; // this sub is already in the subMap
			// apply newKey->newValue to every entry of subMap...
			UnaryOperator<SymbolicExpression> singleSubstituter = info.universe
					.mapSubstituter(new SingletonMap<>(newKey, newValue));
			Iterator<Entry<SymbolicExpression, SymbolicExpression>> iter = subMap
					.entrySet().iterator();

			while (iter.hasNext()) {
				Entry<SymbolicExpression, SymbolicExpression> entry = iter
						.next();
				SymbolicExpression value = entry.getValue();
				SymbolicExpression key = entry.getKey(),
						subKey = transClose(singleSubstituter, key),
						subValue = transClose(singleSubstituter, value);

				if (subKey != key || subValue != value) {
					iter.remove();
					clearSimplifications();
					workList.add(new Pair<>(subKey, subValue));
				}
			}
			updateSub(newKey, newValue);
		}
	}
	