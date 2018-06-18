package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.simplify.IF.Range;
import edu.udel.cis.vsl.sarl.simplify.IF.RangeFactory;
import edu.udel.cis.vsl.sarl.util.Pair;
import edu.udel.cis.vsl.sarl.util.WorkMap;

public class ContextNormalizer {

	private Context context;

	private WorkMap<Monic, Range> rangeMap;

	private Set<SymbolicConstant> theDirtySet;

	private SimplifierInfo info;

	public ContextNormalizer(Context context) {
		this.context = context;
		this.rangeMap = context.rangeMap;
		this.info = context.info;
		this.theDirtySet = context.theDirtySet;
	}

	/**
	 * Does there exist an entry in the subMap with a monic or monomial key
	 * containing a symbolic constant in the given dirty set? If not, there is
	 * no need to re-do Gaussian elimination because nothing in the linear
	 * system could have changed since the last time you did it.
	 * 
	 * @param dirty
	 *            the set of symbolic constants that are "dirty"
	 * @return true iff there exist an entry in the subMap with a monic or
	 *         monomial key containing a symbolic constant in dirty
	 */
	private boolean linearChange(Set<SymbolicConstant> dirty) {
		for (Entry<SymbolicExpression, SymbolicExpression> entry : context
				.getSubEntries()) {
			SymbolicExpression key = entry.getKey();

			if ((key instanceof Monic || key instanceof Monomial)
					&& intersects(key, dirty)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Performs Gaussian Elimination on the numeric entries of the
	 * {@link #subMap}.
	 * 
	 * Does not read or modify {@link #rangeMap}.
	 * 
	 * @return <code>true</code> iff there is a change made to the
	 *         {@link #subMap}
	 * 
	 * @throws InconsistentContextException
	 *             if an inconsistency is detected when modifying the
	 *             {@link #subMap}
	 */
	protected void gauss(Set<SymbolicConstant> dirtyIn,
			Set<SymbolicConstant> dirtyOut)
			throws InconsistentContextException {
		// TODO: change the monic comparator to one that orders
		// from least to greatest:
		// - symbolic constants
		// - array reads
		// ...
		// - function applications
		// - constants
		if (!linearChange(dirtyIn))
			return;

		LinearSolver ls = context.getLinearSolver();

		if (ls == null)
			return;
		if (!ls.isConsistent())
			throw new InconsistentContextException();
		if (!ls.hasChanged())
			return;
		for (SymbolicExpression key : ls.getKeysToRemove())
			context.removeSubkey(key);
		for (Entry<Monic, Monomial> entry : ls.getNewEntries())
			context.addSub(entry.getKey(), entry.getValue(), dirtyOut);
	}

	private boolean intersects(SymbolicExpression expr,
			Set<SymbolicConstant> set) {
		Set<SymbolicConstant> set1 = expr.getFreeVars();
		Set<SymbolicConstant> set2;

		// make set1 the bigger of the two sets
		if (set1.size() >= set.size()) {
			set2 = set;
		} else {
			set2 = set1;
			set1 = set;
		}
		for (SymbolicConstant x : set2) {
			if (set1.contains(x))
				return true;
		}
		return false;
	}

	// private LinkedList<Pair<SymbolicExpression, SymbolicExpression>>
	// buildSubmapWorklist(
	// Set<SymbolicConstant> dirtSet) {
	// LinkedList<Pair<SymbolicExpression, SymbolicExpression>> result = new
	// LinkedList<>();
	//
	// for (Entry<SymbolicExpression, SymbolicExpression> entry : subMap
	// .entrySet()) {
	// SymbolicExpression key = entry.getKey(), value = entry.getValue();
	//
	// if (intersects(key, dirtSet) || intersects(value, dirtSet))
	// result.add(new Pair<>(key, value));
	// }
	// return result;
	// }

	private LinkedList<SymbolicExpression> buildSubmapWorklist(
			Set<SymbolicConstant> dirtSet) {
		LinkedList<SymbolicExpression> result = new LinkedList<>();

		for (Entry<SymbolicExpression, SymbolicExpression> entry : context
				.getSubEntries()) {
			SymbolicExpression key = entry.getKey(), value = entry.getValue();

			if (intersects(key, dirtSet) || intersects(value, dirtSet))
				result.add(key);
		}
		return result;
	}

	// private LinkedList<Pair<Monic, Range>> buildRangemapWorklist(
	// Set<SymbolicConstant> dirtSet) {
	// LinkedList<Pair<Monic, Range>> result = new LinkedList<>();
	//
	// for (Entry<Monic, Range> entry : rangeMap.entrySet()) {
	// Monic key = entry.getKey();
	//
	// if (intersects(key, dirtSet))
	// result.add(new Pair<>(key, entry.getValue()));
	// }
	// return result;
	// }

	@SuppressWarnings("unchecked")
	private Set<SymbolicConstant> cloneDirtySet(Set<SymbolicConstant> set) {
		return (Set<SymbolicConstant>) ((HashSet<SymbolicConstant>) set)
				.clone();
	}

	public void normalize() {
		Set<SymbolicConstant> subMapDirties = cloneDirtySet(theDirtySet);
		Set<SymbolicConstant> rangeMapDirties = cloneDirtySet(
				context.theDirtySet);
		Set<SymbolicConstant> tmpDirties = new HashSet<SymbolicConstant>();

		while (!subMapDirties.isEmpty() || !rangeMapDirties.isEmpty()) {
			try {
				normalizeSubMap(subMapDirties, tmpDirties);
				rangeMapDirties.addAll(tmpDirties);
				subMapDirties.clear();
				tmpDirties.clear();
				simplifyRangeMap(rangeMapDirties, tmpDirties);
				subMapDirties.addAll(tmpDirties);
				rangeMapDirties.clear();
				tmpDirties.clear();
			} catch (InconsistentContextException e) {
				context.makeInconsistent();
				break;
			}
		}
		theDirtySet.clear();
	}

	private void normalizeSubMap(Set<SymbolicConstant> dirtyIn,
			Set<SymbolicConstant> dirtyOut)
			throws InconsistentContextException {
		Set<SymbolicConstant> simpDirties = cloneDirtySet(dirtyIn);
		Set<SymbolicConstant> tupleDirties = cloneDirtySet(dirtyIn);
		Set<SymbolicConstant> gaussDirties = cloneDirtySet(dirtyIn);
		Set<SymbolicConstant> tmpDirties = new HashSet<>();

		while (!simpDirties.isEmpty() || !tupleDirties.isEmpty()
				|| !gaussDirties.isEmpty()) {
			if (!simpDirties.isEmpty()) {
				simplifySubMap(simpDirties, tmpDirties);
				simpDirties.clear();
				tupleDirties.addAll(tmpDirties);
				gaussDirties.addAll(tmpDirties);
				dirtyOut.addAll(tmpDirties);
				tmpDirties.clear();
			}
			if (!tupleDirties.isEmpty()) {
				extractTuples(tupleDirties, tmpDirties);
				tupleDirties.clear();
				simpDirties.addAll(tmpDirties);
				gaussDirties.addAll(tmpDirties);
				dirtyOut.addAll(tmpDirties);
				tmpDirties.clear();
			}
			if (!gaussDirties.isEmpty()) {
				gauss(gaussDirties, tmpDirties);
				gaussDirties.clear();
				simpDirties.addAll(tmpDirties);
				tupleDirties.addAll(tmpDirties);
				dirtyOut.addAll(tmpDirties);
				tmpDirties.clear();
			}
		}

	}

	/**
	 * Simplifies the {@link #subMap}. When this method returns, each key-value
	 * pair in the subMap will be simplified using all other entries.
	 * 
	 * Given the original dirty set which determines the initial set of entries
	 * that must be simplified; upon return, dirtySet will contain all symbolic
	 * constants ...
	 * 
	 * @param dirtyIn
	 *            set of symbolic constants considered dirty, used to determine
	 *            the initial set of entries in the subMap which will be
	 *            simplified. More entries can be added as more variables become
	 *            dirty. This set is not modified by this method.
	 * 
	 * @param dirtyOut
	 *            the actual set of symbolic constants occurring in entries
	 *            which are modified or added to the subMap
	 *
	 */
	private void simplifySubMap(Set<SymbolicConstant> dirtyIn,
			Set<SymbolicConstant> dirtyOut)
			throws InconsistentContextException {
		Set<SymbolicConstant> dirtyNow = new HashSet<>(dirtyIn);
		ContextExtractor extractor = new ContextExtractor(context, dirtyNow);

		while (!dirtyNow.isEmpty()) {
			LinkedList<SymbolicExpression> worklist = buildSubmapWorklist(
					dirtyNow);

			dirtyNow.clear();
			while (!worklist.isEmpty()) {
				SymbolicExpression key1 = worklist.remove(),
						value1 = context.getSub(key1);

				if (value1 == null)
					continue;
				context.removeSubkey(key1);

				SymbolicExpression key2 = context.simplify(key1),
						value2 = context.simplify(value1);
				Pair<SymbolicExpression, SymbolicExpression> pair = new Pair<>(
						key2, value2);

				context.standardizePair(pair);

				SymbolicExpression newKey = pair.left;

				if (newKey == null)
					continue; // a trivial substitution

				SymbolicExpression newValue = pair.right;
				SymbolicExpression oldValue = context.getSub(newKey);

				if (oldValue == newValue) {
					// do nothing: the new sub is already in the subMap
				} else if (newKey == key1 && newValue == value1) {
					// no change: put it back, but don't count it as dirty...
					context.putSub(key1, value1);
				} else if (newValue.isTrue()
						&& SimplifierInfo.isNumericRelational(newKey)) {
					// it goes to the rangeMap...
					extractor.extractClause((BooleanExpression) newKey);
				} else {
					// add the new sub, updating dirty...
					context.addSub(newKey, newValue, dirtyNow);
				}
			}
			dirtyOut.addAll(dirtyNow);
		}
	}

	/**
	 * Computes the simplification of a certain kind of {@link Entry} (which is
	 * just an ordered pair). The left component of the entry is an int division
	 * expression and the right component is an integer range. The pair encodes
	 * the claim that the evaluation of the left expression lands in the range,
	 * for any point satisfying the assumption. If no change, the result
	 * returned will be == the given pair.
	 * 
	 * <pre>
	 * Suppose b>0.
	 * Write Q = Q- U Q0 U Q+, where 
	 * Q-={x in Q | x<0}, Q0={x in Q | x=0}, and Q+={x in Q | x>0}.
	 * 
	 * a div b in Q- <==> a in b*Q- + [1-b,0]
	 * a div b in Q0 <==> a in b*Q0 + [1-b,b-1]
	 * a div b in Q+ <==> a in b*Q+ + [0,b-1]
	 * 
	 * Therefore a div b in Q <==> a in union of above. 
	 *	
	 * Example:
	 * 
	 * a div 3 in {2} <==> a in {3*2}+[0,2] = {6,7,8}
	 * a div 3 in {0} <==> a in {3*0}+[-2,2] = {-2,-1,0,1,2}
	 * a div 3 in {-2} <==> a in {3*-2}+[-2,0] = {-8,-7,-6}.
	 * 
	 * If b<0:
	 * a div b in Q- <==> a in b*Q- + [0,-b-1]
	 * a div b in Q0 <==> a in b*Q0 + [1+b,-b-1]
	 * a div b in Q+ <==> a in b*Q+ + [1+b,0]
	 * </pre>
	 * 
	 * @param pair
	 *            an entry as described above
	 * @return the simplified entry
	 */
	private Entry<Monic, Range> simplifyIntDivide(Entry<Monic, Range> pair)
			throws InconsistentContextException {
		Monic monic = pair.getKey();
		NumericExpression a = (NumericExpression) monic.argument(0),
				b = (NumericExpression) monic.argument(1);
		Range b_range = context.computeRange(b);
		IntegerNumber b_number = (IntegerNumber) b_range.getSingletonValue();

		if (b_number == null)
			return pair;

		NumberFactory nf = info.numberFactory;
		RangeFactory rf = info.rangeFactory;
		IntegerNumber zero = nf.zeroInteger(), one = nf.oneInteger();
		Range empty = rf.emptySet(true);
		Range q = pair.getValue();
		Range q_n = rf.intersect(rf.interval(true, nf.negativeInfinityInteger(),
				true, nf.integer(-1), false), q);
		boolean q_0 = q.containsNumber(zero);
		Range q_p = rf.intersect(rf.interval(true, one, false,
				nf.positiveInfinityInteger(), true), q);
		Range b_n, b_0, b_p;

		if (b_number.signum() > 0) {
			IntegerNumber lo = nf.subtract(one, b_number), hi = nf.negate(lo);

			b_n = rf.interval(true, lo, false, zero, false);
			b_0 = q_0 ? rf.interval(true, lo, false, hi, false) : empty;
			b_p = rf.interval(true, zero, false, hi, false);
		} else {
			IntegerNumber lo = nf.increment(b_number), hi = nf.negate(lo);

			b_n = rf.interval(true, zero, false, hi, false);
			b_0 = q_0 ? rf.interval(true, lo, false, hi, false) : empty;
			b_p = rf.interval(true, lo, false, zero, false);
		}

		Range set_n = q_n.isEmpty() ? empty
				: rf.add(rf.multiply(q_n, b_number), b_n);
		Range set_p = q_p.isEmpty() ? empty
				: rf.add(rf.multiply(q_p, b_number), b_p);
		Range union = rf.union(rf.union(set_n, b_0), set_p);
		Pair<Monic, Range> norm = info.normalize((Monomial) a, union);

		return norm;
	}

	/**
	 * Simplifies an entry removed from the {@link #rangeMap}. If no
	 * simplification occurs, this method returns the same entry it was given.
	 * Otherwise it will return a non-{@code null} {@link Entry}. The first
	 * component will be a non-{@code null} {@link Monic}. The second component
	 * may or may not be {@code null}. If {@code null}, this indicates that the
	 * entry should not be added to the {@link #rangeMap} because it is already
	 * implied by the existing constraints. Otherwise, if the original pair is
	 * (m,r) and the returned pair is (m',r'), it will satisfy
	 * 
	 * context => ( (m in r) <=> (m' in r') ).
	 * 
	 * @param entry
	 *            the entry to be simplified, which is non-{@code null} and both
	 *            components of which are non-{@code null}
	 * @return the simplified entry
	 * @throws InconsistentContextException
	 */
	private Entry<Monic, Range> simplifyRangeEntry(Entry<Monic, Range> entry)
			throws InconsistentContextException {
		Entry<Monic, Range> result = entry;
		Monic oldKey = entry.getKey();
		NumericExpression simpKey = (NumericExpression) context
				.simplify(oldKey);

		if (oldKey != simpKey) {
			Range oldRange = entry.getValue();

			if (simpKey instanceof Constant) {
				if (!oldRange.containsNumber(((Constant) simpKey).number()))
					throw new InconsistentContextException();
				return new Pair<>(oldKey, null);
			}
			result = info.normalize((Monomial) simpKey, oldRange);
		}
		if (result.getKey().operator() == SymbolicOperator.INT_DIVIDE)
			result = simplifyIntDivide(result);
		return result;
	}

	/**
	 * Simplifies the {@link #rangeMap}. Removes one entry from the map,
	 * simplifies it, places it back. Repeats until stabilization. If an entry
	 * ever resolves to a single value, it is removed completely and added to
	 * the {@link #subMap}.
	 * 
	 * @return <code>true</code> iff any change was made
	 */
	private void simplifyRangeMap(Set<SymbolicConstant> dirtyIn,
			Set<SymbolicConstant> dirtyOut)
			throws InconsistentContextException {
		// for now, not using dirtyIn. We will assume all entries
		// are dirty. Eventually fix that.

		rangeMap.makeAllDirty(); // put everything on the work list
		for (Entry<Monic, Range> oldEntry = rangeMap
				.hold(); oldEntry != null; oldEntry = rangeMap.hold()) {
			context.clearSimplifications();

			// the following will not modify anything:
			Entry<Monic, Range> newEntry = simplifyRangeEntry(oldEntry);

			if (newEntry == oldEntry) { // no change
				rangeMap.release(); // put back the entry on hold
			} else { // a change
				Range newRange = newEntry.getValue();

				if (newRange != null)
					context.restrictRange(newEntry.getKey(), newRange,
							dirtyOut);
			}
		}
	}

	/**
	 * <p>
	 * Simplify non-concrete tuple type expressions to concrete tuples. A
	 * concrete tuple is defined in {@link SymbolicTupleSimplifier}.
	 * </p>
	 * 
	 * @throws InconsistentContextException
	 *             if any new substitution from a non-concrete tuple to a
	 *             concrete one violates the invariants of the {@link #subMap}.
	 */
	private void extractTuples(Set<SymbolicConstant> dirtyIn,
			Set<SymbolicConstant> dirtyOut)
			throws InconsistentContextException {
		// TODO: for now, not using dirtyIn. Eventually use this to limit
		// the search in some way.
		Map<SymbolicExpression, SymbolicExpression> ncTuple2concrete = new SymbolicTupleSimplifier(
				context).getTupleSubstitutionMap();

		// simplify non-concrete tuples:
		for (Entry<SymbolicExpression, SymbolicExpression> entry : ncTuple2concrete
				.entrySet())
			context.addSub(entry.getKey(), entry.getValue(), dirtyOut);
	}

}
