package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.io.PrintStream;
import java.util.Comparator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.util.EmptyMap;

/*
 * Plan:
 * 
 * Rename AbstractInterpretation Context.
 * 
 * Add to Context a simplification cache.
 * 
 * Get Methods in Context must all be re-wired to look in parent context. It can
 * be assumed that if a bound for x appears in the Context, there is no need to
 * look in the parent, because the bound in the child must necessarily be more
 * strict than the one in the parent (this is an invariant). [But what about
 * "or" which widens intervals? This does not use a parent context. It clones a
 * context and then modifies the clone.]
 * 
 * Create a new class, ContextBuilder. An instance is used to create a new
 * Context from a parent Context and a boolean expression. This class may create
 * new SimplifierWorkers to simplify things. It does not reference any
 * Simplifier, but may reference universe and other "info".
 * 
 * SimplifierWorker has reference to a Context, but not any Simplifier. It is
 * wants to cache things, it can cache in the Context. If it wants to create a
 * new Context, it can create a ContextBuilder.
 *
 * Simplifier becomes just a shell of its former self.
 */

/**
 * A structured representation of a boolean formula (assumption), suitable for
 * simplifying symbolic expressions.
 * 
 * @author Stephen F. Siegel (siegel)
 *
 */
public class AbstractInterpretation {

	// Static fields...

	public final static boolean debug = false;

	// Instance Fields ...

	/**
	 * The parent context. Everything that holds in the parent also holds in
	 * this context, but more things may hold here. For examples, bounds can be
	 * tightened, a variable may get solved, etc. To find the bounds on a monic,
	 * look here first, then look in the parent.
	 */
	AbstractInterpretation parent;

	/**
	 * A map that assigns concrete boolean values to boolean primitive
	 * expressions.
	 */
	Map<BooleanExpression, Boolean> booleanMap;

	/**
	 * Map assigning concrete numerical values to certain {@link Monic}s.
	 */
	Map<Monic, Number> constantMap;

	/**
	 * General Map for replacing equivalent {@link Monic}s. This map is built at
	 * the same time as {@link #constantMap}, by method
	 * {@link #updateConstantMap()}. It is obtained by performing back
	 * substitution after Gaussian elimination completes.
	 */
	Map<Monic, Monic> reduceMap;

	/**
	 * <p>
	 * A map assigning concrete values to certain symbolic expressions. This map
	 * cannot involve any solved variables. In particular, a key in this map can
	 * not be a symbolic constant, because if it were, it would be a solved
	 * variable. All types are allowed, including arrays. This map is used to
	 * form the assumption (full and reduced).
	 * </p>
	 * 
	 * <p>
	 * Example: if the path condition is XY=0, this map may be {XY=0}. If the
	 * path condition is "forall j . 0<=j<n -> a[i][j]=0", where a[i] is an
	 * array of length n, then this map may contain the entry
	 * a[i]=(int[n])arraylambda j . 0.
	 * </p>
	 * 
	 * <p>
	 * This map may also map certain boolean expressions to either true or
	 * false.
	 * </p>
	 */
	private Map<SymbolicExpression, SymbolicExpression> otherConstantMap;

	/**
	 * <p>
	 * Map giving concrete upper and lower bounds on some {@link Monic}s.
	 * Associates to each monic an {@link Interval} such that the set of all
	 * possible values the monic can assume are contained in that interval.
	 * Monics that have a single concrete value are removed from this map and
	 * placed in either {@link #solvedVariables} (if the monic is a
	 * {@link SymbolicConstant}) or in the {@link #constantMap} (otherwise). No
	 * solved variables can occur in this map.
	 * </p>
	 * 
	 * <p>
	 * This map is used to form the assumption (full and reduced).
	 * </p>
	 */
	private Map<Monic, Interval> boundMap;

	/**
	 * An object that gathers together references to various tools that are
	 * needed for this class to do its work.
	 */
	private SimplifierInfo info;

	/**
	 * Has this AI changed since the last time the mark was set?
	 */
	private boolean change = false;

	/**
	 * An ordering on symbolic constants.  [Could put this in info.]
	 */
	private Comparator<SymbolicConstant> variableComparator;

	// Static methods ...

	@SuppressWarnings("unchecked")
	private static <S, T> TreeMap<S, T> cloneTreeMap(Map<S, T> map) {
		if (map == null)
			return null;
		else
			return (TreeMap<S, T>) ((TreeMap<?, ?>) map).clone();
	}

	// Constructors ...

	private AbstractInterpretation(SimplifierInfo info,
			Map<BooleanExpression, Boolean> booleanMap,
			Map<Monic, Interval> boundMap, Map<Monic, Number> constantMap,
			Map<SymbolicExpression, SymbolicExpression> otherConstantMap) {
		this.info = info;
		this.booleanMap = booleanMap;
		this.boundMap = boundMap;
		this.constantMap = constantMap;
		this.otherConstantMap = otherConstantMap;
		this.reduceMap = new TreeMap<Monic, Monic>(
				info.idealFactory.monicComparator());
		this.parent = null;
		this.variableComparator = new Comparator<SymbolicConstant>() {
			Comparator<SymbolicType> typeComparator = info.universe
					.typeFactory().typeComparator();

			@Override
			public int compare(SymbolicConstant o1, SymbolicConstant o2) {
				int result = o1.name().compareTo(o2.name());

				if (result != 0)
					return result;
				return typeComparator.compare(o1.type(), o2.type());
			}
		};
	}

	public AbstractInterpretation(SimplifierInfo info) {
		this(info, new TreeMap<>(info.booleanFactory.getBooleanComparator()),
				new TreeMap<>(info.idealFactory.monicComparator()),
				new TreeMap<>(info.idealFactory.monicComparator()),
				new TreeMap<>(info.universe.comparator()));
	}

	public AbstractInterpretation(AbstractInterpretation that) {
		this(that.info, cloneTreeMap(that.booleanMap),
				cloneTreeMap(that.boundMap), cloneTreeMap(that.constantMap),
				cloneTreeMap(that.otherConstantMap));
		info.out.println("I am cloned.\n");
		info.out.flush();
	}

	// Helper methods ...

	/**
	 * If <code>monomial</code> is a cast of x from Herbrand integer to integer
	 * or from Herbrand real to real, and <code>value</code> is the known
	 * constant value of that monomial, caches a simplification which maps x to
	 * the result of casting <code>value</code> to the original Herbrand type.
	 * Otherwise, does nothing.
	 * 
	 * @param monomial
	 *            and non-<code>null</code> {@link Monomial}
	 * @param value
	 *            the known concrete value of <code>monomial</code>
	 */
	private void processHerbrandCast(Monomial monomial, Number value) {
		if (monomial.operator() == SymbolicOperator.CAST) {
			SymbolicType type = monomial.type();
			SymbolicExpression original = (SymbolicExpression) monomial
					.argument(0);
			SymbolicType originalType = original.type();

			if (originalType.isHerbrand()
					&& (originalType.isInteger() && type.isInteger()
							|| originalType.isReal() && type.isReal())) {
				original = info.universe.canonic(original);

				SymbolicExpression constant = info.universe
						.cast(original.type(), info.universe.number(value));

				constant = info.universe.canonic(constant);
				// cacheSimplification(original, constant);
				setOtherValue(original, constant);
			}
		}
	}

	private <S, T> void printMap(PrintStream out, Map<S, T> map) {
		for (Entry<S, T> entry : map.entrySet()) {
			out.println("  " + entry.getKey() + " : " + entry.getValue());
		}
		out.flush();
	}

	// Public methods...

	@Override
	public AbstractInterpretation clone() {
		return new AbstractInterpretation(this);
	}

	/**
	 * Sets {@link #change} flag to <code>false</code>. Subsequence calls to
	 * other methods that result in a change of state to this AI will set that
	 * flag to <code>true</code>.
	 */
	public void setMark() {
		change = false;
	}

	/**
	 * Has the state of this AI changed since the last call to
	 * {@link #setMark()}?
	 * 
	 * @return <code>true</code> if the state of this AI has changed since the
	 *         last call to {@link #setMark()}, or since creation if
	 *         {@link #setMark()} was never called on this AI
	 */
	public boolean changed() {
		return change;
	}

	/**
	 * Sets the interval bound associated to <code>key</code> to
	 * <code>bound</code>. The change flag is raised if this changed the bound
	 * associated to <code>key</code>.
	 * 
	 * @param key
	 *            a non-<code>null</code> {@link Monic}
	 * @param bound
	 *            a non-<code>null</code> {@link Interval} of the same type as
	 *            <code>key</code>, the new interval bound
	 */
	public void setBound(Monic key, Interval bound) {
		change = !bound.equals(boundMap.put(key, bound));
	}

	/**
	 * Declares that <code>key</code> has a specific concrete numeric value. The
	 * change flag is raised if this changed the bound associated to
	 * <code>key</code>.
	 * 
	 * @param key
	 *            a non-<code>null</code> {@link Monic}
	 * @param value
	 *            a {@link Number} of the same type as <code>key</code>
	 */
	public void setMonicValue(Monic key, Number value) {
		setBound(key, info.numberFactory.singletonInterval(value));
	}

	/**
	 * Retrieves the interval bound associated to <code>key</code>.
	 * 
	 * @param key
	 *            a non-<code>null</code> {@link Monic}
	 * @return the interval bound associated to <code>key</code> or
	 *         <code>null</code> if there is no such bound
	 */
	public Interval getBound(Monic key) {
		Interval result = boundMap.get(key);

		return result;
	}

	/**
	 * Returns the set of all interval bounds on {@link Monic}s as a set of
	 * {@link Entry}. This may include constants, i.e., {@link Monic}s with a
	 * single value, in which case the bound has the form [x,x] for some
	 * concrete {@link Number} x.
	 * 
	 * @return the set of all {@link Monic}-{@link Interval} pairs specifying
	 *         interval bounds on {@link Monic}s
	 */
	public Set<Entry<Monic, Interval>> getBounds() {
		return boundMap.entrySet();
	}

	/**
	 * Removes any bound associated to <code>key</code> Updates the change flag
	 * if a bound was previously present.
	 * 
	 * @param key
	 *            a non-<code>null</code> {@link Monic}
	 * @return the old interval bound associated to <code>key</code>, or
	 *         <code>null</code> if no bound was associated to <code>key</code>
	 */
	public Interval removeBound(Monic key) {
		Interval result = boundMap.remove(key);

		if (result != null)
			change = true;
		return result;
	}

	/**
	 * Is the bound mapping empty? I.e., are there no {@link Monic}s with an
	 * associated interval bound in this AI?
	 * 
	 * @return <code>true</code> iff the bound mapping is empty
	 */
	public boolean hasNoBounds() {
		return boundMap.isEmpty();
	}

	/**
	 * Returns the number of entries in the bound map.
	 * 
	 * @return the number of entries in the bound map
	 */
	public int getNumBounds() {
		return boundMap.size();
	}

	/**
	 * Declares that <code>key</code> is bounded by <code>bound</code>, hence
	 * any existing bound I associated to <code>key</code> will be replaced by
	 * the intersection of I and <code>bound</code>. If this results in a change
	 * to the bound associated to <code>key</code>, the change flag is raised.
	 * 
	 * @param key
	 *            a non-<code>null</code> {@link Monic}
	 * @param bound
	 *            an interval of the same type as <code>key</code> containing
	 *            all possible values of <code>key</code>
	 * @return the old bound associated to <code>key</code>, or
	 *         <code>null</code> if there was none
	 */
	public Interval restrictBound(Monic key, Interval bound) {
		Interval original = boundMap.get(key), result;

		if (original == null) {
			result = bound;
			boundMap.put(key, result);
			change = true;
		} else {
			result = info.numberFactory.intersection(original, bound);
			if (!result.equals(original)) {
				boundMap.put(key, result);
				change = true;
			}
		}
		return result;
	}

	/**
	 * Enlarges the bound associated to <code>key</code> if necessary so that it
	 * includes <code>bound</bound>.  Specifically, if there
	 * is no existing bound associated to <code>key</code>, then the given
	 * <code>bound</code> becomes the bound associated to <code>key</code>. If
	 * there is an existing bound I associated to <code>key</code>, then that
	 * bound is replaced by the smallest interval containing I and
	 * <code>bound</code>.
	 * 
	 * If this results in a change to the bound associated to <code>key</code>,
	 * the change flag is raised.
	 * 
	 * @param key
	 *            a non-<code>null</code> {@link Monic}
	 * @param bound
	 *            an interval of the same type as <code>key</code>
	 * @return the old bound associated to <code>key</code>, or
	 *         <code>null</code> if there was none
	 */
	public Interval enlargeBound(Monic key, Interval bound) {
		Interval original = boundMap.get(key), result;

		if (original == null) {
			result = bound;
			boundMap.put(key, result);
			change = true;
		} else {
			result = info.numberFactory.join(original, bound);
			if (!result.equals(original)) {
				boundMap.put(key, result);
				change = true;
			}
		}
		return result;
	}

	// if integer type, should the bound be forced to be strict?
	public Interval restrictLowerBound(Monic key, Number value,
			boolean strict) {
		Interval original = boundMap.get(key), result;
		boolean isIntegral = key.type().isInteger();

		if (original == null) {
			Number posInfinity = info.numberFactory.infiniteNumber(isIntegral,
					true);

			result = info.numberFactory.newInterval(isIntegral, value, strict,
					posInfinity, true);
			boundMap.put(key, result);
			change = true;
		} else {
			result = info.numberFactory.restrictLower(original, value, strict);
			if (!result.equals(original)) {
				boundMap.put(key, result);
				change = true;
			}
		}
		return result;
	}

	public Interval restrictUpperBound(Monic key, Number value,
			boolean strict) {
		Interval original = boundMap.get(key), result;
		boolean isIntegral = key.type().isInteger();

		if (original == null) {
			Number negInfinity = info.numberFactory.infiniteNumber(isIntegral,
					false);

			result = info.numberFactory.newInterval(isIntegral, negInfinity,
					true, value, strict);
			boundMap.put(key, result);
			change = true;
		} else {
			result = info.numberFactory.restrictUpper(original, value, strict);
			if (!result.equals(original)) {
				boundMap.put(key, result);
				change = true;
			}
		}
		return result;
	}

	public Boolean setTruth(BooleanExpression formula, boolean value) {
		formula = (BooleanExpression) info.universe.canonic(formula);

		Boolean theValue = value ? Boolean.TRUE : Boolean.FALSE;
		Boolean result = booleanMap.put(formula, theValue);

		if (result != theValue)
			change = true;
		return result;
	}

	public Boolean getTruth(BooleanExpression formula) {
		return booleanMap.get(formula);
	}

	public Boolean removeTruth(BooleanExpression formula) {
		Boolean result = booleanMap.remove(formula);

		if (result != null)
			change = true;
		return result;
	}

	public SymbolicExpression setOtherValue(SymbolicExpression expr,
			SymbolicExpression value) {
		expr = info.universe.canonic(expr);
		value = info.universe.canonic(value);

		SymbolicExpression result = otherConstantMap.put(expr, value);

		change = change || result != value;
		return result;
	}

	public SymbolicExpression getOtherValue(SymbolicExpression expr) {
		return otherConstantMap.get(expr);
	}

	public Set<Entry<Monic, Interval>> getMonicBoundEntries() {
		return boundMap.entrySet();
	}

	public Set<Entry<Monic, Number>> getMonicConstantEntries() {
		return constantMap.entrySet();
	}

	public Set<Entry<SymbolicExpression, SymbolicExpression>> getOtherConstantEntries() {
		return otherConstantMap.entrySet();
	}

	public Set<Entry<BooleanExpression, Boolean>> getBooleanEntries() {
		return booleanMap.entrySet();
	}

	public void print(PrintStream out) {
		out.println("Monic bounds:");
		printMap(out, boundMap);
		out.println("Monic constants:");
		printMap(out, constantMap);
		out.println("Facts:");
		printMap(out, booleanMap);
		out.println("Other constants:");
		printMap(out, otherConstantMap);
		out.flush();
	}

	public boolean updateConstantMap() {
		// The constant map doesn't get cleared because we want to keep
		// accumulating facts. Thus the map might not be empty at this point.
		for (Entry<Monic, Interval> entry : getMonicBoundEntries()) {
			Interval interval = entry.getValue();
			Number lower = interval.lower();

			if (lower != null && lower.equals(interval.upper())) {
				Monic expression = entry.getKey();

				assert !interval.strictLower() && !interval.strictUpper();
				constantMap.put(expression, lower);
				// remove from bound map?
				processHerbrandCast(expression, lower);
			}
		}

		boolean satisfiable = LinearSolver.reduceConstantMap(info.idealFactory,
				constantMap);

		if (debug) {
			info.out.println("Result of updateConstantMap() part 1:");
			print(info.out);
		}
		if (satisfiable) {
			// satisfiability should be same as the result of
			// LinearSolver.reduceConstantMap
			satisfiable = LinearSolver.reduceMap(info.idealFactory, constantMap,
					reduceMap);
			if (debug) {
				info.out.println("Result of updateConstantMap() part 2:");
				print(info.out);
			}
		}
		if (debug) {
			if (!satisfiable)
				info.out.println("Constant map is inconsistent.");
		}
		return satisfiable;
	}

	public Number getConstantValue(Monic monic) {
		return constantMap.get(monic);
	}

	public Interval assumptionAsInterval(SymbolicConstant symbolicConstant) {
		if (!booleanMap.isEmpty() || !otherConstantMap.isEmpty())
			return null;
		if (!constantMap.isEmpty()) {
			if (!boundMap.isEmpty() || constantMap.size() != 1)
				return null;

			Entry<Monic, Number> entry = constantMap.entrySet().iterator()
					.next();

			if (!entry.getKey().equals(symbolicConstant))
				return null;
			return info.numberFactory.singletonInterval(entry.getValue());
		}
		if (boundMap.size() == 1) {
			Entry<Monic, Interval> entry = boundMap.entrySet().iterator()
					.next();

			if (!entry.getKey().equals(symbolicConstant))
				return null;
			return entry.getValue();
		}
		return null;
	}

	/**
	 * Gets the variables that have been "solved", i.e., have an expression in
	 * terms of other (unsolved) variables. These variables can be entirely
	 * eliminated from the state.
	 * 
	 * @return mapping from solved variables to their values
	 */
	public Map<SymbolicConstant, SymbolicExpression> getSolvedVariables() {
		Map<SymbolicConstant, SymbolicExpression> solvedVariables = new TreeMap<>(
				variableComparator);

		for (Entry<Monic, Number> entry : constantMap.entrySet()) {
			Monic fp = entry.getKey();

			if (fp instanceof SymbolicConstant)
				solvedVariables.put((SymbolicConstant) fp,
						info.universe.number(entry.getValue()));
		}
		for (Entry<SymbolicExpression, SymbolicExpression> entry : otherConstantMap
				.entrySet()) {
			SymbolicExpression expr = entry.getKey();

			if (expr instanceof SymbolicConstant)
				solvedVariables.put((SymbolicConstant) expr, entry.getValue());
		}
		for (Entry<BooleanExpression, Boolean> entry : booleanMap.entrySet()) {
			BooleanExpression primitive = entry.getKey();

			if (primitive instanceof SymbolicConstant)
				solvedVariables.put((SymbolicConstant) primitive,
						info.universe.bool(entry.getValue()));
		}
		return solvedVariables;
	}

	/**
	 * This method does not modify anything. It reads {@link #reduceMap}.
	 * 
	 * @param selfupdate
	 * @return
	 */
	public Map<SymbolicExpression, SymbolicExpression> substitutionMap(
			boolean selfupdate) {
		Map<SymbolicExpression, SymbolicExpression> result = new TreeMap<>(
				info.universe.comparator());

		for (Entry<Monic, Monic> entry : reduceMap.entrySet()) {
			result.put(info.universe.canonic(entry.getKey()),
					info.universe.canonic(entry.getValue()));
		}
		if (selfupdate) {
			Map<SymbolicExpression, SymbolicExpression> newSubstituteMap = new TreeMap<>(
					info.universe.comparator());

			newSubstituteMap.putAll(reduceMap);
			for (Entry<SymbolicExpression, SymbolicExpression> entry : result
					.entrySet()) {
				SymbolicExpression key, newKey;

				key = entry.getKey();
				newSubstituteMap.remove(key);
				newKey = info.universe.fullySubstitute(newSubstituteMap, key);
				newSubstituteMap.put(key, entry.getValue());
				if (newKey != key)
					newSubstituteMap.put(newKey, entry.getValue());
			}
			result = newSubstituteMap;
		}
		return result;
	}

	/**
	 * This method changes the {@link #reduceMap}.
	 * 
	 * @param expectedKey
	 * @param selfupdate
	 * @return
	 */
	public Map<SymbolicExpression, SymbolicExpression> substitutionMap(
			SymbolicConstant expectedKey, boolean selfupdate) {
		if (!expectedKey.isNumeric())
			return new EmptyMap<SymbolicExpression, SymbolicExpression>();
		else if (reduceMap.containsKey(expectedKey))
			return substitutionMap(selfupdate);
		else {
			reduceMap.clear();
			LinearSolver.reduceMap(info.idealFactory, (Monic) expectedKey,
					constantMap, reduceMap);
			return substitutionMap(selfupdate);
		}
	}

	/**
	 * Attempts to find, in the context, a clause which states the
	 * differentiability of the given <code>function</code>. This is a clause
	 * with operator {@link SymbolicOperator#DIFFERENTIABLE} and with the
	 * function argument (argument 0) equal to <code>function</code>.
	 * 
	 * @param function
	 *            the function for which a differentiability claim is sought
	 * @return a clause in the context dealing with the differentiability of
	 *         <code>function</code>, or <code>null</code> if no such clause is
	 *         found.
	 */
	BooleanExpression findDifferentiableClaim(SymbolicExpression function) {
		for (Entry<BooleanExpression, Boolean> entry : booleanMap.entrySet()) {
			if (!entry.getValue())
				continue;

			BooleanExpression clause = entry.getKey();

			if (clause.operator() != SymbolicOperator.DIFFERENTIABLE)
				continue;
			if (clause.argument(0).equals(function))
				return clause;
		}
		return null;
	}
}
