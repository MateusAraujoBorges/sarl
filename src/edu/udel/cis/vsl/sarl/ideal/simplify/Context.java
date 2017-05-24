package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.io.PrintStream;
import java.util.Comparator;
import java.util.HashMap;
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
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;

/**
 * A structured representation of a boolean formula (assumption), suitable for
 * simplifying symbolic expressions.
 * 
 * @author Stephen F. Siegel (siegel)
 *
 */
public class Context {

	// Static fields...

	public final static boolean debug = false;

	// Instance Fields ...

	/**
	 * A map that assigns concrete boolean values to boolean primitive
	 * expressions.
	 */
	private Map<BooleanExpression, Boolean> booleanMap;

	/**
	 * Map assigning concrete numerical values to certain {@link Monic}s.
	 */
	private Map<Monic, Number> constantMap;

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
	 * A cache of all simplifications computed under this {@link Context}. For
	 * any entry (x,y), the following formula must be valid: context -> x=y.
	 */
	private Map<SymbolicObject, SymbolicObject> simplificationCache;

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
	 * The full boolean expression upon which this context is based, including
	 * the equalities defining solved variables. This expression is equivalent
	 * to, but not necessarily equal to, the given assumption. It may have been
	 * simplified or put into a canonical form.
	 */
	private BooleanExpression fullAssumption;

	/**
	 * The boolean expression upon which this context is based, but excluding
	 * the solved variables.
	 */
	private BooleanExpression reducedAssumption;

	/**
	 * 
	 * This assumption upon which this context is based, but excluding the
	 * solved variables and excluding all information from the {@link #boundMap}
	 * , {@link #booleanMap}, {@link #constantMap}, and
	 * {@link #otherConstantMap} thrown in. I.e., reducedAssumption =
	 * rawAssumption + boundMap + booleanMap + constantMap + otherConstantMap.
	 * Currently it is used only to implement the method
	 * {@link #assumptionAsInterval()}. Should probably get rid of that method
	 * and this field.
	 */
	private BooleanExpression rawAssumption;

	/**
	 * An ordering on symbolic constants. [Could put this in info.]
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

	private Context(SimplifierInfo info,
			Map<BooleanExpression, Boolean> booleanMap,
			Map<Monic, Interval> boundMap, Map<Monic, Number> constantMap,
			Map<SymbolicExpression, SymbolicExpression> otherConstantMap) {
		this.info = info;
		this.booleanMap = booleanMap;
		this.boundMap = boundMap;
		this.constantMap = constantMap;
		this.otherConstantMap = otherConstantMap;
		// can also use a TreeMap, but HashMap seems faster...
		// this.simplificationCache = new TreeMap<SymbolicObject,
		// SymbolicObject>(info.universe.comparator());
		this.simplificationCache = new HashMap<>();
		// do this once and put it in universe...
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

	/**
	 * Constructs new {@link Context} with all empty maps.
	 * 
	 * @param info
	 *            info structure with references to commonly-used factories and
	 *            other objects
	 * @param parent
	 *            the {@link Context} that should be the parent of this context;
	 *            this context is essentially a sub-context of its parent, i.e.,
	 *            everything that holds in the parent also holds in this
	 *            context. The parent will never be modified by methods in this
	 *            {@link Context}.
	 */
	public Context(SimplifierInfo info) {
		this(info, new TreeMap<>(info.booleanFactory.getBooleanComparator()),
				new TreeMap<>(info.idealFactory.monicComparator()),
				new TreeMap<>(info.idealFactory.monicComparator()),
				new TreeMap<>(info.universe.comparator()));
	}

	// Private methods ...

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

				SymbolicExpression constant = info.universe
						.cast(original.type(), info.universe.number(value));

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

	// Package-private methods ...

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

	/**
	 * Sets {@link #reducedAssumption}.
	 * 
	 * @param new
	 *            value for {@link #reducedAssumption}
	 */
	void setReducedAssumption(BooleanExpression p) {
		this.reducedAssumption = p;
	}

	/**
	 * Sets {@link #rawAssumption}.
	 * 
	 * @param p
	 *            new value for {@link #rawAssumption}
	 */
	void setRawAssumption(BooleanExpression p) {
		this.rawAssumption = p;
	}

	// Public methods...

	@Override
	public Context clone() {
		return new Context(info, cloneTreeMap(booleanMap),
				cloneTreeMap(boundMap), cloneTreeMap(constantMap),
				cloneTreeMap(otherConstantMap));
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

	/**
	 * Associated <code>value</code> to <code>formula</code> in this context's
	 * boolean map.
	 * 
	 * @param formula
	 *            the key
	 * @param value
	 *            the truth value
	 * @return the old value associated to <code>formula</code>
	 */
	public Boolean setTruth(BooleanExpression formula, boolean value) {
		Boolean theValue = value ? Boolean.TRUE : Boolean.FALSE;
		Boolean result = booleanMap.put(formula, theValue);

		if (result != theValue)
			change = true;
		return result;
	}

	/**
	 * Returns the value associated to the given key in this context's boolean
	 * map, or, if there is no entry with that key, in the parent's boolean map,
	 * or <code>null</code> if no entry anywhere.
	 * 
	 * @param formula
	 *            the key
	 * @return value corresponding to that key in this context or an ancestor
	 *         context, or <code>null</code>
	 */
	public Boolean getTruth(BooleanExpression formula) {
		Boolean result = booleanMap.get(formula);

		return result;
	}

	/**
	 * Removes entry with given key from this context's boolean map. The parent
	 * context is never modified or even read.
	 * 
	 * @param formula
	 *            the key
	 * @return the old value corresponding to this key in this context proper,
	 *         or <code>null</code> if there was no entry with this key
	 */
	public Boolean removeTruth(BooleanExpression formula) {
		Boolean result = booleanMap.remove(formula);

		if (result != null)
			change = true;
		return result;
	}

	public SymbolicExpression setOtherValue(SymbolicExpression expr,
			SymbolicExpression value) {
		SymbolicExpression result = otherConstantMap.put(expr, value);

		change = change || result != value;
		return result;
	}

	public SymbolicExpression getOtherValue(SymbolicExpression expr) {
		SymbolicExpression result = otherConstantMap.get(expr);

		return result;
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
		if (!rawAssumption.isTrue())
			return null;
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

	public void cacheSimplification(SymbolicObject key, SymbolicObject value) {
		assert key.isCanonic();
		assert value.isCanonic();
		simplificationCache.put(key, value);
	}

	public SymbolicObject getSimplification(SymbolicObject key) {
		return simplificationCache.get(key);
	}

	public void clearSimplificationCache() {
		simplificationCache.clear();
	}

	public BooleanExpression getReducedAssumption() {
		return reducedAssumption;
	}

	public BooleanExpression getFullAssumption() {
		if (fullAssumption == null) {
			Map<SymbolicConstant, SymbolicExpression> map = getSolvedVariables();

			fullAssumption = getReducedAssumption();
			for (Entry<SymbolicConstant, SymbolicExpression> entry : map
					.entrySet()) {
				SymbolicConstant key = entry.getKey();
				SymbolicExpression value = entry.getValue();
				BooleanExpression equation = info.universe.equals(key, value);

				fullAssumption = info.universe.and(fullAssumption, equation);
			}
		}
		return fullAssumption;
	}

}
