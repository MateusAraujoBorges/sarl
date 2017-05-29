package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;

import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.ideal.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Polynomial;
import edu.udel.cis.vsl.sarl.ideal.IF.RationalExpression;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.simplify.IF.Range;
import edu.udel.cis.vsl.sarl.util.FastList;
import edu.udel.cis.vsl.sarl.util.FastNode;
import edu.udel.cis.vsl.sarl.util.Pair;
import edu.udel.cis.vsl.sarl.util.SingletonMap;

/**
 * A structured representation of a boolean formula (assumption), suitable for
 * simplifying symbolic expressions.
 * 
 * Interface: create from a boolean expression
 * 
 * Worker will need to use.
 * 
 * @author Stephen F. Siegel (siegel)
 *
 */
public class Context2 implements ContextIF {

	// Static fields...

	public final static boolean debug = false;

	// Instance Fields ...

	/**
	 * <p>
	 * The essential substitution map. When simplifying an expression, any
	 * occurrence of the key of an entry in this map will be replaced by the
	 * value of the entry.
	 * </p>
	 *
	 * Invariants:
	 * 
	 * <ul>
	 * <li>If the value of an entry is non-null, it will have a type compatible
	 * with that of the key.</li>
	 * <li>No key occurs as a subexpression of any value or of any other key.
	 * </li>
	 * <li>For each entry, the key is a {@link SymbolicConstant} or the value is
	 * a constant. [Note: this may change in the future.]</li>
	 * <li>If the type of an entry is real, the key is a {@link Monic}. If that
	 * {@link Monic} is a {@link Polynomial}, its constant term is 0.</li>
	 * <li>If the type of an entry is integer, the key and value are
	 * {@link Monomial}s, the coefficients of those two {@link Monomials} are
	 * relatively prime, and the key's coefficient is positive.</li>
	 * </ul>
	 * 
	 * Example: subMap: wx->1, y->x Applied to wy -> wx -> 1. Hence substitution
	 * is not necessarily idempotent, even with these assumptions
	 */
	private Map<SymbolicExpression, SymbolicExpression> subMap;

	/**
	 * <p>
	 * Map giving precise range of {@link Monic}s. Associates to each
	 * {@link Monic} a {@link Range} such that the set of all possible values
	 * the monic can assume are contained in that range. Monics that have a
	 * single concrete value are removed from this map and placed in the
	 * {@link #subMap}. No solved variables can occur in this map.
	 * </p>
	 * 
	 * <p>
	 * This map is used to form the assumption (full and reduced).
	 * </p>
	 */
	private Map<Monic, Range> rangeMap;

	/**
	 * A cache of all simplifications computed under this {@link Context2}. For
	 * any entry (x,y), the following formula must be valid: context -> x=y.
	 */
	private Map<SymbolicObject, SymbolicObject> simplificationCache;

	/**
	 * An object that gathers together references to various tools that are
	 * needed for this class to do its work.
	 */
	private SimplifierInfo info;

	// Static methods ...

	@SuppressWarnings("unchecked")
	private static <S, T> TreeMap<S, T> cloneTreeMap(Map<S, T> map) {
		if (map == null)
			return null;
		else
			return (TreeMap<S, T>) ((TreeMap<?, ?>) map).clone();
	}

	// Constructors ...

	private Context2(SimplifierInfo info,
			Map<SymbolicExpression, SymbolicExpression> subMap,
			Map<Monic, Range> rangeMap) {
		this.info = info;
		this.subMap = subMap;
		this.rangeMap = rangeMap;
		// can also use a TreeMap, but HashMap seems faster...
		// this.simplificationCache = new TreeMap<SymbolicObject,
		// SymbolicObject>(info.universe.comparator());
		this.simplificationCache = new HashMap<>();
	}

	/**
	 * Constructs new {@link Context2} with all empty maps.
	 * 
	 * @param info
	 *            info structure with references to commonly-used factories and
	 *            other objects
	 */
	protected Context2(SimplifierInfo info) {
		this(info, new TreeMap<>(info.universe.comparator()),
				new TreeMap<>(info.idealFactory.monicComparator()));
	}

	/**
	 * Create context from the given assumption. The assumption is parsed and
	 * process to populate the fields of this context.
	 * 
	 * @param info
	 *            info structure with references to commonly-used factories and
	 *            other objects
	 * @param assumption
	 *            the assumption this context will represent
	 */
	public Context2(SimplifierInfo info, BooleanExpression assumption) {
		this(info);
		initialize(assumption);
	}

	// ************************** Private methods **************************

	/**
	 * Returns the boolean formula represented by this context.
	 * 
	 * @param full
	 *            should the formula include the solved variables?
	 * @return the boolean formula as specified
	 */
	private BooleanExpression getAssumption(boolean full) {
		BooleanExpression result = info.trueExpr;

		for (Entry<SymbolicExpression, SymbolicExpression> subEntry : subMap
				.entrySet()) {
			SymbolicExpression key = subEntry.getKey();

			if (full || !(key instanceof SymbolicConstant))
				result = info.universe.and(result,
						info.universe.equals(key, subEntry.getValue()));
		}
		for (Entry<Monic, Range> rangeEntry : rangeMap.entrySet())
			result = info.universe.and(result,
					rangeEntry.getValue().symbolicRepresentation(
							rangeEntry.getKey(), info.universe));
		// for (List<ArrayFact> list : arrayFacts.values())
		// for (ArrayFact fact : list)
		// result = info.universe.and(result, arrayFactToExpression(fact));
		return result;
	}

	/**
	 * TODO: call this whenever a numeric entry is made to the subMap.
	 * 
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

				cacheSimplification(original, constant);
			}
		}
	}

	private <S, T> void printMap(PrintStream out, Map<S, T> map) {
		for (Entry<S, T> entry : map.entrySet()) {
			out.println("  " + entry.getKey() + " : " + entry.getValue());
		}
		out.flush();
	}

	/**
	 * Transforms a pair of {@link Monomial} by dividing both elements by an
	 * appropriate constant so that (1) if the type is real, the coefficient for
	 * the left component is 1; (2) if the type is integer, the coefficient for
	 * the left component is positive and the GCD of the absolute values of the
	 * left and right coefficients is 1.
	 * 
	 * @param pair
	 *            a pair of non-<code>null</code> {@link Monomial}s of the same
	 *            type
	 */
	private void monicizeMonomialPair(Pair<Monomial, Monomial> pair) {
		Monomial x = pair.left;

		if (x instanceof Monic)
			return;

		Monomial y = pair.right;
		IdealFactory idf = info.idealFactory;
		NumberFactory nf = info.numberFactory;
		PreUniverse universe = info.universe;
		Constant constant = ((Monomial) x).monomialConstant(idf);
		Monic xMonic = ((Monomial) x).monic(idf);

		if (x.type().isReal()) {
			pair.left = xMonic;
			pair.right = (Monomial) universe.divide(y, constant);
		} else {
			IntegerNumber yCoefficient = (IntegerNumber) y.monomialConstant(idf)
					.number();
			IntegerNumber xCoefficient = (IntegerNumber) constant.number();
			boolean negate = xCoefficient.signum() < 0;
			IntegerNumber xCoefficientAbs = negate ? nf.negate(xCoefficient)
					: xCoefficient;
			IntegerNumber gcd = nf.gcd(xCoefficientAbs,
					(IntegerNumber) nf.abs(yCoefficient));

			if (gcd.isOne()) {
				if (negate) {
					pair.left = (Monomial) universe.minus(x);
					pair.right = (Monomial) universe.minus(y);
				}
			} else {
				pair.left = idf.monomial(
						idf.constant(nf.divide(xCoefficientAbs, gcd)), xMonic);
				pair.right = idf
						.monomial(
								idf.constant(negate
										? nf.negate(
												nf.divide(yCoefficient, gcd))
										: nf.divide(yCoefficient, gcd)),
								y.monic(idf));
			}
		}
	}

	/**
	 * Given a substitution x->y in which both x and y are {@link Monomial}s,
	 * transform that substitution into a standard form. In the standard form, x
	 * and y are the equivalent symbolic expressions, x is a {@link Monic}, and
	 * if x is a {@link Polynomial} then its constant term is 0. If in the
	 * process of transformation it is determined that x and y are equivalent,
	 * both fields of the pair will be set to <code>null</code>
	 * 
	 * @param pair
	 *            a substitution pair specifying a value x and the value y that
	 *            is to be substituted for x
	 */
	private void standardizeMonomialPair(Pair<Monomial, Monomial> pair) {
		IdealFactory idf = info.idealFactory;
		PreUniverse universe = info.universe;

		while (true) {
			monicizeMonomialPair(pair);
			if (pair.left instanceof Polynomial) {
				Polynomial poly = (Polynomial) pair.left;
				Constant c = poly.constantTerm(idf);

				if (c.isZero())
					break;
				else {
					pair.left = (Monomial) universe.subtract(poly, c);
					pair.right = (Monomial) universe.add(pair.right, c);
				}
			} else { // pair.left is a Monic and not a Polynomial
				break;
			}
		}
		if (pair.left.equals(pair.right)) {
			pair.left = null;
			pair.right = null;
		}
	}

	/**
	 * Places a substitution pair into a standard form. If the original pair is
	 * (x,y) and the new pair is (x',y') then the following formula will be
	 * valid: x=y -> x'=y'.
	 * 
	 * If in the new pair, x and y are the same symbolic expression, both
	 * components of the pair will be set to <code>null</code>.
	 * 
	 * @param pair
	 *            a substitution pair
	 */
	private void standardizePair(
			Pair<SymbolicExpression, SymbolicExpression> pair) {
		if (!pair.left.isNumeric()) {
			if (pair.left.equals(pair.right)) {
				pair.left = null;
				pair.right = null;
			}
		} else {
			assert pair.left instanceof Monomial;
			assert pair.right instanceof Monomial;

			@SuppressWarnings("unchecked")
			Pair<Monomial, Monomial> monomialPair = (Pair<Monomial, Monomial>) (Pair<?, ?>) pair;

			standardizeMonomialPair(monomialPair);
		}
	}

	private SymbolicExpression simplify(SymbolicExpression expr) {
		return new IdealSimplifierWorker2(info, this)
				.simplifyExpressionWork(expr);
		// this should do transitive closure of substitution
	}

	private SymbolicExpression transClose(UnaryOperator<SymbolicExpression> op,
			SymbolicExpression x) {
		SymbolicExpression y = op.apply(x);

		while (x != y) {
			x = y;
			y = op.apply(x);
		}
		return y;
	}

	/**
	 * Declares that <code>key</code> is bounded by <code>bound</code>, hence
	 * any existing bound I associated to <code>key</code> will be replaced by
	 * the intersection of I and <code>bound</code>.
	 * 
	 * Precondition: <code>range</code> is not empty.
	 * 
	 * @param key
	 *            a non-<code>null</code> {@link Monic}
	 * @param range
	 *            a non-empty range of the same type as <code>key</code>
	 *            containing all possible values of <code>key</code>
	 * @return the old bound associated to <code>key</code>, or
	 *         <code>null</code> if there was none
	 * @throws InconsistentContextException
	 *             if the new restricted range is empty
	 */
	private Range restrictRange(Monic key, Range range)
			throws InconsistentContextException {
		Range original = rangeMap.get(key), result;

		if (original == null) {
			result = range;
			rangeMap.put(key, result);
		} else {
			result = info.rangeFactory.intersect(original, range);
			if (!result.equals(original)) {
				if (result.isEmpty())
					throw new InconsistentContextException();
				rangeMap.put(key, result);
			}
		}
		return original;
	}

	/**
	 * Attempts to determine whether the formula <code>value1==value2</code> is
	 * unsatisfiable.
	 * 
	 * @param value1
	 *            a non-<code>null</code> symbolic expression
	 * @param value2
	 *            a non-<code>null</code> symbolic expression of type compatible
	 *            with that of <code>value1</code>
	 * @return
	 */
	private boolean inconsistent(SymbolicExpression value1,
			SymbolicExpression value2) {
		if (value1.operator() == SymbolicOperator.CONCRETE
				&& value2.operator() == SymbolicOperator.CONCRETE) {
			return !value1.equals(value2);
		}
		return false;
	}

	/**
	 * Incorporates a new substitution into the {@link #subMap}. Updates the
	 * {@link #subMap} as needed in order to maintain its invariants.
	 * 
	 * Preconditions: (1) both expressions are non-null and have the same type;
	 * (2) the new substitution cannot introduce a cycle in the {@link #subMap};
	 * (3) the substitution may not involve any {@link RationalExpression}s.
	 * 
	 * Inconsistency can be determined if the same key is mapped to two nonequal
	 * constants.
	 * 
	 * 
	 * @param x
	 *            the expression to be replaced
	 * @param y
	 *            the expression that will be substituted for <code>x</code>
	 */
	private void addSub(SymbolicExpression x, SymbolicExpression y)
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
			SymbolicExpression oldValue = subMap.get(newKey);

			if (oldValue.equals(newValue))
				continue; // this sub is already in the subMap
			if (inconsistent(oldValue, newValue))
				throw new InconsistentContextException();
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
					workList.add(new Pair<>(subKey, subValue));
				}
			}
			subMap.put(newKey, newValue);
		}
	}

	/**
	 * Transforms a claim that a monomial lies in a range to an equivalent
	 * (normalized) form in which the monomial is a {@link Monic}, and if that
	 * {@link Monic} is a {@link Polynomial}, its constant term is 0.
	 * 
	 * @param monomial
	 *            a non-<code>null</code> {@link Monomial}
	 * @param range
	 *            a non-<code>null</code> {@link Range}, with the same type as
	 *            <code>monomial</code>
	 * @return a pair consisting of a {@link Monic} and a {@link Range}
	 */
	private Pair<Monic, Range> getMonicRange(Monomial monomial, Range range) {
		IdealFactory idf = info.idealFactory;

		while (true) {
			if (!(monomial instanceof Monic)) {
				Constant c = monomial.monomialConstant(idf);

				monomial = monomial.monic(idf);
				range = info.rangeFactory.divide(range, c.number());
			}
			// now monomial is a Monic
			if (monomial instanceof Polynomial) {
				Polynomial poly = (Polynomial) monomial;
				Constant constantTerm = poly.constantTerm(idf);
				Number constantTermNumber = constantTerm.number();

				if (constantTermNumber.isZero())
					break;
				range = info.rangeFactory.subtract(range, constantTermNumber);
				monomial = (Monomial) info.universe.subtract(poly,
						constantTerm);
			}
		}
		return new Pair<>((Monic) monomial, range);
	}

	/**
	 * Simplifies the {@link #rangeMap}. Removes one entry from the map,
	 * simplifies it, places it back. Repeats cyclically until stabilization. If
	 * an entry ever resolves to a single value, it is removed completely and
	 * added to the {@link #subMap}.
	 * 
	 * @return <code>true</code> iff any change was made to the
	 *         {@link #rangeMap}
	 */
	private boolean simplifyRangeMap() throws InconsistentContextException {
		FastList<Monic> keyList = new FastList<>();
		boolean change = false;

		for (Monic key : rangeMap.keySet())
			keyList.add(key);

		FastNode<Monic> curr = keyList.getFirst(),
				lastChanged = keyList.getLast();

		while (true) {
			Monic key = curr.getData();
			NumericExpression simpKey = (NumericExpression) simplify(key);

			if (simpKey == key) {
				if (lastChanged == curr)
					break;
				else
					curr = keyList.getNextCyclic(curr);
			} else { // a change has occurred: update rangeMap
				Range range = rangeMap.get(key);

				change = true;
				if (range != null) {
					// We assume simpKey is not a RationalExpression
					Pair<Monic, Range> normalization = getMonicRange(
							(Monomial) simpKey, range);
					Monic newKey = normalization.left;

					range = normalization.right;

					// TODO: if range is empty, this is inconsistent?

					// TODO: does the correctness of this method
					// depend on the fact that ranges are precise
					// representations of inequalities? I.e.,
					// no information can be lost?

					Number value = range.getSingletonValue();

					if (value == null) {
						rangeMap.remove(key);

						Range oldRange = restrictRange(newKey, range);

						if (oldRange == null) {
							curr.setData(newKey);
							lastChanged = curr;
							curr = keyList.getNextCyclic(curr);
							continue;
						}
					} else {
						addSub(newKey, info.universe.number(value));
					}
				}

				// remove current node...
				FastNode<Monic> next = keyList.getNextCyclic(curr);

				keyList.remove(curr);
				if (keyList.isEmpty())
					break;
				curr = next;
				lastChanged = keyList.getPrevCyclic(curr);
			}
		}
		return change;
	}

	private void makeInconsistent() {
		rangeMap.clear();
		subMap.clear();
		subMap.clear();
		// arrayFacts.clear();
		subMap.put(info.falseExpr, info.trueExpr);
	}

	// /**
	// * Removes any bound associated to <code>key</code> Updates the change
	// flag
	// * if a bound was previously present.
	// *
	// * @param key
	// * a non-<code>null</code> {@link Monic}
	// * @return the old interval bound associated to <code>key</code>, or
	// * <code>null</code> if no bound was associated to <code>key</code>
	// */
	// private Range removeRange(Monic key) {
	// Range result = rangeMap.remove(key);
	//
	// return result;
	// }
	//
	// private Range restrictLowerBound(Monic key, Number value, boolean strict)
	// {
	// Range original = getRange(key);
	// boolean isIntegral = key.type().isInteger();
	// Range result = info.rangeFactory.interval(isIntegral, value, strict,
	// info.numberFactory.infiniteNumber(isIntegral, true), true);
	//
	// if (original == null) {
	// rangeMap.put(key, result);
	// } else {
	// result = info.rangeFactory.intersect(original, result);
	// if (!result.equals(original)) {
	// rangeMap.put(key, result);
	// }
	// }
	// return result;
	// }
	//
	// private Range restrictUpperBound(Monic key, Number value, boolean strict)
	// {
	// Range original = getRange(key);
	// boolean isIntegral = key.type().isInteger();
	// Range result = info.rangeFactory.interval(isIntegral,
	// info.numberFactory.infiniteNumber(isIntegral, false), true,
	// value, strict);
	//
	// if (original == null) {
	// rangeMap.put(key, result);
	// } else {
	// result = info.rangeFactory.intersect(original, result);
	// if (!result.equals(original)) {
	// rangeMap.put(key, result);
	// }
	// }
	// return result;
	// }

	private void addMonicConstantsToMap(Map<Monic, Number> map) {
		for (Entry<SymbolicExpression, SymbolicExpression> entry : subMap
				.entrySet()) {
			SymbolicExpression key = entry.getKey();

			if (key instanceof Monic) {
				SymbolicExpression value = entry.getValue();

				if (value instanceof Constant) {
					map.put((Monic) key, ((Constant) value).number());
				}
			}
		}
	}

	private Map<Monic, Number> getMonicConstantMap() {
		Map<Monic, Number> result = new TreeMap<>(info.monicComparator);

		addMonicConstantsToMap(result);
		return result;
	}

	/**
	 * Performs Gaussian Elimination on the numeric entries of the
	 * {@link #subMap}.
	 * 
	 * Does not read or modify {@link #rangeMap}
	 * 
	 * @return <code>true</code> iff there is a change made to the
	 *         {@link #subMap}
	 * 
	 * @throws InconsistentContextException
	 *             if an inconsistency is detected when modifying the
	 *             {@link #subMap}
	 */
	private boolean gauss() throws InconsistentContextException {
		Map<Monic, Number> constantMap = getMonicConstantMap();
		boolean change = false;

		if (!LinearSolver.reduceConstantMap(info.idealFactory, constantMap))
			throw new InconsistentContextException();
		for (Entry<Monic, Number> entry : constantMap.entrySet()) {
			Monic key = entry.getKey();
			Number newNumber = entry.getValue();
			SymbolicExpression oldValue = subMap.get(key);

			if (oldValue instanceof Constant) {
				assert ((Constant) oldValue).number().equals(newNumber);
				// must be the case or else the LinearSolver would
				// have returned inconsistent (false)
			} else {
				SymbolicExpression newValue = info.universe.number(newNumber);

				subMap.put(key, newValue);
				change = change || !oldValue.equals(newValue);
			}
		}
		if (debug) {
			info.out.println("Result of updateConstantMap():");
			print(info.out);
		}
		return change;
	}

	private void addFact(BooleanExpression fact)
			throws InconsistentContextException {

		// TODO
		// process this boolean expression and update the state of this
		// context appropriately.
		// formerly known as "extract..."
	}

	/**
	 * Reduces the context to an equivalent but simplified form.
	 */
	private void reduce() throws InconsistentContextException {
		simplifyRangeMap();

		boolean change = gauss();

		while (change) {
			change = simplifyRangeMap() && gauss();
		}
	}

	// ********************* Package-private methods **********************

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
		for (Entry<SymbolicExpression, SymbolicExpression> entry : subMap
				.entrySet()) {
			if (!entry.getValue().isTrue())
				continue;

			BooleanExpression clause = (BooleanExpression) entry.getKey();

			if (clause.operator() != SymbolicOperator.DIFFERENTIABLE)
				continue;
			if (clause.argument(0).equals(function))
				return clause;
		}
		return null;
	}

	// protected

	protected void initialize(BooleanExpression assumption) {
		try {
			addFact(assumption);
			reduce();
		} catch (InconsistentContextException e) {
			makeInconsistent();
		}
	}

	// ************************** Public methods **************************

	// methods specified in Object ...

	@Override
	public Context2 clone() {
		return new Context2(info, cloneTreeMap(subMap), cloneTreeMap(rangeMap));
	}

	// methods specified in ContextIF ...

	@Override
	public SymbolicExpression getSub(SymbolicExpression key) {
		return subMap.get(key);
	}

	/**
	 * Retrieves the range associated to <code>key</code>.
	 * 
	 * @param key
	 *            a non-<code>null</code> {@link Monic}
	 * @return the range associated to <code>key</code> or <code>null</code> if
	 *         there is no such range
	 */
	@Override
	public Range getRange(Monic key) {
		return rangeMap.get(key);
	}

	@Override
	public void cacheSimplification(SymbolicObject key, SymbolicObject value) {
		simplificationCache.put(key, value);
	}

	@Override
	public SymbolicObject getSimplification(SymbolicObject key) {
		return simplificationCache.get(key);
	}

	@Override
	public void clearSimplificationCache() {
		simplificationCache.clear();
	}

	// other public methods ...

	public BooleanExpression getReducedAssumption() {
		return getAssumption(false);
	}

	public BooleanExpression getFullAssumption() {
		return getAssumption(true);
	}

	public boolean isInconsistent() {
		SymbolicExpression result = subMap.get(info.falseExpr);

		return result != null && result.isTrue();
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
				info.variableComparator);

		for (Entry<SymbolicExpression, SymbolicExpression> entry : subMap
				.entrySet()) {
			SymbolicExpression key = entry.getKey();

			if (key instanceof SymbolicConstant)
				solvedVariables.put((SymbolicConstant) key, entry.getValue());
		}
		return solvedVariables;
	}

	public Interval assumptionAsInterval(SymbolicConstant symbolicConstant) {
		// if (!arrayFacts.isEmpty())
		// return null;
		if (!subMap.isEmpty()) {
			if (!rangeMap.isEmpty() || subMap.size() != 1)
				return null;

			Entry<SymbolicExpression, SymbolicExpression> entry = subMap
					.entrySet().iterator().next();

			if (!entry.getKey().equals(symbolicConstant))
				return null;

			SymbolicExpression value = entry.getValue();

			if (!(value instanceof Constant))
				return null;
			return info.numberFactory
					.singletonInterval(((Constant) value).number());
		}
		if (rangeMap.size() == 1) {
			Entry<Monic, Range> entry = rangeMap.entrySet().iterator().next();

			if (!entry.getKey().equals(symbolicConstant))
				return null;

			Range range = entry.getValue();

			return range.asInterval();
		}
		return null;
	}

	public void print(PrintStream out) {
		out.println("subMap:");
		printMap(out, subMap);
		out.println("rangeMap:");
		printMap(out, rangeMap);
		out.flush();
	}

}
