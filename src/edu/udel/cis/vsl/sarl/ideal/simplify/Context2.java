package edu.udel.cis.vsl.sarl.ideal.simplify;

import static edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator.LESS_THAN;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;

import edu.udel.cis.vsl.sarl.IF.CoreUniverse.ForallStructure;
import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.object.BooleanObject;
import edu.udel.cis.vsl.sarl.IF.object.NumberObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.ideal.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Polynomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal.IF.PrimitivePower;
import edu.udel.cis.vsl.sarl.ideal.IF.RationalExpression;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.simplify.IF.Range;
import edu.udel.cis.vsl.sarl.simplify.IF.RangeFactory;
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
	 * TODO: don't you want pseudo form? Leading coefficient of x to be 1 if
	 * real, else gcd=1 ?  (YES, the comment just doesn't say it)
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
	 * Declares that the values taken on by <code>key</code> are contained in
	 * <code>range</code>, modifying the state of this context accordingly. An
	 * existing range R associated to <code>key</code> will be replaced by the
	 * intersection of R and <code>range</code>. If this results in a singleton
	 * value, the entry is removed from the {@link #rangeMap} altogether and and
	 * is entered into the {@link #subMap}.
	 * 
	 * @param key
	 *            a non-<code>null</code> {@link Monic}
	 * @param range
	 *            a non-empty range of the same type as <code>key</code>
	 *            containing all possible values of <code>key</code>
	 * @return a {@link Pair} consisting of the old range associated to
	 *         <code>key</code> (or <code>null</code> if there was none) and the
	 *         new range associated to <code>key</code>
	 * @throws InconsistentContextException
	 *             if the new restricted range is empty or an inconsistency is
	 *             detected when updating the {@link #subMap}
	 */
	private Pair<Range, Range> restrictRange(Monic key, Range range)
			throws InconsistentContextException {
		Range original = rangeMap.get(key), result;

		if (original == null) {
			result = range;
		} else {
			result = info.rangeFactory.intersect(original, range);
			if (result == original)
				return new Pair<>(original, result);
		}
		if (result.isEmpty())
			throw new InconsistentContextException();

		Number value = result.getSingletonValue();

		if (value == null) {
			rangeMap.put(key, result);
		} else {
			addSub(key, info.universe.number(value));
			if (original != null)
				rangeMap.remove(key);
		}
		return new Pair<>(original, result);
	}

	private Range getGeneralRange(Monic monic) {
		Range range = rangeMap.get(monic);

		if (range == null) {
			SymbolicExpression value = subMap.get(monic);

			if (value instanceof Constant)
				range = info.rangeFactory
						.singletonSet(((Constant) value).number());
		}
		return range;
	}

	private boolean containsZero(Range range) {
		Number zero = range.isIntegral() ? info.numberFactory.zeroInteger()
				: info.numberFactory.zeroRational();

		return range.containsNumber(zero);
	}

	// /**
	// * Attempts to determine whether the formula <code>value1==value2</code>
	// is
	// * unsatisfiable.
	// *
	// * @param value1
	// * a non-<code>null</code> symbolic expression
	// * @param value2
	// * a non-<code>null</code> symbolic expression of type compatible
	// * with that of <code>value1</code>
	// * @return
	// */
	// private boolean inconsistent(SymbolicExpression value1,
	// SymbolicExpression value2) {
	// if (value1.operator() == SymbolicOperator.CONCRETE
	// && value2.operator() == SymbolicOperator.CONCRETE) {
	// return !value1.equals(value2);
	// }
	// return false;
	// }

	private SymbolicExpression updateSub(SymbolicExpression key,
			SymbolicExpression value) throws InconsistentContextException {
		SymbolicExpression old = subMap.put(key, value);

		if (old != null && value.operator() == SymbolicOperator.CONCRETE
				&& old.operator() == SymbolicOperator.CONCRETE
				&& old != value) {
			throw new InconsistentContextException();
		}
		return old;
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
			updateSub(newKey, newValue);
		}
	}

	/**
	 * Transforms a claim that a non-constant monomial lies in a range to an
	 * equivalent (normalized) form in which the monomial is a {@link Monic},
	 * and if that {@link Monic} is a {@link Polynomial}, its constant term is
	 * 0.
	 * 
	 * @param monomial
	 *            a non-<code>null</code>, non-{@link Constant} {@link Monomial}
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

		// idea: keep iterating cyclically over the keys of the
		// rangeMap until it stabilizes. They keys are changing
		// as you iterate.
		// invariant: keyList is a list containing all the keys in the rangeMap
		// (and possibly additional expressions not keys in the rangeMap)
		// lastChanged is the last node to have changed in some way.
		// curr is the current node.
		while (true) {
			Monic oldKey = curr.getData();
			NumericExpression simpKey = (NumericExpression) simplify(oldKey);

			if (simpKey == oldKey) { // no change
				if (lastChanged == curr)
					break; // complete cycle with no change: done!
				curr = keyList.getNextCyclic(curr);
				continue;
			}
			// a change has occurred: simpKey!=oldKey
			// remove oldKey, update rangeMap and/or subMap

			Range oldRange = rangeMap.remove(oldKey);

			if (oldRange != null) {
				change = true;

				// if simpKey is Constant, it is either in the range or not
				if (simpKey instanceof Constant) {
					if (!oldRange.containsNumber(((Constant) simpKey).number()))
						throw new InconsistentContextException();
				} else {
					// We assume simpKey is not a RationalExpression...
					Pair<Monic, Range> normalization = getMonicRange(
							(Monomial) simpKey, oldRange);
					Monic newKey = normalization.left;
					Pair<Range, Range> pair = restrictRange(newKey,
							normalization.right);

					if (pair.left == null
							&& pair.right.getSingletonValue() == null) {
						// oldKey has been removed. newKey was not in the map
						// and now it is. So replace oldKey with newKey in the
						// list.
						curr.setData(newKey);
						lastChanged = curr;
						curr = keyList.getNextCyclic(curr);
						continue;
					}
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
				// must be the case, else the LinearSolver would
				// have returned inconsistent (false)
			} else {
				SymbolicExpression newValue = info.universe.number(newNumber);

				if (oldValue != newValue) {
					change = true;
					addSub(key, newValue);
				}
			}
		}
		if (debug) {
			info.out.println("Result of updateConstantMap():");
			print(info.out);
		}
		return change;
	}

	/**
	 * Processes a boolean expression, updating the state of this context
	 * appropriately. The boolean expression must be in CNF (conjunctive normal
	 * form).
	 * 
	 * @param assumption
	 *            the boolean expression to process
	 * @throws InconsistentContextException
	 *             if this context is determined to be inconsistent
	 */
	private void addFact(BooleanExpression assumption)
			throws InconsistentContextException {
		if (assumption.operator() == SymbolicOperator.AND) {
			for (SymbolicObject arg : assumption.getArguments()) {
				BooleanExpression clause = (BooleanExpression) arg;

				extractOr(clause);
			}
		} else {
			extractOr(assumption);
		}
	}

	/**
	 * Processes an expression in which the operator is not
	 * {@link SymbolicOperator#AND}. In the CNF form, this expression is a
	 * clause of the outer "and" expression.
	 * 
	 * @param or
	 *            the boolean expression to process
	 * @throws InconsistentContextException
	 *             if this context is determined to be inconsistent
	 */
	private void extractOr(BooleanExpression or)
			throws InconsistentContextException {
		if (or.operator() != SymbolicOperator.OR)
			extractClause(or);
		or = info.universe.not(new SubContext(info, this, info.universe.not(or))
				.getFullAssumption());
		if (or.operator() == SymbolicOperator.OR) {
			addSub(or, info.trueExpr);
		} else {
			addFact(or);
		}
	}

	/**
	 * Processes a basic boolean expression --- one in which the operator is
	 * neither {@link SymbolicOperator#AND} nor {@link SymbolicOperator#OR} ---
	 * and updates this context accordingly.
	 * 
	 * @param clause
	 *            the expression which is not an "and" or "or" expression
	 * @throws InconsistentContextException
	 *             if this context is determined to be inconsistent
	 */
	private void extractClause(BooleanExpression clause)
			throws InconsistentContextException {
		SymbolicOperator op = clause.operator();

		switch (op) {
		case CONCRETE:
			if (!((BooleanObject) clause.argument(0)).getBoolean())
				throw new InconsistentContextException();
			break;
		case NOT:
			extractNot((BooleanExpression) clause.argument(0));
			break;
		case FORALL:
			extractForall(clause);
			break;
		case EXISTS:
			extractExists(clause);
			break;
		case EQUALS:
			extractEquals(clause);
			break;
		case NEQ:
			extractNEQ((SymbolicExpression) clause.argument(0),
					(SymbolicExpression) clause.argument(1));
			break;
		case LESS_THAN: // 0<x or x<0
		case LESS_THAN_EQUALS: {// 0<=x or x<=0
			SymbolicExpression arg0 = (SymbolicExpression) clause.argument(0),
					arg1 = (SymbolicExpression) clause.argument(1);

			if (arg0.isZero()) {
				extractIneq((Monic) arg1, true, op == LESS_THAN);
			} else {
				extractIneq((Monic) arg0, false, op == LESS_THAN);
			}
			break;
		}
		default:
			addSub(clause, info.trueExpr);
		}
	}

	private void extractNot(BooleanExpression pred)
			throws InconsistentContextException {
		addSub(pred, info.falseExpr);
	}

	/**
	 * Processes an equality expression and updates the state of this context
	 * accordingly.
	 * 
	 * @param eqExpr
	 *            a symbolic expression in which the operator is
	 *            {@link SymbolicOperator#EQUALS}
	 * @throws InconsistentContextException
	 *             if this context is determined to be inconsistent
	 */
	private void extractEquals(SymbolicExpression eqExpr)
			throws InconsistentContextException {
		SymbolicExpression arg0 = (SymbolicExpression) eqExpr.argument(0);
		SymbolicExpression arg1 = (SymbolicExpression) eqExpr.argument(1);

		if (arg0.type().isNumeric()) { // 0=x for a Primitive x
			extractEQ0((Primitive) arg1);
		} else {
			boolean const0 = arg0.operator() == SymbolicOperator.CONCRETE;
			boolean const1 = arg1.operator() == SymbolicOperator.CONCRETE;

			if (const1 && !const0) {
				addSub(arg0, arg1);
			} else if (const0 && !const1) {
				addSub(arg1, arg0);
			} else if (const0 && const1) {
				if (!arg0.equals(arg1))
					throw new InconsistentContextException();
			} else { // neither is constant
				addSub(eqExpr, info.trueExpr);
			}
		}
	}

	/**
	 * Processes an equality of the form x=0, for a {@link Primitive} x,
	 * updating the state of this context based on that fact.
	 * 
	 * @param primitive
	 *            a non-<code>null</code> numeric {@link Primitive}
	 * @throws InconsistentContextException
	 *             if this context is determined to be inconsistent
	 */
	private void extractEQ0(Primitive primitive)
			throws InconsistentContextException {
		// TODO: probabilistic technique?
		addSub(primitive, info.idealFactory.zero(primitive.type()));
	}

	private void extractNEQ(SymbolicExpression arg0, SymbolicExpression arg1)
			throws InconsistentContextException {
		SymbolicType type = arg0.type();

		if (type.isNumeric()) { // 0!=x, for a Primitive x
			Primitive primitive = (Primitive) arg1;
			RangeFactory rf = info.rangeFactory;
			Number zero = type.isInteger() ? info.numberFactory.zeroInteger()
					: info.numberFactory.zeroRational();

			restrictRange(primitive, rf.complement(rf.singletonSet(zero)));
		} else {
			addSub(info.universe.equals(arg0, arg1), info.falseExpr);
		}
	}

	/**
	 * Processes a numeric inequality and updates the state of this context
	 * accordingly. The inequality has one of the forms: 0&lt;x, 0&le;x, x&lt;0,
	 * or x&le;0.
	 * 
	 * @param monic
	 *            a non-<code>null</code> {@link Monic} (x) which is being
	 *            compared to 0
	 * @param gt
	 *            is the inequality stating that <code>monic</code> is greater
	 *            than (or greater than or equal to) 0? I.e., is the inequality
	 *            form one of 0&lt;x, 0&le;x ?
	 * @param strict
	 *            is the inequality strict, i.e., either of the form 0&lt;x or
	 *            x&lt;0 ?
	 * @throws InconsistentContextException
	 *             if an inconsistency is this context is detected
	 */
	private void extractIneq(Monic monic, boolean gt, boolean strict)
			throws InconsistentContextException {
		NumberFactory nf = info.numberFactory;
		RangeFactory rf = info.rangeFactory;
		boolean isIntegral = monic.type().isInteger();
		Number zero = isIntegral ? nf.zeroInteger() : nf.zeroRational();
		Range range;
		
		if (monic instanceof Polynomial) {
			// example: 0<=2x+2y+3 ---> -3<=2(x+y) ---> -3/2<=x+y ---> 
		}

		if (gt) {
			range = rf.interval(isIntegral, zero, strict,
					nf.infiniteNumber(isIntegral, true), true);
		} else {
			range = rf.interval(isIntegral,
					nf.infiniteNumber(isIntegral, false), true, zero, strict);
		}
		// Convert monic and range together...
		// if monic is a polynomial, get it into affine form
		
	}

	/**
	 * Looks for the pattern: <code>forall int i . 0<=i<=n-1 -> a[i]=expr</code>
	 * . If that pattern is found, adds the substitution to the {@link #subMap}:
	 * <code>a = (T[n]) lambda i . expr</code>. Otherwise, just adds the default
	 * substitution mapping <code>forallExpr</code> to <code>true</code>.
	 * 
	 * @param forallExpr
	 *            an expression in which the operator is
	 *            {@link SymbolicOperator#FORALL}.
	 * @throws InconsistentContextException
	 *             this context is determined to be inconsistent
	 */
	private void extractForall(BooleanExpression forallExpr)
			throws InconsistentContextException {
		ArrayDefinition defn = extractArrayDefinition(forallExpr);

		if (defn != null && defn.array
				.operator() == SymbolicOperator.SYMBOLIC_CONSTANT) {
			addSub(defn.array, defn.lambda);
		} else {
			addSub(forallExpr, info.trueExpr);
		}
	}

	private void extractExists(SymbolicExpression existsExpr)
			throws InconsistentContextException {
		addSub(existsExpr, info.trueExpr);
	}

	// Begin array term analysis....

	/**
	 * Given an <code>equation</code> and a {@link Primitive} <code>p</code>,
	 * attempts to solve for <code>p</code>.
	 * 
	 * @param equation
	 *            an equation that must be off the form 0==x for some numeric
	 *            {@link Primitive} x (this is the canonical form of all numeric
	 *            equations in the {@link IdealFactory}
	 * @param p
	 *            a numeric {@link Primitive}
	 * @return an expression which must be equal to <code>p</code> and does not
	 *         involve <code>p</code>, or <code>null</code> if it could not be
	 *         solved
	 */
	NumericExpression solveFor(Monomial[] terms, Primitive p) {
		int nterms = terms.length;

		if (nterms == 0)
			return null;

		IdealFactory idf = info.idealFactory;
		List<Monomial> deg0List = new LinkedList<>();
		List<Monomial> deg1List = new LinkedList<>();

		for (int i = 0; i < nterms; i++) {
			Monomial term = terms[i];
			Monic monic = term.monic(idf);
			PrimitivePower[] factors = monic.monicFactors(idf);
			int nfactors = factors.length;
			boolean isDeg0 = true;

			for (int j = 0; j < nfactors; j++) {
				PrimitivePower factor = factors[j];

				if (factor.primitive(idf).equals(p)) {
					NumberObject exponent = factor.primitivePowerExponent(idf);

					if (exponent.isOne()) {
						isDeg0 = false;
						break;
					} else {
						// cannot solve non-linear equation -- yet
						return null;
					}
				}
			}
			if (isDeg0)
				deg0List.add(term);
			else
				deg1List.add(term);
		}
		if (deg1List.isEmpty())
			return null;

		SymbolicType type = terms[0].type();
		Monomial zero = idf.zero(type);
		Monomial coefficient = zero;

		for (Monomial term : deg1List) {
			coefficient = idf.addMonomials(coefficient,
					(Monomial) idf.divide(term, p));
		}

		BooleanExpression isNonZero = (BooleanExpression) simplify(
				idf.isNonZero(coefficient));

		if (!isNonZero.isTrue())
			return null;

		NumericExpression offset = info.universe.add(deg0List);
		NumericExpression result = null;

		if (type.isReal()) {
			result = idf.divide(idf.minus(offset), coefficient);
		} else if (coefficient.isOne()) {
			result = idf.minus(offset);
		} else if (idf.minus(coefficient).isOne()) {
			result = offset;
		}
		return result;
	}

	private Iterable<Primitive> findArrayReads(Monomial[] terms,
			NumericSymbolicConstant indexVar) {
		Set<Primitive> nonlinearFactors = new HashSet<>();
		Set<Primitive> linearFactors = new HashSet<>();
		IdealFactory idf = info.idealFactory;

		for (Monomial term : terms) {
			for (PrimitivePower pp : term.monic(idf).monicFactors(idf)) {
				Primitive p = pp.primitive(idf);

				if (p.operator() == SymbolicOperator.ARRAY_READ
						&& p.argument(1).equals(indexVar)
						&& !nonlinearFactors.contains(p)) {
					if (pp.primitivePowerExponent(idf).isOne()) {
						linearFactors.add(p);
					} else {
						linearFactors.remove(p);
						nonlinearFactors.add(p);
					}
				}
			}
		}
		return linearFactors;
	}

	class ArrayEquationSolution {
		SymbolicExpression array;
		SymbolicExpression rhs;
	}

	/**
	 * Given an equation a=b, where a and b are symbolic expressions, and an
	 * integer symbolic constant i, attempts to find an equivalent equation of
	 * the form e[i]=f. If this equivalent form is found, the result is returned
	 * as a structure with the <code>array</code> field e and the
	 * <code>rhs</code> field f.
	 * 
	 * @param equation
	 *            the boolean expression which is an equality
	 * @return a structure as specified above if the equation can be solved, or
	 *         <code>null</code> if <code>equation</code> is not an equality or
	 *         could not be put into that form
	 */
	private ArrayEquationSolution solveArrayEquation(SymbolicExpression arg0,
			SymbolicExpression arg1, NumericSymbolicConstant index) {
		ArrayEquationSolution result;

		if (arg0.operator() == SymbolicOperator.ARRAY_READ
				&& arg0.argument(1).equals(index)) {
			result = new ArrayEquationSolution();
			result.array = (SymbolicExpression) arg0.argument(0);
			result.rhs = arg1;
			return result;
		}
		if (arg1.operator() == SymbolicOperator.ARRAY_READ
				&& arg1.argument(1).equals(index)) {
			result = new ArrayEquationSolution();
			result.array = (SymbolicExpression) arg1.argument(0);
			result.rhs = arg0;
			return result;
		}
		if (arg0.type().isNumeric()) {
			assert arg0.isZero();
			assert arg1 instanceof Primitive;

			IdealFactory idf = info.idealFactory;
			Monomial[] terms = ((Primitive) arg1).expand(idf);

			for (Primitive arrayRead : findArrayReads(terms, index)) {
				NumericExpression solution = solveFor(terms, arrayRead);

				if (solution != null) {
					result = new ArrayEquationSolution();
					result.array = (SymbolicExpression) arrayRead.argument(0);
					result.rhs = solution;
					return result;
				}
			}
		}
		return null;
	}

	/**
	 * A simple structure with two fields: a symbolic expression of array type
	 * and an equivalent array-lambda expression.
	 * 
	 * @see #extractArrayDefinition(BooleanExpression)
	 * 
	 * @author siegel
	 */
	class ArrayDefinition {
		/**
		 * An expression of array type.
		 */
		SymbolicExpression array;

		/**
		 * An {@link SymbolicOperator#ARRAY_LAMBDA} expression equivalent to
		 * {@link #array}.
		 */
		SymbolicExpression lambda;
	}

	/**
	 * If the boolean expression has the form
	 * 
	 * <pre>
	 * forall int i in [0,n-1] . e[i]=f
	 * </pre>
	 * 
	 * where n is an integer expressions not involving i, e has type
	 * "array of length n of T" for some type T, and f is some expression, then
	 * return a structure in which the array field is e and the lambda field is
	 * the expression <code>arraylambda i . f</code>.
	 * 
	 * @param forallExpr
	 *            a boolean expression with operator
	 *            {@link SymbolicOperator#FORALL}
	 * @return if the given boolean expression is a forall expression in the
	 *         form described above, the structure containing the array and the
	 *         array-lambda expression, else <code>null</code>
	 */
	private ArrayDefinition extractArrayDefinition(
			BooleanExpression forallExpr) {
		ForallStructure structure = info.universe
				.getForallStructure(forallExpr);

		if (structure == null)
			return null;

		BooleanExpression body = structure.body;
		NumericSymbolicConstant var = structure.boundVariable;
		ArrayEquationSolution solution = null;

		if (body.operator() == SymbolicOperator.FORALL) {
			ArrayDefinition innerDefn = extractArrayDefinition(body);

			if (innerDefn == null)
				return null;
			solution = solveArrayEquation(innerDefn.array, innerDefn.lambda,
					var);
		} else if (body.operator() == SymbolicOperator.EQUALS) {
			solution = solveArrayEquation((SymbolicExpression) body.argument(0),
					(SymbolicExpression) body.argument(1), var);
		}
		if (solution == null)
			return null;

		SymbolicArrayType arrayType = (SymbolicArrayType) solution.array.type();

		if (!arrayType.isComplete())
			return null;

		SymbolicCompleteArrayType completeType = (SymbolicCompleteArrayType) arrayType;
		NumericExpression length = info.universe.add(structure.upperBound,
				info.universe.oneInt());

		if (structure.lowerBound.isZero() && info.universe
				.equals(length, completeType.extent()).isTrue()) {
			SymbolicExpression lambda = info.universe.arrayLambda(completeType,
					info.universe.lambda(var, solution.rhs));
			ArrayDefinition result = new ArrayDefinition();

			result.array = solution.array;
			result.lambda = lambda;
			return result;
		}
		return null;
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
