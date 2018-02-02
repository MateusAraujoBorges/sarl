package edu.udel.cis.vsl.sarl.ideal.simplify;

import static edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator.LESS_THAN;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;

import edu.udel.cis.vsl.sarl.IF.CoreUniverse.ForallStructure;
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
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
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
import edu.udel.cis.vsl.sarl.number.IF.Numbers;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.simplify.IF.Range;
import edu.udel.cis.vsl.sarl.simplify.IF.RangeFactory;
import edu.udel.cis.vsl.sarl.util.Pair;
import edu.udel.cis.vsl.sarl.util.SingletonMap;
import edu.udel.cis.vsl.sarl.util.WorkMap;

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

	/**
	 * A random number generator with seed very likely to be distinct from all
	 * other seeds. TODO: this must be made thread-safe.
	 */
	private static Random random = new Random();

	/**
	 * Used in a heuristic to determine when to use probabilistic methods to
	 * determine polynomial zero-ness. If the product of the number of variables
	 * and the total degree is greater than or equal to this number, the
	 * polynomial is considered too big to be expanded, and probabilistic
	 * techniques will be used instead (unless the probabilistic bound is 0).
	 */
	private final static IntegerNumber polyProbThreshold = Numbers.REAL_FACTORY
			.integer(100);

	// Instance Fields ...

	// TODO: think about replacing all/some of these memory-inefficient maps
	// with sorted arrays, at least after this Context has been initialized.

	/**
	 * Should backwards substitution be used to solve for variables in terms of
	 * other variables?
	 */
	public final boolean backwardsSub;

	/**
	 * A cache of all simplifications computed under this {@link Context}. For
	 * any entry (x,y), the following formula must be valid: context -> x=y.
	 */
	private Map<SymbolicObject, SymbolicObject> simplificationCache = null;

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
	 * 
	 * <li>If the value of an entry is non-null, it will have a type compatible
	 * with that of the key.</li>
	 * 
	 * <li>No key occurs as a subexpression of any value or of any other key.
	 * </li>
	 * 
	 * <li>For each entry, the key is a {@link SymbolicConstant} or the value is
	 * concrete. [Note: this may change in the future.]</li>
	 * 
	 * <li>If the type of an entry is real, the key is a {@link Monic}. If that
	 * {@link Monic} is a {@link Polynomial}, its constant term is 0.</li>
	 * 
	 * <li>If the type of an entry is integer, the key and value are
	 * {@link Monomial}s, the coefficients of those two {@link Monomials} are
	 * relatively prime, and the key's coefficient is positive. WHY? Suppose
	 * 2X=3Y is an entry. Then X=(3*Y)/2. But the latter form loses information
	 * because the "/" is integer division. It loses the information that Y is
	 * even. However, if the key is a symbolic constant, it is a monic, and if
	 * the value is concrete, then you can always divide both side by the
	 * coefficient, so under the current assumption, the key will always be
	 * monic, and if a polynomial the constant term is 0, exactly as for reals.
	 * </li>
	 * 
	 * </ul>
	 * 
	 * Example: subMap: wx->1, y->x Applied to wy -> wx -> 1. Hence substitution
	 * is not necessarily idempotent, even with these assumptions
	 */
	protected Map<SymbolicExpression, SymbolicExpression> subMap;

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
	protected WorkMap<Monic, Range> rangeMap;

	/**
	 * An object that gathers together references to various tools that are
	 * needed for this class to do its work.
	 */
	protected SimplifierInfo info;

	// Static methods ...

	@SuppressWarnings("unchecked")
	private static <S, T> TreeMap<S, T> cloneTreeMap(Map<S, T> map) {
		if (map == null)
			return null;
		else
			return (TreeMap<S, T>) ((TreeMap<?, ?>) map).clone();
	}

	// Constructors ...

	/**
	 * Constructs new {@link Context} with all empty maps. This represents the
	 * assumption "true". No initialization is done.
	 * 
	 * @param info
	 *            info structure with references to commonly-used factories and
	 *            other objects
	 */
	protected Context(SimplifierInfo info, boolean useBackwardSubstitution) {
		this.info = info;
		this.subMap = new TreeMap<>(info.universe.comparator());
		this.rangeMap = new WorkMap<>(info.idealFactory.monicComparator());
		this.backwardsSub = useBackwardSubstitution;
	}

	/**
	 * Constructs new {@link Context} with given fields. Initialization is
	 * carried out.
	 * 
	 * @param info
	 *            info structure with references to commonly-used factories and
	 *            other objects
	 * @param subMap
	 *            substitution map; see {@link #subMap}
	 * @param rangeMap
	 *            range map; see {@link #rangeMap}
	 */
	protected Context(SimplifierInfo info,
			Map<SymbolicExpression, SymbolicExpression> subMap,
			WorkMap<Monic, Range> rangeMap, boolean useBackwardSubstitution) {
		this.info = info;
		this.subMap = subMap;
		this.rangeMap = rangeMap;
		this.backwardsSub = useBackwardSubstitution;
		initialize(info.trueExpr);
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
	public Context(SimplifierInfo info, BooleanExpression assumption,
			boolean useBackwardSubstitution) {
		this(info, useBackwardSubstitution);
		initialize(assumption);
	}

	// ************************** Private methods **************************

	// *********************************************************************
	// *........................ Utility functions ........................*
	// * These do not use the state. They do not access subMap,rangeMap. ..*
	// *********************************************************************

	/**
	 * Prints the entries of a {@link Map}, putting one entry on each line for
	 * better readability of large {@link Map}s. Flushes the stream at the end.
	 * 
	 * @param out
	 *            the stream to which to print the map
	 * @param map
	 *            a non-<code>null</code> {@link Map} to print
	 */
	private <S, T> void printMap(PrintStream out, Map<S, T> map) {
		for (Entry<S, T> entry : map.entrySet()) {
			out.println("  " + entry.getKey() + " : " + entry.getValue());
		}
		out.flush();
	}

	/**
	 * <p>
	 * Transforms a pair of {@link Monomial} by dividing both elements by an
	 * appropriate constant so that (1) if the type is real, the coefficient for
	 * the left component is 1; (2) if the type is integer, the coefficient for
	 * the left component is positive and the GCD of the absolute values of the
	 * left and right coefficients is 1.
	 * </p>
	 * 
	 * <p>
	 * Example: x is an int, (3x,2). This should be an inconsistency. But
	 * (3x,2y) could be OK. It implies x=(2y) INTDIV 3, but is stronger than
	 * that formula. It is equivalent to (real)x = 2((real)y)/3, but it is
	 * debatable whether you should make this substitution.
	 * </p>
	 * 
	 * @param pair
	 *            a pair of non-<code>null</code> {@link Monomial}s of the same
	 *            type
	 * @throws InconsistentContextException
	 *             if an inconsistency is detected in the course of simplifying
	 *             the equality
	 */
	private void monicizeMonomialPair(Pair<Monomial, Monomial> pair)
			throws InconsistentContextException {
		Monomial x = pair.left;

		if (x instanceof Monic)
			return;

		Monomial y = pair.right;
		IdealFactory idf = info.idealFactory;
		NumberFactory nf = info.numberFactory;
		PreUniverse universe = info.universe;
		Constant constant = x.monomialConstant(idf);
		Monic xMonic = x.monic(idf);

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
			Monic yMonic = y.monic(idf);

			if (gcd.isOne()) {
				if (negate) {
					pair.left = (Monomial) universe.minus(x);
					pair.right = (Monomial) universe.minus(y);
				}
			} else {
				if (yMonic.isOne() && gcd != xCoefficientAbs) {
					// something like 3x=2 can't hold, but 2x=4 is fine...
					throw new InconsistentContextException();
				}
				pair.left = idf.monomial(
						idf.constant(nf.divide(xCoefficientAbs, gcd)), xMonic);
				pair.right = idf
						.monomial(
								idf.constant(negate
										? nf.negate(
												nf.divide(yCoefficient, gcd))
										: nf.divide(yCoefficient, gcd)),
								yMonic);
			}
		}
	}

	/**
	 * <p>
	 * Given a substitution x->y in which both x and y are {@link Monomial}s,
	 * transforms that substitution into a standard form. In the standard form,
	 * x and y are the equivalent symbolic expressions, x is a {@link Monic},
	 * and if x is a {@link Polynomial} then its constant term is 0. Moreover,
	 * (1) if the type is real, the coefficient for the left component is 1; (2)
	 * if the type is integer, the coefficient for the left component is
	 * positive and the GCD of the absolute values of the left and right
	 * coefficients is 1.
	 * </p>
	 * <p>
	 * If in the process of transformation it is determined that x and y are
	 * equivalent, both fields of the pair will be set to <code>null</code>.
	 * </p>
	 * 
	 * @param pair
	 *            a substitution pair specifying a value x and the value y that
	 *            is to be substituted for x
	 * @throws InconsistentContextException
	 *             if the type is integer and an inconsistency is detected such
	 *             as 2x->3
	 */
	private void standardizeMonomialPair(Pair<Monomial, Monomial> pair)
			throws InconsistentContextException {
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
					pair.right = (Monomial) universe.subtract(pair.right, c);
				}
			} else { // pair.left is a Monic and not a Polynomial
				break;
			}
		}
		if (pair.left.equals(pair.right)) {
			pair.left = null;
			pair.right = null;
		} else if (pair.left.isOne() && pair.right instanceof Constant) {
			throw new InconsistentContextException();
		}
	}

	/**
	 * <p>
	 * Places a substitution pair into a standard form. If the original pair is
	 * (x,y) and the new pair is (x',y') then the following formula will be
	 * valid: x=y -> x'=y'.
	 * </p>
	 * <p>
	 * If in the new pair, x and y are the same symbolic expression, both
	 * components of the pair will be set to <code>null</code>.
	 * </p>
	 * 
	 * @param pair
	 *            a substitution pair
	 * @throws InconsistentContextException
	 *             if the type is integer and an inconsistency is detected such
	 *             as 2x->3
	 */
	private void standardizePair(
			Pair<SymbolicExpression, SymbolicExpression> pair)
			throws InconsistentContextException {
		if (pair.left == pair.right) {
			pair.left = null;
			pair.right = null;
			return;
		}
		if (pair.left.type().isIdeal()) {
			if (pair.left.operator() == SymbolicOperator.CAST) {
				// if x has type hint, (int)x->y should be changed to x->(hint)y
				SymbolicType type = pair.left.type();
				SymbolicExpression original = (SymbolicExpression) pair.left
						.argument(0);
				SymbolicType originalType = original.type();

				if (originalType.isHerbrand()
						&& originalType.isInteger() == type.isInteger()) {
					// problem: original expression might not be Monomial. Could
					// be RationalExpression like x/y. Questionable whether such
					// a thing should occur on right side of substitution. If it
					// does, should form the equality expression and process
					// from the beginning.
					pair.left = original;
					pair.right = info.universe.cast(originalType, pair.right);
					return;
				}
			}
			if (!(pair.left instanceof Monomial
					&& pair.right instanceof Monomial)) {
				BooleanExpression equation = info.universe.equals(pair.left,
						pair.right);

				pair.left = (Monomial) equation.argument(0);
				pair.right = (Monomial) equation.argument(1);
			}
			assert pair.left instanceof Monomial;
			assert pair.right instanceof Monomial;

			@SuppressWarnings("unchecked")
			Pair<Monomial, Monomial> monomialPair = (Pair<Monomial, Monomial>) (Pair<?, ?>) pair;

			standardizeMonomialPair(monomialPair);
		}
	}

	// /**
	// * Chooses a random integer with uniform probability from the set of all
	// * 2^32 ints for each "variable" occurring in the polynomial, and
	// evaluates
	// * the polynomial. A "variable" is any maximal sub-expression which is not
	// a
	// * sum or product or difference or negation. Hence the polynomial should
	// * only use +, -, and * to combine the "variable"s into an expression.
	// *
	// * @param poly
	// * the {@link Polynomial} to evaluate
	// * @param map
	// * a {@link Map} with one {@link Entry} for each "variable"
	// * occurring in {@code poly}. The key of the {@link Entry} is the
	// * variable; the value is not used and will be overwritten with
	// * the random integers
	// * @return the result of evaluating; this is guaranteed to be a concrete
	// * number as long as {@code map} includes every variable occurring
	// * in {@code poly}
	// */
	// private NumericExpression evaluateAtRandomPoint32(Polynomial poly,
	// Map<SymbolicExpression, SymbolicExpression> map) {
	//
	// for (Entry<SymbolicExpression, SymbolicExpression> entry : map
	// .entrySet()) {
	// // an int randomly chosen with uniform probability from
	// // the set of all 2^32 ints:
	// int randomInt = random.nextInt();
	// SymbolicExpression concrete = entry.getKey().type().isInteger()
	// ? info.universe.integer(randomInt)
	// : info.universe.rational(randomInt);
	//
	// entry.setValue(concrete);
	// }
	//
	// NumericExpression result = (NumericExpression) info.universe
	// .mapSubstituter(map).apply(poly);
	//
	// return result;
	// }

	// /**
	// * Can you show that <code>poly</code> is equivalent to 0 with probability
	// * of being wrong less than or equal to epsilon?
	// *
	// * @param poly
	// * the {@link Polynomial} being tested for zero-ness
	// * @param totalDegree
	// * the total degree of {@code poly}; see
	// * {@link Monomial#totalDegree(NumberFactory)}
	// *
	// * @param vars
	// * the set of all "variables" occurring in {@code poly}. A
	// * "variable" is a maximal sub-expression which is not a sum or
	// * product or difference or negation. Hence the polynomial should
	// * only use +, -, and * to combine the "variable"s into an
	// * expression. See {@link Monomial#getTruePrimitives()}.
	// * @param epsilon
	// * a real number in (0,1)
	// * @return if this method returns true, then poly is probably 0 and the
	// * probability that it is not 0 is less than or equal to epsilon. If
	// * this method returns false, then poly is not zero.
	// */
	// private boolean is0WithProbability1(Polynomial poly,
	// IntegerNumber totalDegree, Set<Primitive> vars,
	// RationalNumber epsilon) {
	// NumberFactory nf = info.numberFactory;
	// RationalNumber prob = nf.oneRational();
	// RationalNumber twoTo32 = nf.power(nf.rational(nf.integer(2)), 32);
	// RationalNumber ratio = nf.divide(nf.rational(totalDegree), twoTo32);
	// Primitive[] ps = new Primitive[vars.size()];
	//
	// vars.toArray(ps);
	//
	// int maxNumProcs = Runtime.getRuntime().availableProcessors();
	// boolean reachEpsilon = false;
	//
	// do {
	// int nprocs = 0;
	// List<RandomPoint32Evaluation> resultsPool = new LinkedList<>();
	//
	// while (nprocs < maxNumProcs) {
	// prob = nf.multiply(prob, ratio);
	// nprocs++;
	// if (nf.compare(epsilon, prob) >= 0) {
	// reachEpsilon = true;
	// break;
	// }
	// }
	// System.out.println("random points run with " + nprocs + " / "
	// + maxNumProcs + " threads.");
	// for (int i = 0; i < nprocs; i++)
	// resultsPool.add(new RandomPoint32Evaluation());
	// System.gc();
	// resultsPool.parallelStream()
	// .forEach(new ConcurrentRandomPoint32Evaluator(poly, ps,
	// info.universe));
	// for (RandomPoint32Evaluation result : resultsPool) {
	// if (!result.value().isZero())
	// return false;
	// }
	// } while (!reachEpsilon);
	// return true;
	// }

	private boolean is0WithProbability(Polynomial poly,
			IntegerNumber totalDegree, Set<Primitive> vars,
			RationalNumber epsilon) {
		FastEvaluator fe = new FastEvaluator(random, info.numberFactory, poly,
				totalDegree);

		if (debug)
			fe.printTreeInformation(info.out);
		return fe.isZero(epsilon);
		// TODO : when do you want to use GridEvaluator ?
		// FastGridEvaluator fe = new FastGridEvaluator(random,
		// info.numberFactory,
		// poly, totalDegree);
		//
		// return fe.isZero(epsilon);
	}

	/**
	 * Given a {@link Primitive} <code>p</code> and a set of numeric expressions
	 * whose sum is posited to be equal to <code>p</code>, this method attempts
	 * to solve that equation for <code>p</code>.
	 * 
	 * @param terms
	 *            the expressions whose sum is asserted to be equal to
	 *            <code>p</code>
	 * @param p
	 *            a numeric {@link Primitive}
	 * @return an expression which must be equal to <code>p</code> and does not
	 *         involve <code>p</code>, or <code>null</code> if it could not be
	 *         solved
	 */
	private NumericExpression solveFor(Monomial[] terms, Primitive p) {
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

	/**
	 * Given a set of {@link Monomial} terms, and an integer index variable i,
	 * this finds all of the array-read expressions e for which the index
	 * argument is i, and for which e occurs only linearly (or not at all) in
	 * all terms. These are the array-read expressions that can be solved for.
	 * 
	 * @param terms
	 *            the set of terms, as an array
	 * @param indexVar
	 *            the index variable
	 * @return the set of array read expressions, as an iterable object. Each
	 *         array read expression occurs exactly once
	 */
	private Iterable<Primitive> findArrayReads(Monomial[] terms,
			NumericSymbolicConstant indexVar) {
		Set<Primitive> nonlinearFactors = new LinkedHashSet<>();
		Set<Primitive> linearFactors = new LinkedHashSet<>();
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

	/**
	 * A simple structure representing the solution to an array equation.
	 * 
	 * @author siegel
	 */
	private class ArrayEquationSolution {
		/** The array being solved for. Has array type. */
		SymbolicExpression array;

		/**
		 * The value of a[i], where i is the index variable (not specified in
		 * this structure). The type is the element type of the array type of
		 * {@code array}.
		 */
		SymbolicExpression rhs;
	}

	/**
	 * Given an equation a=b, where a and b are symbolic expressions, and an
	 * integer symbolic constant i, attempts to find an equivalent equation of
	 * the form e[i]=f. If this equivalent form is found, the result is returned
	 * as a structure with the <code>array</code> field e and the
	 * <code>rhs</code> field f.
	 * 
	 * @param arg0
	 *            a, one side of the equation
	 * @param arg1
	 *            b, the other side of the equation
	 * @param index
	 *            i, the index variable
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
		if (arg0.type().isIdeal()) {
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
	private class ArrayDefinition {
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
	 * where n is an integer expressions not involving i, e has type "array of
	 * length n of T" for some type T, and f is some expression, then return a
	 * structure in which the array field is e and the lambda field is the
	 * expression <code>arraylambda i . f</code>.
	 * 
	 * TODO (int[n])<lambda i : int . e[i]>, where e has type int[n], should
	 * immediately be replaced by e. Do this in universe.
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
	 * Repeatedly applies {@code op} to {@code x} until stabilization occurs.
	 * 
	 * @param op
	 *            a unary operator on symbolic expressions
	 * @param x
	 *            a non-{@code null} symbolic expression
	 * @return the first element of the sequence
	 *         <code>x, op(x), op(op(x)), ...</code> which is equal to its
	 *         predecessor in that sequence. If there is no such element, this
	 *         method will not return.
	 */
	private SymbolicExpression transClose(UnaryOperator<SymbolicExpression> op,
			SymbolicExpression x) {
		SymbolicExpression y = op.apply(x);

		while (x != y) {
			x = y;
			y = op.apply(x);
		}
		return y;
	}

	// *********************************************************************
	// *........................... Read methods ..........................*
	// * These methods, only read, but do not modify, the state............*
	// *********************************************************************

	/**
	 * Given a normalized {@link Monic} and a {@link Range} range, computes the
	 * intersection of {@code range} with the current known range of the monic
	 * based on the subMap and rangeMap of this context.
	 * 
	 * @param monic
	 *            a normalized {@link Monic}
	 * @param range
	 *            a {@link Range} of the same type as the monic
	 * @return the intersection of {@code range} with the current known range of
	 *         {@link Monic} based on the entries of the {@link #subMap} and
	 *         {@link #rangeMap}
	 */
	private Range intersectWithRangeOf(Monic monic, Range range) {
		SymbolicExpression value = getSub(monic);

		if (value instanceof Constant) {
			Number number = ((Constant) value).number();

			if (range.containsNumber(number)) {
				range = info.rangeFactory.singletonSet(number);
			} else {
				range = info.rangeFactory.emptySet(range.isIntegral());
			}
		} else {
			Range oldRange = getRange(monic);

			if (oldRange != null)
				range = info.rangeFactory.intersect(range, oldRange);
		}
		return range;
	}

	/**
	 * Computes an (over-)estimate of the possible values of a
	 * {@link Polynomial} based on the current assumptions of this
	 * {@link Context}.
	 * 
	 * @param poly
	 *            a non-{@code null} {@link Polynomial}
	 * @return a {@link Range} of concrete values such that the result of
	 *         evaluating {@code poly} at any point satisfying the assumptions
	 *         of this context will lie in that range
	 */
	private Range computeRange(Polynomial poly) {
		IdealFactory idf = info.idealFactory;
		RangeFactory rf = info.rangeFactory;
		Constant constantTerm = poly.constantTerm(idf);
		Number constant = constantTerm.number();
		Range result;

		if (constant.isZero()) {
			result = rf.singletonSet(constant);
			for (Monomial term : poly.termMap(idf)) {
				result = rf.add(result, computeRange(term));
				if (result.isUniversal())
					break;
			}
			result = intersectWithRangeOf(poly, result);
		} else {
			result = rf.add(
					computeRange((Monomial) idf.subtract(poly, constantTerm)),
					constant);
		}
		return result;
	}

	/**
	 * Computes an (over-)estimate of the possible values of a power expression
	 * based on the current assumptions of this {@link Context}.
	 * 
	 * Currently, this is a very rough over-estimate that only tries to get
	 * right the signedness (greater than 0, greater than or equal to 0, etc.).
	 * 
	 * @param base
	 *            the base in the power expression (can have real or integer
	 *            type)
	 * @param exponent
	 *            the exponent in the power expression (must have same type as
	 *            {@code base})
	 * @return a {@link Range} of concrete values such that the result of
	 *         evaluating base raised to the exponent power at any point
	 *         satisfying the assumptions of this context will lie in that range
	 */
	private Range computeRangeOfPower(RationalExpression base,
			RationalExpression exponent) {
		IdealFactory idf = info.idealFactory;
		RangeFactory rf = info.rangeFactory;
		NumberFactory nf = info.numberFactory;
		// Range baseRange = computeRange(base);
		boolean isIntegral = base.type().isInteger();
		Number zero = isIntegral ? info.numberFactory.zeroInteger()
				: info.numberFactory.zeroRational();

		// if base>0, then base^exponent>0:
		if (simplify(idf.isPositive(base)).isTrue())
			return rf.interval(isIntegral, zero, true,
					nf.infiniteNumber(isIntegral, true), true);

		// if base>=0, then base^exponent>=0:

		Range ge0 = rf.interval(isIntegral, zero, false,
				nf.infiniteNumber(isIntegral, true), true);

		if (simplify(idf.isNonnegative(base)).isTrue())
			return ge0;

		// if exponent is not integral or is even, base^exponent>=0:

		Number exponentNumber = idf.extractNumber(exponent);

		if (exponentNumber != null) {
			if (exponentNumber instanceof IntegerNumber) {
				IntegerNumber exponentInteger = (IntegerNumber) exponentNumber;

				if (nf.mod(exponentInteger, nf.integer(2)).isZero()) {
					return ge0;
				}
			} else {
				if (!nf.isIntegral((RationalNumber) exponentNumber))
					return ge0;
				else {
					IntegerNumber exponentInteger = nf
							.integerValue((RationalNumber) exponentNumber);

					if (nf.mod(exponentInteger, nf.integer(2)).isZero())
						return ge0;
				}
			}
		}
		return rf.universalSet(isIntegral);
	}

	/**
	 * Computes an (over-)estimate of the possible values of a {@link Primitive}
	 * based on the current assumptions of this {@link Context}.
	 * 
	 * @param primitive
	 *            a non-{@code null} {@link Primitive} expression
	 * @return a {@link Range} of concrete values such that the result of
	 *         evaluating {@code primitive} at any point satisfying the
	 *         assumptions of this context will lie in that range
	 */
	private Range computeRange(Primitive primitive) {
		if (primitive instanceof Polynomial)
			return computeRange((Polynomial) primitive);
		if (primitive.operator() == SymbolicOperator.POWER)
			return computeRangeOfPower(
					(RationalExpression) primitive.argument(0),
					(RationalExpression) primitive.argument(1));

		SymbolicExpression value = getSub(primitive);

		if (value instanceof Constant)
			return info.rangeFactory.singletonSet(((Constant) value).number());

		Range oldRange = getRange(primitive);

		if (oldRange != null)
			return oldRange;
		if (primitive.operator() == SymbolicOperator.MODULO)
			return computeDefaultModRange((Monomial) primitive.argument(0),
					(Monomial) primitive.argument(1));
		return info.rangeFactory.universalSet(primitive.type().isInteger());
	}

	/**
	 * Computes an (over-)estimate of the possible values of a
	 * {@link PrimitivePower} based on the current assumptions of this
	 * {@link Context}.
	 * 
	 * @param pp
	 *            a non-{@code null} {@link PrimitivePower}
	 * @return a {@link Range} of concrete values such that the result of
	 *         evaluating {@code pp} at any point satisfying the assumptions of
	 *         this context will lie in that range
	 */
	private Range computeRange(PrimitivePower pp) {
		if (pp instanceof Primitive)
			return computeRange((Primitive) pp);

		IntegerNumber exponent = pp.monomialDegree(info.numberFactory);
		Range result = info.rangeFactory
				.power(computeRange(pp.primitive(info.idealFactory)), exponent);

		result = intersectWithRangeOf(pp, result);
		return result;
	}

	/**
	 * Computes an (over-)estimate of the possible values of a {@link Monic}
	 * based on the current assumptions of this {@link Context}.
	 * 
	 * @param monic
	 *            a non-{@code null} {@link Monic}
	 * @return a {@link Range} of concrete values such that the result of
	 *         evaluating {@code monic} at any point satisfying the assumptions
	 *         of this context will lie in that range
	 */
	private Range computeRange(Monic monic) {
		if (monic instanceof PrimitivePower)
			return computeRange((PrimitivePower) monic);

		RangeFactory rf = info.rangeFactory;
		NumberFactory nf = info.numberFactory;
		Range result = rf.singletonSet(
				monic.type().isInteger() ? nf.oneInteger() : nf.oneRational());

		for (PrimitivePower pp : monic.monicFactors(info.idealFactory)) {
			result = rf.multiply(result, computeRange(pp));
			if (result.isUniversal())
				break;
		}
		result = intersectWithRangeOf(monic, result);
		return result;
	}

	/**
	 * Computes an (over-)estimate of the possible values of a {@link Monomial}
	 * based on the current assumptions of this {@link Context}.
	 * 
	 * @param monomial
	 *            a non-{@code null} {@link Monomial}
	 * @return a {@link Range} of concrete values such that the result of
	 *         evaluating {@code monomial} at any point satisfying the
	 *         assumptions of this context will lie in that range
	 */
	private Range computeRange(Monomial monomial) {
		if (monomial instanceof Monic)
			return computeRange((Monic) monomial);
		if (monomial instanceof Constant)
			return info.rangeFactory
					.singletonSet(((Constant) monomial).number());
		return info.rangeFactory.multiply(
				computeRange(monomial.monic(info.idealFactory)),
				monomial.monomialConstant(info.idealFactory).number());
	}

	/**
	 * Returns the boolean formula represented by this context.
	 * 
	 * @param full
	 *            should the formula include the equalities giving the values of
	 *            the solved variables?
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

	// ************ Modification methods for subMap and rangeMap ************
	// * These are basic modification methods for the state.................*
	// **********************************************************************

	/**
	 * Clears the simplification cache.
	 */
	private void clear() {
		if (simplificationCache != null)
			simplificationCache.clear();
	}

	/**
	 * <p>
	 * Inserts an entry into the {@link #subMap} and also checks for an
	 * inconsistency between the old and new values, if an old value existed.
	 * </p>
	 * 
	 * <p>
	 * Preconditions: the {@code key} and {@code value} must satisfy the
	 * invariants described for {@link #subMap}.
	 * </p>
	 * 
	 * @param key
	 *            the expression on the left side of the substitution
	 * @param value
	 *            the expression on the right side which will replace the
	 *            {@code key}
	 * @return the old value associated to {@code key}, or {@code null} if there
	 *         was no entry for {@code key}
	 * @throws InconsistentContextException
	 *             if the old value was a concrete value and not equal to the
	 *             new value
	 */
	private SymbolicExpression updateSub(SymbolicExpression key,
			SymbolicExpression value) throws InconsistentContextException {
		SymbolicExpression old = subMap.put(key, value);

		if (old != value) {
			clear();
			if (old != null) {
				switch (value.type().typeKind()) {
				case BOOLEAN:
				case CHAR:
				case INTEGER:
				case REAL:
					if (value.operator() == SymbolicOperator.CONCRETE
							&& old.operator() == SymbolicOperator.CONCRETE) {
						throw new InconsistentContextException();
					}
				default:
				}
			}
		}
		return old;
	}

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
	 * TODO: think about replacing this with the same technique used for the
	 * rangeMap. It can be done only during reduce time at the end of
	 * initialization.
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
					clear();
					workList.add(new Pair<>(subKey, subValue));
				}
			}
			updateSub(newKey, newValue);
		}
	}

	/**
	 * Compute the minimum of two numbers. Infinities are allowed.
	 * 
	 * TODO: add this to NumberFactory.
	 * 
	 * @param a
	 *            any non-{@code null} SARL {@link Number}
	 * @param b
	 *            any non-{@code null} SARL {@link Number}
	 * @return the minimum of the {@code a} and {@code b}
	 */
	private Number min(Number a, Number b) {
		return info.numberFactory.compare(a, b) >= 0 ? b : a;
	}

	/**
	 * Compute the maximum of two numbers. Infinities are allowed.
	 * 
	 * TODO: add this to NumberFactory.
	 * 
	 * @param a
	 *            any non-{@code null} SARL {@link Number}
	 * @param b
	 *            any non-{@code null} SARL {@link Number}
	 * @return the maximum of the {@code a} and {@code b}
	 */
	private Number max(Number a, Number b) {
		return info.numberFactory.compare(a, b) >= 0 ? a : b;
	}

	/**
	 * Computes a default range for a%b. Recall a = (a div b)*b + a%b. The sign
	 * of a%b is the sign of a. (a div b) is rounded towards 0.
	 * 
	 * Case 1: a>=0 and b>0. Then a%b is in [0,min(a,b-1)].
	 * 
	 * Case 2: a>=0 and b<0. Then a%b is in [0,min(a,-b-1)].
	 * 
	 * Case 3: a<=0 and b>0. Then a%b is in [max(a,1-b),0].
	 * 
	 * Case 4: a<=0 and b<0. Then a%b is in [max(a,1+b),0].
	 * 
	 * If ab>=0, a%b is in [0,b-1]. If ab<=0, a%b is in [1-b,0]. In any case,
	 * a%b is in [1-b,b-1].
	 * 
	 * The behavior is undefined if b could be 0.
	 * 
	 * @param a
	 *            the dividend, an integer expression
	 * @param b
	 *            the divisor, an integer expression
	 * @return a conservative concrete range on a%b under the assumptions of
	 *         this {@link Context}
	 */
	private Range computeDefaultModRange(Monomial a, Monomial b) {
		RangeFactory rf = info.rangeFactory;
		NumberFactory nf = info.numberFactory;
		Interval b_interval = computeRange(b).intervalOverApproximation();
		Interval a_interval = computeRange(a).intervalOverApproximation();
		Range result = null;

		if (a_interval.isEmpty() || b_interval.isEmpty())
			return rf.emptySet(true);
		if (a_interval.lower().signum() >= 0) {
			Number right;

			if (b_interval.lower().signum() >= 0) // [0,min(a,b-1)]
				right = nf.decrement(b_interval.upper());
			else if (b_interval.upper().signum() <= 0) // [0,min(a,-b-1)]
				right = nf.negate(nf.increment(b_interval.lower()));
			else
				right = max(nf.decrement(b_interval.upper()),
						nf.negate(nf.increment(b_interval.lower())));
			right = min(a_interval.upper(), right);
			result = rf.interval(true, nf.zeroInteger(), false, right,
					right.isInfinite());
		} else if (a_interval.upper().signum() <= 0) {
			Number left;

			if (b_interval.lower().signum() >= 0) // [max(a,1-b),0]
				left = nf.increment(nf.negate(b_interval.upper()));
			else if (b_interval.upper().signum() <= 0) // [max(a,1+b),0]
				left = nf.increment(b_interval.lower());
			else
				left = min(nf.increment(nf.negate(b_interval.upper())),
						nf.increment(b_interval.lower()));
			left = max(a_interval.lower(), left);
			result = rf.interval(true, left, left.isInfinite(),
					nf.zeroInteger(), false);
		}
		return result == null ? rf.universalSet(true) : result;
	}

	/**
	 * Updates the state of this {@link Context} by restricting the range of a
	 * normal {@link Monic}. This may result in changes to the {@link #rangeMap}
	 * , {@link #subMap}, or both.
	 * 
	 * @param key
	 *            a normal {@link Monic}
	 * @param range
	 *            a {@link Range} for {@code key}, with the same type
	 * @throws InconsistentContextException
	 *             if the restriction results in the {@code key} having an empty
	 *             range
	 */
	private void restrictRange(Monic key, Range range)
			throws InconsistentContextException {
		Range original = getRange(key);

		if (original == null) {
			SymbolicExpression value = getSub(key);

			if (value instanceof Constant) {
				Number number = ((Constant) value).number();

				if (range.containsNumber(number)) {
					return;
				} else {
					throw new InconsistentContextException();
				}
			}
			if (key.operator() == SymbolicOperator.MODULO) {
				Range modRange = computeDefaultModRange(
						(Monomial) key.argument(0), (Monomial) key.argument(1));

				range = info.rangeFactory.intersect(range, modRange);
			}
		} else {
			range = info.rangeFactory.intersect(original, range);
			if (range.equals(original))
				return;
		}
		if (range.isEmpty())
			throw new InconsistentContextException();

		Number value = range.getSingletonValue();

		if (value == null) {
			rangeMap.put(key, range);
			clear();
		} else {
			addSub(key, info.universe.number(value));
			if (original != null) {
				rangeMap.remove(key);
				clear();
			}
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
	 * 
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
		Range b_range = computeRange(b);
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
		NumericExpression simpKey = (NumericExpression) simplify(oldKey);

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
	private boolean simplifyRangeMap() throws InconsistentContextException {
		boolean change = false;

		rangeMap.makeAllDirty(); // put everything on the work list
		for (Entry<Monic, Range> oldEntry = rangeMap
				.hold(); oldEntry != null; oldEntry = rangeMap.hold()) {
			clear();

			// the following will not modify anything:
			Entry<Monic, Range> newEntry = simplifyRangeEntry(oldEntry);

			if (newEntry == oldEntry) { // no change
				rangeMap.release(); // put back the entry on hold
			} else { // a change
				Range newRange = newEntry.getValue();

				change = true;
				if (newRange != null)
					restrictRange(newEntry.getKey(), newRange);
			}
		}
		return change;
	}

	/**
	 * Puts this {@link Context} into the "inconsistent" state. This occurs when
	 * the assumption is determined to be inconsistent, i.e., equivalent to
	 * <i>false</i>. All maps are cleared except for the single entry
	 * <code>false -> true</code> in the {@link #subMap}.
	 */
	private void makeInconsistent() {
		rangeMap.clear();
		subMap.clear();
		clear();
		// arrayFacts.clear();
		subMap.put(info.falseExpr, info.trueExpr);
	}

	// **********************************************************************
	// *........................ Extraction methods ........................*
	// * These are higher level methods that modify the state. They should..*
	// * use only the methods above to modify the maps......................*
	// **********************************************************************

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
				extractOr((BooleanExpression) arg);
			}
		} else {
			extractOr(assumption);
		}
	}

	/**
	 * <p>
	 * Attempts to combine the clauses of an or-expression into a range
	 * restriction on a single {@link Monic} and add that restriction to the
	 * state of this {@link Context}.
	 * </p>
	 * 
	 * Precondition: the operator of the <code>orExpr</code> is
	 * {@link SymbolicOperator#OR}.
	 * 
	 * Example:
	 * 
	 * <pre>
	 * x<5 && x>3 ---> x in (3,5)
	 * </pre>
	 * 
	 * @param orExpr
	 * @return <code>true</code> if a the or expression was reduced to a single
	 *         range restriction and the information was added to this context;
	 *         otherwise returns <code>false</code> and the state of this
	 *         context was not changed
	 * @throws InconsistentContextException
	 */
	private boolean extractNumericOr(BooleanExpression orExpr)
			throws InconsistentContextException {
		int numArgs = orExpr.numArguments();

		if (numArgs < 2)
			return false;

		Monic theMonic = null;
		Range theRange = null;

		for (SymbolicObject arg : orExpr.getArguments()) {
			// look for 0=p, 0!=p, 0<m, 0<=m, m<0, m<=0
			BooleanExpression theArg = (BooleanExpression) arg;
			Pair<Monic, Range> pair = info.comparisonToRange(theArg);

			if (pair == null)
				return false;
			if (theMonic == null) {
				theMonic = pair.left;
				theRange = pair.right;
			} else {
				if (theMonic != pair.left)
					return false;
				theRange = info.rangeFactory.union(theRange, pair.right);
			}
		}
		restrictRange(theMonic, theRange);
		return true;
	}

	/**
	 * Processes an expression in which the operator is not
	 * {@link SymbolicOperator#AND}. In the CNF form, this expression is a
	 * clause of the outer "and" expression.
	 * 
	 * @param expr
	 *            the boolean expression to process
	 * @throws InconsistentContextException
	 *             if this context is determined to be inconsistent
	 */
	private void extractOr(BooleanExpression expr)
			throws InconsistentContextException {
		if (expr.operator() != SymbolicOperator.OR) {
			extractClause(expr);
			return;
		}
		// this is supposed to be a simple way to simplify an or expression,
		// reusing the code for simplifying and AND expression.
		// But is this really a good idea? don't we want the size of the
		// expression being simplified to strictly decrease?
		expr = info.universe
				.not((BooleanExpression) simplify(info.universe.not(expr)));
		if (expr.operator() != SymbolicOperator.OR) {
			addFact(expr);
			return;
		}
		if (extractNumericOr(expr))
			return;
		addSub(expr, info.trueExpr);
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
				extractIneqMonic((Monic) arg1, true, op == LESS_THAN);
			} else {
				extractIneqMonic((Monic) arg0, false, op == LESS_THAN);
			}
			break;
		}
		default:
			addSub(clause, info.trueExpr);
		}
	}

	/**
	 * Processes the assumption that <code>pred</code> is <i>false</i>, updating
	 * the state of this context appropriately.
	 * 
	 * @param pred
	 *            a non-<code>null</code> boolean expression, asserted to be
	 *            equivalent to <i>false</i> in this context
	 * @throws InconsistentContextException
	 *             if an inconsistency is detected in the context in the process
	 *             of consuming this assumption
	 * 
	 */
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

		if (arg0.type().isIdeal()) { // 0=x for a Primitive x
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
		SymbolicType type = primitive.type();
		boolean isInteger = type.isInteger();
		NumberFactory nf = info.numberFactory;
		Number zero = isInteger ? nf.zeroInteger() : nf.zeroRational();
		Pair<Monic, Number> pair = info.normalize(primitive, zero);

		if (pair == null)
			throw new InconsistentContextException();

		Monic monic = pair.left;
		Number value = pair.right; // monic=value <==> primitive=0
		Range range = computeRange(monic);

		if (!range.containsNumber(value))
			throw new InconsistentContextException();
		if (primitive instanceof Polynomial)
			extractEQ0Poly((Polynomial) primitive, monic, value);
		else {
			addSub(monic, info.universe.number(value));
		}
	}

	/**
	 * Processes an equality expression of the form p=0, where p is a
	 * {@link Polynomial}, updating the state of this {@link OldContext}
	 * accordingly. Probabilistic techniques may be used if the
	 * {@link PreUniverse#getProbabilisticBound()} is non-0.
	 * 
	 * @param poly
	 *            a non-{@code null} {@link Polynomial} asserted to be 0
	 * @param monic
	 *            if all else fails, use this as the key to the new entry in the
	 *            subMap
	 * @param value
	 *            if all else fails, use this as the value to the new entry in
	 *            the subMap
	 * @throws InconsistentContextException
	 *             if an inconsistency is detected in this context upon adding
	 *             this new assumption
	 */
	private void extractEQ0Poly(Polynomial poly, Monic monic, Number value)
			throws InconsistentContextException {
		RationalNumber prob = info.universe.getProbabilisticBound();
		NumberFactory nf = info.numberFactory;

		if (!prob.isZero()) {
			Set<Primitive> vars = poly.getTruePrimitives();
			IntegerNumber totalDegree = poly.totalDegree(nf);
			int numVars = vars.size();
			IntegerNumber numVarsNumber = nf.integer(numVars);
			IntegerNumber product = nf.multiply(totalDegree, numVarsNumber);

			if (debug) {
				info.out.println("Poly0: product = " + product
						+ ", threshold = " + polyProbThreshold);
				info.out.flush();
			}
			if (nf.compare(product, polyProbThreshold) >= 0) {
				if (debug) {
					info.out.println("Entering probabilistic mode...");
					info.out.flush();
				}

				boolean answer = is0WithProbability(poly, totalDegree, vars,
						prob);

				if (answer) {
					info.out.print(
							"Warning: verified probabilistically with probability of error < ");
					info.out.println(nf.scientificString(prob, 4));
					info.out.flush();
				} else {
					// there is no sense in expanding this polynomial
					// since you know it cannot expand to 0
					addSub(monic, info.universe.number(value));
				}
				return;
			}
		}

		IdealFactory idf = info.idealFactory;

		if (poly.hasTermWithNontrivialExpansion(idf)) {
			Monomial[] termMap = poly.expand(idf);

			if (termMap.length == 0)
				return; // poly is 0 after all

			Monomial newMonomial = idf.factorTermMap(termMap);
			Number zero = newMonomial.type().isInteger() ? nf.zeroInteger()
					: nf.zeroRational();
			Pair<Monic, Number> pair = info.normalize(newMonomial, zero);

			addSub(pair.left, info.universe.number(pair.right));
		} else {
			addSub(monic, info.universe.number(value));
		}
	}

	/**
	 * Processes the claim that two expressions are not equal, updating the
	 * {@link #subMap} and/or {@link #rangeMap} to reflect this claim.
	 * 
	 * @param arg0
	 *            one side of the inequality, any non-{@code null} symbolic
	 *            expression
	 * @param arg1
	 *            the other side of the inequality, a symbolic expression of the
	 *            same type as {@code arg0}
	 * @throws InconsistentContextException
	 *             if an inconsistency in this context is detected in the
	 *             process of processing this claim
	 */
	private void extractNEQ(SymbolicExpression arg0, SymbolicExpression arg1)
			throws InconsistentContextException {
		SymbolicType type = arg0.type();

		if (type.isIdeal()) { // 0!=x, for a Primitive x
			Primitive primitive = (Primitive) arg1;
			RangeFactory rf = info.rangeFactory;
			Number zero = type.isInteger() ? info.numberFactory.zeroInteger()
					: info.numberFactory.zeroRational();
			Pair<Monic, Number> pair = info.normalize(primitive, zero);

			restrictRange(pair.left,
					rf.complement(rf.singletonSet(pair.right)));
		} else {
			addSub(info.universe.equals(arg0, arg1), info.falseExpr);
		}
	}

	/**
	 * <p>
	 * Extracts information from an inequality of one of the forms: x&gt;0,
	 * x&ge;0, x&lt;0, x&le;0, where x is a {@link Monic} in which the maximum
	 * degree of any {@link Primitive} is 1. Updates the state of this context
	 * accordingly.
	 * </p>
	 * 
	 * Strategy:
	 * 
	 * <ul>
	 * <li>if polynomial, reduce to pseudo. If this is non-trivial, get best
	 * bound on pseudo, convert to bound on original polynomial, return.</li>
	 * <li>else: look in rangeMap, store the result</li>
	 * <li>if non-trivial product, get best bounds on factors and multiply</li>
	 * <li>if non-trivial sum, get best bounds on terms and add</li>
	 * <li>if non-trivial primitive power, get bound on base, raise to power
	 * </li>
	 * <li>if POWER operation : if exponent is constant, ditto, else: ?</li>
	 * <li>intersect result with whatever you got from rangeMap</li>
	 * </ul>
	 * 
	 * Then: intersect with bound specified by these arguments. Restrict bound
	 * on the monic accordingly.
	 * 
	 * @param monic
	 *            a non-<code>null</code> {@link Monic}
	 * @param gt
	 *            is the condition one of x&gt;0 or x&ge;0 (i.e., not x&lt;0 or
	 *            x&le;0)
	 * @param strict
	 *            is the form one of x&gt;0 or x&lt;0 (strict inequality)
	 * @throws InconsistentContextException
	 *             if, in the course of processing this inequality, an
	 *             inconsistency in this {@link Context} is detected
	 */
	private void extractIneqMonic(Monic monic, boolean gt, boolean strict)
			throws InconsistentContextException {
		RangeFactory rf = info.rangeFactory;
		NumberFactory nf = info.numberFactory;
		SymbolicType type = monic.type();
		boolean isIntegral = type.isInteger();
		Number zero = isIntegral ? nf.zeroInteger() : nf.zeroRational();
		Range range = gt
				? rf.interval(isIntegral, zero, strict,
						nf.infiniteNumber(isIntegral, true), true)
				: rf.interval(isIntegral, nf.infiniteNumber(isIntegral, false),
						true, zero, strict);
		Pair<Monic, Range> pair = info.normalize(monic, range);

		monic = pair.left;
		range = pair.right;

		Range oldRange = computeRange(monic);
		Range newRange = rf.intersect(oldRange, range);

		if (!oldRange.equals(newRange))
			restrictRange(monic, newRange);
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

	/**
	 * Processes an exists expression, updating this {@link Context}
	 * appropriately. For now, a trivial implementation.
	 * 
	 * @param existsExpr
	 *            the exists expression
	 * @throws InconsistentContextException
	 *             if an inconsistency is detected
	 */
	private void extractExists(SymbolicExpression existsExpr)
			throws InconsistentContextException {
		addSub(existsExpr, info.trueExpr);
	}

	/**
	 * Reduces the context to an equivalent but simplified form.
	 * 
	 * @throws InconsistentContextException
	 *             if an inconsistency in this {@link Context} is detected in
	 *             the process of simplifying it
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

	// ************************ Protected methods ************************

	/**
	 * Initializes this context by consuming and analyzing the given assumption
	 * and updating all data structures to represent the assumption in a
	 * structured way. After initialization, this context is basically immutable
	 * (an exception being the {@link #simplificationCache}).
	 * 
	 * @param assumption
	 *            the boolean expression which is to be represented by this
	 *            context
	 */
	protected void initialize(BooleanExpression assumption) {
		simplificationCache = new HashMap<>();
		// can also use a TreeMap, but HashMap seems faster...
		// this.simplificationCache = new TreeMap<SymbolicObject,
		// SymbolicObject>(info.universe.comparator());
		if (debug)
			System.out.println("Creating context : " + assumption);
		try {
			addFact(assumption);
			reduce();
		} catch (InconsistentContextException e) {
			makeInconsistent();
		}
		// simplificationCache = new HashMap<>();
	}

	/**
	 * Adds all entries in the {@link #subMap} to the specified map.
	 * 
	 * @param map
	 *            a map to which the entries of the {@link #subMap} will be
	 *            added
	 */
	protected void addSubsToMap(
			Map<SymbolicExpression, SymbolicExpression> map) {
		map.putAll(subMap);
	}

	/**
	 * Returns an instance of {@link LinearSolver} that can be used to simplify
	 * the {@link #subMap} of this {@link Context}.
	 * 
	 * @return a linear solver for simplifying the {@link #subMap}, or
	 *         {@code null} if no simplifications are possible
	 */
	protected LinearSolver getLinearSolver() {
		if (subMap.isEmpty())
			return null;
		return LinearSolver.reduce(info, subMap, info.monicComparator,
				backwardsSub);
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
	protected boolean gauss() throws InconsistentContextException {
		// TODO: change the monic comparator to one that orders
		// from least to greatest:
		// - symbolic constants
		// - array reads
		// ...
		// - function applications
		// - constants
		LinearSolver ls = getLinearSolver();

		if (ls == null)
			return false;
		if (!ls.isConsistent())
			throw new InconsistentContextException();
		if (!ls.hasChanged())
			return false;
		for (SymbolicExpression key : ls.getKeysToRemove())
			subMap.remove(key);
		for (Entry<Monic, Monomial> entry : ls.getNewEntries())
			addSub(entry.getKey(), entry.getValue());
		return true;
	}

	/**
	 * Gets the variables that have been "solved", i.e., have an expression in
	 * terms of other (unsolved) variables. These variables can be entirely
	 * eliminated from the state.
	 * 
	 * @return mapping from solved variables to their values
	 */
	protected Map<SymbolicConstant, SymbolicExpression> getSolvedVariables() {
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

	/**
	 * If this assumption is exactly equivalent to the claim that the given
	 * symbolic constant lies in some interval, returns that interval.
	 * Otherwise, returns {@code null}.
	 * 
	 * @param symbolicConstant
	 *            the symbolic constant
	 * @return the interval or {@code null}
	 */
	protected Interval assumptionAsInterval(SymbolicConstant symbolicConstant) {
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

	/**
	 * Returns the simplifier utility used by this context. That object provides
	 * references to many different commonly used fields, and basic utility
	 * methods.
	 * 
	 * @return the simplifier utility
	 */
	protected SimplifierInfo getInfo() {
		return info;
	}

	/**
	 * Looks up an entry in the substitution map of this context.
	 * 
	 * @param key
	 *            the key to look up
	 * @return the value associated to that key in the substitution map. This is
	 *         the value that will always be substituted for {@code key} when a
	 *         symbolic expression is simplified by this {@link Context}.
	 */
	protected SymbolicExpression getSub(SymbolicExpression key) {
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
	protected Range getRange(Monic key) {
		return rangeMap.get(key);
	}

	protected void cacheSimplification(SymbolicObject key,
			SymbolicObject value) {
		// TODO: don't do this if in init mode?
		simplificationCache.put(key, value);
	}

	protected SymbolicObject getSimplification(SymbolicObject key) {
		return simplificationCache.get(key);
	}

	// protected boolean isInitialized() {
	// return simplificationCache != null;
	// }

	/**
	 * Computes an (over-)estimate of the possible values of a
	 * {@link RationalExpression} based on the current assumptions of this
	 * {@link Context}. Points at which this rational expression are undefined
	 * (because, e.g., the denominator is 0) are ignored.
	 * 
	 * @param rat
	 *            a non-{@code null} {@link RationalExpression}
	 * @return a {@link Range} of concrete values such that the result of
	 *         evaluating {@code rat} at any point satisfying the assumptions of
	 *         this context will lie in that range
	 */
	protected Range computeRange(NumericExpression expression) {
		if (expression instanceof Monomial)
			return computeRange((Monomial) expression);

		IdealFactory idf = info.idealFactory;
		RationalExpression rat = (RationalExpression) expression;

		return info.rangeFactory.divide(computeRange(rat.numerator(idf)),
				computeRange(rat.denominator(idf)));
	}

	/**
	 * Returns a map consisting of all entries in the substitution map of this
	 * {@link Context} and all of its ancestors. An entry from a child overrides
	 * an entry with the same key from the parent.
	 * 
	 * @return a map consisting of all subMap entries from this context and its
	 *         ancestors
	 */
	protected Map<SymbolicExpression, SymbolicExpression> getFullSubMap() {
		return subMap;
	}

	/**
	 * <p>
	 * Returns the collapsed context. That is the context obtained by
	 * "collapsing" this context and all of its super-contexts into a single
	 * context.
	 * </p>
	 * 
	 * <p>
	 * In this case, since this has no super-context, this method just returns
	 * <code>this</code>.
	 * </p>
	 * 
	 * <p>
	 * This method may be overridden in subclasses.
	 * </p>
	 * 
	 * @return <code>this</code>
	 */
	protected Context collapse() {
		return this;
	}

	/**
	 * Simplifies a symbolic expression using the current state of this
	 * {@link Context}.
	 * 
	 * @param expr
	 *            the expression to simplify
	 * @return the simplified expression
	 */
	protected SymbolicExpression simplify(SymbolicExpression expr) {
		Set<SymbolicExpression> simplificationStack = new HashSet<>();

		return new IdealSimplifierWorker(this, simplificationStack)
				.simplifyExpression(expr);
	}

	// Public methods...

	/**
	 * Prints this {#link Context} is a human-readable multi-line format.
	 * 
	 * @param out
	 *            the stream to which to print
	 */
	public void print(PrintStream out) {
		out.println("subMap:");
		printMap(out, subMap);
		out.println("rangeMap:");
		printMap(out, rangeMap);
		out.flush();
	}

	/**
	 * Is this context empty? This means that both the {@link #subMap} and
	 * {@link #rangeMap} are empty. Note that emptiness of this context does not
	 * necessarily imply the super-context (if any) is empty.
	 * 
	 * @return <code>true</code> iff this context is empty, else
	 *         <code>false</code>
	 */
	public boolean isEmpty() {
		return subMap.isEmpty() && rangeMap.isEmpty();
	}

	/**
	 * Is this {@link Context} inconsistent, i.e., is the assumption it
	 * represents equivalent to "false"?
	 * 
	 * @return <code>true</code> if this context is known to be inconsistent. A
	 *         return value of <code>true</code> implies the context is
	 *         inconsistent; a return value of <code>false</code> means the
	 *         context may or may not be inconsistent.
	 */
	public boolean isInconsistent() {
		SymbolicExpression result = subMap.get(info.falseExpr);

		return result != null && result.isTrue();
	}

	/**
	 * Returns the reduced assumption represented by this {@link Context}. That
	 * means it does not include the equations of the form x=e, where x is a
	 * solved symbolic constant. The related method {@link #getFullAssumption()}
	 * returns the conjunction of this reduced assumption with those equations.
	 * 
	 * @return the reduced assumption
	 */
	public BooleanExpression getReducedAssumption() {
		return getAssumption(false);
	}

	/**
	 * Returns the full assumption represented by this {@link Context}. This
	 * means the assumption will include the clauses which are equations of the
	 * form "x=e" where x is a solved {@link SymbolicConstant}.
	 * 
	 * If this is a sub-context, this assumption does not include the assumption
	 * of its super-context.
	 * 
	 * @return the full assumption
	 */
	public BooleanExpression getFullAssumption() {
		return getAssumption(true);
	}

	// methods specified in Object ...

	@Override
	public Context clone() {
		return new Context(info, cloneTreeMap(subMap), rangeMap.clone(),
				backwardsSub);
	}

	@Override
	public String toString() {
		return "Context[" + subMap + ", " + rangeMap + "]";
	}

}
