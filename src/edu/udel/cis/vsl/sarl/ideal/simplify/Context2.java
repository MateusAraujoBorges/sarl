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

	/** The original, unaltered, assumption used to initialize this context. */
	BooleanExpression originalAssumption;

	private boolean initialized = false;

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
	private Map<SymbolicObject, SymbolicObject> simplificationCache = null;

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

	private Context2(SimplifierInfo info,
			Map<SymbolicExpression, SymbolicExpression> subMap,
			Map<Monic, Range> rangeMap) {
		this.info = info;
		this.subMap = subMap;
		this.rangeMap = rangeMap;
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

	/**
	 * Chooses a random integer with uniform probability from the set of all
	 * 2^32 ints for each "variable" occurring in the polynomial, and evaluates
	 * the polynomial. A "variable" is any maximal sub-expression which is not a
	 * sum or product or difference or negation. Hence the polynomial should
	 * only use +, -, and * to combine the "variable"s into an expression.
	 *
	 * @param poly
	 *            the {@link Polynomial} to evaluate
	 * @param map
	 *            a {@link Map} with one {@link Entry} for each "variable"
	 *            occurring in {@code poly}. The key of the {@link Entry} is the
	 *            variable; the value is not used and will be overwritten with
	 *            the random integers
	 * @return the result of evaluating; this is guaranteed to be a concrete
	 *         number as long as {@code map} includes every variable occurring
	 *         in {@code poly}
	 */
	private NumericExpression evaluateAtRandomPoint32(Polynomial poly,
			Map<SymbolicExpression, SymbolicExpression> map) {

		for (Entry<SymbolicExpression, SymbolicExpression> entry : map
				.entrySet()) {
			// an int randomly chosen with uniform probability from
			// the set of all 2^32 ints:
			int randomInt = random.nextInt();
			SymbolicExpression concrete = entry.getKey().type().isInteger()
					? info.universe.integer(randomInt)
					: info.universe.rational(randomInt);

			entry.setValue(concrete);
		}

		NumericExpression result = (NumericExpression) info.universe
				.mapSubstituter(map).apply(poly);

		return result;
	}

	/**
	 * Can you show that <code>poly</code> is equivalent to 0 with probability
	 * of being wrong less than or equal to epsilon?
	 *
	 * @param poly
	 *            the {@link Polynomial} being tested for zero-ness
	 * @param totalDegree
	 *            the total degree of {@code poly}; see
	 *            {@link Monomial#totalDegree(NumberFactory)}
	 * 
	 * @param vars
	 *            the set of all "variables" occurring in {@code poly}. A
	 *            "variable" is a maximal sub-expression which is not a sum or
	 *            product or difference or negation. Hence the polynomial should
	 *            only use +, -, and * to combine the "variable"s into an
	 *            expression. See {@link Monomial#getTruePrimitives()}.
	 * @param epsilon
	 *            a real number in (0,1)
	 * @return if this method returns true, then poly is probably 0 and the
	 *         probability that it is not 0 is less than or equal to epsilon. If
	 *         this method returns false, then poly is not zero.
	 */
	private boolean is0WithProbability(Polynomial poly,
			IntegerNumber totalDegree, Set<Primitive> vars,
			RationalNumber epsilon) {
		NumberFactory nf = info.numberFactory;
		RationalNumber prob = nf.oneRational();
		RationalNumber twoTo32 = nf.power(nf.rational(nf.integer(2)), 32);
		RationalNumber ratio = nf.divide(nf.rational(totalDegree), twoTo32);
		Map<SymbolicExpression, SymbolicExpression> localSubMap = new HashMap<>();

		for (Primitive var : vars)
			localSubMap.put(var, null);
		do {
			NumericExpression evaluation = evaluateAtRandomPoint32(poly,
					localSubMap);

			if (!evaluation.isZero())
				return false;
			prob = nf.multiply(prob, ratio);
		} while (nf.compare(epsilon, prob) < 0);
		return true;
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
	 * Simplifies a symbolic expression using the current state of this
	 * {@link Context2}.
	 * 
	 * @param expr
	 *            the expression to simplify
	 * @return the simplified expression
	 */
	@Override
	public SymbolicExpression simplify(SymbolicExpression expr) {
		return new IdealSimplifierWorker2(this).simplifyExpressionWork(expr);
		// this should do transitive closure of substitution
	}

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
	 * {@link Context2}.
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
	 * based on the current assumptions of this {@link Context2}.
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
	 * based on the current assumptions of this {@link Context2}.
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

		if (value instanceof Constant) {
			return info.rangeFactory.singletonSet(((Constant) value).number());
		} else {
			Range oldRange = getRange(primitive);

			if (oldRange != null)
				return oldRange;
		}
		return info.rangeFactory.universalSet(primitive.type().isInteger());
	}

	/**
	 * Computes an (over-)estimate of the possible values of a
	 * {@link PrimitivePower} based on the current assumptions of this
	 * {@link Context2}.
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
	 * based on the current assumptions of this {@link Context2}.
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
	 * based on the current assumptions of this {@link Context2}.
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
	 * Computes an (over-)estimate of the possible values of a
	 * {@link RationalExpression} based on the current assumptions of this
	 * {@link Context2}. Points at which this rational expression are undefined
	 * (because, e.g., the denominator is 0) are ignored.
	 * 
	 * @param rat
	 *            a non-{@code null} {@link RationalExpression}
	 * @return a {@link Range} of concrete values such that the result of
	 *         evaluating {@code rat} at any point satisfying the assumptions of
	 *         this context will lie in that range
	 */
	@Override
	public Range computeRange(NumericExpression expression) {
		if (expression instanceof Monomial)
			return computeRange((Monomial) expression);

		IdealFactory idf = info.idealFactory;
		RationalExpression rat = (RationalExpression) expression;

		return info.rangeFactory.divide(computeRange(rat.numerator(idf)),
				computeRange(rat.denominator(idf)));
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

	/**
	 * Selects from the {@link #subMap} those entries in which the key is a
	 * {@link Monic} and the value is a {@link Constant} and add corresponding
	 * entries to {@code map}. The only different between the entries is that in
	 * {@code map} the value is the {@link Number} that has been extracted from
	 * the {@link Constant}. This is the form needed to perform Gaussian
	 * Elimination.
	 * 
	 * @param map
	 *            a non-{@code null} map. The map is not necessarily empty.
	 *            Existing entries will simply be overwritten.
	 */
	protected void addMonicConstantsToMap(Map<Monic, Number> map) {
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

	/**
	 * Constructs a map with an entry for each {@link Monic} that has a known
	 * concrete value. The map may be modified without affecting the state of
	 * this context.
	 * 
	 * @return a map mapping each {@link Monic} to the {@link Number} value
	 *         associated to that monic in this context
	 */
	@Override
	public Map<Monic, Number> getMonicConstantMap() {
		Map<Monic, Number> map = new TreeMap<>(info.monicComparator);

		addMonicConstantsToMap(map);
		return map;
	}

	// ************ Modification methods for subMap and rangeMap ************
	// * These are basic modification methods for the state.................*
	// **********************************************************************

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
			simplificationCache.clear();
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
					simplificationCache.clear();
					workList.add(new Pair<>(subKey, subValue));
				}
			}
			updateSub(newKey, newValue);
		}
	}

	// /**
	// * Given a normalized {@link Monic} and its value, update state
	// * appropriately to indicate that the key equals the value.
	// *
	// * @param key
	// * normal {@link Monic}
	// * @param value
	// * a number of the same type as {@code key}
	// * @throws InconsistentContextException
	// * if the new value contradicts an existing {@link Range} or
	// * value for {@code key}
	// */
	// private void updateValue(Monic key, Number value)
	// throws InconsistentContextException {
	// // look in the range map, then sub map
	// Range range = getRange(key);
	//
	// if (range == null) {
	// SymbolicExpression oldValue = getSub(key);
	//
	// if (oldValue == null) {
	// addSub(key, info.universe.number(value));
	// } else {
	//
	// }
	// } else {
	//
	// }
	// }

	/**
	 * Updates the state of this {@link Context} by restricting the range of a
	 * normal {@link Monic}. This may result in changes to the {@link #rangeMap}
	 * , {@link #subMap}, or both.
	 * 
	 * @param key
	 *            a normal {@link Monic}
	 * @param range
	 *            a {@link Range} for {@code key}, with the same tyep
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
			simplificationCache.clear();
		} else {
			addSub(key, info.universe.number(value));
			if (original != null) {
				rangeMap.remove(key);
				simplificationCache.clear();
			}
		}
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
		// rangeMap until it stabilizes. The keys are changing
		// as you iterate.
		// invariant: keyList is a list containing all the keys in the rangeMap
		// (and possibly additional expressions not keys in the rangeMap)
		// lastChanged is the last node to have changed in some way.
		// curr is the current node.
		while (curr != null) {
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

			simplificationCache.clear();
			if (oldRange != null) {
				change = true;

				// if simpKey is Constant, it is either in the range or not
				if (simpKey instanceof Constant) {
					if (!oldRange.containsNumber(((Constant) simpKey).number()))
						throw new InconsistentContextException();
				} else {
					// We assume simpKey is not a RationalExpression...
					Pair<Monic, Range> normalization = info
							.normalize((Monomial) simpKey, oldRange);
					Monic newKey = normalization.left;
					int oldSize = rangeMap.size();

					restrictRange(newKey, normalization.right);

					int newSize = rangeMap.size();

					if (newSize == oldSize + 1) {
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
		simplificationCache.clear();
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
				BooleanExpression clause = (BooleanExpression) arg;

				extractOr(clause);
			}
		} else {
			extractOr(assumption);
		}
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
			SymbolicExpression oldValue = getSub(key); // subMap.get(key);

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
		} else {
			expr = info.universe
					.not((BooleanExpression) simplify(info.universe.not(expr)));
			if (expr.operator() == SymbolicOperator.OR) {
				addSub(expr, info.trueExpr);
			} else {
				addFact(expr);
			}
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
	 * {@link Polynomial}, updating the state of this {@link Context}
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
	 * Extracts information from an inequality of one of the forms: x&gt;0,
	 * x&ge;0, x&lt;0, x&le;0, where x is a {@link Monic} in which the maximum
	 * degree of any {@link Primitive} is 1. Updates the state of this context
	 * accordingly.
	 * 
	 * Strategy:
	 * 
	 * 
	 * Need method Range getBound(Monomial) which does everything possible to
	 * get the most precise bound on the monomial from the existing context:
	 * First, simplify the Monomial. This should yield a Monomial.
	 * 
	 * - if polynomial, reduce to pseudo. If this is non-trivial, get best bound
	 * on pseudo, convert to bound on original polynomial, return. - else: look
	 * in rangeMap, store the result - if non-trivial product, get best bounds
	 * on factors and multiply - if non-trivial sum, get best bounds on factors
	 * and add - if non-trivial primitive power, get bound on base, raise to
	 * power - if POWER operation : if exponent is constant, ditto, else:? -
	 * intersect result with whatever you got from rangeMap
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

	private void extractExists(SymbolicExpression existsExpr)
			throws InconsistentContextException {
		addSub(existsExpr, info.trueExpr);
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

	// ************************ Protected methods ************************

	protected void initialize(BooleanExpression assumption) {
		this.originalAssumption = assumption;
		simplificationCache = new HashMap<>();

		if (debug) {
			System.out.println("Creating context : " + assumption);
		}

		try {
			addFact(assumption);
			reduce();
		} catch (InconsistentContextException e) {
			makeInconsistent();
		}
		// can also use a TreeMap, but HashMap seems faster...
		// this.simplificationCache = new TreeMap<SymbolicObject,
		// SymbolicObject>(info.universe.comparator());
		initialized = true;
	}

	// ************************** Public methods **************************

	// public methods not specified in other interfaces...

	@Override
	public BooleanExpression getReducedAssumption() {
		return getAssumption(false);
	}

	@Override
	public BooleanExpression getFullAssumption() {
		return getAssumption(true);
	}

	@Override
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

	// methods specified in Object ...

	@Override
	public Context2 clone() {
		return new Context2(info, cloneTreeMap(subMap), cloneTreeMap(rangeMap));
	}

	// methods specified in ContextIF ...

	@Override
	public SimplifierInfo getInfo() {
		return info;
	}

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

	@Override
	public BooleanExpression getOriginalAssumption() {
		return originalAssumption;
	}

	@Override
	public boolean isInitialized() {
		return initialized;
	}

}
