package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import edu.udel.cis.vsl.sarl.IF.CoreUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.IF.BooleanExpressionFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Polynomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal.IF.PrimitivePower;
import edu.udel.cis.vsl.sarl.ideal.IF.RationalExpression;
import edu.udel.cis.vsl.sarl.simplify.common.CommonSimplifierWorker;

/**
 * An ideal simplifier worker is created by an {@link IdealSimplifier} to
 * simplify one symbolic expression. It disappears once that task has completed.
 * The {@link IdealSimplifier} is persistent and will usually continue to live
 * through the lifetime of the JVM.
 * 
 * @author siegel
 */
public class IdealSimplifierWorker2 extends CommonSimplifierWorker {

	// static members...
	
	// TODO: move:

//	/**
//	 * A random number generator with seed very likely to be distinct from all
//	 * other seeds. TODO: this must be made thread-safe.
//	 */
//	private static Random random = new Random();

//	/**
//	 * Used in a heuristic to determine when to use probabilistic methods to
//	 * determine polynomial zero-ness. If the product of the number of variables
//	 * and the total detree is greater than or equal to this number, the
//	 * polynomial is considered too big to be expanded, and probabilistic
//	 * techniques will be used instead (unless the probabilistic bound is 0).
//	 */
//	private final static IntegerNumber polyProbThreshold = Numbers.REAL_FACTORY
//			.integer(100);

	// Instance fields...

	/**
	 * The context which represents the assumptions under which simplification
	 * is taking place. It is a structured representation of a boolean
	 * expression.
	 */
	private ContextIF theContext;

	/**
	 * Structure which includes references to commonly used factories and other
	 * objects, for convenience.
	 */
	private SimplifierInfo info;

	// Constructors ...

	/**
	 * Creates new simplifier worker from given info object and context
	 * (assumption). Does not do anything.
	 * 
	 * @param info
	 *            the info object to use
	 * @param context
	 *            the assumption under which simplification is taking place
	 */
	public IdealSimplifierWorker2(SimplifierInfo info, ContextIF context) {
		super(info.universe);
		this.theContext = context;
		this.info = info;
	}

	// Private methods ...

	private IdealFactory idealFactory() {
		return info.idealFactory;
	}

	private NumberFactory numberFactory() {
		return info.numberFactory;
	}

//	private PreUniverse universe() {
//		return info.universe;
//	}

	private BooleanExpressionFactory booleanFactory() {
		return info.booleanFactory;
	}

//	private BooleanExpression falseExpr() {
//		return info.falseExpr;
//	}
//
//	private BooleanExpression trueExpr() {
//		return info.trueExpr;
//	}
//
//	private AffineFactory affineFactory() {
//		return info.affineFactory;
//	}

	/**
	 * Build up entries in power map from the monic factors of a {@link Monic}.
	 * This method modifies two given {@link Map}s. The first map encodes a set
	 * of power expressions in which the base is a {@link Primitive} (in
	 * particular, is not concrete) and the second map encodes a set of power
	 * expressions in which the base is a concrete number. The final values of
	 * the maps is essentially the original value multiplied by the factors of
	 * the {@link Monic} (if <code>positive</code> is <code>true</code>)) or
	 * divided by the factors of the {@link Monic} (if <code>positive</code> is
	 * <code>false</code>). Simplifications are performed under the assumptions
	 * of {@link #theContext}).
	 * 
	 * @param powerMap1
	 *            map from the primitives to the exponent assigned to that
	 *            primitive; this is an input/output variable
	 * @param powerMap2
	 *            like <code>powerMap1</code>, but for expressions in which the
	 *            base is {@link Constant}; this is an input/output variable
	 * @param positive
	 *            if true, exponents should be added to the entries in the
	 *            powerMaps, otherwise they should be subtracted from entries;
	 *            an input
	 * @param monic
	 *            the {@link Monic} expression that is being simplified and
	 *            decomposed into a product of powers; this is an input
	 * 
	 * @return true iff change occurred
	 */
	private boolean simplifyPowers(Map<Primitive, RationalExpression> powerMap1,
			Map<Constant, RationalExpression> powerMap2, boolean positive,
			Monic monic) {
		IdealFactory idf = idealFactory();
		PrimitivePower[] factors = monic.monicFactors(idf);
		boolean isInteger = monic.type().isInteger();
		boolean change = false;
		NumberFactory nf = numberFactory();

		for (PrimitivePower pp : factors) {
			Primitive primitive = pp.primitive(idf);
			IntegerNumber outerExp = (IntegerNumber) pp
					.primitivePowerExponent(idf).getNumber();
			IntegerNumber signedOuterExp = positive ? outerExp
					: nf.negate(outerExp);
			RationalExpression realSignedOuterExp = idf.constant(isInteger
					? signedOuterExp : nf.integerToRational(signedOuterExp));
			RationalExpression newExp;
			SymbolicObject baseObj = primitive.argument(0);
			Primitive base;

			if (baseObj instanceof Constant) {
				Constant baseConst;

				if (primitive.operator() == SymbolicOperator.POWER) {
					baseConst = (Constant) primitive.argument(0);
					newExp = idf.multiply(realSignedOuterExp,
							(RationalExpression) primitive.argument(1));
					change = change || outerExp.numericalCompareTo(
							nf.abs(idf.getConcreteExponent(newExp))) != 0;

					NumericExpression oldExponent = powerMap2.get(baseConst);

					if (oldExponent == null) {
						powerMap2.put(baseConst, newExp);
						powerMap1.remove(primitive);
					} else {
						powerMap2.put(baseConst, idf.add(oldExponent, newExp));
						change = true;
					}
				}
			} else {
				if (primitive.operator() == SymbolicOperator.POWER) {
					base = (Primitive) primitive.argument(0);
					newExp = idf.multiply(realSignedOuterExp,
							(RationalExpression) primitive.argument(1));
					change = change || outerExp.numericalCompareTo(
							nf.abs(idf.getConcreteExponent(newExp))) != 0;
				} else {
					base = primitive;
					newExp = realSignedOuterExp;
				}

				NumericExpression oldExponent = powerMap1.get(base);

				if (oldExponent == null) {
					powerMap1.put(base, newExp);
				} else {
					powerMap1.put(base, idf.add(oldExponent, newExp));
					change = true;
				}
			}
		}
		return change;
	}

	/**
	 * Simplifies any {@link SymbolicOperator#POWER} operations occurring in a
	 * rational expression.
	 * 
	 * @param rational
	 *            a rational expression
	 * @return equivalent rational expression in which power operations that can
	 *         be combined are combined or simplified
	 */
	private RationalExpression simplifyPowersRational(
			RationalExpression rational) {
		IdealFactory idf = idealFactory();
		Monomial numerator = rational.numerator(idf),
				denominator = rational.denominator(idf);
		Monic m1 = numerator.monic(idf), m2 = denominator.monic(idf);
		Map<Primitive, RationalExpression> powerMap = new HashMap<>();
		Map<Constant, RationalExpression> powerMap2 = new HashMap<>();
		boolean change1 = simplifyPowers(powerMap, powerMap2, true, m1);
		boolean change2 = simplifyPowers(powerMap, powerMap2, false, m2);

		if (change1 || change2) {
			RationalExpression result = idf.one(rational.type());

			for (Entry<Constant, RationalExpression> entry : powerMap2
					.entrySet()) {
				result = idf.multiply(result,
						idf.power(entry.getKey(), entry.getValue()));
			}
			for (Entry<Primitive, RationalExpression> entry : powerMap
					.entrySet()) {
				result = idf.multiply(result,
						idf.power(entry.getKey(), entry.getValue()));
			}
			result = idf.divide(
					idf.multiply(result, numerator.monomialConstant(idf)),
					denominator.monomialConstant(idf));
			return result;
		}
		return rational;
	}

	/**
	 * Simplifies a {@link Monic} that is not a {@link Polynomial}.
	 * 
	 * @param monic
	 *            a non-<code>null</code> {@link Monic} which is not an instance
	 *            of {@link Polynomial}.
	 * 
	 * @return a simplified version of <code>monic</code> which is equivalent to
	 *         <code>monic</code> under the current assumptions
	 */
	private Monomial simplifyMonic(Monic monic) {
		assert !(monic instanceof Polynomial);

		// TODO: don't we already do this for every expression?
		Monomial result = (Monomial) theContext.getSub(monic);

		if (result != null)
			return result;
		return (Monomial) simplifyExpressionGeneric(monic);
	}

	/**
	 * <p>
	 * Simplifies a {@link Polynomial}. Note that method
	 * {@link #simplifyGenericExpression(SymbolicExpression)} cannot be used,
	 * since that method will invoke
	 * {@link CoreUniverse#make(SymbolicOperator, SymbolicType, SymbolicObject[])}
	 * , which will apply binary addition repeatedly on the terms of a
	 * {@link Polynomial}, which will not result in the correct form.
	 * </p>
	 * 
	 * <p>
	 * The following strategies are used:
	 * <ul>
	 * <li>look up the polynomial in the {@link #constantMap()}</li>
	 * <li>convert to an {@link AffineExpression} and look for a constant value
	 * of the pseudo</li>
	 * <li>simplify the individual terms and sum the results</li>
	 * <li>full expand the polynomial</li>
	 * </ul>
	 * The process is repeated until it stabilizes or a constant value is
	 * determined.
	 * </p>
	 * 
	 * @param poly
	 *            a {@link Polynomial} with at least 2 terms
	 * @return a simplified version of <code>poly</code> equivalent to
	 *         <code>poly</code> under the existing assumptions
	 */
	private Monomial simplifyPolynomial(Polynomial poly) {
		// IdealFactory id = idealFactory();
		//
		// while (true) { // repeat until stabilization
		// Number constant = theContext.getConstantValue(poly);
		//
		// if (constant != null)
		// return id.constant(constant);
		//
		// // try rewriting poly as aX+b for some pseudo monomial X...
		// AffineExpression affine = affineFactory().affine(poly);
		//
		// if (!affine.coefficient().isOne() || !affine.offset().isZero()) {
		// constant = theContext.getConstantValue(affine.pseudo());
		// if (constant != null)
		// return id.constant(
		// affineFactory().affineValue(affine, constant));
		// }
		//
		// if (debug) {
		// // out.println("simplifyPoly: starting term simplification of "
		// // + poly.id());
		// // TODO: need toString method which will check how long the
		// // description is and cut it off and use a different description
		// // instead.
		// out.flush();
		// }
		//
		// Monomial[] termMap = poly.termMap(id);
		// int size = termMap.length;
		// Monomial[] terms = new Monomial[size];
		// boolean simplified = false;
		//
		// for (int i = 0; i < size; i++) {
		// Monomial term = termMap[i];
		// Monomial simplifiedTerm = (Monomial) simplifyExpression(term);
		//
		// simplified = simplified || term != simplifiedTerm;
		// terms[i] = simplifiedTerm;
		// }
		//
		// Monomial result = simplified ? id.addMonomials(terms) : poly;
		//
		// // can't decide whether to expand or not.
		// // For now, only expanding for "=0"...
		// if (result == poly)
		// return result;
		// if (!(result instanceof Polynomial))
		// return (Monomial) simplifyExpression(result);
		// if (debug) {
		// // out.println("simplifyPoly: poly = " + poly);
		// // out.println("simplifyPoly: result = " + result);
		// }
		// poly = (Polynomial) result;
		// }
		// TODO:
		return null;
	}

//	/**
//	 * Computes a simplified version of the expression <code>monic</code>=0.
//	 * 
//	 * @param monic
//	 *            a non-<code>null</code> {@link Monic}
//	 * @return simplified expression equivalent to <code>monic</code>=0
//	 */
//	private BooleanExpression simplifiedEQ0Monic(Monic monic) {
//		NumericExpression zero = idealFactory().zero(monic.type());
//		BooleanExpression expr = idealFactory().equals(zero, monic);
//		BooleanExpression result = (BooleanExpression) simplifyExpression(expr);
//
//		return result;
//	}

//	/**
//	 * Computes a simplified version of the expression <code>monic</code>&ne;0.
//	 * 
//	 * @param monic
//	 *            a non-<code>null</code> {@link Monic}
//	 * @return simplified expression equivalent to <code>monic</code>&ne;0
//	 */
//	private BooleanExpression simplifiedNEQ0Monic(Monic monic) {
//		NumericExpression zero = idealFactory().zero(monic.type());
//		BooleanExpression expr = idealFactory().neq(zero, monic);
//		BooleanExpression result = (BooleanExpression) simplifyExpression(expr);
//
//		return result;
//	}

	// /**
	// * Given the fact that x is in the set specified by the {@link BoundType}
	// * <code>bt</code>, attempts to compute a simplified version of the
	// * expression "monic OP 0", where OP is one of le, lt, gt, or ge. Returns
	// * <code>null</code> if no simplified version is possible.
	// *
	// * @param monic
	// * @param bt
	// * @param gt
	// * @param strict
	// * @return
	// */
	// private BooleanExpression ineqFromBoundType(Monic monic, BoundType bt,
	// boolean gt, boolean strict) {
	// switch (bt) {
	// case ALL:
	// return null;
	// case EMPTY:
	// return trueExpr();
	// case EQ0:
	// return strict ? falseExpr() : trueExpr();
	// case GE0:
	// if (gt)
	// return strict ? simplifiedNEQ0Monic(monic) : trueExpr();
	// else
	// return strict ? falseExpr() : simplifiedEQ0Monic(monic);
	// case GT0:
	// return gt ? trueExpr() : falseExpr();
	// case LE0:
	// if (gt)
	// return strict ? falseExpr() : simplifiedEQ0Monic(monic);
	// else
	// return strict ? simplifiedNEQ0Monic(monic) : trueExpr();
	// case LT0:
	// return gt ? falseExpr() : trueExpr();
	// default:
	// return null;
	// }
	// }

	// TODO: use this logic in the Context2:
	
//	private BoundType getBoundTypePower(Primitive powerExpr) {
//		IdealFactory idf = idealFactory();
//		RationalExpression base = (RationalExpression) powerExpr.argument(0);
//
//		// if base>0, then base^exponent>0:
//		if (simplifyExpression(idf.isPositive(base)).isTrue())
//			return BoundType.GT0;
//		// if base>=0, then base^exponent>=0:
//		if (simplifyExpression(idf.isNonnegative(base)).isTrue())
//			return BoundType.GE0;
//
//		// if exponent is not integral or is even, base^exponent>=0:
//		RationalExpression exponent = (RationalExpression) powerExpr
//				.argument(1);
//		Number exponentNumber = idf.extractNumber(exponent);
//		NumberFactory nf = numberFactory();
//
//		if (exponentNumber != null) {
//			if (exponentNumber instanceof IntegerNumber) {
//				IntegerNumber exponentInteger = (IntegerNumber) exponentNumber;
//
//				if (nf.mod(exponentInteger, nf.integer(2)).isZero()) {
//					return BoundType.GE0;
//				}
//			} else {
//				if (!nf.isIntegral((RationalNumber) exponentNumber))
//					return BoundType.GE0;
//				else {
//					IntegerNumber exponentInteger = nf
//							.integerValue((RationalNumber) exponentNumber);
//
//					if (nf.mod(exponentInteger, nf.integer(2)).isZero())
//						return BoundType.GE0;
//				}
//			}
//		}
//		return null;
//	}

//	private Range getGeneralRange(Monic monic) {
//		Range range = theContext.getRange(monic);
//
//		if (range == null) {
//			SymbolicExpression value = theContext.getSub(monic);
//
//			if (value instanceof Constant)
//				range = info.rangeFactory
//						.singletonSet(((Constant) value).number());
//		}
//		return range;
//	}

//	private boolean containsZero(Range range) {
//		Number zero = range.isIntegral() ? info.numberFactory.zeroInteger()
//				: info.numberFactory.zeroRational();
//
//		return range.containsNumber(zero);
//	}

//	/**
//	 * <p>
//	 * Tries to compute a simplified version of the expression
//	 * <code>primitive</code>=0. Returns <code>null</code> if no simplification
//	 * is possible, else returns a {@link BooleanExpression} equivalent to
//	 * <code>primitive</code>=0.
//	 * </p>
//	 * 
//	 * <p>
//	 * Precondition: primitive has been simplified
//	 * </p>
//	 * 
//	 * @param primitive
//	 *            a non-<code>null</code>, non-constant {@link Primitive}
//	 * @return <code>null</code> or a {@link BooleanExpression} equivalent to
//	 *         <code>primitive</code>=0
//	 */
//	private BooleanExpression simplifyEQ0(Primitive primitive) {
//		Range range = theContext.getRange(primitive);
//
//		if (range != null && !containsZero(range))
//			return info.falseExpr;
//		if (primitive instanceof Polynomial)
//			return simplifyEQ0Poly((Polynomial) primitive);
//		return null;
//	}

	
	// TODO: use some of this logic in Context2 to simplify poly=0?
	
//	/**
//	 * <p>
//	 * Tries to compute a simplified version of the expression <code>poly</code>
//	 * =0. Returns <code>null</code> if no simplification is possible, else
//	 * returns a {@link BooleanExpression} equivalent to <code>poly</code>=0.
//	 * </p>
//	 * 
//	 * <p>
//	 * Pre-condition: <code>poly</code> has already gone through generic
//	 * simplification and the method {@link #simplifiedEQ0Monic(Monic)}.
//	 * </p>
//	 * 
//	 * @param primitive
//	 *            a non-<code>null</code>, non-constant {@link Polynomial}
//	 * @return <code>null</code> or a {@link BooleanExpression} equivalent to
//	 *         <code>poly</code>=0
//	 */
//	private BooleanExpression simplifyEQ0Poly(Polynomial poly) {
//		NumberFactory nf = numberFactory();
//		IdealFactory id = idealFactory();
//		SymbolicType type = poly.type();
//		AffineExpression affine = affineFactory().affine(poly);
//		Monic pseudo = affine.pseudo(); // non-null since poly non-constant
//
//		// if pseudo==poly, you have already tried looking it up
//		// in the bound map in the monic method
//		if (pseudo != poly) {
//			// aX+b=0 => -b/a=X is an integer
//			if (type.isInteger() && !nf
//					.mod((IntegerNumber) affine.offset(),
//							(IntegerNumber) nf
//									.abs((IntegerNumber) affine.coefficient()))
//					.isZero())
//				return falseExpr();
//
//			Range range = getGeneralRange(pseudo);
//
//			if (range == null)
//				return null;
//
//			Number pseudoValue = nf
//					.negate(nf.divide(affine.offset(), affine.coefficient()));
//
//			if (!range.containsNumber(pseudoValue))
//				return info.falseExpr;
//		}
//
//		RationalNumber prob = universe.getProbabilisticBound();
//
//		if (!prob.isZero()) {
//			Set<Primitive> vars = poly.getTruePrimitives();
//			IntegerNumber totalDegree = poly.totalDegree(nf);
//			int numVars = vars.size();
//			IntegerNumber numVarsNumber = nf.integer(numVars);
//			IntegerNumber product = nf.multiply(totalDegree, numVarsNumber);
//
//			if (debug) {
//				info.out.println("Poly0: product = " + product
//						+ ", threshold = " + polyProbThreshold);
//				info.out.flush();
//			}
//			if (nf.compare(product, polyProbThreshold) >= 0) {
//				if (debug) {
//					info.out.println("Entering probabalistic mode...");
//					info.out.flush();
//				}
//
//				boolean answer = is0WithProbability(poly, totalDegree, vars,
//						prob);
//
//				if (answer) {
//					info.out.print(
//							"Warning: verified probabilistically with probability of error < ");
//					info.out.println(nf.scientificString(prob, 4));
//					info.out.flush();
//					return info.trueExpr;
//				} else {
//					return info.falseExpr;
//				}
//			}
//		}
//		// is the expansion different from the term map?
//		if (poly.hasTermWithNontrivialExpansion(id)) {
//			Monomial[] termMap = poly.expand(id);
//
//			if (termMap.length == 0)
//				return trueExpr();
//
//			Monomial newMonomial = id.factorTermMap(termMap);
//			BooleanExpression newExpression = id.isZero(newMonomial);
//			BooleanExpression result = (BooleanExpression) simplifyExpression(
//					newExpression);
//
//			if (result != poly)
//				return result;
//		}
//		return null;
//	}

	// TODO: move:
	
//	/**
//	 * Chooses a random integer with uniform probability from the set of all
//	 * 2^32 ints for each variable.
//	 * 
//	 * @param poly
//	 * @return
//	 */
//	private NumericExpression evaluateAtRandomPoint32(Polynomial poly,
//			Map<SymbolicExpression, SymbolicExpression> subMap) {
//
//		for (Entry<SymbolicExpression, SymbolicExpression> entry : subMap
//				.entrySet()) {
//			// an int randomly chosen with uniform probability from
//			// the set of all 2^32 ints:
//			int randomInt = random.nextInt();
//			SymbolicExpression concrete = entry.getKey().type().isInteger()
//					? universe.integer(randomInt)
//					: universe.rational(randomInt);
//
//			entry.setValue(concrete);
//		}
//
//		NumericExpression result = (NumericExpression) universe
//				.mapSubstituter(subMap).apply(poly);
//
//		return result;
//	}
//	
	// TODO: move logic:

//	/**
//	 * Can you show that <code>poly</code> is equivalent to 0 with probability
//	 * of being wrong less than or equal to epsilon?
//	 * 
//	 * @param poly
//	 *            the {@link Polynomial} being tested for zero-ness
//	 * @param epsilon
//	 *            a real number in (0,1)
//	 * @return if this method returns true, then poly is probably 0 and the
//	 *         probability that it is not 0 is less than or equal to epsilon. If
//	 *         this method returns false, then poly is not zero.
//	 */
//	private boolean is0WithProbability(Polynomial poly,
//			IntegerNumber totalDegree, Set<Primitive> vars,
//			RationalNumber epsilon) {
//		NumberFactory nf = info.numberFactory;
//		RationalNumber prob = nf.oneRational();
//		// IntegerNumber totalDegree = poly.totalDegree(nf);
//		RationalNumber twoTo32 = nf.power(nf.rational(nf.integer(2)), 32);
//		RationalNumber ratio = nf.divide(nf.rational(totalDegree), twoTo32);
//		// Set<Primitive> vars = getTruePrimitives(poly);
//		Map<SymbolicExpression, SymbolicExpression> subMap = new HashMap<>();
//
//		for (Primitive var : vars)
//			subMap.put(var, null);
//		do {
//			NumericExpression evaluation = evaluateAtRandomPoint32(poly,
//					subMap);
//
//			if (!evaluation.isZero())
//				return false;
//			prob = nf.multiply(prob, ratio);
//		} while (nf.compare(epsilon, prob) < 0);
//		return true;
//	}

	private RationalExpression simplifyRationalExpression(
			RationalExpression expression) {
		if (expression instanceof Constant)
			return expression;

		RationalExpression result1;

		if (expression instanceof Polynomial)
			result1 = simplifyPolynomial((Polynomial) expression);
		else if (expression instanceof Monic)
			result1 = simplifyMonic((Monic) expression);
		else
			result1 = (RationalExpression) simplifyExpressionGeneric(
					expression);
		if (result1 instanceof Primitive || result1 instanceof Constant)
			return result1;

		RationalExpression result2 = simplifyPowersRational(result1);

		if (result1 == result2)
			return result1;
		return (RationalExpression) simplifyExpression(result2);
	}

	private BooleanExpression simplifyBoolean(BooleanExpression expression) {
		// TODO: shouldn't constants be caught earlier?
		if (expression.isTrue() || expression.isFalse())
			return expression;
		switch (expression.operator()) {
		case AND:
		case EQUALS:
		case EXISTS:
		case FORALL:
		case LESS_THAN:
		case LESS_THAN_EQUALS:
		case NEQ:
		case NOT:
		case OR:
			return new SubContext(info, theContext, expression)
					.getFullAssumption();
		// case APPLY:
		// case ARRAY_READ:
		// case CAST:
		// case CONCRETE:
		// case COND:
		// case DIFFERENTIABLE:
		// case SYMBOLIC_CONSTANT:
		// case TUPLE_READ:
		// case UNION_EXTRACT:
		// case UNION_TEST:
		default:
			return (BooleanExpression) simplifyExpressionGeneric(expression);
		}
	}

	// Package-private methods...

	/**
	 * Produces an expression equivalent to the claim that <code>monic</code>
	 * lies in <code>interval</code>, using simplifications supported by the
	 * current {@link #assumption}. Returns <code>null</code> if
	 * <code>interval</code> is (-&infin;,&infin;). Note that the "variable" (
	 * <code>monic</code>) is simplified using method
	 * {@link #apply(SymbolicExpression)}.
	 * 
	 * @param monic
	 *            a non-<code>null</code> {@link Monic}
	 * @param interval
	 *            a non-<code>null</code> {@link Interval} of same type as
	 *            <code>monic</code>
	 * @return <code>null</code> if <code>interval</code> is (-&infin;,&infin;),
	 *         else a {@link BooleanExpression} equivalent to the statement that
	 *         <code>monic</code> lies in <code>interval</code>
	 */
	BooleanExpression boundToIdeal(Monic monic, Interval interval) {
		Number lower = interval.lower(), upper = interval.upper();
		BooleanExpression result = null;
		// this was apply():
		Monomial ideal = (Monomial) simplifyExpressionWork(monic);
		IdealFactory idf = idealFactory();

		if (!lower.isInfinite()) {
			if (interval.strictLower())
				result = idf.lessThan(idf.constant(lower), ideal);
			else
				result = idf.lessThanEquals(idf.constant(lower), ideal);
		}
		if (!upper.isInfinite()) {
			BooleanExpression upperResult;

			if (interval.strictUpper())
				upperResult = idf.lessThan(ideal, idf.constant(upper));
			else
				upperResult = idf.lessThanEquals(ideal, idf.constant(upper));
			if (result == null)
				result = upperResult;
			else
				result = booleanFactory().and(result, upperResult);
		}
		return result;
	}

	// Interval intervalApproximation(NumericExpression expr) {
	// if (expr instanceof Monic)
	// return intervalMonic((Monic) expr);
	// if (expr instanceof Monomial)
	// return intervalMonomial((Monomial) expr);
	//
	// Monomial numerator = ((RationalExpression) expr)
	// .numerator(idealFactory());
	// Monomial denominator = ((RationalExpression) expr)
	// .denominator(idealFactory());
	// Interval i1 = intervalMonomial(numerator),
	// i2 = intervalMonomial(denominator);
	//
	// return numberFactory().divide(i1, i2);
	// }

	// Methods specified in CommonSimplifierWorker...

	@Override
	protected SymbolicObject getCachedSimplification(SymbolicObject object) {
		return theContext.getSimplification(object);
	}

	@Override
	protected void cacheSimplification(SymbolicObject object,
			SymbolicObject result) {
		theContext.cacheSimplification(object, result);
	}

	/**
	 * {@inheritDoc}
	 * 
	 * <p>
	 * This is the main simplification routine for the Ideal arithmetic package.
	 * The basic strategy is as follows:
	 * 
	 * <ul>
	 * <li>If <code>expression</code> is a {@link RationalExpression} (which is
	 * to say that it has real type --- check this), invoke
	 * {@link #simplifyRationalExpression}.</li>
	 * <li>Otherwise, if it has boolean type, try looking it up in the
	 * {@link #booleanMap()}.</li>
	 * <li>If it's boolean but not in the boolean map, but it's a numeric
	 * relational expression, try {@link #simplifyRelational(BooleanExpression)}
	 * .</li>
	 * <li>If it's not numeric, try looking it up in the
	 * {@link #otherConstantMap()}.</li>
	 * <li>If all else fails, invoke
	 * {@link #simplifyExpressionGeneric(SymbolicExpression)}.
	 * </ul>
	 * </p>
	 */
	@Override
	protected SymbolicExpression simplifyExpressionWork(
			SymbolicExpression expression) {
		SymbolicExpression result = theContext.getSub(expression);

		if (result != null)
			return result;

		SymbolicType type = expression.type();

		if (type == null)
			return expression;
		if (type.isNumeric())
			return simplifyRationalExpression((RationalExpression) expression);
		if (type.isBoolean()) {
			return simplifyBoolean((BooleanExpression) expression);
		}
		return simplifyExpressionGeneric(expression);
	}

}
