package edu.udel.cis.vsl.sarl.ideal.simplify;

import static edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator.EQUALS;
import static edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator.LESS_THAN;
import static edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator.LESS_THAN_EQUALS;
import static edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator.NEQ;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;

import edu.udel.cis.vsl.sarl.IF.CoreUniverse;
import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
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
import edu.udel.cis.vsl.sarl.number.IF.Numbers;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.simplify.common.CommonSimplifierWorker;
import edu.udel.cis.vsl.sarl.util.SingletonMap;

/**
 * An ideal simplifier worker is created by an {@link IdealSimplifier} to
 * simplify one symbolic expression. It disappears once that task has completed.
 * The {@link IdealSimplifier} is persistent and will usually continue to live
 * through the lifetime of the JVM.
 * 
 * @author siegel
 */
public class IdealSimplifierWorker extends CommonSimplifierWorker {

	// static members...

	/**
	 * A random number generator with seed very likely to be distinct from all
	 * other seeds. TODO: this must be made thread-safe.
	 */
	private static Random random = new Random();

	/**
	 * Used in a heuristic to determine when to use probabilistic methods to
	 * determine polynomial zero-ness. If the product of the number of variables
	 * and the total detree is greater than or equal to this number, the
	 * polynomial is considered too big to be expanded, and probabilistic
	 * techniques will be used instead (unless the probabilistic bound is 0).
	 */
	private final static IntegerNumber polyProbThreshold = Numbers.REAL_FACTORY
			.integer(100);

	/**
	 * A categorization of intervals based on their relationship to 0. Every
	 * interval falls into exactly one of these categories.
	 * 
	 * @author siegel
	 */
	private static enum BoundType {
		/**
		 * Every element of the interval is less than 0 and the interval is not
		 * empty.
		 */
		LT0,
		/**
		 * Every element of the interval is less than or equal to 0 and the
		 * interval contains 0 and a negative number.
		 */
		LE0,
		/** The interval consists exactly of 0 and nothing else. */
		EQ0,
		/**
		 * The interval contains 0 and a positive number and every element of
		 * the interval is greater than or equal to 0.
		 */
		GE0,
		/**
		 * Every element of the interval is greater than 0 and the interval is
		 * non-empty.
		 */
		GT0,
		/** The interval is empty */
		EMPTY,
		/** The interval contains a negative number, 0, and a positive number */
		ALL
	};

	/**
	 * Determines if the operator is one of the relation operators
	 * {@link SymbolicOperator#LESS_THAN},
	 * {@link SymbolicOperator#LESS_THAN_EQUALS},
	 * {@link SymbolicOperator#EQUALS}, or {@link SymbolicOperator#NEQ}.
	 * 
	 * @param operator
	 *            a non-<code>null</code> symbolic operator
	 * @return <code>true</code> iff <code>operator</code> is one of the four
	 *         relational operators
	 */
	private static boolean isRelational(SymbolicOperator operator) {
		switch (operator) {
		case LESS_THAN:
		case LESS_THAN_EQUALS:
		case EQUALS:
		case NEQ:
			return true;
		default:
			return false;
		}
	}

	/**
	 * Determines whether the expression is a numeric relational expression,
	 * i.e., the operator is one of the four relation operators and argument 0
	 * has numeric type.
	 * 
	 * @param expression
	 *            any non-<code>null</code> symbolic expression
	 * @return <code>true</code> iff the expression is relational with numeric
	 *         arguments
	 */
	private static boolean isNumericRelational(SymbolicExpression expression) {
		return isRelational(expression.operator())
				&& ((SymbolicExpression) expression.argument(0)).isNumeric();
	}

	// Instance fields...

	/**
	 * The context which represents the assumptions under which simplification
	 * is taking place. It is a structured representation of a boolean
	 * expression.
	 */
	private Context theContext;

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
	public IdealSimplifierWorker(SimplifierInfo info, Context context) {
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

	private PreUniverse universe() {
		return info.universe;
	}

	private BooleanExpressionFactory booleanFactory() {
		return info.booleanFactory;
	}

	private BooleanExpression falseExpr() {
		return info.falseExpr;
	}

	private BooleanExpression trueExpr() {
		return info.trueExpr;
	}

	private AffineFactory affineFactory() {
		return info.affineFactory;
	}

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
	 * Strategy: look up in {@link #constantMap()}. If found, great. Otherwise
	 * try generic simplification.
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

		Number constant = theContext.getConstantValue(monic);

		if (constant != null)
			return idealFactory().constant(constant);
		return (Monomial) simplifyExpressionGeneric(monic);
	}

	@SuppressWarnings("unused")
	private Monomial simplifyPolynomial2(Polynomial poly) {
		IdealFactory id = idealFactory();

		Number constant = theContext.getConstantValue(poly);

		if (constant != null)
			return id.constant(constant);

		// try rewriting poly as aX+b for some pseudo monomial X...
		AffineExpression affine = affineFactory().affine(poly);

		if (!affine.coefficient().isOne() || !affine.offset().isZero()) {
			constant = theContext.getConstantValue(affine.pseudo());
			if (constant != null)
				return id.constant(
						affineFactory().affineValue(affine, constant));
		}

		Monomial[] termMap = poly.termMap(id);
		int size = termMap.length;
		Monomial[] terms = new Monomial[size];
		boolean simplified = false;

		for (int i = 0; i < size; i++) {
			Monomial term = termMap[i];

			if (debug) {
				out.println("Simplifying term " + i + " of poly " + poly.id());
				out.flush();
			}

			Monomial simplifiedTerm = (Monomial) simplifyExpression(term);

			if (debug) {
				out.println("Simplification of term " + i + " of poly "
						+ poly.id() + " complete");
				out.flush();
			}

			simplified = simplified || term != simplifiedTerm;
			terms[i] = simplifiedTerm;
		}

		if (debug) {
			out.println("Adding simplified monomials of poly " + poly.id());
			out.flush();
		}

		Monomial result = simplified ? id.addMonomials(terms) : poly;

		if (debug) {
			out.println("Completed addition of simplified monomials of poly "
					+ poly.id());
			out.flush();
		}

		return result;
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
		IdealFactory id = idealFactory();

		while (true) { // repeat until stabilization
			Number constant = theContext.getConstantValue(poly);

			if (constant != null)
				return id.constant(constant);

			// try rewriting poly as aX+b for some pseudo monomial X...
			AffineExpression affine = affineFactory().affine(poly);

			if (!affine.coefficient().isOne() || !affine.offset().isZero()) {
				constant = theContext.getConstantValue(affine.pseudo());
				if (constant != null)
					return id.constant(
							affineFactory().affineValue(affine, constant));
			}

			if (debug) {
				// out.println("simplifyPoly: starting term simplification of "
				// + poly.id());
				// TODO: need toString method which will check how long the
				// description is and cut it off and use a different description
				// instead.
				out.flush();
			}

			Monomial[] termMap = poly.termMap(id);
			int size = termMap.length;
			Monomial[] terms = new Monomial[size];
			boolean simplified = false;

			for (int i = 0; i < size; i++) {
				Monomial term = termMap[i];
				Monomial simplifiedTerm = (Monomial) simplifyExpression(term);

				simplified = simplified || term != simplifiedTerm;
				terms[i] = simplifiedTerm;
			}

			Monomial result = simplified ? id.addMonomials(terms) : poly;

			// can't decide whether to expand or not.
			// For now, only expanding for "=0"...
			if (result == poly)
				return result;
			if (!(result instanceof Polynomial))
				return (Monomial) simplifyExpression(result);
			if (debug) {
				// out.println("simplifyPoly: poly = " + poly);
				// out.println("simplifyPoly: result = " + result);
			}
			poly = (Polynomial) result;
		}
	}

	/**
	 * Simplifies a relational expression. Assumes expression does not already
	 * exist in simplification cache. Does NOT assume that generic
	 * simplification has been performed on expression. Current strategy:
	 * 
	 * <pre>
	 * 1. simplifyGeneric
	 * 2. if no change: "generic" simplification
	 * 3. otherwise (change): if concrete, finished
	 * 4. otherwise (change, not concrete): look up in cache
	 * 5. if found in cache, finished
	 * 6. otherwise (change, not concrete, not cached): if relational,
	 *    simplifyRelationalWork
	 * 7. otherwise (change, not concrete, not cached, not relational):
	 *    simplifyGeneric
	 * </pre>
	 * 
	 * @param expression
	 *            any boolean expression
	 * @return simplified version of the expression, which may be the original
	 *         expression
	 */
	private BooleanExpression simplifyRelational(BooleanExpression expression) {
		BooleanExpression result1 = (BooleanExpression) simplifyExpressionGeneric(
				expression);
		// to substitute constants, etc.

		if (result1 == expression)
			return simplifyRelationalWork(expression);
		if (result1.operator() == SymbolicOperator.CONCRETE)
			return result1;

		BooleanExpression result2 = (BooleanExpression) getCachedSimplification(
				result1);

		if (result2 != null)
			return result2;
		if (isRelational(result1.operator()))
			return simplifyRelationalWork(result1);
		return (BooleanExpression) simplifyExpressionGeneric(result1);
	}

	/**
	 * Simplifies a relational expression. Assumes expression has already gone
	 * through generic simplification and result is not in cache.
	 * 
	 * @param expression
	 *            a relation expression, i.e., one in which the operator is one
	 *            of &lt;, &le;, =, &ne;.
	 * @return possibly simplified version of <code>expression</code>
	 */
	private BooleanExpression simplifyRelationalWork(
			BooleanExpression expression) {
		SymbolicOperator operator = expression.operator();
		Monomial arg0 = (Monomial) expression.argument(0),
				arg1 = (Monomial) expression.argument(1);
		BooleanExpression result;

		// 0=Primitive, 0<Monic, 0<=Monic, Monic<0, Monic<=0, 0!=Primitive.

		switch (operator) {
		case LESS_THAN:
		case LESS_THAN_EQUALS: {
			boolean strict = operator == SymbolicOperator.LESS_THAN;

			if (arg0.isZero()) {// 0<?arg1
				result = simplifyIneq0((Monic) arg1, true, strict);
			} else if (arg1.isZero()) {
				result = simplifyIneq0((Monic) arg0, false, strict);
			} else
				throw new SARLInternalException(
						"unreachable: impossible expression " + expression);
			if (result == null) {
				return expression;
			} else {
				if (debugSimps) {
					out.println("Simplify ineq input:  " + expression);
					out.println("Simplify ineq result: " + result);
					out.flush();
				}
				return result;
			}
		}
		case EQUALS: {
			assert arg0.isZero();
			// arg1 has already been simplified by apply()
			result = simplifyEQ0((Primitive) arg1);
			if (result == null) {
				return expression;
			} else {
				if (debugSimps) {
					out.println("Simplify EQ0 input : " + expression);
					out.println("Simplify EQ0 result: " + result);
					out.flush();
				}
				return result;
			}
		}
		case NEQ: {
			assert arg0.isZero();

			BooleanExpression negExpression = universe().not(expression);

			result = (BooleanExpression) simplifyExpression(negExpression);
			result = universe().not(result);
			return result;
		}
		default:
			throw new SARLInternalException("unreachable");
		}
	}

	/**
	 * Computes a simplified version of the expression <code>monic</code>=0.
	 * 
	 * @param monic
	 *            a non-<code>null</code> {@link Monic}
	 * @return simplified expression equivalent to <code>monic</code>=0
	 */
	private BooleanExpression simplifiedEQ0Monic(Monic monic) {
		NumericExpression zero = idealFactory().zero(monic.type());
		BooleanExpression expr = idealFactory().equals(zero, monic);
		BooleanExpression result = (BooleanExpression) simplifyExpression(expr);

		return result;
	}

	/**
	 * Computes a simplified version of the expression <code>monic</code>&ne;0.
	 * 
	 * @param monic
	 *            a non-<code>null</code> {@link Monic}
	 * @return simplified expression equivalent to <code>monic</code>&ne;0
	 */
	private BooleanExpression simplifiedNEQ0Monic(Monic monic) {
		NumericExpression zero = idealFactory().zero(monic.type());
		BooleanExpression expr = idealFactory().neq(zero, monic);
		BooleanExpression result = (BooleanExpression) simplifyExpression(expr);

		return result;
	}

	/**
	 * Computes the bound type of the given {@link Interval}.
	 * 
	 * @param interval
	 *            a non-<code>null</code> {@link Interval}
	 * @return the unique category (instance of {@link BoundType}) into which
	 *         <code>interval</code> falls
	 */
	private BoundType boundType(Interval interval) {
		if (interval.isEmpty())
			return BoundType.EMPTY;

		Number l = interval.lower(), r = interval.upper();
		int lsign = l == null ? -1 : l.signum();
		int rsign = r == null ? 1 : r.signum();

		if (lsign > 0)
			return BoundType.GT0;
		if (rsign < 0)
			return BoundType.LT0;

		if (lsign < 0) {
			if (rsign == 0) {
				return interval.strictUpper() ? BoundType.LT0 : BoundType.LE0;
			} else { // rsign > 0
				return BoundType.ALL;
			}
		} else { // lsign == 0
			if (rsign == 0) {
				return BoundType.EQ0;
			} else { // rsign > 0
				return interval.strictLower() ? BoundType.GT0 : BoundType.GE0;
			}
		}
	}

	/**
	 * Given the fact that x is in the set specified by the {@link BoundType}
	 * <code>bt</code>, attempts to compute a simplified version of the
	 * expression "monic OP 0", where OP is one of le, lt, gt, or ge. Returns
	 * <code>null</code> if no simplified version is possible.
	 * 
	 * @param monic
	 * @param bt
	 * @param gt
	 * @param strict
	 * @return
	 */
	private BooleanExpression ineqFromBoundType(Monic monic, BoundType bt,
			boolean gt, boolean strict) {
		switch (bt) {
		case ALL:
			return null;
		case EMPTY:
			return trueExpr();
		case EQ0:
			return strict ? falseExpr() : trueExpr();
		case GE0:
			if (gt)
				return strict ? simplifiedNEQ0Monic(monic) : trueExpr();
			else
				return strict ? falseExpr() : simplifiedEQ0Monic(monic);
		case GT0:
			return gt ? trueExpr() : falseExpr();
		case LE0:
			if (gt)
				return strict ? falseExpr() : simplifiedEQ0Monic(monic);
			else
				return strict ? simplifiedNEQ0Monic(monic) : trueExpr();
		case LT0:
			return gt ? falseExpr() : trueExpr();
		default:
			return null;
		}
	}

	/**
	 * Given a {@link Monic}, returns an interval over-approximation of the
	 * values that can be assumed by that monic under the assumptions of this
	 * simplifier.
	 * 
	 * @param monic
	 *            a non-<code>null</code> {@link Monic}
	 * @return a non-<code>null</code> {@link Interval} of same type as
	 *         <code>monic</code> containing all values that can be assumed by
	 *         <code>monic</code>
	 */
	private Interval intervalMonic(Monic monic) {
		Interval result = theContext.getBound(monic);

		if (result == null) {
			BoundType type = getBoundTypeMonic(monic);

			if (type == null) {
				NumberFactory nf = numberFactory();

				result = monic.type().isInteger()
						? nf.universalIntegerInterval()
						: nf.universalRealInterval();
			} else
				result = intervalOfBoundType(type, monic.type().isInteger());
		}
		return result;
	}

	private Interval intervalMonomial(Monomial monomial) {
		return numberFactory().multiply(
				monomial.monomialConstant(idealFactory()).number(),
				intervalMonic(monomial.monic(idealFactory())));
	}

	private Interval intervalOfBoundType(BoundType type, boolean isInteger) {
		NumberFactory nf = numberFactory();

		switch (type) {
		case ALL:
			return isInteger ? nf.universalIntegerInterval()
					: nf.universalRealInterval();
		case EMPTY:
			return isInteger ? nf.emptyIntegerInterval()
					: nf.emptyRealInterval();
		case EQ0:
			return nf.singletonInterval(
					isInteger ? nf.zeroInteger() : nf.zeroRational());
		case GE0:
			return nf.newInterval(isInteger,
					isInteger ? nf.zeroInteger() : nf.zeroRational(), false,
					null, true);
		case GT0:
			return nf.newInterval(isInteger,
					isInteger ? nf.zeroInteger() : nf.zeroRational(), true,
					null, true);
		case LE0:
			return nf.newInterval(isInteger, null, true,
					isInteger ? nf.zeroInteger() : nf.zeroRational(), false);
		case LT0:
			return nf.newInterval(isInteger, null, true,
					isInteger ? nf.zeroInteger() : nf.zeroRational(), true);
		}
		throw new SARLInternalException("unreachable");
	}

	private BoundType getBoundTypePower(Primitive powerExpr) {
		IdealFactory idf = idealFactory();
		RationalExpression base = (RationalExpression) powerExpr.argument(0);

		// if base>0, then base^exponent>0:
		if (simplifyExpression(idf.isPositive(base)).isTrue())
			return BoundType.GT0;
		// if base>=0, then base^exponent>=0:
		if (simplifyExpression(idf.isNonnegative(base)).isTrue())
			return BoundType.GE0;

		// if exponent is not integral or is even, base^exponent>=0:
		RationalExpression exponent = (RationalExpression) powerExpr
				.argument(1);
		Number exponentNumber = idf.extractNumber(exponent);
		NumberFactory nf = numberFactory();

		if (exponentNumber != null) {
			if (exponentNumber instanceof IntegerNumber) {
				IntegerNumber exponentInteger = (IntegerNumber) exponentNumber;

				if (nf.mod(exponentInteger, nf.integer(2)).isZero()) {
					return BoundType.GE0;
				}
			} else {
				if (!nf.isIntegral((RationalNumber) exponentNumber))
					return BoundType.GE0;
				else {
					IntegerNumber exponentInteger = nf
							.integerValue((RationalNumber) exponentNumber);

					if (nf.mod(exponentInteger, nf.integer(2)).isZero())
						return BoundType.GE0;
				}
			}
		}
		return null;
	}

	private BoundType getBoundTypeMonic(Monic monic) {
		if (monic.isOne())
			return BoundType.GT0;

		Interval monicBound = theContext.getBound(monic);

		if (monicBound != null)
			return boundType(monicBound);

		SymbolicOperator op = monic.operator();

		if (op == SymbolicOperator.POWER) {
			return getBoundTypePower((Primitive) monic);
		}
		return null;
	}

	/**
	 * Simplifies an inequality of one of the forms: x&gt;0, x&ge;0, x&lt;0,
	 * x&le;0, where x is a {@link Monic} in which the maximum degree of any
	 * {@link Primitive} is 1. Assumes <code>monic</code> is already simplified.
	 * 
	 * @param monic
	 *            a non-<code>null</code>, simplified, {@link Monic}
	 * @param gt
	 *            is the condition one of x&gt;0 or x&ge;0 (i.e., not x&lt;0 or
	 *            x&le;0)
	 * @param strict
	 *            is the form one of x&gt;0 or x&lt;0 (strict inequality)
	 * @return simplified version of the inequality or <code>null</code> if no
	 *         simplification was possible
	 */
	private BooleanExpression simplifyIneq0(Monic monic, boolean gt,
			boolean strict) {
		SymbolicType type = monic.type();
		BooleanExpression result = null;
		BoundType boundType = getBoundTypeMonic(monic);

		if (boundType != null) {
			result = ineqFromBoundType(monic, boundType, gt, strict);
			return result;
		}
		if (monic instanceof Polynomial)
			return simplifyIneq0Poly((Polynomial) monic, gt, strict);
		if (monic instanceof Primitive)
			return null;

		// look for bounds on the primitive factors...
		PrimitivePower[] factorMap = monic.monicFactors(idealFactory());
		int numFactors = factorMap.length;
		boolean[] mask = new boolean[numFactors]; // unconstrained primitives
		List<Primitive> zeroList = new LinkedList<>();
		boolean positive = gt;
		int count = 0, unconstrained = 0;

		for (PrimitivePower pp : factorMap) {
			Primitive p = pp.primitive(idealFactory());
			BoundType primitiveBoundType = getBoundTypeMonic(p);

			if (primitiveBoundType == null) {
				mask[count] = true;
				unconstrained++;
			} else {
				switch (primitiveBoundType) {
				case ALL:
					mask[count] = true;
					unconstrained++;
					break;
				case EMPTY:
					// this means there is an inconsistency. this should have
					// been dealt with immediately when the inconsistency was
					// found
					throw new SARLInternalException(
							"unreachable: inconsistent primitive: " + p);
				case EQ0:
					// if one factor is 0, the whole product is 0
					return strict ? falseExpr() : trueExpr();
				case GE0:
					// assume x>=0.
					// xy>=0 <=> x=0 || y>=0.
					// xy>0 <=> x!=0 && y>0.
					// xy<=0 <=> x=0 || y<=0.
					// xy<0 <=> x!=0 && y<0.
					zeroList.add(p);
					break;
				case GT0:
					// assume x>0.
					// xy>=0 <=> y>=0.
					// xy>0 <=> y>0.
					// xy<=0 <=> y<=0.
					// xy<0 <=> y<0.
					break;
				case LE0:
					// assume x<=0.
					// xy>=0 <=> x=0 || y<=0.
					// xy>0 <=> x!=0 && y<0.
					// xy<=0 <=> x=0 || y>=0.
					// xy<0 <=> x!=0 && y>0.
					zeroList.add(p);
					positive = !positive;
					break;
				case LT0:
					positive = !positive;
					break;
				default:
					throw new SARLInternalException("unreachable");
				}
			}
			count++;
		}
		if (numFactors == unconstrained)
			// everything unconstrained; no simplification possible
			return null;

		BooleanExpressionFactory bf = booleanFactory();
		Monomial zero = idealFactory().zero(type);

		if (unconstrained > 0) {
			// create new Monic from the unconstrained primitives
			Monic newMonic = idealFactory().monicMask(monic, mask);
			SymbolicOperator op = strict ? LESS_THAN : LESS_THAN_EQUALS;

			result = positive ? bf.booleanExpression(op, zero, newMonic)
					: bf.booleanExpression(op, newMonic, zero);
		} else { // newMonic is essentially 1
			result = positive ? trueExpr() : falseExpr();
		}
		// if strict: conjunction (&&) with !=0 from zeroList
		// if !strict: disjunction(||) with ==0 from zeroList
		if (strict) {
			for (Primitive p : zeroList)
				result = bf.and(result, bf.booleanExpression(NEQ, zero, p));
		} else {
			for (Primitive p : zeroList)
				result = bf.or(result, bf.booleanExpression(EQUALS, zero, p));
		}
		return result;
	}

	/**
	 * <p>
	 * Simplifies expression poly OP 0, where poly is a {@link Polynomial} and
	 * OP is one of LT, LE, GT, or GE.
	 * </p>
	 * 
	 * Preconditions:
	 * <ul>
	 * <li>there is no entry in the {@link #constantMap()} for <code>poly</code>
	 * </li>
	 * <li><code>poly</code> is fully expanded</li>
	 * <li><code>poly</code> has at least 2 terms</li>
	 * </ul>
	 * 
	 * @param poly
	 *            a {@link Polynomial} with at least 2 terms
	 * @param gt
	 *            is the condition one of <code>poly</code>&gt;0 or
	 *            <code>poly</code>&ge;0 ?
	 * @param strict
	 *            is the inequality strict, i.e., is the condition one of
	 *            <code>poly</code>&gt;0 or <code>poly</code>&lt;0 ?
	 * @return <code>null</code> if there is no way to express the constraint
	 *         beyond the obvious, else an expression equivalent to
	 *         <code>poly</code> OP 0, where the OP is the inequality operator
	 *         specified by <code>gt</code> and <code>strict</code>
	 */
	private BooleanExpression simplifyIneq0Poly(Polynomial poly, boolean gt,
			boolean strict) {
		AffineExpression affine = affineFactory().affine(poly);
		Monic pseudo = affine.pseudo(); // non-null since zep non-constant
		Number pseudoValue = theContext.getConstantValue(pseudo);
		AffineFactory af = affineFactory();

		if (pseudoValue != null) {
			// substitute known constant value for pseudo...
			Number val = af.affineValue(affine, pseudoValue);
			int sgn = val.signum();
			BooleanExpression result;

			if (gt) {
				result = (strict ? sgn > 0 : sgn >= 0) ? trueExpr()
						: falseExpr();
			} else {
				result = (strict ? sgn < 0 : sgn <= 0) ? trueExpr()
						: falseExpr();
			}
			return result;
		}

		Interval pseudoBound = theContext.getBound(pseudo);

		if (pseudoBound == null)
			return null;

		// the following is a bound on poly
		Interval polyBound = numberFactory().affineTransform(pseudoBound,
				affine.coefficient(), affine.offset());
		BoundType boundType = boundType(polyBound);
		BooleanExpression result = ineqFromBoundType(poly, boundType, gt,
				strict);

		return result;
	}

	/**
	 * <p>
	 * Tries to compute a simplified version of the expression
	 * <code>primitive</code>=0. Returns <code>null</code> if no simplification
	 * is possible, else returns a {@link BooleanExpression} equivalent to
	 * <code>primitive</code>=0.
	 * </p>
	 * 
	 * <p>
	 * Precondition: primitive has been simplified
	 * </p>
	 * 
	 * @param primitive
	 *            a non-<code>null</code>, non-constant {@link Primitive}
	 * @return <code>null</code> or a {@link BooleanExpression} equivalent to
	 *         <code>primitive</code>=0
	 */
	private BooleanExpression simplifyEQ0(Primitive primitive) {
		Interval interval = theContext.getBound(primitive);

		if (interval != null) {
			Number lo = interval.lower();

			if (lo != null) {
				int los = lo.signum();

				if (los > 0 || (los == 0 && interval.strictLower()))
					return falseExpr();
			}

			Number hi = interval.upper();

			if (hi != null) {
				int his = hi.signum();

				if (his < 0 || (his == 0 && interval.strictUpper()))
					return falseExpr();
			}
		}
		if (primitive instanceof Polynomial)
			return simplifyEQ0Poly((Polynomial) primitive);
		return null;
	}

	/**
	 * <p>
	 * Tries to compute a simplified version of the expression <code>poly</code>
	 * =0. Returns <code>null</code> if no simplification is possible, else
	 * returns a {@link BooleanExpression} equivalent to <code>poly</code>=0.
	 * </p>
	 * 
	 * <p>
	 * Pre-condition: <code>poly</code> has already gone through generic
	 * simplification and the method {@link #simplifiedEQ0Monic(Monic)}. So
	 * there is no need to look in the {@link #constantMap()} or
	 * {@link #boundMap()} for <code>poly</code>.
	 * </p>
	 * 
	 * @param primitive
	 *            a non-<code>null</code>, non-constant {@link Polynomial}
	 * @return <code>null</code> or a {@link BooleanExpression} equivalent to
	 *         <code>poly</code>=0
	 */
	private BooleanExpression simplifyEQ0Poly(Polynomial poly) {
		NumberFactory nf = numberFactory();
		IdealFactory id = idealFactory();
		SymbolicType type = poly.type();
		AffineExpression affine = affineFactory().affine(poly);
		Monic pseudo = affine.pseudo(); // non-null since zep non-constant

		// if pseudo==poly, you have already tried looking it up
		// in the bound map in the monic method
		if (pseudo != poly) {
			// aX+b=0 => -b/a=X is an integer
			if (type.isInteger() && !nf
					.mod((IntegerNumber) affine.offset(),
							(IntegerNumber) nf
									.abs((IntegerNumber) affine.coefficient()))
					.isZero())
				return falseExpr();

			Interval interval = theContext.getBound(pseudo);

			if (interval == null)
				return null;

			Number pseudoValue = nf
					.negate(nf.divide(affine.offset(), affine.coefficient()));

			// Know: lower <? pseudoValue <? upper
			// (Here "<?" means "<" or "<=".). So
			// lower - pseudoValue <? 0
			// upper - pseudoValue >? 0
			// if either of these is not true, you have a contradiction,
			// simplify to "false".
			// leftSign = sign of (lower-pseudoValue)
			// rightSign = sign of (upper-pseudoValue)

			Number lower = interval.lower();
			int leftSign = lower == null ? -1
					: nf.subtract(lower, pseudoValue).signum();

			// if 0 is not in that interval, return FALSE
			if (leftSign > 0 || (leftSign == 0 && interval.strictLower()))
				return falseExpr();

			Number upper = interval.upper();
			int rightSign = upper == null ? 1
					: nf.subtract(upper, pseudoValue).signum();

			if (rightSign < 0 || (rightSign == 0 && interval.strictUpper()))
				return falseExpr();
		}

		RationalNumber prob = universe.getProbabilisticBound();

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
					info.out.println("Entering probabalistic mode...");
					info.out.flush();
				}

				boolean answer = is0WithProbability(poly, totalDegree, vars,
						prob);

				if (answer) {
					info.out.print(
							"Warning: verified probabilistically with probability of error < ");
					info.out.println(nf.scientificString(prob, 4));
					info.out.flush();
					return info.trueExpr;
				} else {
					return info.falseExpr;
				}
			}
		}
		// is the expansion different from the term map?
		if (poly.hasTermWithNontrivialExpansion(id)) {
			Monomial[] termMap = poly.expand(id);

			if (termMap.length == 0)
				return trueExpr();

			Monomial newMonomial = id.factorTermMap(termMap);
			BooleanExpression newExpression = id.isZero(newMonomial);
			BooleanExpression result = (BooleanExpression) simplifyExpression(
					newExpression);

			if (result.operator() != SymbolicOperator.EQUALS
					|| !((SymbolicExpression) result.argument(0)).isZero()
					|| result.argument(1) != poly)
				return result;
		}
		return null;
	}

	/**
	 * Searches for a "true" primitive (i.e., an instance of {@link Primitive}
	 * which is not a {@link Polynomial}) in the expression <code>expr</code>.
	 * The search is recursive on the structure but backtracks as soon as a node
	 * which is not a {@link RationalExpression} is encountered.
	 * 
	 * @param expr
	 * @return
	 */
	private Primitive findATruePrimitive(Monomial m) {
		if (m instanceof Primitive && !(m instanceof Polynomial))
			return (Primitive) m;
		switch (m.operator()) {
		case ADD:
		case MULTIPLY:
			int n = m.numArguments();

			for (int i = 0; i < n; i++) {
				SymbolicObject arg = m.argument(i);
				Primitive p = findATruePrimitive((Monomial) arg);

				if (p != null)
					return p;
			}
			return null;
		case POWER:
			return findATruePrimitive((Monomial) m.argument(0));
		default:
			return null;
		}
	}

	/*
	 * private void addTruePrimitives(Monomial m, Set<Primitive> set) { if (m
	 * instanceof Primitive && !(m instanceof Polynomial)) { set.add((Primitive)
	 * m); } else { switch (m.operator()) { case ADD: case MULTIPLY: int n =
	 * m.numArguments();
	 * 
	 * for (int i = 0; i < n; i++) { SymbolicObject arg = m.argument(i);
	 * 
	 * addTruePrimitives((Monomial) arg, set); } break; case POWER:
	 * addTruePrimitives((Monomial) m.argument(0), set); break; default: } } }
	 * 
	 * private Set<Primitive> getTruePrimitives(Monomial m) { Set<Primitive> set
	 * = new HashSet<>();
	 * 
	 * addTruePrimitives(m, set); return set; }
	 */

	/**
	 * Chooses a random integer with uniform probability from the set of all
	 * 2^32 ints for each variable.
	 * 
	 * @param poly
	 * @return
	 */
	private NumericExpression evaluateAtRandomPoint32(Polynomial poly,
			Map<SymbolicExpression, SymbolicExpression> subMap) {

		for (Entry<SymbolicExpression, SymbolicExpression> entry : subMap
				.entrySet()) {
			// an int randomly chosen with uniform probability from
			// the set of all 2^32 ints:
			int randomInt = random.nextInt();
			SymbolicExpression concrete = entry.getKey().type().isInteger()
					? universe.integer(randomInt)
					: universe.rational(randomInt);

			entry.setValue(concrete);
		}

		NumericExpression result = (NumericExpression) universe
				.mapSubstituter(subMap).apply(poly);

		return result;
	}

	/**
	 * Can you show that <code>poly</code> is equivalent to 0 with probability
	 * of being wrong less than or equal to epsilon?
	 * 
	 * @param poly
	 *            the {@link Polynomial} being tested for zero-ness
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
		// IntegerNumber totalDegree = poly.totalDegree(nf);
		RationalNumber twoTo32 = nf.power(nf.rational(nf.integer(2)), 32);
		RationalNumber ratio = nf.divide(nf.rational(totalDegree), twoTo32);
		// Set<Primitive> vars = getTruePrimitives(poly);
		Map<SymbolicExpression, SymbolicExpression> subMap = new HashMap<>();

		for (Primitive var : vars)
			subMap.put(var, null);
		do {
			NumericExpression evaluation = evaluateAtRandomPoint32(poly,
					subMap);

			if (!evaluation.isZero())
				return false;
			prob = nf.multiply(prob, ratio);
		} while (nf.compare(epsilon, prob) < 0);
		return true;
	}

	/**
	 * This one attempts to simplify an expression of the form poly=0 by
	 * evaluating the primitives at each point on a discrete finite grid.
	 * Specifically, let P be the set of primitives that occur in poly. Let
	 * deg(p) be the maximum degree for which p occurs. In the grid, p takes on
	 * all integer values from 0 to deg(p) (inclusive). The number of points in
	 * the grid is therefore the product over all p in P of (1+deg(p)).
	 * 
	 * Approach: pick a primitive, find its max degree. Take conjunction over
	 * i=0,...,deg(p), of the result of simplifying poly[p/i]=0. Here poly[p/i]
	 * is the expression that results from substituting i for p in poly.
	 * 
	 * Currently not used --- slower than expansion for most cases.
	 * 
	 * @param poly
	 * @return
	 */
	@SuppressWarnings("unused")
	private boolean is0byEvaluation(Polynomial poly) {
		IdealFactory id = idealFactory();
		Primitive primitive = findATruePrimitive(poly);

		assert primitive != null;

		IntegerNumber deg = poly.maxDegreeOf(id.numberFactory(), primitive);

		if (debugSimps) {
			out.println("Max degree of " + primitive + " is " + deg);
			out.flush();
		}

		BooleanExpression result = trueExpr();
		SymbolicType type = poly.type();
		boolean isInteger = type.isInteger();

		for (int i = 0; id.numberFactory().integer(i)
				.numericalCompareTo(deg) <= 0; i++) {
			SymbolicExpression point = isInteger ? universe().integer(i)
					: universe().rational(i);
			Map<SymbolicExpression, SymbolicExpression> map = new SingletonMap<>(
					primitive, point);
			UnaryOperator<SymbolicExpression> substituter = universe()
					.mapSubstituter(map);
			Monomial newExpr = ((RationalExpression) substituter.apply(poly))
					.numerator(id);
			BooleanExpression clause = id.isZero(newExpr);

			clause = (BooleanExpression) simplifyExpression(clause);
			result = universe().and(result, clause);
			if (result.isFalse())
				break;
		}
		return result.isTrue();
	}

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

	Interval intervalApproximation(NumericExpression expr) {
		if (expr instanceof Monic)
			return intervalMonic((Monic) expr);
		if (expr instanceof Monomial)
			return intervalMonomial((Monomial) expr);

		Monomial numerator = ((RationalExpression) expr)
				.numerator(idealFactory());
		Monomial denominator = ((RationalExpression) expr)
				.denominator(idealFactory());
		Interval i1 = intervalMonomial(numerator),
				i2 = intervalMonomial(denominator);

		return numberFactory().divide(i1, i2);
	}

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
		if (expression instanceof RationalExpression)
			return simplifyRationalExpression((RationalExpression) expression);

		SymbolicType type = expression.type();

		if (type != null) {
			if (type.isBoolean()) {
				if (expression.isTrue() || expression.isFalse())
					return expression;

				Boolean booleanResult = theContext
						.getTruth((BooleanExpression) expression);

				if (booleanResult != null) {
					SymbolicExpression result = booleanResult ? trueExpr()
							: falseExpr();

					if (debugSimps) {
						out.println("Simplifier boolean :" + expression);
						out.println("Simplifier result  :" + result);
					}
					return result;
				}
				if (isNumericRelational(expression))
					return simplifyRelational((BooleanExpression) expression);
			} else {
				// if (!type.isNumeric()) {
				SymbolicExpression constant = theContext
						.getOtherValue(expression);

				if (constant != null) {
					if (debugSimps) {
						out.println("Simplify constant expr   : " + expression);
						out.println("Simplify constant result: " + constant);
					}
					return constant;
				}
			}
		}
		return simplifyExpressionGeneric(expression);
	}

}
