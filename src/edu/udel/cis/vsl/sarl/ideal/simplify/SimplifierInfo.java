/*******************************************************************************
 * Copyright (c) 2013 Stephen F. Siegel, University of Delaware.
 * 
 * This file is part of SARL.
 * 
 * SARL is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free
 * Software Foundation, either version 3 of the License, or (at your option) any
 * later version.
 * 
 * SARL is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE. See the GNU Lesser General Public License for more
 * details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with SARL. If not, see <http://www.gnu.org/licenses/>.
 ******************************************************************************/
package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.io.PrintStream;
import java.util.Comparator;

import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.IF.BooleanExpressionFactory;
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
import edu.udel.cis.vsl.sarl.simplify.IF.Simplify;
import edu.udel.cis.vsl.sarl.util.Pair;

/**
 * An object that gathers together a variety of objects as fields needed to
 * perform simplification.
 * 
 * @author siegel
 * 
 */
public class SimplifierInfo {

	// put this in info?
	// private class ArrayFactComparator implements Comparator<ArrayFact> {
	//
	// private Comparator<SymbolicObject> ec;
	//
	// ArrayFactComparator(Comparator<SymbolicObject> ec) {
	// this.ec = ec;
	// }
	//
	// @Override
	// public int compare(ArrayFact o1, ArrayFact o2) {
	// int result = ec.compare(o1.array, o2.array);
	//
	// if (result != 0)
	// return result;
	//
	// int n = o1.boundVars.length;
	//
	// result = n - o2.boundVars.length;
	// if (result != 0)
	// return result;
	// for (int i = 0; i < n; i++) {
	// result = ec.compare(o1.boundVars[i], o2.boundVars[i]);
	// if (result != 0)
	// return result;
	// }
	// result = ec.compare(o1.constraint, o2.constraint);
	// if (result != 0)
	// return result;
	// n = o1.indexExprs.length;
	// result = n - o2.indexExprs.length;
	// if (result != 0)
	// return result;
	// for (int i = 0; i < n; i++) {
	// result = ec.compare(o1.indexExprs[i], o2.indexExprs[i]);
	// if (result != 0)
	// return result;
	// }
	// result = ec.compare(o1.value, o2.value);
	// return result;
	// }
	// }

	/**
	 * Treat every polynomial as a linear combination of monomials, so Gaussian
	 * elimination is performed on all equalities, and not just degree 1
	 * equalities.
	 */
	boolean linearizePolynomials = true;

	/** Print lots of stuff. */
	boolean verbose = false;

	PreUniverse universe;

	IdealFactory idealFactory;

	NumberFactory numberFactory;

	RangeFactory rangeFactory;

	BooleanExpressionFactory booleanFactory;

	AffineFactory affineFactory;

	PrintStream out;

	BooleanExpression trueExpr;

	BooleanExpression falseExpr;

	// Range[][] signRanges;

	/**
	 * An ordering on symbolic constants. [Could put this in info.]
	 */
	Comparator<SymbolicConstant> variableComparator;

	// Comparator<ArrayFact> arrayFactComparator;

	/**
	 * An ordering on {@link Monic}s.
	 */
	Comparator<Monic> monicComparator;

	SimplifierInfo(PreUniverse universe, IdealFactory idealFactory) {
		this.idealFactory = idealFactory;
		this.universe = universe;
		this.affineFactory = new AffineFactory(idealFactory);
		this.booleanFactory = idealFactory.booleanFactory();
		this.falseExpr = (BooleanExpression) universe.bool(false);
		this.trueExpr = (BooleanExpression) universe.bool(true);
		this.numberFactory = universe.numberFactory();
		this.rangeFactory = Simplify.newIntervalUnionFactory();
		this.out = System.out;
		// do this once and put it in universe...
		this.variableComparator = new Comparator<SymbolicConstant>() {
			Comparator<SymbolicType> typeComparator = universe.typeFactory()
					.typeComparator();

			@Override
			public int compare(SymbolicConstant o1, SymbolicConstant o2) {
				int result = o1.name().compareTo(o2.name());

				if (result != 0)
					return result;
				return typeComparator.compare(o1.type(), o2.type());
			}
		};
		this.monicComparator = idealFactory.monicComparator();
		// this.arrayFactComparator = new ArrayFactComparator(
		// universe.comparator());

		// case ALL: // (-infty,infty)
		// case EMPTY: // empty
		// case EQ0: // [0,0]
		// case GE0: // [0,infty)
		// case GT0: // (0,infty)
		// case LE0: // (-infty, 0]
		// case LT0: // (-infty, 0)
		// this.signRanges = new Range[2][];
		// signRanges[0] = new Range[] {
		// rangeFactory.interval(true,
		// numberFactory.infiniteNumber(true, false), true,
		// numberFactory.infiniteNumber(true, true), true),
		// rangeFactory.emptySet(true),
		// rangeFactory.singletonSet(numberFactory.zeroInteger()),
		// rangeFactory.interval(true, numberFactory.zeroInteger(), false,
		// numberFactory.infiniteNumber(true, true), true),
		// rangeFactory.interval(true, numberFactory.zeroInteger(), true,
		// numberFactory.infiniteNumber(true, true), true),
		// rangeFactory.interval(true,
		// numberFactory.infiniteNumber(true, false), true,
		// numberFactory.zeroInteger(), false),
		// rangeFactory.interval(true,
		// numberFactory.infiniteNumber(true, false), true,
		// numberFactory.integer(-1), false) };
		// signRanges[1] = new Range[] {
		// rangeFactory.interval(false,
		// numberFactory.infiniteNumber(true, false), true,
		// numberFactory.infiniteNumber(true, true), true),
		// rangeFactory.emptySet(false),
		// rangeFactory.singletonSet(numberFactory.zeroInteger()),
		// rangeFactory.interval(false, numberFactory.zeroInteger(), false,
		// numberFactory.infiniteNumber(true, true), true),
		// rangeFactory.interval(false, numberFactory.zeroInteger(), true,
		// numberFactory.infiniteNumber(true, true), true),
		// rangeFactory.interval(false,
		// numberFactory.infiniteNumber(true, false), true,
		// numberFactory.zeroInteger(), false),
		// rangeFactory.interval(false,
		// numberFactory.infiniteNumber(true, false), true,
		// numberFactory.zeroInteger(), true) };
	}

	// /**
	// * A categorization of intervals based on their relationship to 0. Every
	// * interval falls into exactly one of these categories.
	// *
	// * @author siegel
	// */
	// static enum BoundType {
	// /**
	// * Every element of the interval is less than 0 and the interval is not
	// * empty.
	// */
	// LT0,
	// /**
	// * Every element of the interval is less than or equal to 0 and the
	// * interval contains 0 and a negative number.
	// */
	// LE0,
	// /** The interval consists exactly of 0 and nothing else. */
	// EQ0,
	// /**
	// * The interval contains 0 and a positive number and every element of
	// * the interval is greater than or equal to 0.
	// */
	// GE0,
	// /**
	// * Every element of the interval is greater than 0 and the interval is
	// * non-empty.
	// */
	// GT0,
	// /** The interval is empty */
	// EMPTY,
	// /** The interval contains a negative number, 0, and a positive number */
	// ALL
	// };

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
	static boolean isRelational(SymbolicOperator operator) {
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
	static boolean isNumericRelational(SymbolicExpression expression) {
		return isRelational(expression.operator())
				&& ((SymbolicExpression) expression.argument(0)).isNumeric();
	}

	/**
	 * Converts a numeric relational expression to a constraint on a
	 * {@link Monic}. Returns <code>null</code> if this is not possible.
	 * 
	 * @param relationalExpr
	 * @return
	 */
	Pair<Monic, Range> comparisonToRange(BooleanExpression relationalExpr) {
		SymbolicOperator op = relationalExpr.operator();

		if (!isRelational(op))
			return null;

		SymbolicExpression left = (SymbolicExpression) relationalExpr
				.argument(0);
		SymbolicType type = left.type();

		if (!type.isNumeric())
			return null;

		boolean isInteger = type.isInteger();
		NumberFactory nf = numberFactory;
		RangeFactory rf = rangeFactory;
		boolean leftIsZero = left.isZero();
		Monic expr = leftIsZero ? (Monic) relationalExpr.argument(1)
				: (Monic) left;
		Number pos_inf = isInteger ? nf.positiveInfinityInteger()
				: nf.positiveInfinityRational();
		Number neg_inf = isInteger ? nf.negativeInfinityInteger()
				: nf.negativeInfinityRational();
		Range range;
		Monic monic;

		if (expr instanceof Polynomial) {
			// aX+b<0, aX+b<=0, aX+b==0, aX+b>=0, aX+b>0, aX+b!=0
			// convert to inequality on X
			Polynomial poly = (Polynomial) expr;
			AffineExpression affine = affineFactory.affine(poly);
			Number a = affine.coefficient();
			Number b = affine.offset();
			RationalNumber a_rat, b_rat;

			monic = affine.pseudo();
			if (isInteger) {
				a_rat = nf.integerToRational((IntegerNumber) a);
				b_rat = nf.integerToRational((IntegerNumber) b);
			} else {
				a_rat = (RationalNumber) a;
				b_rat = (RationalNumber) b;
			}

			RationalNumber c = nf.negate(nf.divide(b_rat, a_rat));
			boolean aIsNeg = a.signum() < 0;

			switch (op) {
			case LESS_THAN:
				assert !isInteger;
				if (leftIsZero == aIsNeg) {
					// 0<aX+b and a<0 => X<-b/a=c
					// aX+b<0 and a>0 => X<-b/a=c
					// if (isInteger)
					// range = rf.interval(null, true,
					// nf.ceil(nf.decrement(c)), false, true);
					// else
					range = rf.interval(false, neg_inf, true, c, true);
				} else { // X>c
					// if (isInteger)
					// range = rf.interval(nf.floor(nf.increment(c)), false,
					// null, true, true);
					// else
					range = rf.interval(false, c, true, pos_inf, true);
				}
				break;
			case LESS_THAN_EQUALS:
				if (leftIsZero == aIsNeg) // X<=c
					range = rf.interval(isInteger, neg_inf, true,
							isInteger ? nf.floor(c) : c, false);
				else // X>=c
					range = rf.interval(isInteger, isInteger ? nf.ceil(c) : c,
							false, pos_inf, true);
				break;
			case EQUALS: // aX+b=0, X=c.
				if (isInteger)
					range = nf.isIntegral(c) ? rf.singletonSet(nf.floor(c))
							: rf.emptySet(true);
				else
					range = rf.singletonSet(c);
				break;
			case NEQ: // aX+b!=0, X!=c
				if (isInteger) {
					if (nf.isIntegral(c)) {
						range = rf.complement(rf.singletonSet(nf.floor(c)));
					} else {
						range = rf.interval(true, neg_inf, true, pos_inf, true);
					}
				} else {
					range = rf.complement(rf.singletonSet(c));
				}
				break;
			default:
				throw new SARLException("unreachable");
			}
		} else { // expr is not a Polynomial, just a Monic
			// X<0, X<=0, X==0, X>=0, X>0, X!=0
			Number zero = isInteger ? nf.zeroInteger() : nf.zeroRational();

			monic = expr;
			switch (op) {
			case LESS_THAN:
				assert !isInteger;
				if (leftIsZero) { // X>0
					range = rf.interval(false, zero, true, pos_inf, true);
				} else { // X<0
					range = rf.interval(false, neg_inf, true, zero, true);
				}
				break;
			case LESS_THAN_EQUALS:
				if (leftIsZero) { // X>=0
					range = rf.interval(isInteger, zero, false, pos_inf, true);
				} else { // X<=0
					range = rf.interval(isInteger, neg_inf, true, zero, false);
				}
				break;
			case EQUALS: // X==0
				range = rf.singletonSet(zero);
				break;
			case NEQ: // X!=0
				range = rf.complement(rf.singletonSet(zero));
				break;
			default:
				throw new SARLException("unreachable");
			}
		}
		return new Pair<>(monic, range);
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
	static Primitive findATruePrimitive(Monomial m) {
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

	// /**
	// * Computes the bound type of the given {@link Interval}.
	// *
	// * @param interval
	// * a non-<code>null</code> {@link Interval}
	// * @return the unique category (instance of {@link BoundType}) into which
	// * <code>interval</code> falls
	// */
	// static BoundType boundType(Interval interval) {
	// if (interval.isEmpty())
	// return BoundType.EMPTY;
	//
	// Number l = interval.lower(), r = interval.upper();
	// int lsign = l == null ? -1 : l.signum();
	// int rsign = r == null ? 1 : r.signum();
	//
	// if (lsign > 0)
	// return GT0;
	// if (rsign < 0)
	// return LT0;
	//
	// if (lsign < 0) {
	// if (rsign == 0) {
	// return interval.strictUpper() ? LT0 : LE0;
	// } else { // rsign > 0
	// return BoundType.ALL;
	// }
	// } else { // lsign == 0
	// if (rsign == 0) {
	// return EQ0;
	// } else { // rsign > 0
	// return interval.strictLower() ? GT0 : GE0;
	// }
	// }
	// }
	//
	// Interval intervalOfBoundType(BoundType type, boolean isInteger) {
	// NumberFactory nf = numberFactory;
	//
	// switch (type) {
	// case ALL:
	// return isInteger ? nf.universalIntegerInterval()
	// : nf.universalRealInterval();
	// case EMPTY:
	// return isInteger ? nf.emptyIntegerInterval()
	// : nf.emptyRealInterval();
	// case EQ0:
	// return nf.singletonInterval(
	// isInteger ? nf.zeroInteger() : nf.zeroRational());
	// case GE0:
	// return nf.newInterval(isInteger,
	// isInteger ? nf.zeroInteger() : nf.zeroRational(), false,
	// null, true);
	// case GT0:
	// return nf.newInterval(isInteger,
	// isInteger ? nf.zeroInteger() : nf.zeroRational(), true,
	// null, true);
	// case LE0:
	// return nf.newInterval(isInteger, null, true,
	// isInteger ? nf.zeroInteger() : nf.zeroRational(), false);
	// case LT0:
	// return nf.newInterval(isInteger, null, true,
	// isInteger ? nf.zeroInteger() : nf.zeroRational(), true);
	// }
	// throw new SARLInternalException("unreachable");
	// }

	/**
	 * Determines whether <code>constraint</code> has the form a*X +b ? 0, where
	 * ? is one of less-than, less-than-or-equal-to, not-equal-to; X is
	 * <code>var</code>, and a and b are symbolic expressions that do not
	 * involve X.
	 * 
	 * @param var
	 *            the variable X on which to focus
	 * @param constraint
	 *            the boolean expression to analyze
	 * @return <code>true</code> iff <code>constraint</code> has the form
	 *         specified above
	 */
	boolean isLinearInequality(NumericSymbolicConstant var,
			BooleanExpression constraint) {
		SymbolicOperator op = constraint.operator();

		if (op != SymbolicOperator.LESS_THAN_EQUALS
				&& op != SymbolicOperator.LESS_THAN
				&& op != SymbolicOperator.NEQ)
			return false;

		NumericExpression arg0 = (NumericExpression) constraint.argument(0);
		NumericExpression arg1 = (NumericExpression) constraint.argument(1);
		Monic expr;

		if (arg0.isZero()) { // 0 <= arg1 = v+e
			expr = (Monic) arg1;
		} else {
			assert arg1.isZero();
			expr = (Monic) arg0;
		}

		IdealFactory idf = idealFactory;
		Monomial[] terms = expr.expand(idf);
		boolean degreeOneTermFound = false;

		// every term should have v-degree at most 1
		// and at least one term must have degree 1.
		for (Monomial term : terms) {
			boolean degOneFactorFound = false;

			for (PrimitivePower pp : term.monic(idf).monicFactors(idf)) {
				if (pp.equals(var)) {
					degOneFactorFound = true;
				} else if (universe.getFreeSymbolicConstants(pp)
						.contains(var)) {
					return false;
				}
			}
			degreeOneTermFound = degreeOneTermFound || degOneFactorFound;
		}
		return degreeOneTermFound;
	}

	// GeneralForallStructure getGeneralForallStructure(
	// BooleanExpression forallExpr) {
	// if (forallExpr.operator() != SymbolicOperator.FORALL)
	// return null;
	//
	// SymbolicConstant boundVar = (SymbolicConstant) forallExpr.argument(0);
	// GeneralForallStructure result = new GeneralForallStructure();
	// BooleanExpression forallBody = (BooleanExpression) forallExpr
	// .argument(1);
	// BooleanExpression constraint, body;
	//
	// result.boundVar = boundVar;
	// if (!(boundVar instanceof NumericSymbolicConstant)) {
	// constraint = trueExpr;
	// body = forallBody;
	// } else {
	// NumericSymbolicConstant var = (NumericSymbolicConstant) boundVar;
	//
	// constraint = trueExpr;
	// body = falseExpr;
	// if (forallBody.operator() == SymbolicOperator.OR) {
	// for (SymbolicObject arg : forallBody.getArguments()) {
	// BooleanExpression clause = (BooleanExpression) arg;
	// BooleanExpression negClause = universe.not(clause);
	//
	// if (isLinearInequality(var, negClause))
	// constraint = universe.and(constraint, negClause);
	// else
	// body = universe.or(body, clause);
	// }
	// } else {
	// BooleanExpression negClause = universe.not(forallBody);
	//
	// if (isLinearInequality(var, negClause)) {
	// constraint = negClause;
	// body = falseExpr;
	// } else {
	// constraint = trueExpr;
	// body = forallBody;
	// }
	// }
	// }
	// result.constraint = constraint;
	// result.body = body;
	// return result;
	// }
	//
	// DeepForallStructure getDeepForallStructure(BooleanExpression forallExpr)
	// {
	// GeneralForallStructure struct0 = getGeneralForallStructure(forallExpr);
	//
	// if (struct0 == null)
	// return null;
	//
	// LinkedList<NumericSymbolicConstant> boundVars = new LinkedList<>();
	// BooleanExpression constraint = trueExpr;
	// BooleanExpression body = null;
	//
	// while (struct0 != null) {
	// SymbolicConstant x = struct0.boundVar;
	//
	// if (!(x instanceof NumericSymbolicConstant))
	// return null;
	// boundVars.add((NumericSymbolicConstant) x);
	// constraint = universe.and(constraint, struct0.constraint);
	// body = struct0.body;
	// struct0 = getGeneralForallStructure(body);
	// }
	//
	// DeepForallStructure result = new DeepForallStructure();
	//
	// result.boundVars = boundVars
	// .toArray(new NumericSymbolicConstant[boundVars.size()]);
	// result.constraint = constraint;
	// result.body = body;
	// return result;
	// }

	// public static enum RangeSign {
	// /**
	// * Every element of the range is less than 0 and the range is not empty.
	// */
	// LT0,
	// /**
	// * Every element of the range is less than or equal to 0 and the range
	// * contains 0 and a negative number.
	// */
	// LE0,
	// /** The range consists exactly of 0 and nothing else. */
	// EQ0,
	// /**
	// * The range contains 0 and a positive number and every element of the
	// * range is greater than or equal to 0.
	// */
	// GE0,
	// /**
	// * Every element of the range is greater than 0 and the range is
	// * non-empty.
	// */
	// GT0,
	// /** The range is empty */
	// EMPTY,
	// /** The range contains a negative number, 0, and a positive number */
	// ALL
	// };

	// private RangeSign sign(Range range) {
	// // TODO: this will be a method in Range
	// return null;
	// }

	// public Range rangeOf(RangeSign sign, boolean integral) {
	// int i = integral ? 0 : 1;
	//
	// switch (sign) {
	// case ALL: // (-infty,infty)
	// return signRanges[i][0];
	// case EMPTY: // empty
	// return signRanges[i][1];
	// case EQ0: // [0,0]
	// return signRanges[i][2];
	// case GE0: // [0,infty)
	// return signRanges[i][3];
	// case GT0: // (0,infty)
	// return signRanges[i][4];
	// case LE0: // (-infty, 0]
	// return signRanges[i][5];
	// case LT0: // (-infty, 0)
	// return signRanges[i][6];
	// default:
	// throw new SARLException("unreachable");
	// }
	// }

}
