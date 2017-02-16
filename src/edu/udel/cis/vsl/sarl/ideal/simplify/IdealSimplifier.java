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

import static edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator.LESS_THAN;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import edu.udel.cis.vsl.sarl.IF.CoreUniverse.ForallStructure;
import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.IF.object.BooleanObject;
import edu.udel.cis.vsl.sarl.IF.object.NumberObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject.SymbolicObjectKind;
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
import edu.udel.cis.vsl.sarl.simplify.IF.Simplifier;
import edu.udel.cis.vsl.sarl.simplify.common.CommonSimplifier;

/**
 * <p>
 * An implementation of {@link Simplifier} for the "ideal" numeric factory
 * {@link IdealFactory}.
 * </p>
 *
 */
public class IdealSimplifier extends CommonSimplifier {

	/**
	 * A categorization of intervals based on their relationship to 0. Every
	 * interval falls into exactly one of these categories.
	 * 
	 * @author siegel
	 */
	enum BoundType {
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

	// Instance fields...

	/**
	 * The operator used to rename bound variables so that their names do not
	 * conflict with those of free variables.
	 */
	UnaryOperator<SymbolicExpression> boundCleaner;

	/**
	 * Object that gathers together references to various objects needed for
	 * simplification.
	 */
	SimplifierInfo info;

	/**
	 * The current assumption underlying this simplifier. Initially this is the
	 * assumption specified at construction, but it can be simplified during
	 * construction. After construction completes, it does not change. It does
	 * not include the symbolic constants occurring in the
	 * {@link #substitutionMap} as these have been replaced by their constant
	 * values. Hence: the original assumption (which is not stored) is
	 * equivalent to {@link #assumption} and {@link #substitutionMap}.
	 */
	BooleanExpression assumption;

	/**
	 * This is the same as the {@link #assumption}, but without the information
	 * from the {@link #boundMap}, {@link #booleanMap}, {@link #constantMap},
	 * and {@link #otherConstantMap} thrown in. I.e., assumption = rawAssumption
	 * + boundMap + booleanMap + constantMap + otherConstantMap. Currently it is
	 * used only to implement the method {@link #assumptionAsInterval()}. Should
	 * probably get rid of that method and this field.
	 */
	BooleanExpression rawAssumption;

	/**
	 * A simplified version of the context, including the substitutions.
	 */
	BooleanExpression fullContext = null;

	/**
	 * General Map for replacing equivalent {@link Monic}s.
	 */
	// Map<Monic, Monic> reduceMap = new HashMap<>();

	/**
	 * Abstract representation of the {@link #fullContext}.
	 */
	private AbstractInterpretation ai;

	// Constructors...

	/**
	 * Constructs new simplifier based on the given assumption. The assumption
	 * is analyzed to extract information such as bounds, and the maps which are
	 * fields of this class are populated based on that information.
	 * 
	 * @param info
	 *            the info object wrapping together references to all objects
	 *            needed for this simplifier to do its job
	 * @param assumption
	 *            the assumption ("context") on which this simplifier will be
	 *            based
	 */
	public IdealSimplifier(SimplifierInfo info, BooleanExpression assumption) {
		super(info.universe);
		this.info = info;
		this.boundCleaner = universe.newMinimalBoundCleaner();
		// rename bound variables so every variable has a unique name...
		this.assumption = (BooleanExpression) boundCleaner.apply(assumption);
		this.ai = new AbstractInterpretation(info);
		initialize();
	}

	// private methods...

	// ****************************************************************
	// *.........................Initialization.......................*
	// *........ Extraction of information from the assumption........*
	// ****************************************************************

	/**
	 * The main initialization method: extract information from
	 * {@link #assumption} and populates the various maps and other fields of
	 * this class. This is run once, when this object is instantiated.
	 */
	private void initialize() {
		IdealSimplifierWorker worker = newWorker();

		while (true) {
			// because simplifications can improve...
			// better to just turn caching off until done?
			clearSimplificationCache();

			boolean satisfiable = extractBounds();

			if (!satisfiable) {
				if (info.verbose) {
					info.out.println("Path condition is unsatisfiable.");
					info.out.flush();
				}
				rawAssumption = assumption = info.falseExpr;
				return;
			}

			// need to substitute into assumption new value of symbolic
			// constants.
			BooleanExpression newAssumption = (BooleanExpression) worker
					.simplifyExpressionWork(assumption);

			rawAssumption = newAssumption;

			// At this point, rawAssumption and newAssumption contain
			// only those facts that could not be determined from the
			// booleanMap, boundMap, constantMap, and otherConstantMap.
			// These facts need to be added back in to newAssumption---except
			// for the case where a symbolic constant is mapped to a concrete
			// value in the constantMap.
			// Such symbolic constants will be entirely eliminated from the
			// assumption.

			// After simplifyExpression, the removable symbolic constants
			// should all be gone, replaced with their concrete values.
			// However, as we add back in facts from the constant map,
			// bound map, boolean map, and other constant map,
			// those symbolic constants might sneak back in!
			// We will remove them again later.

			for (Entry<Monic, Interval> entry : ai.getMonicBoundEntries()) {
				Monic key = entry.getKey();
				Interval interval = entry.getValue();
				Number lo = interval.lower(), hi = interval.upper();

				// if this is a constant no need to add this constraint...
				if (!lo.isInfinite() && !hi.isInfinite() && lo.equals(hi)
						&& !interval.strictLower() && !interval.strictUpper())
					continue;

				BooleanExpression constraint = worker.boundToIdeal(key,
						interval);
				// note that the key is simplified before forming the
				// constraint, hence information from the boundMap
				// may have been used to simplify it. really we only
				// want to apply the constantMap to it.

				if (constraint != null)
					newAssumption = info.booleanFactory.and(newAssumption,
							constraint);
			}

			// also need to add facts from constant map.
			// but can eliminate any constant values for primitives since
			// those will never occur in the state.

			for (Entry<Monic, Number> entry : ai.getMonicConstantEntries()) {
				Monic monic = entry.getKey();

				if (monic instanceof SymbolicConstant) {
					// symbolic constant: will be entirely eliminated
				} else {
					Monomial key = (Monomial) worker
							.simplifyExpressionGeneric(monic);
					BooleanExpression constraint = info.idealFactory.equals(key,
							info.idealFactory.constant(entry.getValue()));

					newAssumption = info.booleanFactory.and(newAssumption,
							constraint);
				}
			}

			for (Entry<SymbolicExpression, SymbolicExpression> entry : ai
					.getOtherConstantEntries()) {
				SymbolicExpression key = entry.getKey();

				if (key instanceof SymbolicConstant) {
					// symbolic constant: will be entirely eliminated
				} else {
					SymbolicExpression simplifiedKey = worker
							.simplifyExpressionGeneric(key);
					BooleanExpression constraint = info.universe
							.equals(simplifiedKey, entry.getValue());

					newAssumption = info.booleanFactory.and(newAssumption,
							constraint);
				}
			}

			for (Entry<BooleanExpression, Boolean> entry : ai
					.getBooleanEntries()) {
				BooleanExpression primitive = entry.getKey();

				if (primitive instanceof SymbolicConstant) {
					// symbolic constant: will be entirely eliminated
				} else {
					BooleanExpression simplifiedPrimitive = (BooleanExpression) worker
							.simplifyExpressionGeneric(primitive);

					newAssumption = universe.and(newAssumption,
							entry.getValue() ? simplifiedPrimitive
									: universe.not(simplifiedPrimitive));
				}
			}

			// substitute constant values for symbolic constants...

			Map<SymbolicExpression, SymbolicExpression> substitutionMap = new HashMap<>();

			for (Entry<Monic, Number> entry : ai.getMonicConstantEntries()) {
				SymbolicExpression key = entry.getKey();

				if (key.operator() == SymbolicOperator.SYMBOLIC_CONSTANT)
					substitutionMap.put(key, universe.number(entry.getValue()));
			}
			for (Entry<SymbolicExpression, SymbolicExpression> entry : ai
					.getOtherConstantEntries()) {
				SymbolicExpression key = entry.getKey();

				if (key.operator() == SymbolicOperator.SYMBOLIC_CONSTANT)
					substitutionMap.put(key, entry.getValue());
			}
			newAssumption = (BooleanExpression) universe
					.mapSubstituter(substitutionMap).apply(newAssumption);

			// check for stabilization...
			if (assumption.equals(newAssumption))
				break;
			assumption = (BooleanExpression) universe.canonic(newAssumption);
		}
		extractRemainingFacts();
	}

	/**
	 * Attempts to determine bounds (upper and lower) on {@link Monic}
	 * expressions by examining the {@link #assumption}. Returns
	 * <code>false</code> if {@link assumption} is determined to be
	 * unsatisfiable. Updates {@link #boundMap}, {@link #booleanMap},
	 * {@link #constantMap}, and {@link #otherConstantMap}.
	 */
	private boolean extractBounds() {
		if (assumption.operator() == SymbolicOperator.AND) {
			for (SymbolicObject arg : assumption.getArguments()) {
				BooleanExpression clause = (BooleanExpression) arg;

				if (!extractBoundsOr(clause, ai))
					return false;
			}
		} else if (!extractBoundsOr(assumption, ai))
			return false;
		return ai.updateConstantMap();
	}

	private boolean extractBoundsOr(BooleanExpression or,
			AbstractInterpretation anAI) {
		if (or.operator() != SymbolicOperator.OR)
			return extractBoundsFromClause(or, anAI);

		// p & (q0 | ... | qn) = (p & q0) | ... | (p & qn)
		// copies of original maps, corresponding to p. these never
		// change...
		AbstractInterpretation originalAI = anAI.clone();
		Iterator<? extends SymbolicObject> clauses = or.getArguments()
				.iterator();
		boolean satisfiable = extractBoundsBasic(
				(BooleanExpression) clauses.next(), anAI);

		// result <- p & q0:
		// result <- result | ((p & q1) | ... | (p & qn)) :
		while (clauses.hasNext()) {
			BooleanExpression clause = (BooleanExpression) clauses.next();
			AbstractInterpretation newAI = originalAI.clone();
			// compute p & q_i:
			boolean newSatisfiable = extractBoundsBasic(clause, newAI);

			// result <- result | (p & q_i) where result is (aBoundMap,
			// aBooleanMap)....
			satisfiable = satisfiable || newSatisfiable;
			if (newSatisfiable) {
				LinkedList<Monic> boundRemoveList = new LinkedList<>();
				LinkedList<BooleanExpression> booleanRemoveList = new LinkedList<>();

				for (Entry<Monic, Interval> entry : anAI
						.getMonicBoundEntries()) {
					Monic primitive = entry.getKey();
					Interval oldBound = entry.getValue();
					Interval newBound = newAI.getBound(primitive);

					if (newBound == null) {
						boundRemoveList.add(primitive);
					} else {
						newBound = info.numberFactory.join(oldBound, newBound);
						if (!oldBound.equals(newBound)) {
							if (newBound.isUniversal())
								boundRemoveList.add(primitive);
							else
								entry.setValue(newBound);
						}
					}
				}
				for (Monic primitive : boundRemoveList)
					anAI.removeBound(primitive);
				for (Entry<BooleanExpression, Boolean> entry : anAI
						.getBooleanEntries()) {
					BooleanExpression primitive = entry.getKey();
					Boolean oldValue = entry.getValue();
					Boolean newValue = newAI.getTruth(primitive);

					if (newValue == null || !newValue.equals(oldValue))
						booleanRemoveList.add(primitive);
				}
				for (BooleanExpression primitive : booleanRemoveList)
					anAI.removeTruth(primitive);
			} // end if newSatisfiable
		} // end while (clauses.hasNext())
		return satisfiable;
	}

	/**
	 * Extracts bounds from a conjunctive clause which is not an "or"
	 * expression.
	 * 
	 * @param clause
	 *            a clause in the context which is not an "or" expression
	 * @param aBoundMap
	 *            a bound map
	 * @param aBooleanMap
	 *            a boolean map
	 * @return <code>true</code> unless an inconsistency was discovered
	 */
	private boolean extractBoundsFromClause(BooleanExpression clause,
			AbstractInterpretation anAI) {
		SymbolicOperator op = clause.operator();

		// if this is of the form EQ x,y where y is a constant and
		// x and y are not-numeric, add to otherConstantMap
		if (op == SymbolicOperator.EQUALS) {
			SymbolicExpression arg0 = (SymbolicExpression) clause.argument(0),
					arg1 = (SymbolicExpression) clause.argument(1);
			SymbolicType type = arg0.type();

			if (!type.isNumeric()) {
				boolean const0 = arg0.operator() == SymbolicOperator.CONCRETE;
				boolean const1 = (arg1.operator() == SymbolicOperator.CONCRETE);

				if (const1 && !const0) {
					anAI.setOtherValue(arg0, arg1);
					return true;
				} else if (const0 && !const1) {
					anAI.setOtherValue(arg1, arg0);
					return true;
				} else if (const0 && const1) {
					return arg0.equals(arg1);
				} else {
					return true;
				}
			}
		}
		// look for the pattern:
		// forall int i . 0<=i<=n-1 -> a[i]=expr
		// In such cases, add to otherConstantMap:
		// a = (T[n])arraylambda i . expr
		if (op == SymbolicOperator.FORALL) {
			ArrayDefinition defn = extractArrayDefinition(clause);

			if (defn != null && defn.array
					.operator() == SymbolicOperator.SYMBOLIC_CONSTANT) {
				// TODO: further checking needed here: make sure no free
				// variables
				anAI.setOtherValue(defn.array, defn.lambda);
			}
		}
		return extractBoundsBasic(clause, anAI);
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

		BooleanExpression isNonZero = (BooleanExpression) newWorker()
				.simplifyExpression(idf.isNonZero(coefficient));

		if (!isNonZero.isTrue())
			return null;

		NumericExpression offset = universe.add(deg0List);
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

	// class ArrayTermOut {
	// SymbolicExpression array;
	// boolean isNegative;
	// }

	// /**
	// * If <code>constantExpr</code> is +1 or -1 and <code>arrayReadExpr</code>
	// * is equivalent to +/- an array read expression in which the index
	// argument
	// * is <code>index</code>, this method will return a structure giving the
	// * sign and array expression used in the array-read. Else
	// <code>null</code>
	// *
	// * @param constantExpr
	// * a numeric expression, non-<code>null</code>; if not a
	// * constant, this method will return <code>null</code>
	// * @param arrayReadExpr
	// * a numeric expression, non-<code>null</code>; if not an
	// * array-read expression, this method will return
	// * <code>null</code>
	// * @param index
	// * the index expression of the array read expression
	// * @return structure as specified above or <code>null</code>
	// */
	// private ArrayTermOut arrayTermOfProductHelper(
	// NumericExpression constantExpr, NumericExpression arrayReadExpr,
	// NumericSymbolicConstant index) {
	// ArrayTermOut result = arrayTerm(arrayReadExpr, index);
	//
	// if (result != null) {
	// Number constant = universe.extractNumber(constantExpr);
	//
	// if (constant != null) {
	// if (constant.isOne()) {
	// return result;
	// } else if (info.numberFactory.negate(constant).isOne()) {
	// result.isNegative = !result.isNegative;
	// return result;
	// }
	// }
	// }
	// return null;
	// }

	// /**
	// * Attempts to determine if one of the two given arguments is the constant
	// 1
	// * or -1 and the other is + or - an array-read expression with the given
	// * index.
	// *
	// * @param arg0
	// * @param arg1
	// * @param index
	// * @return
	// */
	// private ArrayTermOut arrayTermOfBinaryProduct(NumericExpression arg0,
	// NumericExpression arg1, NumericSymbolicConstant index) {
	// ArrayTermOut result = arrayTermOfProductHelper(arg0, arg1, index);
	//
	// if (result != null)
	// return result;
	// result = arrayTermOfProductHelper(arg1, arg0, index);
	// return result;
	// }

	// /**
	// * Given an expression in which the operator is
	// * {@link SymbolicOperator#MULTIPLY} and an integer variable i, attempts
	// to
	// * determine whether the expression is equivalent to a[i] or -a[i] for
	// some
	// * array expression a.
	// *
	// * @param product
	// * the expression with operator {@link SymbolicOperator#MULTIPLY}
	// * @param index
	// * the integer index variable i
	// * @return a structure with the array a and sign or <code>null</code> if
	// * <code>product</code> does not have the desired form
	// */
	// private ArrayTermOut arrayTermOfProduct(NumericExpression product,
	// NumericSymbolicConstant index) {
	// @SuppressWarnings("unchecked")
	// Iterable<? extends NumericExpression> iterable = (Iterable<? extends
	// NumericExpression>) product
	// .getArguments();
	// Iterator<? extends NumericExpression> iter = iterable.iterator();
	//
	// if (!iter.hasNext())
	// return null;
	//
	// NumericExpression arg0 = iter.next();
	//
	// if (!iter.hasNext()) {
	// return arrayTerm(arg0, index);
	// }
	//
	// NumericExpression arg1 = iter.next();
	//
	// if (!iter.hasNext()) {
	// return arrayTermOfBinaryProduct(arg0, arg1, index);
	// }
	// return null;
	// }

	// /**
	// * Determines whether the given expression has the form a[i] or -a[i] for
	// * some array a.
	// *
	// * @param term
	// * the given expression
	// * @param index
	// * the index variable i
	// * @return structure specifying the array a and whether or not it is
	// * negated, or <code>null</code> if <code>term</code> is not in that
	// * form
	// */
	// private ArrayTermOut arrayTerm(NumericExpression term,
	// NumericSymbolicConstant index) {
	// ArrayTermOut result = null;
	//
	// switch (term.operator()) {
	// case ARRAY_READ:
	// if (term.argument(1).equals(index)) {
	// result = new ArrayTermOut();
	// result.isNegative = false;
	// result.array = (SymbolicExpression) term.argument(0);
	// }
	// break;
	// case NEGATIVE:
	// result = arrayTerm((NumericExpression) term.argument(0), index);
	// if (result != null)
	// result.isNegative = !result.isNegative;
	// break;
	// case MULTIPLY:
	// result = arrayTermOfProduct(term, index);
	// break;
	// default:
	// }
	// return result;
	// }

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
		// NumericExpression diff = universe().subtract(
		// (NumericExpression) arg1, (NumericExpression) arg0);
		// NumericExpression[] terms = universe().getSummands(diff);
		// List<NumericExpression> otherTerms = new LinkedList<>();
		// SymbolicExpression array = null;
		// boolean negate = false;
		//
		// for (int i = 0; i < terms.length; i++) {
		// NumericExpression term = terms[i];
		// ArrayTermOut termAnalysis = arrayTerm(term, index);
		//
		// if (termAnalysis != null) {
		// if (array != null)
		// return null;
		// array = termAnalysis.array;
		// negate = !termAnalysis.isNegative;
		// } else {
		// otherTerms.add(term);
		// }
		// }
		// if (array == null)
		// return null;
		//
		// NumericExpression rhs = universe().add(otherTerms);
		//
		// if (negate)
		// rhs = universe().minus(rhs);
		// result = new ArrayEquationSolution();
		// result.array = array;
		// result.rhs = rhs;
		// return result;
		// }
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
		ForallStructure structure = universe.getForallStructure(forallExpr);

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
		NumericExpression length = universe.add(structure.upperBound,
				universe.oneInt());

		if (structure.lowerBound.isZero()
				&& universe.equals(length, completeType.extent()).isTrue()) {
			SymbolicExpression lambda = universe.arrayLambda(completeType,
					universe.lambda(var, solution.rhs));
			ArrayDefinition result = new ArrayDefinition();

			result.array = solution.array;
			result.lambda = lambda;
			return result;
		}
		// else if (false) {
		// // TODO: this won't work. Just sticking it in simplification
		// // cache won't work because it doesn't change the assumption
		// // and therefore
		//
		// // partial result
		// // array -> arraylambda i . (low<=i<=hi ? rhs : array[i])
		// SymbolicExpression conditional = universe.cond(
		// universe.and(
		// universe.lessThanEquals(structure.lowerBound, var),
		// universe.lessThanEquals(var, structure.upperBound)),
		// solution.rhs, universe.arrayRead(solution.array, var));
		// SymbolicExpression lambda = universe.canonic(universe.arrayLambda(
		// completeType, universe.lambda(var, conditional)));
		//
		// // is this risky? the simplification of a still involves a...
		//
		// out.println("array : " + solution.array);
		// out.println("length : " + completeType.extent());
		// out.println("lambda : " + lambda);
		// out.flush();
		//
		// super.cacheSimplification(solution.array, lambda);
		// }
		return null;
	}

	/**
	 * Extracts information from a "basic expression", updating
	 * <code>aBoundMap</code> and <code>aBooleanMap</code> in the process. A
	 * basic expression is either a concrete boolean (true/false), a relational
	 * expression (0=Primitive, 0<Monic, 0<=Monic, Monic<0, Monic<=0, or
	 * 0!=Primitive), a quantified expression, or a "not" expression (!
	 * Primitive).
	 */
	private boolean extractBoundsBasic(BooleanExpression basic,
			AbstractInterpretation anAI) {
		SymbolicOperator operator = basic.operator();

		if (operator == SymbolicOperator.CONCRETE)
			return ((BooleanObject) basic.argument(0)).getBoolean();
		if (isRelational(operator)) {
			// Cases: 0=Primitive, 0<Monic, 0<=Monic, Monic<0, Monic<=0,
			// 0!=Primitive.
			SymbolicExpression arg0 = (SymbolicExpression) basic.argument(0);
			SymbolicExpression arg1 = (SymbolicExpression) basic.argument(1);

			// could be a scope argument, ignore those
			if (arg0.type().isNumeric()) {
				switch (operator) {
				case EQUALS: // 0==x
					return extractEQ0Bounds((Primitive) arg1, anAI);
				case NEQ:
					return extractNEQ0Bounds((Primitive) arg1, anAI);
				case LESS_THAN: // 0<x or x<0
				case LESS_THAN_EQUALS: // 0<=x or x<=0
					if (arg0.isZero()) {
						return extractIneqBounds((Monic) arg1, true,
								operator == LESS_THAN, anAI);
					} else {
						return extractIneqBounds((Monic) arg0, false,
								operator == LESS_THAN, anAI);
					}
				default:
					throw new SARLInternalException(
							"Unknown RelationKind: " + operator);
				}
			}
		} else if (operator == SymbolicOperator.EXISTS
				|| operator == SymbolicOperator.FORALL) {
			// TODO: forall and exists are difficult
			// forall x: can substitute whatever you want for x
			// and extract bounds.
			// example: forall i: a[i]<7. Look for all occurrences of a[*]
			// and add bounds
			return true;
		} else if (operator == SymbolicOperator.NOT) {
			BooleanExpression primitive = (BooleanExpression) basic.argument(0);
			Boolean value = anAI.getTruth(primitive);

			if (value != null)
				return !value;
			anAI.setTruth(primitive, false);
			return true;
		}

		Boolean value = anAI.getTruth(basic);

		if (value != null)
			return value;
		anAI.setTruth(basic, true);
		return true;
	}

	private boolean extractEQ0Bounds(Primitive primitive,
			AbstractInterpretation anAI) {
		if (primitive instanceof Polynomial)
			return extractEQ0BoundsPoly((Polynomial) primitive, anAI);

		NumberFactory nf = info.numberFactory;
		Interval bound = anAI.getBound(primitive);
		SymbolicType type = primitive.type();
		Number zero = type.isInteger() ? nf.zeroInteger() : nf.zeroRational();

		if (bound != null && !bound.contains(zero))
			return false;

		BooleanExpression neq0 = info.booleanFactory.booleanExpression(
				SymbolicOperator.NEQ, info.idealFactory.zero(primitive.type()),
				primitive);
		Boolean neq0Truth = anAI.getTruth(neq0);

		if (neq0Truth != null && neq0Truth.booleanValue())
			return false;
		anAI.setMonicValue(primitive, zero);
		return true;
	}

	/**
	 * Given the fact that poly==0, for some {@link Polynomial} poly, updates
	 * the specified bound map and boolean map appropriately.
	 * 
	 * @param poly
	 *            a non-<code>null</code> polynomial
	 * @param aBoundMap
	 *            a bound map: a map from pseudo-primitive polynomials to bound
	 *            objects specifying an interval bound for those polynomials
	 * @param aBooleanMap
	 *            a map specifying a concrete boolean value for some set of
	 *            boolean-valued symbolic expressions
	 * @return <code>false</code> if it is determined that the given assertion
	 *         is inconsistent with the information in the bound map and boolean
	 *         map; else <code>true</code>
	 */
	private boolean extractEQ0BoundsPoly(Polynomial poly,
			AbstractInterpretation anAI) {
		NumberFactory nf = info.numberFactory;
		AffineExpression affine = info.affineFactory.affine(poly);
		Monic pseudo = affine.pseudo();
		RationalNumber coefficient = nf.rational(affine.coefficient());
		RationalNumber offset = nf.rational(affine.offset());
		RationalNumber rationalValue = nf
				.negate(info.numberFactory.divide(offset, coefficient));
		Number value; // same as rationalValue but IntegerNumber if type is
						// integer
		Interval bound = anAI.getBound(pseudo);

		if (pseudo.type().isInteger()) {
			if (!nf.isIntegral(rationalValue))
				return false;
			value = nf.integerValue(rationalValue);
		} else {
			value = rationalValue;
		}
		if (bound != null && !bound.contains(value))
			return false;
		anAI.setMonicValue(pseudo, value);
		return true;
	}

	private boolean extractNEQ0Bounds(Primitive primitive,
			AbstractInterpretation anAI) {

		if (primitive instanceof Polynomial)
			return extractNEQ0BoundsPoly((Polynomial) primitive, anAI);

		Interval bound = anAI.getBound(primitive);
		SymbolicType type = primitive.type();
		Constant zero = info.idealFactory.zero(type);

		if (bound == null) {
			// for now, nothing can be done, since the bounds are
			// plain intervals. we need a more precise abstraction
			// than intervals here.
		} else if (bound.contains(zero.number())) {
			NumberFactory nf = info.numberFactory;
			Interval oldBound = bound;

			// is value an end-point? Might be able to sharpen bound...
			if (bound.lower() != null && bound.lower().isZero()
					&& !bound.strictLower())
				bound = nf.restrictLower(bound, bound.lower(), true);
			if (bound.upper() != null && bound.upper().isZero()
					&& !bound.strictUpper())
				bound = nf.restrictUpper(bound, bound.upper(), true);
			if (bound.isEmpty())
				return false;
			if (!bound.equals(oldBound))
				anAI.setBound(primitive, bound);
		}
		anAI.setTruth(info.universe.neq(zero, primitive), true);
		return true;
	}

	/**
	 * Given the fact that poly!=0, for some {@link Polynomial} poly, updates
	 * the specified bound map and boolean map appropriately.
	 * 
	 * @param poly
	 *            a non-<code>null</code> polynomial
	 * @param aBoundMap
	 *            a bound map: a map from pseudo-primitive polynomials to bound
	 *            objects specifying an interval bound for those polynomials
	 * @param aBooleanMap
	 *            a map specifying a concrete boolean value for some set of
	 *            boolean-valued symbolic expressions
	 * @return <code>false</code> if it is determined that the given assertion
	 *         is inconsistent with the information in the bound map and boolean
	 *         map; else <code>true</code>
	 */
	private boolean extractNEQ0BoundsPoly(Polynomial poly,
			AbstractInterpretation anAI) {
		// poly=aX+b. if X=-b/a, contradiction.
		NumberFactory nf = info.numberFactory;
		SymbolicType type = poly.type();
		AffineExpression affine = info.affineFactory.affine(poly);
		Monic pseudo = affine.pseudo();
		RationalNumber coefficient = nf.rational(affine.coefficient());
		RationalNumber offset = nf.rational(affine.offset());
		RationalNumber rationalValue = nf
				.negate(nf.divide(offset, coefficient));
		Number value; // same as rationalValue but IntegerNumber if type is
						// integer
		Interval bound = anAI.getBound(pseudo);
		Monomial zero = info.idealFactory.zero(type);

		if (type.isInteger()) {
			if (nf.isIntegral(rationalValue)) {
				value = nf.integerValue(rationalValue);
			} else {
				// an integer cannot equal a non-integer.
				anAI.setTruth(info.idealFactory.neq(zero, poly), true);
				return true;
			}
		} else {
			value = rationalValue;
		}
		// interpret fact pseudo!=value, where pseudo is in bound
		if (bound == null) {
			// TODO:
			// for now, nothing can be done, since the bounds are
			// plain intervals. we need a more precise abstraction
			// than intervals here, like Range.
		} else if (bound.contains(value)) {
			Interval oldBound = bound;

			// is value an end-point? Might be able to sharpen bound...
			if (bound.lower() != null && bound.lower().equals(value)
					&& !bound.strictLower())
				bound = nf.restrictLower(bound, bound.lower(), true);
			if (bound.upper() != null && bound.upper().equals(value)
					&& !bound.strictUpper())
				bound = nf.restrictUpper(bound, bound.upper(), true);
			if (bound.isEmpty())
				return false;
			if (!bound.equals(oldBound))
				anAI.setBound(pseudo, bound);
		}
		anAI.setTruth(info.universe.neq(zero, poly), true);
		return true;
	}

	private boolean extractIneqBounds(Monic monic, boolean gt, boolean strict,
			AbstractInterpretation anAI) {
		if (monic instanceof Polynomial)
			return extractIneqBoundsPoly((Polynomial) monic, gt, strict, anAI);

		NumberFactory nf = info.numberFactory;
		Number zero = monic.type().isInteger() ? nf.zeroInteger()
				: nf.zeroRational();
		Interval interval = gt ? anAI.restrictLowerBound(monic, zero, strict)
				: anAI.restrictUpperBound(monic, zero, strict);

		return !interval.isEmpty();
	}

	private boolean extractIneqBoundsPoly(Polynomial poly, boolean gt,
			boolean strict, AbstractInterpretation anAI) {
		AffineExpression affine = info.affineFactory.affine(poly);
		Monic pseudo = affine.pseudo();
		Number coefficient = affine.coefficient();
		boolean pos = coefficient.signum() > 0;
		Number theBound = info.affineFactory.bound(affine, gt, strict);
		Interval interval;

		// aX+b>0.
		// a>0:lower bound (X>-b/a).
		// a<0: upper bound (X<-b/a).
		assert pseudo != null;
		if (poly.type().isInteger())
			strict = false;
		if ((pos && gt) || (!pos && !gt)) // lower bound
			interval = anAI.restrictLowerBound(pseudo, theBound, strict);
		else
			// upper bound
			interval = anAI.restrictUpperBound(pseudo, theBound, strict);
		return !interval.isEmpty();
	}

	private void declareFact(SymbolicExpression booleanExpression,
			boolean truth) {
		BooleanExpression value = truth ? info.trueExpr : info.falseExpr;

		cacheSimplification(booleanExpression, value);
	}

	private void declareClauseFact(BooleanExpression clause) {
		if (isNumericRelational(clause)) {
			if (clause.operator() == SymbolicOperator.NEQ) {
				BooleanExpression eq0 = info.universe.not(clause);

				eq0 = (BooleanExpression) universe.canonic(eq0);
				declareFact(eq0, false);
			}
		} else
			declareFact(clause, true);
	}

	/**
	 * This method inserts into the simplification cache all facts from the
	 * assumption that are not otherwise encoded in the {@link #constantMap},
	 * {@link #booleanMap}, or {@link #boundMap}. It is to be invoked only after
	 * the assumption has been simplified for the final time.
	 */
	private void extractRemainingFacts() {
		SymbolicOperator operator = assumption.operator();

		if (operator == SymbolicOperator.AND) {
			for (SymbolicObject arg : assumption.getArguments()) {
				declareClauseFact((BooleanExpression) arg);
			}
		} else {
			declareClauseFact(assumption);
		}
	}

	// Exported methods.............................................

	@Override
	protected IdealSimplifierWorker newWorker() {
		return new IdealSimplifierWorker(this, ai);
	}

	@Override
	public SymbolicExpression apply(SymbolicExpression x) {
		// some optimizations...no need to create new worker in these
		// basic cases...
		if (x.isNull())
			return x;

		SymbolicOperator operator = x.operator();

		if (operator == SymbolicOperator.CONCRETE) {
			SymbolicObject object = (SymbolicObject) x.argument(0);
			SymbolicObjectKind kind = object.symbolicObjectKind();

			switch (kind) {
			case BOOLEAN:
			case INT:
			case NUMBER:
			case STRING:
				return x;
			default:
			}
		}
		simplifyCount++;
		// rename bound variables with counts starting from where the
		// original assumption renaming left off. This ensures that
		// all bound variables in the assumption and x are unique, but
		// two different x's can have same bound variables (thus
		// improving canonicalization)...
		x = universe.cloneBoundCleaner(boundCleaner).apply(x);
		return newWorker().simplifyExpression(x);
	}

	@Override
	public Interval assumptionAsInterval(SymbolicConstant symbolicConstant) {
		if (!rawAssumption.isTrue())
			return null;
		return ai.assumptionAsInterval(symbolicConstant);
	}

	@Override
	public Map<SymbolicConstant, SymbolicExpression> constantSubstitutionMap() {
		return ai.getSolvedVariables();
	}

	@Override
	public BooleanExpression getReducedContext() {
		return assumption;
	}

	@Override
	public BooleanExpression getFullContext() {
		if (fullContext == null) {
			Map<SymbolicConstant, SymbolicExpression> map = constantSubstitutionMap();

			fullContext = getReducedContext();
			for (Entry<SymbolicConstant, SymbolicExpression> entry : map
					.entrySet()) {
				SymbolicConstant key = entry.getKey();
				SymbolicExpression value = entry.getValue();
				BooleanExpression equation = universe.equals(key, value);

				fullContext = universe.and(fullContext, equation);
			}
		}
		return fullContext;
	}

	@Override
	public Interval intervalApproximation(NumericExpression expr) {
		return newWorker().intervalApproximation(expr);
	}

	@Override
	public Map<SymbolicExpression, SymbolicExpression> substitutionMap(
			boolean selfupdate) {
		return ai.substitutionMap(selfupdate);
	}

	@Override
	public Map<SymbolicExpression, SymbolicExpression> substitutionMap(
			SymbolicConstant expectedKey, boolean selfupdate) {
		return ai.substitutionMap(expectedKey, selfupdate);
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
		return ai.findDifferentiableClaim(function);
	}

}
