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
package edu.udel.cis.vsl.sarl.ideal2.simplify;

import static edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator.EQUALS;
import static edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator.LESS_THAN;
import static edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator.LESS_THAN_EQUALS;
import static edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator.NEQ;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.IF.object.BooleanObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicMap;
import edu.udel.cis.vsl.sarl.expr.IF.BooleanExpressionFactory;
import edu.udel.cis.vsl.sarl.ideal2.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal2.IF.Polynomial;
import edu.udel.cis.vsl.sarl.ideal2.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal2.IF.PrimitivePower;
import edu.udel.cis.vsl.sarl.simplify.IF.Simplifier;
import edu.udel.cis.vsl.sarl.simplify.common.CommonSimplifier;

/**
 * An implementation of {@link Simplifier} for the "Ideal" (mathematical)
 * Universe. Provides methods to take a symbolic expression from an ideal
 * universe and return a "simplified" version of the expression which is
 * equivalent to the original in the mathematical "ideal" semantics. Similar
 * method is provided for types.
 * 
 * TODO: also would like to map symbolic constants that can be solved for in
 * terms of earlier ones to expressions...
 * 
 * NOTE: in this Ideal2 module, the canonical form ensures that relational
 * operators only occur in the following forms:
 * 
 * 0=Primitive, 0<Monic, 0<=Monic, Monic<0, Monic<=0, 0!=Primitive.
 * 
 * Furthermore, in the Monics, the highest exponent is 1.
 * 
 * Simplification strategies:
 * 
 * Only Monics (and Polynomials, which are a kind of Monic) do not follow
 * default protocols.
 * 
 * To simplify a Monic: look up in constant map. If found, great. Otherwise, if
 * the Monic is a Polynomial, apply simplifyPolynomial below. Otherwise,
 * default.
 * 
 * simplifyPolynomial: first, there must be no known factorization, else it
 * would not be a Polynomial. Try expanding the terms and if any of them change,
 * adding the resulting term maps and refactoring to form a Monomial. (There may
 * be cancellations that only appear at this time.) However, only expand if the
 * term map's size is below a threshold. Example: (X+Y)^2 + X^2 -->
 * 2X^2+2XY+Y^2. But is this better? (Determine metric for "better"?)
 * 
 * To simplify relational expressions:
 * 
 * Methods on Monomials: getBound()
 * 
 * getBound(Monomial m): getBoundMonic(m.monic), scale by constant
 * 
 * getBoundMonic(Monic m): if m is a Polynomial, do getBoundPoly(m). Otherwise:
 * look up m in boundMap. If that doesn't give a definitive answer, take product
 * of two intervals, take power of interval. Wikipedia article on interval
 * arithmetic has all the formulas.
 * https://en.wikipedia.org/wiki/Interval_arithmetic
 * 
 * getBoundPoly: rewrite in pseudo form, look up m in boundMap. If that doesn't
 * give a definitive answer, getBound on each Monomial term and add them up.
 * 
 * To simplify:
 * 
 * 0<Monic: First see if you can get a bound on the monic. If that doesn't
 * resolve, iterate over the primitive factors X and see if you can get a bound
 * on X. If you can show that X must be negative, or X=0, or X must be positive,
 * then you can eliminate X. This simplifies the formula.
 * 
 * 0>Monic: Similar
 * 
 * 0=Primitive: First see if you can get a bound on the primitive. If that
 * doesn't resolve, if Primitive is a Poly, put in pseudo form, look for bound
 * on the pseudo.
 * 
 * 0!=Primitive.
 * 
 * Need complementary bounds. Just for a!=0. Do we look for pseudo != something?
 * 
 */
public class IdealSimplifier extends CommonSimplifier {

	// Static fields...

	/**
	 * Print debugging information?
	 */
	public final static boolean debug = false;

	public final static PrintStream out = System.out;

	// Instance fields...

	/**
	 * Object that gathers together references to various objects needed for
	 * simplification.
	 */
	private SimplifierInfo info;

	/**
	 * The current assumption underlying this simplifier. Initially this is the
	 * assumption specified at construction, but it can be simplified during
	 * construction. After construction completes, it does not change. It does
	 * not include the symbolic constants occurring in the substitutionMap.
	 */
	private BooleanExpression assumption;

	/**
	 * This is the same as the assumption, but without the information from the
	 * boundMap, booleanMap, and constantMap thrown in.
	 */
	private BooleanExpression rawAssumption;

	/**
	 * Map from symbolic constants to their "solved" values. These symbolic
	 * constants will be replaced by their corresponding values in all
	 * expressions simplified by this simplifier.
	 */
	private Map<SymbolicConstant, SymbolicExpression> substitutionMap = null;

	/**
	 * A simplified version of the context, including the substitutions.
	 */
	private BooleanExpression fullContext = null;

	/**
	 * A map that assigns bounds to monics.
	 */
	private BoundMap boundMap;

	/**
	 * A map that assigns concrete boolean values to boolean primitive
	 * expressions.
	 */
	private Map<BooleanExpression, Boolean> booleanMap = new HashMap<>();

	/**
	 * Map assigning concrete numerical values to certain {@link Monic}s.
	 */
	private Map<Monic, Number> constantMap = new HashMap<>();

	/**
	 * Map assigning concrete values to certain non-numeric expressions.
	 */
	private Map<SymbolicExpression, SymbolicExpression> otherConstantMap = new HashMap<>();

	/**
	 * Has the interval interpretation of this context been computed?
	 */
	private boolean intervalComputed = false;

	/**
	 * The interpretation of the context as an Interval, or <code>null</code> if
	 * it cannot be so interpreted.
	 */
	private Interval theInterval = null;

	/**
	 * The variable bound by the interval.
	 */
	private SymbolicConstant intervalVariable = null;

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
		this.assumption = assumption;
		this.boundMap = new BoundMap(info);
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
		while (true) {
			// because simplifications can improve...
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
			BooleanExpression newAssumption = (BooleanExpression) simplifyExpression(
					assumption);

			rawAssumption = newAssumption;
			// at this point, rawAssumption contains only those facts that
			// could not be
			// determined from the booleanMap, boundMap, or constantMap.
			// these facts need to be added back in---except for the case
			// where
			// a symbolic constant is mapped to a concrete value in the
			// constantMap.
			// such symbolic constants will be entirely eliminated from the
			// assumption

			// after SimplifyExpression, the removable symbolic constants
			// should all be gone, replaced with their concrete values.
			// However, as we add back in facts from the constant map,
			// bound map and boolean
			// map, those symbolic constants might sneak back in!
			// We will remove them again later.

			for (Entry<Monic, Interval> entry : boundMap.entrySet()) {
				BooleanExpression constraint = boundToIdeal(entry.getKey(),
						entry.getValue());

				if (constraint != null)
					newAssumption = info.booleanFactory.and(newAssumption,
							constraint);
			}
			// also need to add facts from constant map.
			// but can eliminate any constant values for primitives since
			// those will never occur in the state.
			for (Entry<Monic, Number> entry : constantMap.entrySet()) {
				Monic fp = entry.getKey();

				if (fp instanceof SymbolicConstant) {
					// symbolic constant: will be entirely eliminated
				} else {
					BooleanExpression constraint = info.idealFactory.equals(fp,
							info.idealFactory.constant(entry.getValue()));

					newAssumption = info.booleanFactory.and(newAssumption,
							constraint);
				}
			}

			for (Entry<SymbolicExpression, SymbolicExpression> entry : otherConstantMap
					.entrySet()) {
				SymbolicExpression key = entry.getKey();

				if (key instanceof SymbolicConstant) {
					// symbolic constant: will be entirely eliminated
				} else {
					BooleanExpression constraint = info.universe.equals(key,
							entry.getValue());

					newAssumption = info.booleanFactory.and(newAssumption,
							constraint);
				}
			}

			for (Entry<BooleanExpression, Boolean> entry : booleanMap
					.entrySet()) {
				BooleanExpression primitive = entry.getKey();

				if (primitive instanceof SymbolicConstant) {
					// symbolic constant: will be entirely eliminated
				} else {
					newAssumption = info.booleanFactory.and(newAssumption,
							entry.getValue() ? primitive
									: info.booleanFactory.not(primitive));
				}
			}

			// now we remove those removable symbolic constants...

			Map<SymbolicExpression, SymbolicExpression> substitutionMap = new HashMap<>();

			for (Entry<Monic, Number> entry : constantMap.entrySet()) {
				SymbolicExpression key = entry.getKey();

				if (key.operator() == SymbolicOperator.SYMBOLIC_CONSTANT)
					substitutionMap.put(key, universe.number(entry.getValue()));
			}
			for (Entry<SymbolicExpression, SymbolicExpression> entry : otherConstantMap
					.entrySet()) {
				SymbolicExpression key = entry.getKey();

				if (key.operator() == SymbolicOperator.SYMBOLIC_CONSTANT)
					substitutionMap.put(key, entry.getValue());
			}
			newAssumption = (BooleanExpression) universe
					.mapSubstituter(substitutionMap).apply(newAssumption);

			if (assumption.equals(newAssumption))
				break;
			assumption = (BooleanExpression) universe.canonic(newAssumption);
		}
		extractRemainingFacts();
	}

	/**
	 * Converts the bound to a boolean expression in canonical form. Returns
	 * null if both upper and lower bound are infinite (equivalent to "true").
	 * Note that the variable in the bound is simplified.
	 */
	private BooleanExpression boundToIdeal(Monic monic, Interval bound) {
		Number lower = bound.lower(), upper = bound.upper();
		BooleanExpression result = null;
		Monomial ideal = (Monomial) apply(monic);

		if (lower != null) {
			if (bound.strictLower())
				result = info.idealFactory
						.lessThan(info.idealFactory.constant(lower), ideal);
			else
				result = info.idealFactory.lessThanEquals(
						info.idealFactory.constant(lower), ideal);
		}
		if (upper != null) {
			BooleanExpression upperResult;

			if (bound.strictUpper())
				upperResult = info.idealFactory.lessThan(ideal,
						info.idealFactory.constant(upper));
			else
				upperResult = info.idealFactory.lessThanEquals(ideal,
						info.idealFactory.constant(upper));
			if (result == null)
				result = upperResult;
			else
				result = info.booleanFactory.and(result, upperResult);
		}
		return result;
	}

	/**
	 * Attempts to determine bounds (upper and lower) on primitive expressions
	 * by examining the assumption. Returns false if assumption is determined to
	 * be unsatisfiable.
	 */
	private boolean extractBounds() {
		if (assumption.operator() == SymbolicOperator.AND) {
			for (BooleanExpression clause : assumption.booleanCollectionArg(0))
				if (!extractBoundsOr(clause, boundMap, booleanMap))
					return false;
		} else if (!extractBoundsOr(assumption, boundMap, booleanMap))
			return false;
		return updateConstantMap();
	}

	private void processHerbrandCast(Monomial poly, Number value) {
		if (poly.operator() == SymbolicOperator.CAST) {
			SymbolicType type = poly.type();
			SymbolicExpression original = (SymbolicExpression) poly.argument(0);
			SymbolicType originalType = original.type();

			if (originalType.isHerbrand() && originalType.isInteger()
					&& type.isInteger()
					|| originalType.isReal() && type.isReal()) {
				SymbolicExpression constant = universe.cast(originalType,
						universe.number(value));

				cacheSimplification(original, constant);
			}
		}
	}

	private boolean updateConstantMap() {
		// The constant map doesn't get cleared because we want to keep
		// accumulating facts. Thus the map might not be empty at this point.
		for (Entry<Monic, Interval> entry : boundMap.entrySet()) {
			Interval interval = entry.getValue();
			Number lower = interval.lower();

			if (lower != null && lower.equals(interval.upper())) {
				Monic expression = entry.getKey();

				assert !interval.strictLower() && !interval.strictUpper();
				constantMap.put(expression, lower);
				processHerbrandCast(expression, lower);
			}
		}

		boolean satisfiable = LinearSolver.reduceConstantMap(info.idealFactory,
				constantMap);

		if (debug) {
			printBoundMap(info.out);
			printConstantMap(info.out);
			printBooleanMap(info.out);
		}
		return satisfiable;
	}

	private void printBoundMap(PrintStream out) {
		out.println("Bound map:");
		boundMap.print(out);
	}

	private void printConstantMap(PrintStream out) {
		out.println("Constant map:");
		for (Entry<Monic, Number> entry : constantMap.entrySet()) {
			out.print(entry.getKey() + " = ");
			out.println(entry.getValue());
		}
		out.println();
		out.flush();
	}

	private void printBooleanMap(PrintStream out) {
		out.println("Boolean map:");
		for (Entry<BooleanExpression, Boolean> entry : booleanMap.entrySet()) {
			out.print(entry.getKey() + " = ");
			out.println(entry.getValue());
		}
		out.println();
		out.flush();
	}

	@SuppressWarnings("unchecked")
	private Map<BooleanExpression, Boolean> copyBooleanMap(
			Map<BooleanExpression, Boolean> map) {
		return (Map<BooleanExpression, Boolean>) (((HashMap<?, ?>) map)
				.clone());
	}

	// TODO: why not combine the boolean map into the BoundMap
	// and call it Interpretation?
	// make some of the code below methods

	private boolean extractBoundsOr(BooleanExpression or, BoundMap aBoundMap,
			Map<BooleanExpression, Boolean> aBooleanMap) {
		SymbolicOperator op = or.operator();

		if (op == SymbolicOperator.OR) {
			// p & (q0 | ... | qn) = (p & q0) | ... | (p & qn)
			// copies of original maps, corresponding to p. these never
			// change...
			BoundMap originalBoundMap = aBoundMap.clone();
			Map<BooleanExpression, Boolean> originalBooleanMap = copyBooleanMap(
					aBooleanMap);
			Iterator<? extends BooleanExpression> clauses = or
					.booleanCollectionArg(0).iterator();
			boolean satisfiable = extractBoundsBasic(clauses.next(), aBoundMap,
					aBooleanMap); // result <- p & q0:

			// result <- result | ((p & q1) | ... | (p & qn)) :
			while (clauses.hasNext()) {
				BooleanExpression clause = clauses.next();
				BoundMap newBoundMap = originalBoundMap.clone();
				Map<BooleanExpression, Boolean> newBooleanMap = copyBooleanMap(
						originalBooleanMap);
				// compute p & q_i:
				boolean newSatisfiable = extractBoundsBasic(clause, newBoundMap,
						newBooleanMap);

				// result <- result | (p & q_i) where result is (aBoundMap,
				// aBooleanMap)....
				satisfiable = satisfiable || newSatisfiable;
				if (newSatisfiable) {
					LinkedList<Monic> boundRemoveList = new LinkedList<>();
					LinkedList<BooleanExpression> booleanRemoveList = new LinkedList<>();

					for (Entry<Monic, Interval> entry : aBoundMap.entrySet()) {
						Monic primitive = entry.getKey();
						Interval oldBound = entry.getValue();
						Interval newBound = newBoundMap.get(primitive);

						if (newBound == null) {
							boundRemoveList.add(primitive);
						} else {
							newBound = info.numberFactory.join(oldBound,
									newBound);
							if (!oldBound.equals(newBound)) {
								if (newBound.isUniversal())
									boundRemoveList.add(primitive);
								else
									entry.setValue(newBound);
							}
						}
					}
					for (Monic primitive : boundRemoveList)
						aBoundMap.remove(primitive);
					for (Entry<BooleanExpression, Boolean> entry : aBooleanMap
							.entrySet()) {
						BooleanExpression primitive = entry.getKey();
						Boolean oldValue = entry.getValue();
						Boolean newValue = newBooleanMap.get(primitive);

						if (newValue == null || !newValue.equals(oldValue))
							booleanRemoveList.add(primitive);
					}
					for (BooleanExpression primitive : booleanRemoveList)
						aBooleanMap.remove(primitive);
				}
			}
			return satisfiable;
		} else { // 1 clause
			// if this is of the form EQ x,y where y is a constant and
			// x and y are not-numeric, add to otherConstantMap
			if (op == SymbolicOperator.EQUALS) {
				SymbolicExpression arg0 = (SymbolicExpression) or.argument(0),
						arg1 = (SymbolicExpression) or.argument(1);
				SymbolicType type = arg0.type();

				if (!type.isNumeric()) {
					boolean const0 = arg0
							.operator() == SymbolicOperator.CONCRETE;
					boolean const1 = (arg1
							.operator() == SymbolicOperator.CONCRETE);

					if (const1 && !const0) {
						otherConstantMap.put(arg0, arg1);
						return true;
					} else if (const0 && !const1) {
						otherConstantMap.put(arg1, arg0);
						return true;
					} else if (const0 && const1) {
						return arg0.equals(arg1);
					} else {
						return true;
					}
				}
			}
			return extractBoundsBasic(or, aBoundMap, aBooleanMap);
		}
	}

	/**
	 * A basic expression is either a boolean constant (true/false), a
	 * LiteralExpression (p or !p) or QuantifierExpression
	 */
	private boolean extractBoundsBasic(BooleanExpression basic,
			BoundMap aBoundMap, Map<BooleanExpression, Boolean> aBooleanMap) {
		SymbolicOperator operator = basic.operator();

		if (operator == SymbolicOperator.CONCRETE)
			return ((BooleanObject) basic.argument(0)).getBoolean();
		if (isRelational(operator)) {

			// Cases: 0=Primitive, 0<Monic, 0<=Monic, Monic<0, Monic<=0,
			// 0!=Primitive.

			SymbolicExpression arg0 = (SymbolicExpression) basic.argument(0);
			SymbolicExpression arg1 = (SymbolicExpression) basic.argument(1);

			if (arg0.type().isNumeric()) {
				switch (operator) {
				case EQUALS: // 0==x
					return extractEQ0Bounds((Primitive) arg1, aBoundMap,
							aBooleanMap);
				case NEQ:
					return extractNEQ0Bounds((Primitive) arg1, aBoundMap,
							aBooleanMap);
				case LESS_THAN: // 0<x or x<0
				case LESS_THAN_EQUALS: // 0<=x or x<=0
					if (arg0.isZero()) {
						return extractIneqBounds((Monic) arg1, true,
								operator == LESS_THAN, aBoundMap, aBooleanMap);
					} else {
						return extractIneqBounds((Monic) arg0, false,
								operator == LESS_THAN, aBoundMap, aBooleanMap);
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
			BooleanExpression primitive = basic.booleanArg(0);
			Boolean value = aBooleanMap.get(primitive);

			if (value != null)
				return !value;
			aBooleanMap.put(primitive, false);
			return true;
		}

		Boolean value = aBooleanMap.get(basic);

		if (value != null)
			return value;
		aBooleanMap.put(basic, true);
		return true;
	}

	private boolean extractEQ0Bounds(Primitive primitive, BoundMap aBoundMap,
			Map<BooleanExpression, Boolean> aBooleanMap) {
		if (primitive instanceof Polynomial)
			return extractEQ0BoundsPoly((Polynomial) primitive, aBoundMap,
					aBooleanMap);

		NumberFactory nf = info.numberFactory;
		Interval bound = aBoundMap.get(primitive);
		Number zero = primitive.type().isInteger() ? nf.zeroInteger()
				: nf.zeroRational();

		if (bound != null && !bound.contains(zero))
			return false;
		aBoundMap.set(primitive, zero);
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
	private boolean extractEQ0BoundsPoly(Polynomial poly, BoundMap aBoundMap,
			Map<BooleanExpression, Boolean> aBooleanMap) {
		NumberFactory nf = info.numberFactory;
		AffineExpression affine = info.affineFactory.affine(poly);
		Monic pseudo = affine.pseudo();
		RationalNumber coefficient = nf.rational(affine.coefficient());
		RationalNumber offset = nf.rational(affine.offset());
		RationalNumber rationalValue = nf
				.negate(info.numberFactory.divide(offset, coefficient));
		Number value; // same as rationalValue but IntegerNumber if type is
						// integer
		Interval bound = aBoundMap.get(pseudo);

		if (pseudo.type().isInteger()) {
			if (!nf.isIntegral(rationalValue))
				return false;
			value = nf.integerValue(rationalValue);
		} else {
			value = rationalValue;
		}
		if (bound != null && !bound.contains(value))
			return false;
		aBoundMap.set(pseudo, value);
		return true;
	}

	private boolean extractNEQ0Bounds(Primitive primitive, BoundMap aBoundMap,
			Map<BooleanExpression, Boolean> aBooleanMap) {

		if (primitive instanceof Polynomial)
			return extractNEQ0BoundsPoly((Polynomial) primitive, aBoundMap,
					aBooleanMap);

		Interval bound = aBoundMap.get(primitive);
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
				aBoundMap.set(primitive, bound);
		}
		aBooleanMap.put(info.universe.neq(zero, primitive), true);
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
	private boolean extractNEQ0BoundsPoly(Polynomial poly, BoundMap aBoundMap,
			Map<BooleanExpression, Boolean> aBooleanMap) {
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
		Interval bound = aBoundMap.get(pseudo);
		Monomial zero = info.idealFactory.zero(type);

		if (type.isInteger()) {
			if (nf.isIntegral(rationalValue)) {
				value = nf.integerValue(rationalValue);
			} else {
				// an integer cannot equal a non-integer.
				aBooleanMap.put(info.idealFactory.neq(zero, poly), true);
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
				aBoundMap.set(pseudo, bound);
		}
		aBooleanMap.put(info.universe.neq(zero, poly), true);
		return true;
	}

	private boolean extractIneqBounds(Monic monic, boolean gt, boolean strict,
			BoundMap aBoundMap, Map<BooleanExpression, Boolean> aBooleanMap) {
		if (monic instanceof Polynomial)
			return extractIneqBoundsPoly((Polynomial) monic, gt, strict,
					aBoundMap, aBooleanMap);

		NumberFactory nf = info.numberFactory;
		Number zero = monic.type().isInteger() ? nf.zeroInteger()
				: nf.zeroRational();
		Interval interval = gt ? aBoundMap.restrictLower(monic, zero, strict)
				: aBoundMap.restrictUpper(monic, zero, strict);

		return !interval.isEmpty();
	}

	private boolean extractIneqBoundsPoly(Polynomial poly, boolean gt,
			boolean strict, BoundMap aBoundMap,
			Map<BooleanExpression, Boolean> aBooleanMap) {
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
			interval = aBoundMap.restrictLower(pseudo, theBound, strict);
		else // upper bound
			interval = aBoundMap.restrictUpper(pseudo, theBound, strict);
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
				BooleanExpression eq0 = (BooleanExpression) info.universe
						.not(clause);

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
			for (BooleanExpression or : assumption.booleanCollectionArg(0)) {
				declareClauseFact(or);
			}
		} else {
			declareClauseFact(assumption);
		}
	}

	// ****************************************************************
	// * ................. Simplification Routines................... *
	// ****************************************************************

	/**
	 * Simplifies a {@link Monic}.
	 * 
	 * Look up in constant map. If found, great. Otherwise, if the Monic is a
	 * {@link Polynomial}, try expanding.
	 * 
	 * 
	 * @param monic
	 * @return
	 */
	private Monomial simplifyMonic(Monic monic) {
		Number constant = constantMap.get(monic);

		if (constant != null)
			return info.idealFactory.constant(constant);

		Monomial result = (Monomial) super.simplifyGenericExpression(monic);

		if (result != monic)
			return result;

		if (monic instanceof Polynomial
				&& monic.hasNontrivialExpansion(info.idealFactory)) {
			Polynomial poly = (Polynomial) monic;
			SymbolicMap<Monic, Monomial> expansion = poly
					.expand(info.idealFactory);

			if (expansion.isEmpty())
				return info.idealFactory.zero(monic.type());
			result = info.idealFactory.factorTermMap(expansion);
			if (result != monic)
				result = (Monomial) simplifyExpression(result);
		}
		return result;
	}

	/**
	 * Determines if the operator is one of the relation operators
	 * {@link SymbolicOperator#LESS_THAN},
	 * {@link SymbolicOperator#LESS_THAN_EQUALS},
	 * {@link SymbolicOperator#EQUALS}, or {@link SymbolicOperator#NEQ}.
	 * 
	 * @param operator
	 *            a non-<code>null</code> symbolic operator
	 * @return <code>true</code> iff <code>operator</code> is one of the four
	 *         relationals
	 */
	private boolean isRelational(SymbolicOperator operator) {
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
	private boolean isNumericRelational(SymbolicExpression expression) {
		return isRelational(expression.operator())
				&& ((SymbolicExpression) expression.argument(0)).isNumeric();
	}

	/**
	 * Simplifies a relational expression. Assumes expression does not already
	 * exist in simplification cache. Does NOT assume that generic
	 * simplification has been performed on expression. Current strategy:
	 * 
	 * <pre>
	 * 1. simplifyGeneric
	 * 2. if no change: simplifyRelationalWork
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
		BooleanExpression result1 = (BooleanExpression) simplifyGenericExpression(
				expression);

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
		return (BooleanExpression) simplifyGenericExpression(result1);
	}

	/**
	 * Simplifies a relational expression. Assumes expression has already gone
	 * through generic simplification and result is not in cache.
	 * 
	 * @param expression
	 * @return
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
			return result == null ? expression : result;
		}
		case EQUALS: {
			assert arg0.isZero();
			// arg1 has already been simplified.
			result = simplifyEQ0((Primitive) arg1);
			// if (result != null && (result.isTrue() || result.isFalse()))
			// return result;
			//
			// if (debug) {
			// out.println("Starting: =0 expanding primitive of total degree "
			// + arg1.totalDegree());
			// out.flush();
			// }

			// SymbolicMap<Monic, Monomial> termMap = arg1
			// .expand(info.idealFactory);
			//
			// if (debug) {
			// out.println("Finsished: =0 expanding primitive of total degree "
			// + arg1.totalDegree() + ": result has size "
			// + termMap.size());
			// out.flush();
			// }
			//
			// if (termMap.isEmpty())
			// return info.trueExpr;

			// Monomial newArg = info.idealFactory.factorTermMap(termMap);

			// TODO: to check if a poly==0, don't blindly expand.
			// instead:
			// (a/b+c/d)=0 <==> (a(d/g))+(c(b/g))=0, where g=gcd(b,d)

			// if (arg0.equals(newArg))
			return result == null ? expression : result;
			// return (BooleanExpression) apply(
			// info.idealFactory.equals(arg0, newArg));
		}
		case NEQ: {
			assert arg0.isZero();

			BooleanExpression negExpression = universe.not(expression);

			result = (BooleanExpression) simplifyExpression(negExpression);
			result = universe.not(result);
			return result;
		}
		default:
			throw new SARLInternalException("unreachable");
		}
	}

	private BooleanExpression simplifiedEQ0Monic(Monic monic) {
		NumericExpression zero = info.idealFactory.zero(monic.type());
		BooleanExpression expr = info.idealFactory.equals(zero, monic);
		BooleanExpression result = (BooleanExpression) simplifyExpression(expr);

		return result;
	}

	// returns null if no simplification possible beyond obvious...
	private BooleanExpression simplifiedNEQ0Monic(Monic monic) {
		NumericExpression zero = info.idealFactory.zero(monic.type());
		BooleanExpression expr = info.idealFactory.neq(zero, monic);
		BooleanExpression result = (BooleanExpression) simplifyExpression(expr);

		return result;
	}

	/**
	 * A categorization of intervals. Every interval falls into exactly one of
	 * these categories.
	 * 
	 * @author siegel
	 *
	 */
	private enum BoundType {
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

	private BoundType boundType(Interval bound) {
		if (bound.isEmpty())
			return BoundType.EMPTY;

		Number l = bound.lower(), r = bound.upper();
		int lsign = l == null ? -1 : l.signum();
		int rsign = r == null ? 1 : r.signum();

		if (lsign > 0)
			return BoundType.GT0;
		if (rsign < 0)
			return BoundType.LT0;

		if (lsign < 0) {
			if (rsign == 0) {
				return bound.strictUpper() ? BoundType.LT0 : BoundType.LE0;
			} else { // rsign > 0
				return BoundType.ALL;
			}
		} else { // lsign == 0
			if (rsign == 0) {
				return BoundType.EQ0;
			} else { // rsign > 0
				return bound.strictLower() ? BoundType.GT0 : BoundType.EQ0;
			}
		}
	}

	/**
	 * Does every x in the bound interval satisfy x OP 0, where OP is one of
	 * <, <=, >, >=. Answer can be
	 * 
	 * @param bound
	 * @param gt
	 * @param strict
	 * @return
	 */
	private BooleanExpression ineqFromBound(Monic monic, Interval bound,
			boolean gt, boolean strict) {
		Number l = bound.lower(), r = bound.upper();

		if (strict) { // bound>0 or bound<0
			if (l != null) {
				int lsign = l.signum();

				if (lsign > 0 || (lsign == 0 && bound.strictLower()))
					return gt ? info.trueExpr : info.falseExpr;
				if (lsign == 0 && !bound.strictLower())
					return gt ? simplifiedNEQ0Monic(monic) : info.falseExpr;
			}
			if (r != null) {
				int rsign = r.signum();

				if (rsign < 0 || (rsign == 0 && bound.strictUpper()))
					return gt ? info.falseExpr : info.trueExpr;
				if (rsign == 0 && !bound.strictUpper())
					return gt ? info.falseExpr : simplifiedNEQ0Monic(monic);
			}
		} else { // bound>=0 or bound<=0
			if (gt) { // bound>=0
				if (l != null && l.signum() >= 0)
					return info.trueExpr;
				if (r != null) {
					int rsign = r.signum();

					if (rsign < 0)
						return info.falseExpr;
					if (rsign == 0)
						return bound.strictUpper() ? info.falseExpr
								: simplifiedEQ0Monic(monic);
				}
			} else {// bound<=0
				if (r != null && r.signum() <= 0)
					return info.trueExpr;
				if (l != null) {
					int lsign = l.signum();

					if (lsign > 0)
						return info.falseExpr;
					if (lsign == 0)
						return bound.strictLower() ? info.falseExpr
								: simplifiedEQ0Monic(monic);
				}
			}
		}
		return null;
	}

	/**
	 * Simplifies an inequality of one of the forms: x>0, x>=0, x<0, x<=0, where
	 * x is a {@link Monic} in which the maximum degree of any {@link Primitive}
	 * is 1. Assumes <code>monic</code> is already simplified.
	 * 
	 * @param monic
	 * @param gt
	 *            is the form one of x>0, x>=0
	 * @param strict
	 *            is the form one of x>0 or x<0 (strict inequality)
	 * @return simplified version of the inequality of <code>null</code> if no
	 *         simplification was possible
	 */
	private BooleanExpression simplifyIneq0(Monic monic, boolean gt,
			boolean strict) {
		// see if there is a bound on this monic...
		SymbolicType type = monic.type();
		Interval bound = boundMap.get(monic);
		BooleanExpression result;

		if (bound != null) {
			result = ineqFromBound(monic, bound, gt, strict);
			if (result != null)
				return result;
		}
		if (monic instanceof Polynomial)
			return simplifyIneq0Poly((Polynomial) monic, gt, strict);
		if (monic instanceof Primitive)
			return null;

		// look for bounds on the primitive factors...

		SymbolicMap<Primitive, PrimitivePower> factorMap = monic
				.monicFactors(info.idealFactory);
		int numFactors = factorMap.size();
		boolean[] mask = new boolean[numFactors]; // unconstrained primitives
		List<Primitive> zeroList = new LinkedList<>();
		boolean positive = gt;
		int count = 0, unconstrained = 0;

		for (Primitive p : factorMap.keys()) {
			Interval pb = boundMap.get(p);

			if (pb == null) {
				mask[count] = true;
				unconstrained++;
			} else {
				switch (boundType(pb)) {
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
					return strict ? info.falseExpr : info.trueExpr;
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

		BooleanExpressionFactory bf = info.booleanFactory;
		Monomial zero = info.idealFactory.zero(type);

		if (unconstrained > 0) {
			// create new Monic from the unconstrained primitives
			Monic newMonic = info.idealFactory.monicMask(monic, mask);
			SymbolicOperator op = strict ? LESS_THAN : LESS_THAN_EQUALS;

			result = positive ? bf.booleanExpression(op, zero, newMonic)
					: bf.booleanExpression(op, newMonic, zero);
		} else { // newMonic is essentially 1
			result = positive ? info.trueExpr : info.falseExpr;
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
	 * Simplifies expression poly OP 0, where poly is a {@link Polynomial} and
	 * OP is one of LT, LE, GT, or GE.
	 * 
	 * Preconditions:
	 * <ul>
	 * <li>there is no entry in the {@link #constantMap} for <code>poly</code>
	 * </li>
	 * <li><code>poly</code> is fully expanded</li> <lil><code>poly</code> has
	 * at least 2 terms</li>
	 * </ul>
	 * 
	 * @param poly
	 * @param gt
	 * @param strict
	 * @return
	 */
	private BooleanExpression simplifyIneq0Poly(Polynomial poly, boolean gt,
			boolean strict) {
		AffineExpression affine = info.affineFactory.affine(poly);
		Monic pseudo = affine.pseudo(); // non-null since zep non-constant
		Number pseudoValue = constantMap.get(pseudo);
		AffineFactory af = info.affineFactory;

		if (pseudoValue != null) {
			// substitute known constant value for pseudo...
			Number val = af.affineValue(affine, pseudoValue);
			int sgn = val.signum();

			if (gt) {
				return (strict ? sgn > 0 : sgn >= 0) ? info.trueExpr
						: info.falseExpr;
			} else {
				return (strict ? sgn < 0 : sgn < 0) ? info.trueExpr
						: info.falseExpr;
			}
		}

		Interval pseudoBound = boundMap.get(pseudo);

		if (pseudoBound == null)
			return null;

		// the following is a bound on poly
		Interval polyBound = info.numberFactory.affineTransform(pseudoBound,
				affine.coefficient(), affine.offset());

		return ineqFromBound(poly, polyBound, gt, strict);
	}

	/**
	 * Attempts to simplify the expression poly=0. Returns <code>null</code> if
	 * no simplification is possible, else returns a {@link BooleanExpression}
	 * equivalent to poly=0.
	 * 
	 * @param poly
	 *            a non-<code>null</code>, non-constant {@link Polynomial}
	 * @return <code>null</code> or a {@link BooleanExpression} equivalent to
	 *         poly=0
	 */
	private BooleanExpression simplifyEQ0(Primitive primitive) {
		if (primitive instanceof Polynomial)
			return simplifyEQ0Poly((Polynomial) primitive);

		// a true primitive...
		Number number = constantMap.get(primitive);

		if (number != null)
			return number.isZero() ? info.trueExpr : info.falseExpr;
		return null;
	}

	private BooleanExpression simplifyEQ0Poly(Polynomial poly) {
		SymbolicType type = poly.type();
		AffineExpression affine = info.affineFactory.affine(poly);
		Monic pseudo = affine.pseudo(); // non-null since zep non-constant
		Number pseudoValue = constantMap.get(pseudo);

		if (pseudoValue != null)
			// substitute known constant value for pseudo...
			return info.affineFactory.affineValue(affine, pseudoValue).isZero()
					? info.trueExpr : info.falseExpr;

		Number offset = affine.offset();
		Number coefficient = affine.coefficient();

		// aX+b=0 => -b/a=X is an integer
		if (type.isInteger()
				&& !info.numberFactory
						.mod((IntegerNumber) offset,
								(IntegerNumber) info.numberFactory
										.abs((IntegerNumber) coefficient))
						.isZero())
			return info.falseExpr;
		pseudoValue = info.numberFactory
				.negate(info.numberFactory.divide(offset, coefficient));

		Interval oldBounds = boundMap.get(pseudo);

		if (oldBounds == null)
			return null;

		// Know: lower <? pseudoValue <? upper
		// (Here "<?" means "<" or "<=".). So
		// lower - pseudoValue <? 0
		// upper - pseudoValue >? 0
		// if either of these is not true, you have a contradiction,
		// simplify to "false".

		// leftSign = sign of (lower-pseudoValue)
		// rightSign = sign of (upper-pseudoValue)
		int leftSign, rightSign;

		{
			Number lower = oldBounds.lower();

			if (lower == null)
				leftSign = -1; // -infinity
			else
				leftSign = info.numberFactory.subtract(lower, pseudoValue)
						.signum();

			Number upper = oldBounds.upper();

			if (upper == null) // +infinity
				rightSign = 1;
			else
				rightSign = info.numberFactory.subtract(upper, pseudoValue)
						.signum();
		}
		// if 0 is not in that interval, return FALSE
		if (leftSign > 0 || (leftSign == 0 && oldBounds.strictLower()))
			return info.falseExpr;
		if (rightSign < 0 || (rightSign == 0 && oldBounds.strictUpper()))
			return info.falseExpr;
		return null;
	}

	// Exported methods.............................................

	/**
	 * {@inheritDoc}
	 * 
	 * <p>
	 * Simplifies an expression, providing special handling beyond the generic
	 * simplification for ideal expressions. Relational expressions also get
	 * special handling. All other expressions are simplified generically.
	 * </p>
	 * 
	 * <p>
	 * This method does not look in the simplify cache for an existing
	 * simplification of expression. See the documentation for the super method.
	 * </p>
	 * 
	 * @see {@link #simplifyGenericExpression}
	 * @see {@link #simplifyRelational}
	 * @see {@link #simplifyPolynomial}
	 */
	@Override
	protected SymbolicExpression simplifyExpression(
			SymbolicExpression expression) {
		if (expression instanceof Constant) // optimization
			return expression;
		if (expression instanceof Monic)
			return simplifyMonic((Monic) expression);

		SymbolicType type = expression.type();

		if (type != null) {
			if (type.isBoolean()) {
				if (expression.isTrue() || expression.isFalse())
					return expression;

				Boolean booleanResult = booleanMap.get(expression);

				if (booleanResult != null) {
					return booleanResult ? universe.trueExpression()
							: universe.falseExpression();
				}
				if (isNumericRelational(expression))
					return simplifyRelational((BooleanExpression) expression);
			} else if (!type.isNumeric()) {
				SymbolicExpression constant = otherConstantMap.get(expression);

				if (constant != null)
					return constant;
			}
		}
		return simplifyGenericExpression(expression);
	}

	@Override
	public Interval assumptionAsInterval(SymbolicConstant symbolicConstant) {
		if (intervalComputed) {
			if (theInterval != null
					&& intervalVariable.equals(symbolicConstant))
				return theInterval;
			return null;
		}
		intervalComputed = true;
		if (!booleanMap.isEmpty() || !rawAssumption.isTrue()) {
			return null;
		}
		if (!constantMap.isEmpty()) {
			if (!boundMap.isEmpty() || constantMap.size() != 1) {
				return null;
			}
			Entry<Monic, Number> entry = constantMap.entrySet().iterator()
					.next();
			Monic fp1 = entry.getKey();
			Number value = entry.getValue();

			if (!fp1.equals(symbolicConstant)) {
				return null;
			}
			theInterval = info.numberFactory.singletonInterval(value);
			intervalVariable = symbolicConstant;
			return theInterval;
		}
		if (boundMap.size() == 1) {
			Entry<Monic, Interval> entry = boundMap.entrySet().iterator()
					.next();
			Monic fp1 = entry.getKey();

			if (!fp1.equals(symbolicConstant)) {
				return null;
			}
			theInterval = entry.getValue();
			intervalVariable = symbolicConstant;
			return theInterval;
		}
		return null;
	}

	@Override
	public Map<SymbolicConstant, SymbolicExpression> substitutionMap() {
		if (substitutionMap == null) {
			substitutionMap = new HashMap<SymbolicConstant, SymbolicExpression>();
			for (Entry<Monic, Number> entry : constantMap.entrySet()) {
				Monic fp = entry.getKey();

				if (fp instanceof SymbolicConstant)
					substitutionMap.put((SymbolicConstant) fp,
							universe.number(entry.getValue()));
			}
			for (Entry<SymbolicExpression, SymbolicExpression> entry : otherConstantMap
					.entrySet()) {
				SymbolicExpression expr = entry.getKey();

				if (expr instanceof SymbolicConstant)
					substitutionMap.put((SymbolicConstant) expr,
							entry.getValue());
			}
			for (Entry<BooleanExpression, Boolean> entry : booleanMap
					.entrySet()) {
				BooleanExpression primitive = entry.getKey();

				if (primitive instanceof SymbolicConstant)
					substitutionMap.put((SymbolicConstant) primitive,
							universe.bool(entry.getValue()));
			}
		}
		return substitutionMap;
	}

	/**
	 * This method takes the assumption in the IdealSimplifier and reduces the
	 * Context to its basic form.
	 */
	@Override
	public BooleanExpression getReducedContext() {
		return assumption;
	}

	/**
	 * This method takes the assumption in the IdealSimplifier and
	 */
	@Override
	public BooleanExpression getFullContext() {
		if (fullContext == null) {
			Map<SymbolicConstant, SymbolicExpression> map = substitutionMap();

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
}
