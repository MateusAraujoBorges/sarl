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
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;

/**
 * A context builder is used to create a new {@link Context} from a
 * {@link BooleanExpression} called the "assumption".
 * 
 * @author siegel
 *
 */
public class ContextBuilder {

	/**
	 * The instance of {@link Context} which is being built by this builder.
	 */
	private Context theContext;

	/**
	 * The assumption which is being converted to a {@link Context}. It may be
	 * changed in the process of building the context, principally by replacing
	 * solved variables with their constant values to form what is called the
	 * "reduced assumption".
	 */
	private BooleanExpression assumption;

	/**
	 * This is the same as the {@link #assumption}, but without the information
	 * from the context's boundMap, booleanMap, constantMap, and
	 * otherConstantMap. I.e., assumption = rawAssumption + boundMap +
	 * booleanMap + constantMap + otherConstantMap. Currently it is used only to
	 * implement the method {@link Context#assumptionAsInterval()}. Should
	 * probably get rid of that method and this field.
	 */
	BooleanExpression rawAssumption;

	/**
	 * A structure with references to the most commonly used factories and other
	 * objects.
	 */
	private SimplifierInfo info;

	/**
	 * The symbolic universe used for constructing new expressions and other
	 * symbolic objects.
	 */
	private PreUniverse universe;

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
	 * Constructs a new {@link Context} with given parameters. The
	 * <code>assumption</code> is analyzed and the context fields updated
	 * accordingly. The resulting {@link Context} can then be obtained by method
	 * {@link #getClass()}.
	 * 
	 * @param info
	 *            simple structure with fields for all required factories and
	 *            other commonly-used objects needed by this builder
	 * @param assumption
	 *            the boolean expression which is being analyze and converted
	 *            into an abstract representation which is an instance of
	 *            {@link Context}
	 */
	public ContextBuilder(SimplifierInfo info, BooleanExpression assumption) {
		theContext = new Context(info);
		this.assumption = assumption;
		this.info = info;
		this.universe = info.universe;
		initialize();
		this.theContext.setRawAssumption(this.rawAssumption);
		this.theContext.setReducedAssumption(this.assumption);
	}

	// private methods...

	/**
	 * Creates a new simplifier worker for carrying out a simplification task
	 * under the assumption of {@link #theContext}.
	 * 
	 * @return new instance of {@link IdealSimplifierWorker} with the context
	 *         {@link #theContext}
	 */
	private IdealSimplifierWorker newWorker() {
		return new IdealSimplifierWorker(info, theContext);
	}

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
			theContext.clearSimplificationCache();

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

			for (Entry<Monic, Interval> entry : theContext
					.getMonicBoundEntries()) {
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

			for (Entry<Monic, Number> entry : theContext
					.getMonicConstantEntries()) {
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

			for (Entry<SymbolicExpression, SymbolicExpression> entry : theContext
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

			for (Entry<BooleanExpression, Boolean> entry : theContext
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

			for (Entry<Monic, Number> entry : theContext
					.getMonicConstantEntries()) {
				SymbolicExpression key = entry.getKey();

				if (key.operator() == SymbolicOperator.SYMBOLIC_CONSTANT)
					substitutionMap.put(key, universe.number(entry.getValue()));
			}
			for (Entry<SymbolicExpression, SymbolicExpression> entry : theContext
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
			assumption = newAssumption;
		}
		extractRemainingFacts();
	}

	/**
	 * Attempts to determine bounds (upper and lower) on {@link Monic}
	 * expressions by examining the {@link #assumption}. Returns
	 * <code>false</code> if {@link #assumption} is determined to be
	 * unsatisfiable. Updates boundMap, booleanMap, constantMap, and
	 * otherConstantMap.
	 */
	private boolean extractBounds() {
		if (assumption.operator() == SymbolicOperator.AND) {
			for (SymbolicObject arg : assumption.getArguments()) {
				BooleanExpression clause = (BooleanExpression) arg;

				if (!extractBoundsOr(clause, theContext))
					return false;
			}
		} else if (!extractBoundsOr(assumption, theContext))
			return false;
		return theContext.updateConstantMap();
	}
	
	// let's try this again:
	// p||q : assume !p, simplify q.  Replace q with simplified q.
	// Then assume !q and simplify p.
	// Example : x>0 || x>3 --> x>0 || false --> x>0

	// need to do same thing for simplifying AND.
	// p&&q : assume p, simplify q.
	

	private boolean extractBoundsOr(BooleanExpression or, Context context) {
		if (or.operator() != SymbolicOperator.OR)
			return extractBoundsFromClause(or, context);

		// p & (q0 | ... | qn) = (p & q0) | ... | (p & qn)
		// copies of original maps, corresponding to p. these never
		// change...
		Context originalAI = context.clone();
		Iterator<? extends SymbolicObject> clauses = or.getArguments()
				.iterator();
		boolean satisfiable = extractBoundsBasic(
				(BooleanExpression) clauses.next(), context);

		// result <- p & q0:
		// result <- result | ((p & q1) | ... | (p & qn)) :
		while (clauses.hasNext()) {
			BooleanExpression clause = (BooleanExpression) clauses.next();
			Context newAI = originalAI.clone();
			// compute p & q_i:
			boolean newSatisfiable = extractBoundsBasic(clause, newAI);

			// result <- result | (p & q_i) where result is (aBoundMap,
			// aBooleanMap)....
			satisfiable = satisfiable || newSatisfiable;
			if (newSatisfiable) {
				LinkedList<Monic> boundRemoveList = new LinkedList<>();
				LinkedList<BooleanExpression> booleanRemoveList = new LinkedList<>();

				for (Entry<Monic, Interval> entry : context
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
					context.removeBound(primitive);
				for (Entry<BooleanExpression, Boolean> entry : context
						.getBooleanEntries()) {
					BooleanExpression primitive = entry.getKey();
					Boolean oldValue = entry.getValue();
					Boolean newValue = newAI.getTruth(primitive);

					if (newValue == null || !newValue.equals(oldValue))
						booleanRemoveList.add(primitive);
				}
				for (BooleanExpression primitive : booleanRemoveList)
					context.removeTruth(primitive);
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
			Context context) {
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
					context.setOtherValue(arg0, arg1);
					return true;
				} else if (const0 && !const1) {
					context.setOtherValue(arg1, arg0);
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
				context.setOtherValue(defn.array, defn.lambda);
			}
		}
		return extractBoundsBasic(clause, context);
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
			Context context) {
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
					return extractEQ0Bounds((Primitive) arg1, context);
				case NEQ:
					return extractNEQ0Bounds((Primitive) arg1, context);
				case LESS_THAN: // 0<x or x<0
				case LESS_THAN_EQUALS: // 0<=x or x<=0
					if (arg0.isZero()) {
						return extractIneqBounds((Monic) arg1, true,
								operator == LESS_THAN, context);
					} else {
						return extractIneqBounds((Monic) arg0, false,
								operator == LESS_THAN, context);
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
			Boolean value = context.getTruth(primitive);

			if (value != null)
				return !value;
			context.setTruth(primitive, false);
			return true;
		}

		Boolean value = context.getTruth(basic);

		if (value != null)
			return value;
		context.setTruth(basic, true);
		return true;
	}

	private boolean extractEQ0Bounds(Primitive primitive, Context context) {
		if (primitive instanceof Polynomial)
			return extractEQ0BoundsPoly((Polynomial) primitive, context);

		NumberFactory nf = info.numberFactory;
		Interval bound = context.getBound(primitive);
		SymbolicType type = primitive.type();
		Number zero = type.isInteger() ? nf.zeroInteger() : nf.zeroRational();

		if (bound != null && !bound.contains(zero))
			return false;

		BooleanExpression neq0 = info.booleanFactory.booleanExpression(
				SymbolicOperator.NEQ, info.idealFactory.zero(primitive.type()),
				primitive);
		Boolean neq0Truth = context.getTruth(neq0);

		if (neq0Truth != null && neq0Truth.booleanValue())
			return false;
		context.setMonicValue(primitive, zero);
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
	private boolean extractEQ0BoundsPoly(Polynomial poly, Context context) {
		NumberFactory nf = info.numberFactory;
		AffineExpression affine = info.affineFactory.affine(poly);
		Monic pseudo = affine.pseudo();
		RationalNumber coefficient = nf.rational(affine.coefficient());
		RationalNumber offset = nf.rational(affine.offset());
		RationalNumber rationalValue = nf
				.negate(info.numberFactory.divide(offset, coefficient));
		// same as rationalValue but IntegerNumber if type is integer:
		Number value;
		Interval bound = context.getBound(pseudo);

		if (pseudo.type().isInteger()) {
			if (!nf.isIntegral(rationalValue))
				return false;
			value = nf.integerValue(rationalValue);
		} else {
			value = rationalValue;
		}
		if (bound != null && !bound.contains(value))
			return false;
		context.setMonicValue(pseudo, value);
		return true;
	}

	private boolean extractNEQ0Bounds(Primitive primitive, Context context) {
		if (primitive instanceof Polynomial)
			return extractNEQ0BoundsPoly((Polynomial) primitive, context);

		Interval bound = context.getBound(primitive);
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
				context.setBound(primitive, bound);
		}
		context.setTruth(info.universe.neq(zero, primitive), true);
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
	private boolean extractNEQ0BoundsPoly(Polynomial poly, Context context) {
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
		Interval bound = context.getBound(pseudo);
		Monomial zero = info.idealFactory.zero(type);

		if (type.isInteger()) {
			if (nf.isIntegral(rationalValue)) {
				value = nf.integerValue(rationalValue);
			} else {
				// an integer cannot equal a non-integer.
				context.setTruth(info.idealFactory.neq(zero, poly), true);
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
				context.setBound(pseudo, bound);
		}
		context.setTruth(info.universe.neq(zero, poly), true);
		return true;
	}

	private boolean extractIneqBounds(Monic monic, boolean gt, boolean strict,
			Context context) {
		if (monic instanceof Polynomial)
			return extractIneqBoundsPoly((Polynomial) monic, gt, strict,
					context);

		NumberFactory nf = info.numberFactory;
		Number zero = monic.type().isInteger() ? nf.zeroInteger()
				: nf.zeroRational();
		Interval interval = gt ? context.restrictLowerBound(monic, zero, strict)
				: context.restrictUpperBound(monic, zero, strict);

		return !interval.isEmpty();
	}

	private boolean extractIneqBoundsPoly(Polynomial poly, boolean gt,
			boolean strict, Context context) {
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
			interval = context.restrictLowerBound(pseudo, theBound, strict);
		else
			// upper bound
			interval = context.restrictUpperBound(pseudo, theBound, strict);
		return !interval.isEmpty();
	}

	private void declareFact(SymbolicExpression booleanExpression,
			boolean truth) {
		BooleanExpression value = truth ? info.trueExpr : info.falseExpr;

		theContext.cacheSimplification(booleanExpression, value);
	}

	private void declareClauseFact(BooleanExpression clause) {
		if (isNumericRelational(clause)) {
			if (clause.operator() == SymbolicOperator.NEQ) {
				BooleanExpression eq0 = info.universe.not(clause);

				declareFact(eq0, false);
			}
		} else
			declareFact(clause, true);
	}

	/**
	 * This method inserts into the simplification cache all facts from the
	 * assumption that are not otherwise encoded in the constantMap, booleanMap,
	 * or boundMap. It is to be invoked only after the assumption has been
	 * simplified for the final time.
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

	// public methods ...

	/**
	 * Gets the {@link Context} that was built by this builder. The context is
	 * built at construction time, then this method is used to get it.
	 * 
	 * @return the context that was built
	 */
	public Context getContext() {
		return theContext;
	}

}
