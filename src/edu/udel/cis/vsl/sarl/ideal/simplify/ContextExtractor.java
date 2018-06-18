package edu.udel.cis.vsl.sarl.ideal.simplify;

import static edu.udel.cis.vsl.sarl.IF.SARLConstants.polyProbThreshold;
import static edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator.LESS_THAN;

import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.Set;

import edu.udel.cis.vsl.sarl.IF.CoreUniverse.ForallStructure;
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
import edu.udel.cis.vsl.sarl.IF.object.BooleanObject;
import edu.udel.cis.vsl.sarl.IF.object.NumberObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Polynomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal.IF.PrimitivePower;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.simplify.IF.Range;
import edu.udel.cis.vsl.sarl.simplify.IF.RangeFactory;
import edu.udel.cis.vsl.sarl.util.Pair;
import edu.udel.cis.vsl.sarl.util.SingletonSet;

public class ContextExtractor {

	public final static boolean debug = false;

	/**
	 * A random number generator with seed very likely to be distinct from all
	 * other seeds.
	 * 
	 * Note from Java API: "Instances of java.util.Random are threadsafe.
	 * However, the concurrent use of the same java.util.Random instance across
	 * threads may encounter contention and consequent poor performance.
	 * Consider instead using ThreadLocalRandom in multithreaded designs."
	 */
	private static Random random = new Random();

	private Set<SymbolicConstant> dirtySet;

	private Context context;

	private SimplifierInfo info;

	/**
	 * A simple structure with two fields: a symbolic expression of array type
	 * and an equivalent array-lambda expression.
	 * 
	 * @see #extractArrayDefinition(BooleanExpression)
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

	public ContextExtractor(Context context, Set<SymbolicConstant> dirtySet) {
		this.context = context;
		this.info = context.info;
		this.dirtySet = dirtySet;
	}

	// ************************ Extraction Methods ************************
	// These methods parse a boolean expression and update the subMap
	// and rangeMap appropriately. They do not simplify.

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
	public void extractAnd(BooleanExpression assumption)
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
	 * Processes an expression in which the operator is not
	 * {@link SymbolicOperator#AND}. In the CNF form, this expression is a
	 * clause of the outer "and" expression.
	 * 
	 * TODO: think about this: this is supposed to be a simple way to simplify
	 * an or expression, reusing the code for simplifying an AND expression. But
	 * is this really a good idea? don't we want the size of the expression
	 * being simplified to strictly decrease?
	 * 
	 * @param expr
	 *            the boolean expression to process
	 * @throws InconsistentContextException
	 *             if this context is determined to be inconsistent
	 */
	public void extractOr(BooleanExpression expr)
			throws InconsistentContextException {
		if (expr.operator() != SymbolicOperator.OR) {
			extractClause(expr);
			return;
		}
		if (extractNumericOr(expr))
			return;
		context.addSub(expr, info.trueExpr, dirtySet);
	}

	private boolean extractNumericOr(Iterable<? extends SymbolicObject> clauses)
			throws InconsistentContextException {
		Monic theMonic = null;
		Range theRange = null;

		for (SymbolicObject clause : clauses) {
			// look for 0=p, 0!=p, 0<m, 0<=m, m<0, m<=0
			BooleanExpression theArg = (BooleanExpression) clause;
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
		context.restrictRange(theMonic, theRange, dirtySet);
		return true;
	}

	/**
	 * <p>
	 * Attempts to combine the clauses of an or-expression into a range
	 * restriction on a single {@link Monic} and add that restriction to the
	 * state of this {@link Context}.  If the given expression is not an
	 * or-expression then it is treated as an or-expression with one clause.
	 * </p>
	 * 
	 * Examples:
	 * 
	 * <pre>
	 * x<5 && x>3 ---> x in (3,5)
	 * x<5 ---> x in (-infty, 5)
	 * x<5 || y>3 ---> null 
	 * </pre>
	 * 
	 * @param orExpr
	 * @return <code>true</code> if a the or expression was reduced to a single
	 *         range restriction and the information was added to this context;
	 *         otherwise returns <code>false</code> and the state of this
	 *         context was not changed
	 * @throws InconsistentContextException
	 *             if the or expression involves a numeric constraint that
	 *             implies some {@link Monic} has an empty range
	 */
	protected boolean extractNumericOr(BooleanExpression orExpr)
			throws InconsistentContextException {
		if (orExpr.operator() == SymbolicOperator.OR)
			return extractNumericOr(orExpr.getArguments());
		else
			return extractNumericOr(
					new SingletonSet<BooleanExpression>(orExpr));
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
	public void extractClause(BooleanExpression clause)
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
			context.addSub(clause, info.trueExpr, dirtySet);
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
		context.addSub(pred, info.falseExpr, dirtySet);
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
				context.addSub(arg0, arg1, dirtySet);
			} else if (const0 && !const1) {
				context.addSub(arg1, arg0, dirtySet);
			} else if (const0 && const1) {
				if (!arg0.equals(arg1))
					throw new InconsistentContextException();
			} else { // neither is constant
				context.addSub(eqExpr, info.trueExpr, dirtySet);
			}
		}
	}

	/**
	 * Attempts to determine whether a polynomial is identically zero using a
	 * probabilistic technique (the Schwartz-Zippel lemma).
	 * 
	 * @param poly
	 *            the polynomial, non-{@code null}, of integer or real type
	 * @param totalDegree
	 *            an upper bound on the total degree of the polynomial
	 * @param vars
	 *            the "variables" occurring in the polynomial; the polynomial
	 *            must be an expression in these variables using only power
	 *            operators to natural number exponents, +, -, and *, and
	 *            constants.
	 * @param epsilon
	 *            an upper bound on the probability of error
	 * @return if {@code true}, the given polynomial is probably zero, with the
	 *         probability of error at most {@code epsilon}; if {@code false},
	 *         the polynomial is not identically zero
	 */
	private boolean is0WithProbability(Polynomial poly,
			IntegerNumber totalDegree, Set<Primitive> vars,
			RationalNumber epsilon) {
		FastEvaluator fe = new FastEvaluator(random, info.numberFactory, poly,
				totalDegree);

		if (debug)
			fe.printTreeInformation(info.out);
		return fe.isZero(epsilon);
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
					context.addSub(monic, info.universe.number(value),
							dirtySet);
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

			if (pair == null)
				throw new InconsistentContextException();
			// check again for range: is there a better place to do this?
			if (!context.computeRange(pair.left).containsNumber(pair.right))
				throw new InconsistentContextException();
			context.addSub(pair.left, info.universe.number(pair.right),
					dirtySet);
		} else {
			context.addSub(monic, info.universe.number(value), dirtySet);
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
		Range range = context.computeRange(monic);

		if (!range.containsNumber(value))
			throw new InconsistentContextException();
		if (primitive instanceof Polynomial)
			extractEQ0Poly((Polynomial) primitive, monic, value);
		else {
			context.addSub(monic, info.universe.number(value), dirtySet);
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

			if (pair != null)
				context.restrictRange(pair.left,
						rf.complement(rf.singletonSet(pair.right)), dirtySet);
		} else {
			context.addSub(info.universe.equals(arg0, arg1), info.falseExpr,
					dirtySet);
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

		Range oldRange = context.computeRange(monic);
		Range newRange = rf.intersect(oldRange, range);

		if (!oldRange.equals(newRange))
			context.restrictRange(monic, newRange, dirtySet);
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

		BooleanExpression isNonZero = (BooleanExpression) context
				.simplify(idf.isNonZero(coefficient));

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
	 * TODO: This requires simplify.
	 * 
	 * 
	 * If the boolean expression has the form
	 * 
	 * <pre>
	 * forall int i in [0,n-1] . e[i]=f
	 * </pre>
	 * 
	 * where n is an integer expression not involving i, e has type "array of
	 * length n of T" for some type T, and f is some expression, then return a
	 * structure in which the array field is e and the lambda field is the
	 * expression <code>arraylambda i . f</code>.
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
			context.addSub(defn.array, defn.lambda, dirtySet);
		} else {
			context.addSub(forallExpr, info.trueExpr, dirtySet);
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
		context.addSub(existsExpr, info.trueExpr, dirtySet);
	}

}
