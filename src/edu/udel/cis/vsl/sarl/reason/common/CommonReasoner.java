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
package edu.udel.cis.vsl.sarl.reason.common;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.ModelResult;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.prove.IF.Prove;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProver;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProverFactory;
import edu.udel.cis.vsl.sarl.simplify.IF.Simplifier;
import edu.udel.cis.vsl.sarl.simplify.IF.SimplifierFactory;

/**
 * An implementation of Reasoner based on a given Simplifier and
 * TheoremProverFactory.
 * 
 * @author Stephen F. Siegel
 */
public class CommonReasoner implements Reasoner {

	private TheoremProver prover = null;

	private Simplifier simplifier;

	private TheoremProverFactory factory;

	// TODO: init me...
	private SimplifierFactory simplifierFactory;

	private Map<BooleanExpression, ValidityResult> validityCache = new HashMap<>();

	public CommonReasoner(Simplifier simplifier, TheoremProverFactory factory) {
		this.simplifier = simplifier;
		this.factory = factory;
	}

	public PreUniverse universe() {
		return simplifier.universe();
	}

	@Override
	public BooleanExpression getReducedContext() {
		return simplifier.getReducedContext();
	}

	@Override
	public BooleanExpression getFullContext() {
		return simplifier.getFullContext();
	}

	@Override
	public Interval assumptionAsInterval(SymbolicConstant symbolicConstant) {
		return simplifier.assumptionAsInterval(symbolicConstant);
	}

	@Override
	public SymbolicExpression simplify(SymbolicExpression expression) {
		if (expression == null)
			throw new SARLException("Argument to Reasoner.simplify is null.");
		return simplifier.apply(expression);
	}

	@Override
	public BooleanExpression simplify(BooleanExpression expression) {
		return (BooleanExpression) simplify((SymbolicExpression) expression);
	}

	@Override
	public NumericExpression simplify(NumericExpression expression) {
		return (NumericExpression) simplify((SymbolicExpression) expression);
	}

	@Override
	public ValidityResult valid(BooleanExpression predicate) {
		boolean showQuery = universe().getShowQueries();

		if (showQuery) {
			PrintStream out = universe().getOutputStream();
			int id = universe().numValidCalls();

			out.println("Query " + id + " assumption: "
					+ simplifier.getFullContext());
			out.println("Query " + id + " predicate:  " + predicate);
		}
		if (predicate == null)
			throw new SARLException("Argument to Reasoner.valid is null.");
		else {
			ValidityResult result = null;
			BooleanExpression fullContext = getFullContext();

			universe().incrementValidCount();
			if (fullContext.isTrue()) {
				ResultType resultType = predicate.getValidity();

				if (resultType != null) {
					switch (resultType) {
					case MAYBE:
						result = Prove.RESULT_MAYBE;
						break;
					case NO:
						result = Prove.RESULT_NO;
						break;
					case YES:
						result = Prove.RESULT_YES;
						break;
					default:
						throw new SARLInternalException("unrechable");
					}
				}
			}
			if (result == null) {
				BooleanExpression simplifiedPredicate = (BooleanExpression) simplifier
						.apply(predicate);

				if (simplifiedPredicate.isTrue())
					result = Prove.RESULT_YES;
				else if (simplifiedPredicate.isFalse())
					result = Prove.RESULT_NO;
				else {
					result = validityCache.get(simplifiedPredicate);
					if (result == null) {
						if (prover == null)
							prover = factory.newProver(getReducedContext());
						result = prover.valid(simplifiedPredicate);
						validityCache.put(predicate, result);
					}
				}
			}
			if (showQuery) {
				int id = universe().numValidCalls() - 1;
				PrintStream out = universe().getOutputStream();

				out.println("Query " + id + " result:     " + result);
			}
			if (fullContext.isTrue()) {
				predicate.setValidity(result.getResultType());
			}
			return result;
		}
	}

	@Override
	public ValidityResult validOrModel(BooleanExpression predicate) {
		BooleanExpression simplifiedPredicate = (BooleanExpression) simplifier
				.apply(predicate);
		ValidityResult result;

		universe().incrementValidCount();
		if (simplifiedPredicate.isTrue())
			result = Prove.RESULT_YES;
		else {
			result = validityCache.get(simplifiedPredicate);
			if (result != null && result instanceof ModelResult)
				return result;
			if (prover == null)
				prover = factory.newProver(getReducedContext());
			result = prover.validOrModel(simplifiedPredicate);
			validityCache.put(predicate, result);
		}
		return result;
	}

	@Override
	public Map<SymbolicConstant, SymbolicExpression> constantSubstitutionMap() {
		return simplifier.constantSubstitutionMap();
	}

	@Override
	public boolean isValid(BooleanExpression predicate) {
		return valid(predicate).getResultType() == ResultType.YES;
	}

	@Override
	public Number extractNumber(NumericExpression expression) {
		NumericExpression simple = (NumericExpression) simplify(expression);

		return universe().extractNumber(simple);
	}

	@Override
	public Interval intervalApproximation(NumericExpression expr) {
		return simplifier.intervalApproximation(expr);
	}

	@Override
	public ValidityResult validWTDeduction(BooleanExpression predicate) {
		return valid(predicate);
	}

	@Override
	public Map<SymbolicExpression, SymbolicExpression> substitutionMap(
			boolean selfUpdate) {
		return simplifier.substitutionMap(selfUpdate);
	}

	@Override
	public Map<SymbolicExpression, SymbolicExpression> substitutionMap(
			SymbolicConstant expectedKey, boolean selfUpdate) {
		return simplifier.substitutionMap(expectedKey, selfUpdate);
	}

	/**
	 * Attempts to prove a uniform "Big-O" claim. The claim has the following
	 * form:
	 * 
	 * <pre>
	 * lhs = O(h1^n1) + ... + O(hk^nk)
	 * </pre>
	 * 
	 * Here, lhs or "left hand side expression" is an expression of real type.
	 * The h1, ..., hk or "limit variables" are symbolic constants of real type,
	 * the variables that are tending towards 0. The n1, ..., nk the
	 * corresponding "orders" of the limit variables; they are are concrete
	 * nonnegative integers.
	 * 
	 * The lhs may involve the hi and also some integer-type symbolic constants
	 * i1,...,im called the "index variables". The ij are assumed to satisfy
	 * some "index constraint".
	 * 
	 * The real intervals defined a closed rectangular interval in R^m that
	 * contain the "grid points". The grid points are not explicit here, but
	 * they are functions of the index variables.
	 * 
	 * @param realIntervals
	 *            intervals bounding the grid, an array of length m
	 * @param indexVars
	 *            the index variables, an array of length m of symbolic
	 *            constants of integer type
	 * @param indexConstraint
	 *            the constraint on the index variables
	 * @param lhs
	 *            the left hand side expression, an expression of real type
	 *            involving any or all of the symbolic constants mentioned, as
	 *            well as others
	 * @param limitVars
	 *            the limit variables; an array of length k
	 * @param orders
	 *            the orders of the limit variables; the length must be the same
	 *            as the length of <code>limitVars</code> (k)
	 * @return <code>true</code> if the O-claim can be proved. A
	 *         <code>false</code> result does not mean the O-claim is false, it
	 *         just means it could not be proved
	 */
	public boolean validUniform(Interval[] realIntervals,
			SymbolicConstant[] indexVars, BooleanExpression indexConstraint,
			NumericExpression lhs, SymbolicConstant[] limitVars, int[] orders) {
		// strategy:
		// create new context and add index constraint to the assumption.
		// look for function calls to an abstract function from R^m to R.
		// Within such a function call, look for an index i such that argument
		// i has the form term+hi. Taylor expand that call around parameter i.
		// First check that all parameters are in the bounding interval.

		// rename the indexConstraint and the limitVars if they conflict with
		// any
		// frees.

		BooleanExpression oldContext = simplifier.getFullContext();
		BooleanExpression newContext = simplifier.universe().and(oldContext,
				indexConstraint);

		// would like whole new reasoner for the newContext.
		// Simplifier newSimplifier =
		// simplifierFactory.newSimplifier(newContext);

		// need general expression substituter interface
		// method:
		// SymbolicObject replace(SymbolicObject o)

		// need to extend ExpressionSubstituter

		// need to use Ideal factory ?

		return false;
	}
}
