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
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.prove.IF.Prove;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProver;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProverFactory;
import edu.udel.cis.vsl.sarl.reason.IF.ReasonerFactory;
import edu.udel.cis.vsl.sarl.simplify.IF.Simplifier;

/**
 * A very basic implementation of {@link Reasoner} based on a given
 * {@link Simplifier} and {@link TheoremProverFactory}. The context and other
 * information is already in the {@link Simplifier} that is created before this
 * {@link Reasoner} is created and becomes a field in this {@link Reasoner}. The
 * validity reasoning basically works by attempting to simplify an expression to
 * "true" or "false" and if that doesn't work then applying the prover.
 * 
 * @author Stephen F. Siegel
 */
public class CommonReasoner implements Reasoner {

	/**
	 * The factory that was used to produce this {@link CommonReasoner}. It may
	 * be used again to produce new instances of {@link CommonReasoner} with
	 * different contexts if the need arises.
	 */
	private ReasonerFactory reasonerFactory;

	/**
	 * The theorem prover is created only if needed and once created will be
	 * re-used for subsequence queries. It is stored in this variable.
	 */
	private TheoremProver prover = null;

	/**
	 * The simplifier, which must be non-<code>null</code> and is set at
	 * initialization.
	 */
	private Simplifier simplifier;

	/**
	 * The cached results of previous validity queries, i.e., calls to method
	 * {@link #valid(BooleanExpression)},
	 * {@link #validOrModel(BooleanExpression)}.
	 */
	private Map<BooleanExpression, ValidityResult> validityCache = new HashMap<>();

	/**
	 * @param reasonerFactory
	 *            the factory that created this {@link Reasoner}, and can be
	 *            used to create more {@link Reasoner}s if they are needed by
	 *            this one
	 * @param simplifier
	 *            a {@link Simplifier} formed from the context that undergirds
	 *            this {@link Reasoner}; can be used by this {@link Reasoner}
	 *            for simplifying expressions
	 * @param factory
	 *            a factory for producing new {@link TheoremProver}s
	 */
	public CommonReasoner(ReasonerFactory reasonerFactory,
			Simplifier simplifier) {
		this.reasonerFactory = reasonerFactory;
		this.simplifier = simplifier;
	}

	/**
	 * Returns the symbolic universe used by this {@link Reasoner}.
	 * 
	 * @return the symbolic universe
	 */
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
							prover = reasonerFactory.getTheoremProverFactory()
									.newProver(getReducedContext());
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
				prover = reasonerFactory.getTheoremProverFactory()
						.newProver(getReducedContext());
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
	// TODO: get rid of lowerBounds and upperBounds.
	// instead, when you encounter a function symbol used in an application
	// in lhs, look in path condition to find out if it is DIFFERENTIABLE,
	// get the intervals from there, and the degree.
	public boolean checkBigOClaim(SymbolicConstant[] indexVars,
			BooleanExpression indexConstraint, NumericExpression lhs,
			NumericSymbolicConstant[] limitVars, int[] orders) {
		// strategy: create new context and add index constraint to the
		// assumption. Perform Taylor expansions where appropriate.
		// TODO: rename the indexConstraint and the limitVars if they conflict
		// with any free variables.
		PreUniverse universe = universe();
		BooleanExpression oldContext = simplifier.getFullContext();
		BooleanExpression newContext = universe.and(oldContext,
				indexConstraint);
		Reasoner newReasoner = reasonerFactory.getReasoner(newContext);
		UnaryOperator<SymbolicExpression> taylorSubstituter = new TaylorSubstituter(
				universe, universe.objectFactory(), universe.typeFactory(),
				newReasoner, limitVars, orders);
		NumericExpression newLhs = (NumericExpression) taylorSubstituter
				.apply(lhs);

		return newReasoner
				.isValid(universe.equals(newLhs, universe.zeroReal()));
	}
}
