/*******************************************************************************
 * Copyright (c) 2013 Stephen F. Siegel, University of Delaware.
 * 
 * This file is part of SARL.
 * 
 * SARL is free software: you can redistribute it and/or modify it under
 * the terms of the GNU Lesser General Public License as published by the
 * Free Software Foundation, either version 3 of the License, or (at your
 * option) any later version.
 * 
 * SARL is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
 * License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public
 * License along with SARL. If not, see <http://www.gnu.org/licenses/>.
 ******************************************************************************/
package edu.udel.cis.vsl.sarl.prove.ideal;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.Simplifier;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.prove.TernaryResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.prove.TheoremProver;
import edu.udel.cis.vsl.sarl.IF.prove.TheoremProverException;

/**
 * A very simple prover. It works by just simplifying the predicate based on the
 * assumption. If the result of simplification is true, return YES, if result is
 * false, return no, if it is any other expression, return MAYBE. Results are
 * cached.
 */
public class SimpleIdealProver implements TheoremProver {

	private Map<SymbolicQuery, ResultType> queryCache;

	private SymbolicUniverse universe;

	private int numValidCalls = 0;

	SimpleIdealProver(SymbolicUniverse universe) {
		this.universe = universe;
		queryCache = new HashMap<SymbolicQuery, ResultType>();
	}

	@Override
	public void close() {

	}

	@Override
	public void reset() {
		queryCache = new HashMap<SymbolicQuery, ResultType>();
	}

	@Override
	public SymbolicUniverse universe() {
		return universe;
	}

	@Override
	public ResultType valid(BooleanExpression assumption,
			BooleanExpression predicate) {
		SymbolicQuery query = new SymbolicQuery(assumption, predicate);
		ResultType result = queryCache.get(query);

		numValidCalls++;
		if (result == null) {
			Simplifier simplifier = universe.simplifier(assumption);
			BooleanExpression simple = (BooleanExpression) simplifier
					.apply(predicate);
			Boolean concrete = universe.extractBoolean(simple);

			if (concrete == null)
				result = ResultType.MAYBE;
			else if (concrete)
				result = ResultType.YES;
			else
				result = ResultType.NO;
			queryCache.put(query, result);
		}
		return result;
	}

	/**
	 * Used to find a model for a path condition. Cannot be done using the
	 * simple ideal prover.
	 * 
	 * @throws TheoremProverException
	 */
	@Override
	public Map<SymbolicConstant, SymbolicExpression> findModel(
			BooleanExpression context) throws TheoremProverException {
		throw new TheoremProverException(
				"Concretization cannot be done using the simple ideal prover.");
	}

	@Override
	public int numInternalValidCalls() {
		return 0;
	}

	@Override
	public int numValidCalls() {
		return numValidCalls;
	}

	@Override
	public void setOutput(PrintStream out) {
	}

	// TODO: do some more intelligent things:
	// 1. separate variables. Consider set of symbolic constants that occur
	// in predicate. Make undirected graph in which nodes are all symbolic
	// constants and there is an edge (x,y) if there is a clause in the and
	// expression which is the assumption such that both x and y occur in the
	// clause. Find all nodes/edges reachable from the symbolic constants
	// occurring in the predicate. These are the only ones that need to
	// considered in the proof.
	//
	// Problem: what about:

	// pc: 0<=X1<=10 && a[X1-1]<5.0
	// query X1>0 ?
	// for some reason, can eliminate the constraint involving a as it imposes
	// no constraint on X1 (as long as it is satisfiable---but our contract
	// says result is undefined if pc not satisfiable)

	// pc: 0<=X1<=10 && X2<=X1
	// query X1>0 ? leave these to CVC3

}
