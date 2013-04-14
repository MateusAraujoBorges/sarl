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
package edu.udel.cis.vsl.sarl.reason.common;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.TheoremProverException;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.prove.Prove;
import edu.udel.cis.vsl.sarl.simplify.IF.Simplifier;
import edu.udel.cis.vsl.sarl.universe.IF.ExtendedUniverse;

// reasoner hierarchy. no real need for simple prover

// Universe needs a ReasonerFactory.

// ReasonerFactory simpleReasonerFactory(SimplifierFactory s);
// ReasonerFactory commonReasonerFactory(SimplifierFactory s,
// TheoremProverFactory p);

// TheoremProverFactory cvc3TheoremProverFactory();
// etc. for other provers

// in class Ideal:
// SimplifierFactory newIdealSimplifierFactory();

// SimplifierFactory methods:
// newSimplifier(context);
// TheoremProverFactory methods:
// newProver(context);

public class SimpleReasoner implements Reasoner {

	private Simplifier simplifier;

	private Map<BooleanExpression, ValidityResult> validityCache = new HashMap<BooleanExpression, ValidityResult>();

	public SimpleReasoner(Simplifier simplifier) {
		this.simplifier = simplifier;
	}

	@Override
	public ExtendedUniverse universe() {
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
		return simplifier.apply(expression);
	}

	@Override
	public ValidityResult valid(BooleanExpression predicate) {
		ValidityResult result = validityCache.get(predicate);

		universe().incrementProverValidCount();
		if (result == null) {
			BooleanExpression simple = (BooleanExpression) simplifier
					.apply(predicate);
			Boolean concrete = universe().extractBoolean(simple);

			if (concrete == null)
				result = Prove.RESULT_MAYBE;
			else if (concrete)
				result = Prove.RESULT_YES;
			else
				result = Prove.RESULT_NO;
			validityCache.put(predicate, result);
		}
		return result;
	}

	@Override
	public ValidityResult validOrModel(BooleanExpression predicate) {
		throw new TheoremProverException(
				"SimpleIdealProver cannot be used to find models");
	}

	@Override
	public void setOutput(PrintStream out) {
	}

	@Override
	public Map<SymbolicConstant, SymbolicExpression> substitutionMap() {
		return simplifier.substitutionMap();
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
