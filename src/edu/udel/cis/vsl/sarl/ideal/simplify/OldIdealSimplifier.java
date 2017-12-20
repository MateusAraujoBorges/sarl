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

import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject.SymbolicObjectKind;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.simplify.IF.Simplifier;
import edu.udel.cis.vsl.sarl.simplify.common.CommonSimplifier;

/**
 * <p>
 * An implementation of {@link Simplifier} for the "ideal" numeric factory
 * {@link IdealFactory}.
 * </p>
 *
 */
public class OldIdealSimplifier extends CommonSimplifier {

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
	 * Abstract representation of the {@link #fullContext}.
	 */
	private OldContext theContext;

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
	public OldIdealSimplifier(SimplifierInfo info, BooleanExpression assumption) {
		super(info.universe);
		this.info = info;
		this.boundCleaner = universe.newMinimalBoundCleaner();
		// rename bound variables so every variable has a unique name...
		assumption = (BooleanExpression) boundCleaner.apply(assumption);
		this.theContext = new ContextBuilder(info, assumption).getContext();
	}

	@Override
	protected OldIdealSimplifierWorker newWorker() {
		return new OldIdealSimplifierWorker(info, theContext);
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
		return theContext.assumptionAsInterval(symbolicConstant);
	}

	@Override
	public Map<SymbolicConstant, SymbolicExpression> constantSubstitutionMap() {
		return theContext.getSolvedVariables();
	}

	@Override
	public BooleanExpression getReducedContext() {
		return theContext.getReducedAssumption();
	}

	@Override
	public BooleanExpression getFullContext() {
		return theContext.getFullAssumption();
	}

	@Override
	public Interval intervalApproximation(NumericExpression expr) {
		return newWorker().intervalApproximation(expr);
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
		return theContext.findDifferentiableClaim(function);
	}
}