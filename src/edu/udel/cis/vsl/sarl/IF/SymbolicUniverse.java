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
package edu.udel.cis.vsl.sarl.IF;

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.prove.IF.ProverFunctionInterpretation;

/**
 * <p>
 * A symbolic universe is used for the creation and manipulation of
 * {@link SymbolicObject}s. The symbolic objects created by this universe are
 * said to belong to this universe. Every symbolic object belongs to one
 * universe, though a reference to the universe is not necessarily stored in the
 * object.
 * </p>
 * 
 * <p>
 * {@SymbolicExpression}s are one kind of symbolic object. Other symbolic
 * objects include {@link SymbolicCollection}s (such as sequences, sets, and
 * maps), {@link SymbolicType}s, and various concrete {@link SymbolicObject}s.
 * </p>
 * <p>
 * {@link SymbolicObject}s implement the Immutable Pattern: all symbolic objects
 * are immutable, i.e., they cannot be modified after they are created.
 * </p>
 * 
 * @author siegel
 */
public interface SymbolicUniverse extends CoreUniverse {

	// ************************************************************************

	// Methods in SymbolicUniverse not in CoreUniverse.
	// These generally require use of theorem provers/simplifiers

	/**
	 * Returns a {@link Reasoner} for the given context. A {@link Reasoner}
	 * provides simplification and reasoning services. The context is the
	 * boolean expression assumed to hold by the reasoner. The Reasoner can be
	 * used to determine if a boolean predicate is valid; it may use an external
	 * theorem prover to assist in this task.
	 * 
	 * @param context
	 *            the boolean expression assumed to hold by the {@link Reasoner}
	 * @return a {@link Reasoner} with the given context
	 */
	Reasoner reasoner(BooleanExpression context);

	/**
	 * Attempts to extract a concrete numeric value from the given expression,
	 * using the assumption if necessary to simplify the expression. For
	 * example, if the assumption is "N=5" and the expression is "N", this
	 * method will probably return the number 5. If it cannot obtain a concrete
	 * value for whatever reason, it will return null.
	 * 
	 * @param assumption
	 *            a boolean expression that is assumed to hold
	 * @param expression
	 *            a symbolic expression of numeric type
	 * @return a concrete Number or null
	 */
	Number extractNumber(BooleanExpression assumption,
			NumericExpression expression);

	/**
	 * Same as {@link #reasoner(BooleanExpression, boolean)} but only Why3 prove
	 * platform will be used if it is installed. If Why3 is not installed, this
	 * function is equivalent to {@link #reasoner(BooleanExpression, boolean)}
	 * 
	 * @param context
	 *            a non-<code>null</code> boolean expression to be used as the
	 *            context for the {@link Reasoner}
	 * @param proverPredicates
	 *            {@link ProverFunctionInterpretation}s which factor out the
	 *            common parts of boolean expressions from complex prover
	 *            contexts and queries
	 * @return a {@link Reasoner} based on the given <code>context</code>
	 */
	Reasoner why3Reasoner(BooleanExpression context,
			ProverFunctionInterpretation[] proverPredicates);
}
