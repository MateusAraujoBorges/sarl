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
package edu.udel.cis.vsl.sarl.ideal2.common;

import java.util.Collection;

import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.common.CommonSymbolicExpression;

/**
 * <p>
 * The base class for all ideal expressions.
 * </p>
 * 
 * <p>
 * This class extends {@link CommonSymbolicExpression}, which is the root of the
 * symbolic expression hierarchy.
 * </p>
 * 
 * TODO: currently this class does not provide any services beyond those already
 * provided by {@link CommonSymbolicExpression}. Consider getting rid of it.
 */
public abstract class IdealExpression extends CommonSymbolicExpression
		implements NumericExpression {

	protected IdealExpression(SymbolicOperator operator, SymbolicType type,
			SymbolicObject[] arguments) {
		super(operator, type, arguments);
	}

	protected IdealExpression(SymbolicOperator operator, SymbolicType type,
			Collection<SymbolicObject> arguments) {
		super(operator, type, arguments);
	}

	protected IdealExpression(SymbolicOperator kind, SymbolicType type,
			SymbolicObject arg0) {
		super(kind, type, arg0);
	}

	protected IdealExpression(SymbolicOperator kind, SymbolicType type,
			SymbolicObject arg0, SymbolicObject arg1) {
		super(kind, type, arg0, arg1);
	}

	protected IdealExpression(SymbolicOperator kind, SymbolicType type,
			SymbolicObject arg0, SymbolicObject arg1, SymbolicObject arg2) {
		super(kind, type, arg0, arg1, arg2);
	}

}
