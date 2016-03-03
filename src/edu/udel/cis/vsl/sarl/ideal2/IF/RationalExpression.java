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
package edu.udel.cis.vsl.sarl.ideal2.IF;

import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;

/**
 * A {@link RationalExpression} is the quotient of two {@link Monomial}s of real
 * type. It also has real type.
 * 
 * @author siegel
 */
public interface RationalExpression extends NumericExpression {

	/**
	 * Returns the numerator of this rational expression
	 * 
	 * @param factory
	 *            the ideal factory responsible for this expression
	 * 
	 * @return the numerator of this rational expression
	 */
	Monomial numerator(Ideal2Factory factory);

	/**
	 * Returns the denominator of this rational expression.
	 * 
	 * @param factory
	 *            the ideal factory responsible for this expression
	 * 
	 * @return the denominator of this rational expression
	 */
	Monomial denominator(Ideal2Factory factory);
}
