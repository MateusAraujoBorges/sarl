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

import edu.udel.cis.vsl.sarl.ideal2.IF.Ideal2Factory;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal2.IF.RationalExpression;

/**
 * A nontrivial rational expression. It consists of a numerator and denominator,
 * both factored polynomials.
 * 
 * @author siegel
 * 
 */
public class NTRationalExpression extends IdealExpression
		implements RationalExpression {

	protected NTRationalExpression(Monomial numerator, Monomial denominator) {
		super(SymbolicOperator.DIVIDE, numerator.type(), numerator,
				denominator);
		assert !denominator.isOne();
		assert !denominator.isZero();
		assert !numerator.isZero();
		assert !numerator.equals(denominator);
	}

	public Monomial numerator(Ideal2Factory factory) {
		return (Monomial) argument(0);
	}

	public Monomial numerator() {
		return (Monomial) argument(0);
	}

	public Monomial denominator(Ideal2Factory factory) {
		return (Monomial) argument(1);
	}

	public Monomial denominator() {
		return (Monomial) argument(1);
	}

	@Override
	public IdealKind idealKind() {
		return IdealKind.NTRationalExpression;
	}

}
