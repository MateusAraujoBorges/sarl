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

import edu.udel.cis.vsl.sarl.collections.IF.SymbolicMap;
import edu.udel.cis.vsl.sarl.ideal2.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal2.IF.Ideal2Factory;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal2.IF.Polynomial;

/**
 * A non-trivial monomial is the product of a constant and a monic. The constant
 * must not be 0 or 1 and the monic must not be empty.
 * 
 * @author siegel
 * 
 */
public class NTMonomial extends IdealExpression implements Monomial {

	protected NTMonomial(Constant constant, Monic monic) {
		super(SymbolicOperator.MULTIPLY, constant.type(), constant, monic);
		assert !constant.isZero();
		assert !constant.isOne();
		assert !monic.isOne();
	}

	@Override
	public Monic monic(Ideal2Factory factory) {
		return (Monic) argument(1);
	}

	/**
	 * Creates a Monic expression
	 * 
	 * @return a Monic
	 */
	public Monic monic() {
		return (Monic) argument(1);
	}

	@Override
	public Constant monomialConstant(Ideal2Factory factory) {
		return (Constant) argument(0);
	}

	public Constant monomialConstant() {
		return (Constant) argument(0);
	}

	@Override
	public Monomial numerator(Ideal2Factory factory) {
		return this;
	}

	@Override
	public Monomial denominator(Ideal2Factory factory) {
		return factory.one(type());
	}

	@Override
	public SymbolicMap<Monic, Monomial> expand(Ideal2Factory factory) {
		Monic monic = this.monic();
		SymbolicMap<Monic, Monomial> expandedMonic = monic.expand(factory);

		if (monic == expandedMonic)
			return factory.monicSingletonMap(monic, this);
		return factory.multiplyConstantTermMap(monomialConstant(),
				expandedMonic);
	}

	@Override
	public int monomialDegree() {
		return monic().monomialDegree();
	}

	@Override
	public IdealKind idealKind() {
		return IdealKind.NTMonomial;
	}

	@Override
	public SymbolicMap<Monic, Monomial> termMap(Ideal2Factory factory) {
		Monic monic = monic();

		if (monic instanceof Polynomial) {
			return factory.multiplyConstantTermMap((Constant) argument(0),
					monic.termMap(factory));
		}
		return factory.monicSingletonMap(monic, this);
	}

}
