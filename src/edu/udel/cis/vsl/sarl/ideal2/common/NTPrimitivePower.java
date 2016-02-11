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

import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicMap;
import edu.udel.cis.vsl.sarl.ideal2.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal2.IF.Ideal2Factory;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal2.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal2.IF.PrimitivePower;

/**
 * A non-trivial primitive power represents a Primitive expression raised to
 * some concrete integer exponent; the exponent is at least 2.
 * 
 * @author siegel
 * 
 */
public class NTPrimitivePower extends IdealExpression
		implements PrimitivePower {

	/**
	 * Cached result of {@link #expand(Ideal2Factory)}.
	 */
	private SymbolicMap<Monic, Monomial> expansion = null;

	protected NTPrimitivePower(Primitive primitive, IntObject exponent) {
		super(SymbolicOperator.POWER, primitive.type(), primitive, exponent);
		assert exponent.getInt() >= 2;
	}

	/**
	 * Creates a primitive which is any symbol or number raised to the 1st power
	 * 
	 * @return - a primitive such as 'x' or 'y'
	 */
	public NumericPrimitive primitive() {
		return (NumericPrimitive) argument(0);
	}

	@Override
	public SymbolicMap<Primitive, PrimitivePower> monicFactors(
			Ideal2Factory factory) {
		return factory.primitiveSingletonMap(primitive(),
				(PrimitivePower) this);
	}

	@Override
	public Constant monomialConstant(Ideal2Factory factory) {
		return factory.one(type());
	}

	@Override
	public Monic monic(Ideal2Factory factory) {
		return this;
	}

	@Override
	public IntObject primitivePowerExponent(Ideal2Factory factory) {
		return exponent();
	}

	/**
	 * The number that is raised as a power to any particular expression or any
	 * constants This exponent number is of type intObject.
	 * 
	 * @return - the value by multiplying the expression or any constant, number
	 *         of times equal to the integer that is raised to the power.
	 */
	public IntObject exponent() {
		return (IntObject) argument(1);
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
	public NumericPrimitive primitive(Ideal2Factory factory) {
		return (NumericPrimitive) argument(0);
	}

	@Override
	public boolean isTrivialMonic() {
		return false;
	}

	@Override
	public SymbolicMap<Monic, Monomial> expand(Ideal2Factory factory) {
		if (expansion == null) {
			NumericPrimitive primitive = primitive();
			SymbolicMap<Monic, Monomial> expandedPrimitive = primitive
					.expand(factory);

			if (primitive.equals(expandedPrimitive))
				expansion = factory.monicSingletonMap(this, this);
			else
				expansion = factory.powerTermMap(type(), expandedPrimitive,
						exponent());
		}
		return expansion;
	}

	@Override
	public String toString() {
		return primitive().atomString() + "^" + exponent();
	}

	@Override
	public int monomialDegree() {
		return exponent().getInt();
	}

	@Override
	public IdealKind idealKind() {
		return IdealKind.NTPrimitivePower;
	}

	@Override
	public SymbolicMap<Monic, Monomial> termMap(Ideal2Factory factory) {
		return factory.monicSingletonMap(this, this);
	}

}
