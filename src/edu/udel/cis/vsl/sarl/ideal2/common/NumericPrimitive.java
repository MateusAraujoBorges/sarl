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

import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicMap;
import edu.udel.cis.vsl.sarl.ideal2.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal2.IF.Ideal2Factory;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal2.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal2.IF.PrimitivePower;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;

/**
 * A numeric primitive expression---one which is to be considered as an atomic
 * "variable" when used in other numeric expressions. Other classes may want to
 * extend this. Examples: symbolic constant, array read, tuple read, function
 * application, when those have numeric type.
 * 
 * @author siegel
 */
public class NumericPrimitive extends IdealExpression implements Primitive {

	/**
	 * Singleton map from this to this, cached.
	 */
	private SymbolicMap<Primitive, PrimitivePower> monicFactors = null;

	/**
	 * Cached expansion.
	 */
	private SymbolicMap<Monic, Monomial> expansion = null;

	public NumericPrimitive(SymbolicOperator operator, SymbolicType type,
			SymbolicObject[] arguments) {
		super(operator, type, arguments);
	}

	public NumericPrimitive(SymbolicOperator operator, SymbolicType type,
			Collection<SymbolicObject> arguments) {
		super(operator, type, arguments);
	}

	public NumericPrimitive(SymbolicOperator operator, SymbolicType type,
			SymbolicObject arg0) {
		super(operator, type, arg0);
	}

	public NumericPrimitive(SymbolicOperator operator, SymbolicType type,
			SymbolicObject arg0, SymbolicObject arg1) {
		super(operator, type, arg0, arg1);
	}

	public NumericPrimitive(SymbolicOperator operator, SymbolicType type,
			SymbolicObject arg0, SymbolicObject arg1, SymbolicObject arg2) {
		super(operator, type, arg0, arg1, arg2);
	}

	@Override
	public SymbolicMap<Primitive, PrimitivePower> monicFactors(
			Ideal2Factory factory) {
		if (monicFactors == null)
			monicFactors = factory.primitiveSingletonMap(this,
					(PrimitivePower) this);
		return monicFactors;
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
	public NumericPrimitive primitive(Ideal2Factory factory) {
		return this;
	}

	@Override
	public IntObject primitivePowerExponent(Ideal2Factory factory) {
		return factory.oneIntObject();
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
	public boolean isTrivialMonic() {
		return false;
	}

	@Override
	public int monomialDegree() {
		return 1;
	}

	@Override
	public SymbolicMap<Monic, Monomial> expand(Ideal2Factory factory) {
		if (expansion == null) {
			expansion = factory.monicSingletonMap(this, this);
			if (isCanonic())
				expansion = factory.objectFactory().canonic(expansion);
		}
		return expansion;
	}

	@Override
	public SymbolicMap<Monic, Monomial> termMap(Ideal2Factory factory) {
		return factory.monicSingletonMap(this, this);
	}

	@Override
	public int totalDegree() {
		return 1;
	}

	@Override
	public boolean hasNontrivialExpansion(Ideal2Factory factory) {
		return false;
	}

	@Override
	public void canonizeChildren(ObjectFactory of) {
		super.canonizeChildren(of);
		if (expansion != null && !expansion.isCanonic())
			expansion = of.canonic(expansion);
		if (monicFactors != null && !monicFactors.isCanonic())
			monicFactors = of.canonic(monicFactors);
	}

}
