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

import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.object.NumberObject;
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
 * Empty monic: equivalent to 1.
 * 
 * @author siegel
 * 
 */
public class One extends IdealExpression implements Constant, Monic {

	private SymbolicMap<Monic, Monomial> expansion = null;

	protected One(SymbolicType type, NumberObject oneObj) {
		super(SymbolicOperator.CONCRETE, type, oneObj);
		assert oneObj.isOne();
	}

	@Override
	public Constant monomialConstant(Ideal2Factory factory) {
		return this;
	}

	@Override
	public Monic monic(Ideal2Factory factory) {
		return this;
	}

	@Override
	public Monomial numerator(Ideal2Factory factory) {
		return this;
	}

	@Override
	public Monomial denominator(Ideal2Factory factory) {
		return this;
	}

	@Override
	public SymbolicMap<Primitive, PrimitivePower> monicFactors(
			Ideal2Factory factory) {
		return factory.emptyPrimitiveMap();
	}

	@Override
	public boolean isTrivialMonic() {
		return true;
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
	public boolean isOne() {
		return true;
	}

	@Override
	public String toString() {
		return "1";
	}

	@Override
	public NumberObject value() {
		return (NumberObject) argument(0);
	}

	@Override
	public Number number() {
		return value().getNumber();
	}

	@Override
	public int monomialDegree() {
		return 0;
	}

	@Override
	public SymbolicMap<Monic, Monomial> termMap(Ideal2Factory factory) {
		return factory.monicSingletonMap(this, this);
	}

	@Override
	public int totalDegree() {
		return 0;
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
	}

}
