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
package edu.udel.cis.vsl.sarl.ideal.common;

import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.common.HomogeneousExpression;
import edu.udel.cis.vsl.sarl.ideal.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal.IF.Ideal2Factory;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal.IF.PrimitivePower;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;

/**
 * A numeric primitive expression---one which is to be considered as an atomic
 * "variable" when used in other numeric expressions. Other classes may want to
 * extend this. Examples: symbolic constant, array read, tuple read, function
 * application, when those have numeric type.
 * 
 * @author siegel
 */
public class NumericPrimitive extends HomogeneousExpression<SymbolicObject>
		implements Primitive {

	/**
	 * Cache of value returned by {@link #monicFactors(Ideal2Factory)}.
	 * Singleton map from this to this, cached.
	 */
	private PrimitivePower[] monicFactors = null;

	/**
	 * Cache of value returned by {@link #termMap(Ideal2Factory)}.
	 */
	private Monomial[] termMap = null;

	public NumericPrimitive(SymbolicOperator operator, SymbolicType type,
			SymbolicObject... arguments) {
		super(operator, type, arguments);
	}

	@Override
	public PrimitivePower[] monicFactors(Ideal2Factory factory) {
		if (monicFactors == null) {
			monicFactors = new PrimitivePower[] { this };
			if (isCanonic())
				factory.objectFactory().canonize(monicFactors);
		}
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
	public Primitive primitive(Ideal2Factory factory) {
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
	public Monomial[] termMap(Ideal2Factory factory) {
		if (termMap == null) {
			termMap = new Monomial[] { this };
			if (isCanonic())
				factory.objectFactory().canonize(termMap);
		}
		return termMap;
	}

	@Override
	public Monomial[] expand(Ideal2Factory factory) {
		return termMap(factory);
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
		if (termMap != null)
			of.canonize(termMap);
		if (monicFactors != null)
			of.canonize(monicFactors);
	}

	@Override
	public int monomialOrder(Ideal2Factory factory) {
		return 0;
	}

	@Override
	public Monomial[] lower(Ideal2Factory factory) {
		return termMap(factory);
	}
}
