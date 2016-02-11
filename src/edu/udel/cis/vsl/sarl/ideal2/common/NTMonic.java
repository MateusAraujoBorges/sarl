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

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicMap;
import edu.udel.cis.vsl.sarl.ideal2.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal2.IF.Ideal2Factory;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal2.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal2.IF.PrimitivePower;

/**
 * <p>
 * A non-trivial monic ("NTMonic") is the product of at least two
 * {@link PrimitivePower}s. The set of primitive powers comprising this product
 * is represented as a {@link SymbolicMap}.
 * </p>
 * 
 * <p>
 * A key in the map is a {@link Primitive}. The value associated to that key is
 * a {@link PrimitivePower}.
 * </p>
 * 
 * @author siegel
 * 
 */
public class NTMonic extends IdealExpression implements Monic {

	/**
	 * Cached value returned by method {@link #degree()}.
	 */
	private int degree = -1;

	/**
	 * Cached result of {@link #expand(Ideal2Factory)}.
	 */
	private SymbolicMap<Monic, Monomial> expansion = null;

	protected NTMonic(SymbolicType type,
			SymbolicMap<Primitive, PrimitivePower> factorMap) {
		super(SymbolicOperator.MULTIPLY, type, factorMap);
		assert factorMap.size() >= 2;
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
	public SymbolicMap<Primitive, PrimitivePower> monicFactors(
			Ideal2Factory factory) {
		return monicFactors();
	}

	@SuppressWarnings("unchecked")
	public SymbolicMap<Primitive, PrimitivePower> monicFactors() {
		return (SymbolicMap<Primitive, PrimitivePower>) argument(0);
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
	public SymbolicMap<Monic, Monomial> expand(Ideal2Factory factory) {
		if (expansion == null) {
			expansion = factory.oneTermMap(type());

			for (PrimitivePower ppower : monicFactors())
				expansion = factory.multiplyTermMaps(expansion,
						ppower.expand(factory));
		}
		return expansion;
	}

	public StringBuffer toStringBuffer() {
		StringBuffer buffer = new StringBuffer();

		for (SymbolicExpression expr : monicFactors())
			buffer.append(expr.atomString());
		return buffer;
	}

	@Override
	public IdealKind idealKind() {
		return IdealKind.NTMonic;
	}

	@Override
	public int monomialDegree() {
		if (degree < 0) {
			degree = 0;
			for (PrimitivePower expr : monicFactors())
				degree += expr.monomialDegree();
		}
		return degree;
	}

	@Override
	public SymbolicMap<Monic, Monomial> termMap(Ideal2Factory factory) {
		return factory.monicSingletonMap(this, this);
	}

}
