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

import java.io.PrintStream;

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

	public final static boolean debug = false;

	public final static PrintStream out = System.out;

	/**
	 * Cached value returned by method {@link #degree()}.
	 */
	private int monomialDegree = -1;

	private int totalDegree = -1;

	/**
	 * Cached result for method {@link #hasNontrivialExpansion(Ideal2Factory)}.
	 * -1 means this has not yet been computed. 0 means false. 1 means true.
	 */
	byte hasNTE = -1;

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
			SymbolicMap<Primitive, PrimitivePower> factors = monicFactors();
			int totalDegree, numFactors;

			if (debug) {
				totalDegree = totalDegree();
				numFactors = factors.size();
				out.println("Starting: expanding monic of total degree "
						+ totalDegree + " with " + numFactors + " factors");
				//out.println("monic: " + this);
				out.flush();
			}
			expansion = factory.oneTermMap(type());
			for (PrimitivePower ppower : monicFactors())
				expansion = factory.multiplyTermMaps(expansion,
						ppower.expand(factory));
			if (debug) {
				out.println("Finished: expanding monic of total degree "
						+ totalDegree + " with " + numFactors
						+ " factors: result has size " + expansion.size());
				out.flush();
			}
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
	public int monomialDegree() {
		if (monomialDegree < 0) {
			monomialDegree = 0;
			for (PrimitivePower expr : monicFactors())
				monomialDegree += expr.monomialDegree();
		}
		return monomialDegree;
	}

	@Override
	public int totalDegree() {
		if (totalDegree < 0) {
			totalDegree = 0;
			for (PrimitivePower expr : monicFactors())
				totalDegree += expr.totalDegree();
		}
		return totalDegree;
	}

	@Override
	public SymbolicMap<Monic, Monomial> termMap(Ideal2Factory factory) {
		return factory.monicSingletonMap(this, this);
	}

	@Override
	public boolean hasNontrivialExpansion(Ideal2Factory factory) {
		if (hasNTE < 0) {
			hasNTE = 0;
			for (Primitive p : monicFactors().keys()) {
				if (p instanceof NTPolynomial
						|| p.hasNontrivialExpansion(factory)) {
					hasNTE = 1;
					break;
				}
			}
		}
		return hasNTE == 1;
	}

}
