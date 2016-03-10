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

import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicMap;
import edu.udel.cis.vsl.sarl.expr.common.CommonSymbolicExpression;
import edu.udel.cis.vsl.sarl.ideal2.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal2.IF.Ideal2Factory;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal2.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal2.IF.PrimitivePower;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;

/**
 * <p>
 * A non-trivial monic ("NTMonic") is the product of at least two
 * {@link PrimitivePower}s. The set of primitive powers comprising this product
 * is represented as a {@link SymbolicMap}.
 * </p>
 * 
 * <p>
 * A key in the map is a {@link Primitive} <i>p</i>. The value associated to
 * <i>p</i> is a {@link PrimitivePower} <i>p<sup>n</sup></i> for some <i>n</i>
 * &ge;1.
 * </p>
 * 
 * @author siegel
 * 
 */
public class NTMonic extends CommonSymbolicExpression implements Monic {

	/**
	 * Print debugging output?
	 */
	public final static boolean debug = false;

	/**
	 * The stream to which debugging output should be sent.
	 */
	public final static PrintStream out = System.out;

	/**
	 * Cached value returned by method {@link #degree()}. Initial value is -1,
	 * indicating the method has not yet been called.
	 */
	private int monomialDegree = -1;

	// /**
	// * Cached value returned by method {@link #monomialOrder()}.
	// */
	// private int monomialOrder = -1;

	/**
	 * Cached value returned by method {@link #totalDegree()}. Initial value is
	 * -1, indicating the method has not yet been called.
	 */
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

	/**
	 * Cached result of {@link #termMap(Ideal2Factory)}.
	 */
	private SymbolicMap<Monic, Monomial> termMap = null;

	// /**
	// * Cached result of {@link #lowering(Ideal2Factory)}.
	// */
	// private SymbolicMap<Monic, Monomial> lowering = null;

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
			if (!hasNontrivialExpansion(factory)) {
				expansion = termMap(factory);
			} else {
				SymbolicMap<Primitive, PrimitivePower> factors = monicFactors();
				int totalDegree, numFactors;

				if (debug) {
					totalDegree = totalDegree();
					numFactors = factors.size();
					out.println("Starting: expanding monic of total degree "
							+ totalDegree + " with " + numFactors + " factors");
					// out.println("monic: " + this);
					out.flush();
				}
				expansion = factory.oneTermMap(type());
				for (PrimitivePower ppower : factors)
					expansion = factory.multiplyTermMaps(expansion,
							ppower.expand(factory));
				if (debug) {
					out.println("Finished: expanding monic of total degree "
							+ totalDegree + " with " + numFactors
							+ " factors: result has size " + expansion.size());
					out.flush();
				}
				if (isCanonic())
					expansion = factory.objectFactory().canonic(expansion);
			}
		}
		return expansion;
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
		if (termMap == null) {
			termMap = factory.monicSingletonMap(this, (Monomial) this);
			if (isCanonic())
				termMap = factory.objectFactory().canonic(termMap);
		}
		return termMap;
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

	@Override
	public void canonizeChildren(ObjectFactory of) {
		super.canonizeChildren(of);
		if (expansion != null && !expansion.isCanonic())
			expansion = of.canonic(expansion);
		if (termMap != null && !termMap.isCanonic())
			termMap = of.canonic(termMap);
		// if (lowering != null && !lowering.isCanonic())
		// lowering = of.canonic(lowering);
	}

	@Override
	public int monomialOrder(Ideal2Factory factory) {
		// if (monomialOrder < 0) {
		int monomialOrder = 0;
		for (Primitive p : monicFactors().keys()) {
			int po = p.monomialOrder(factory);

			if (po > monomialOrder)
				monomialOrder = po;
		}
		// }
		return monomialOrder;
	}

	@Override
	public SymbolicMap<Monic, Monomial> lower(Ideal2Factory factory) {
		// if (lowering == null) {
		SymbolicMap<Monic, Monomial> lowering = null;
		int order = monomialOrder(factory);

		if (order == 0) {
			lowering = termMap(factory);
		} else {
			SymbolicMap<Primitive, PrimitivePower> factors = monicFactors();

			lowering = factory.oneTermMap(type());
			for (PrimitivePower ppower : factors)
				lowering = factory.multiplyTermMaps(lowering,
						ppower instanceof Primitive ? ppower.termMap(factory)
								: ppower.lower(factory));
			if (isCanonic())
				lowering = factory.objectFactory().canonic(lowering);
		}
		// }
		return lowering;
	}
}
