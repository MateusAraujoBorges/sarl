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

import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.expr.common.HomogeneousExpression;
import edu.udel.cis.vsl.sarl.ideal2.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal2.IF.Ideal2Factory;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal2.IF.Polynomial;
import edu.udel.cis.vsl.sarl.ideal2.IF.Primitive;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;

/**
 * A non-trivial {@link Monomial} is the product of a {@link Constant} and a
 * {@link Monic}. The constant must not be 0 or 1 and the monic must not be
 * empty.
 * 
 * @author siegel
 */
public class NTMonomial extends HomogeneousExpression<SymbolicObject>
		implements Monomial {

	/**
	 * Cached value returned by {@link #expand(Ideal2Factory)}.
	 */
	private Monomial[] expansion = null;

	/**
	 * Cache value returned by {@link #termMap(Ideal2Factory)}.
	 */
	private Monomial[] termMap = null;

	// /**
	// * Cache value returned by {@link #lower(Ideal2Factory)}.
	// */
	// private SymbolicMap<Monic, Monomial> lowering = null;

	/**
	 * Constructs new {@link NTMonomial} using given <code>constant</code> and
	 * <code>monic</code>. Preconditions (checked by assertions only):
	 * <ul>
	 * <li><code>constant</code> is not 0 or 1</li>
	 * <li><code>monic</code> is not empty (i.e., monic is not 1)</li>
	 * </ul>
	 * 
	 * @param constant
	 *            the constant in the new monomial
	 * @param monic
	 *            the monic in the new monomial
	 */
	protected NTMonomial(Constant constant, Monic monic) {
		super(SymbolicOperator.MULTIPLY, constant.type(),
				new SymbolicObject[] { constant, monic });
		assert !constant.isZero();
		assert !constant.isOne();
		assert !monic.isOne();
	}

	@Override
	public Monic monic(Ideal2Factory factory) {
		return (Monic) argument(1);
	}

	/**
	 * Returns the {@link Monic} component of this {@link Monomial}.
	 * 
	 * @return the {@link Monic} component of this
	 */
	public Monic monic() {
		return (Monic) argument(1);
	}

	@Override
	public Constant monomialConstant(Ideal2Factory factory) {
		return (Constant) argument(0);
	}

	/**
	 * Returns the {@link Constant} component of this {@link Monomial}.
	 * 
	 * @return the constant component of this
	 */
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
	public Monomial[] expand(Ideal2Factory factory) {
		if (expansion == null) {
			Monic monic = this.monic();

			if (monic.hasNontrivialExpansion(factory))
				expansion = factory.multiplyConstantTermMap(monomialConstant(),
						monic.expand(factory));
			else
				expansion = new Monomial[] { this };
			if (isCanonic())
				factory.objectFactory().canonize(expansion);
		}
		return expansion;
	}

	@Override
	public int monomialDegree() {
		return monic().monomialDegree();
	}

	@Override
	public Monomial[] termMap(Ideal2Factory factory) {
		if (termMap == null) {
			Monic monic = monic();

			if (monic instanceof Polynomial) {
				termMap = factory.multiplyConstantTermMap(
						(Constant) argument(0), monic.termMap(factory));
			} else {
				termMap = new Monomial[] { this };
			}
			if (isCanonic())
				factory.objectFactory().canonize(termMap);
		}
		return termMap;
	}

	@Override
	public int totalDegree() {
		return monic().totalDegree();
	}

	@Override
	public boolean hasNontrivialExpansion(Ideal2Factory factory) {
		return monic().hasNontrivialExpansion(factory);
	}

	@Override
	public void canonizeChildren(ObjectFactory of) {
		super.canonizeChildren(of);
		if (expansion != null)
			of.canonize(expansion);
		if (termMap != null)
			of.canonize(termMap);
	}

	@Override
	public int monomialOrder(Ideal2Factory factory) {
		return ((Monic) argument(1)).monomialOrder(factory);
	}

	@Override
	public Monomial[] lower(Ideal2Factory factory) {
		// if (lowering == null) {
		Monomial[] lowering;
		int order = monomialOrder(factory);
		Monic monic = this.monic();

		if (order == 0) {
			lowering = new Monomial[] { this };
		} else {
			lowering = factory.multiplyConstantTermMap(monomialConstant(),
					monic instanceof Primitive ? monic.termMap(factory)
							: monic.lower(factory));
		}
		if (isCanonic())
			factory.objectFactory().canonize(lowering);
		// }
		return lowering;
	}
}
