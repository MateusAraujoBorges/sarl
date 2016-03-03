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
import edu.udel.cis.vsl.sarl.IF.type.SymbolicIntegerType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicRealType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicMap;
import edu.udel.cis.vsl.sarl.ideal2.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal2.IF.Ideal2Factory;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal2.IF.Polynomial;
import edu.udel.cis.vsl.sarl.ideal2.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal2.IF.PrimitivePower;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;

/**
 * <p>
 * An {@link NTPolynomial} ("non-trivial polynomial") is the sum of at least 2
 * {@link Monomial}s with different underlying monics, e.g., 1+<i>x</i>
 * <sup>2</sup>, <i>x</i>+<i>y</i>, or <i>x</i>+<i>xy</i>.
 * </p>
 * 
 * <p>
 * The set of {@link Monomial} terms is represented as a {@link SymbolicMap}. A
 * key in this map is a {@link Monic} <i>m</i>. The value associated to <i>m</i>
 * is a {@link Monomial} of the form <i>c*m</i> for some non-zero
 * {@link Constant} <i>c</i>. This kind of map is called a <i>term map</i>. The
 * reason for using a map is to provide efficient look-up of terms using the
 * {@link Monic}.
 * </p>
 * 
 * @author siegel
 */
public class NTPolynomial extends IdealExpression implements Polynomial {

	/**
	 * The total degree of the polynomial, or -1 if the degree has not yet been
	 * computed.
	 */
	private int totalDegree = -1;

	/**
	 * Cached value returned by {@link #expand(Ideal2Factory)}.
	 */
	private SymbolicMap<Monic, Monomial> expansion = null;

	/**
	 * Cached value returned by {@link #monicFactors(Ideal2Factory)}: a
	 * singleton map from this to this.
	 */
	private SymbolicMap<Primitive, PrimitivePower> monicFactors = null;

	/**
	 * Cached result for method {@link #hasNontrivialExpansion(Ideal2Factory)}.
	 * -1 means this has not yet been computed. 0 means false. 1 means true.
	 */
	byte hasNTE = -1;

	/**
	 * <p>
	 * Constructs new {@link NTPolynomial} wrapping the given term map. The
	 * <code>type</code> must equal the type of <code>termMap</code>. The caller
	 * provides is just for reasons of efficiency.
	 * </p>
	 * 
	 * Preconditions (not necessarily checked):
	 * <ul>
	 * <li><code>termMap</code> has at least 2 entries</li>
	 * <li>every key and value in <code>termMap</code> has type
	 * <code>type</code></li>
	 * <li>the {@link Monomial} value associated to a {@link Monic} key <i>m</i>
	 * has {@link Monic} equal to <i>m</i></li>
	 * </ul>
	 * 
	 * @param type
	 *            either {@link SymbolicRealType} or {@link SymbolicIntegerType}
	 * @param termMap
	 *            a term map with at least 2 entries
	 */
	protected NTPolynomial(SymbolicType type,
			SymbolicMap<Monic, Monomial> termMap) {
		super(SymbolicOperator.ADD, type, termMap);
		assert termMap.size() >= 2;
	}

	@Override
	public SymbolicMap<Monic, Monomial> termMap(Ideal2Factory factory) {
		return termMap();
	}

	@SuppressWarnings("unchecked")
	public SymbolicMap<Monic, Monomial> termMap() {
		return (SymbolicMap<Monic, Monomial>) argument(0);
	}

	@Override
	public int polynomialDegree() {
		// since the monics are ordered by decreasing degree,
		// the first one should be the degree of this polynomial:
		return termMap().getFirst().monomialDegree();
	}

	@Override
	public Constant constantTerm(Ideal2Factory factory) {
		SymbolicType type = type();
		Constant constant = (Constant) termMap().get((Monic) factory.one(type));

		return constant == null ? factory.zero(type) : constant;
	}

	@Override
	public SymbolicMap<Monic, Monomial> expand(Ideal2Factory factory) {
		if (expansion == null) {
			SymbolicMap<Monic, Monomial> termMap = termMap();

			if (hasNontrivialExpansion(factory)) {
				expansion = factory.emptyMonicMap();
				for (Monomial oldTerm : termMap.values())
					expansion = factory.addTermMaps(expansion,
							oldTerm.expand(factory));
				if (isCanonic())
					expansion = factory.objectFactory().canonic(expansion);
			} else {
				expansion = termMap;
			}
		}
		return expansion;
	}

	@Override
	public boolean hasNontrivialExpansion(Ideal2Factory factory) {
		if (hasNTE < 0) {
			hasNTE = 0;
			for (Monic m : termMap().keys()) {
				if (m.hasNontrivialExpansion(factory)) {
					hasNTE = 1;
					break;
				}
			}
		}
		return hasNTE == 1;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * <p>
	 * Gets the maximum of the total degrees of the terms. Note that the terms
	 * are sorted by decreasing monomial degrees (not total degrees), so we have
	 * to search over all terms. We might consider changing the order to use
	 * total degrees, in which case this method can just look at the first term.
	 * </p>
	 * 
	 */
	@Override
	public int totalDegree() {
		if (totalDegree < 0) {
			for (Monic monic : termMap().keys()) {
				int d = monic.totalDegree();

				if (d > totalDegree)
					totalDegree = d;
			}
		}
		return totalDegree;
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
	public SymbolicMap<Primitive, PrimitivePower> monicFactors(
			Ideal2Factory factory) {
		if (monicFactors == null) {
			monicFactors = factory.primitiveSingletonMap(this,
					(PrimitivePower) this);
			if (isCanonic())
				monicFactors = factory.objectFactory().canonic(monicFactors);
		}
		return monicFactors;
	}

	@Override
	public boolean isTrivialMonic() {
		return false;
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
	public int monomialDegree() {
		return 1;
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
	public void canonizeChildren(ObjectFactory of) {
		super.canonizeChildren(of);
		if (expansion != null && !expansion.isCanonic())
			expansion = of.canonic(expansion);
		if (monicFactors != null && !monicFactors.isCanonic())
			monicFactors = of.canonic(monicFactors);
	}

}
