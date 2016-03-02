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

import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicMap;
import edu.udel.cis.vsl.sarl.ideal2.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal2.IF.Ideal2Factory;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal2.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal2.IF.PrimitivePower;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;

/**
 * A non-trivial primitive power represents a Primitive expression raised to
 * some concrete integer exponent; the exponent is at least 2.
 * 
 * @author siegel
 * 
 */
public class NTPrimitivePower extends IdealExpression
		implements PrimitivePower {

	public final static boolean debug = false;

	public final static PrintStream out = System.out;

	/**
	 * Cached result of {@link #expand(Ideal2Factory)}.
	 */
	private SymbolicMap<Monic, Monomial> expansion = null;

	private SymbolicMap<Primitive, PrimitivePower> monicFactors = null;

	private SymbolicMap<Monic, Monomial> termMap = null;

	protected NTPrimitivePower(Primitive primitive, IntObject exponent) {
		super(SymbolicOperator.POWER, primitive.type(), primitive, exponent);
		assert exponent.getInt() >= 2;
	}

	/**
	 * Creates a primitive which is any symbol or number raised to the 1st power
	 * 
	 * @return - a primitive such as 'x' or 'y'
	 */
	public Primitive primitive() {
		return (Primitive) argument(0);
	}

	@Override
	public SymbolicMap<Primitive, PrimitivePower> monicFactors(
			Ideal2Factory factory) {
		if (monicFactors == null) {
			monicFactors = factory.primitiveSingletonMap(primitive(),
					(PrimitivePower) this);
			if (isCanonic())
				monicFactors = factory.objectFactory().canonic(monicFactors);
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
	public Primitive primitive(Ideal2Factory factory) {
		return (Primitive) argument(0);
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
				IntObject exponent = exponent();
				int totalDegree;

				if (debug) {
					totalDegree = totalDegree();
					out.println(
							"Starting: expanding primitive power of total degree "
									+ totalDegree + " with exponent "
									+ exponent);
					out.flush();
				}

				Primitive primitive = primitive();
				SymbolicMap<Monic, Monomial> expandedPrimitive = primitive
						.expand(factory);

				expansion = factory.powerTermMap(type(), expandedPrimitive,
						exponent);
				if (debug) {
					out.println(
							"Finished: expanding primitive power of total degree "
									+ totalDegree + " with exponent " + exponent
									+ ": result has size " + expansion.size());
					out.flush();
				}
				if (isCanonic())
					expansion = factory.objectFactory().canonic(expansion);
			}
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
	public SymbolicMap<Monic, Monomial> termMap(Ideal2Factory factory) {
		if (termMap == null) {
			termMap = factory.monicSingletonMap(this, this);
			if (isCanonic())
				termMap = factory.objectFactory().canonic(termMap);
		}
		return termMap;
	}

	@Override
	public int totalDegree() {
		return exponent().getInt() * primitive().totalDegree();
	}

	@Override
	public boolean hasNontrivialExpansion(Ideal2Factory factory) {
		Primitive p = primitive();

		return p instanceof NTPolynomial || p.hasNontrivialExpansion(factory);
	}

	@Override
	public void canonizeChildren(ObjectFactory of) {
		super.canonizeChildren(of);
		if (termMap != null && !termMap.isCanonic())
			termMap = of.canonic(termMap);
		if (expansion != null && !expansion.isCanonic())
			expansion = of.canonic(expansion);
		if (monicFactors != null && !monicFactors.isCanonic())
			monicFactors = of.canonic(monicFactors);
	}

}
