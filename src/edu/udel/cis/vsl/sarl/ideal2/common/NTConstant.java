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
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicIntegerType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicRealType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.common.HomogeneousExpression;
import edu.udel.cis.vsl.sarl.ideal2.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal2.IF.Ideal2Factory;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monomial;

/**
 * A constant which is not 1.
 * 
 * @author siegel
 * 
 */
public class NTConstant extends HomogeneousExpression<SymbolicObject>
		implements Constant {

	/**
	 * Constructs new {@link NTConstant} of given type, wrapping given numeric
	 * value.
	 * 
	 * @param type
	 *            either a {@link SymbolicRealType} or
	 *            {@link SymbolicIntegerType}
	 * @param value
	 *            the numeric value to be wrapped; its type must be consistent
	 *            with <code>type</code>
	 */
	protected NTConstant(SymbolicType type, NumberObject value) {
		super(SymbolicOperator.CONCRETE, type, new SymbolicObject[] { value });
		assert !value.isOne();
	}

	public NumberObject value() {
		return (NumberObject) argument(0);
	}

	public Number number() {
		return value().getNumber();
	}

	public boolean isZero() {
		return value().isZero();
	}

	public boolean isOne() {
		return false;
	}

	@Override
	public Constant monomialConstant(Ideal2Factory factory) {
		return this;
	}

	@Override
	public Monic monic(Ideal2Factory factory) {
		return (Monic) factory.one(type());
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
	public Monomial[] termMap(Ideal2Factory factory) {
		return isZero() ? Ideal2Factory.emptyTermList : new Monomial[] { this };
	}

	@Override
	public int monomialDegree() {
		return isZero() ? -1 : 0;
	}

	@Override
	public Monomial[] expand(Ideal2Factory factory) {
		return termMap(factory);
	}

	@Override
	public int totalDegree() {
		return isZero() ? -1 : 0;
	}

	@Override
	public boolean hasNontrivialExpansion(Ideal2Factory factory) {
		return false;
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
