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
import edu.udel.cis.vsl.sarl.ideal2.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal2.IF.Polynomial;

/**
 * A non-trivial polynomial is the sum of at least 2 monomials with different
 * underlying monics, e.g., 1+x^2, x+y, or x+xy.
 * 
 * The set of monomials is represented as a map. A key in this map is a Monic.
 * The value associated to the Monic is a Monomial.
 * 
 * @author siegel
 * 
 */
public class NTPolynomial extends NumericPrimitive implements Polynomial {

	// /**
	// * The degree of the polynomial, or -1 if the degree has not yet been
	// * computed.
	// */
	// private int degree = -1;

	protected NTPolynomial(SymbolicType type,
			SymbolicMap<Monic, Monomial> termMap) {
		super(SymbolicOperator.ADD, type, termMap);
		assert termMap.size() >= 2;
	}

	@Override
	public SymbolicMap<Monic, Monomial> termMap(IdealFactory factory) {
		return termMap();
	}

	@SuppressWarnings("unchecked")
	public SymbolicMap<Monic, Monomial> termMap() {
		return (SymbolicMap<Monic, Monomial>) argument(0);
	}

	public StringBuffer toStringBuffer() {
		StringBuffer buffer = new StringBuffer();
		boolean first = true;

		for (SymbolicExpression expr : termMap()) {
			if (first)
				first = false;
			else
				buffer.append("+");
			buffer.append(expr.toString());
		}
		return buffer;
	}

	@Override
	public String toString() {
		return toStringBuffer().toString();
	}

	@Override
	public int polynomialDegree() {
		// since the monics are ordered by decreasing degree,
		// the first one should be the degree of this polynomial:
		return termMap().getFirst().monomialDegree();
	}

	@Override
	public IdealKind idealKind() {
		return IdealKind.NTPolynomial;
	}

	@Override
	public Constant constantTerm(IdealFactory factory) {
		SymbolicType type = type();
		Constant constant = (Constant) termMap().get(factory.one(type));

		return constant == null ? factory.zero(type) : constant;
	}

	@Override
	public SymbolicMap<Monic, Monomial> expand(IdealFactory factory) {
		SymbolicMap<Monic, Monomial> termMap = termMap();
		int numTerms = termMap.size();
		@SuppressWarnings("unchecked")
		SymbolicMap<Monic, Monomial>[] newTerms = (SymbolicMap<Monic, Monomial>[]) new SymbolicMap<?, ?>[numTerms];
		int count = 0;
		boolean change = false;

		for (Monomial oldTerm : termMap.values()) {
			SymbolicMap<Monic, Monomial> newTerm = oldTerm.expand(factory);

			newTerms[count] = newTerm;
			count++;
			change = change || newTerm.size() != 1;
		}
		if (change) {
			SymbolicMap<Monic, Monomial> result = factory.emptyMonicMap();

			for (SymbolicMap<Monic, Monomial> newTerm : newTerms)
				result = factory.addTermMaps(result, newTerm);
			return result;
		} else {
			return this.termMap();
		}
	}

}
