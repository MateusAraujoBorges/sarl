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
package edu.udel.cis.vsl.sarl.ideal2.IF;

import edu.udel.cis.vsl.sarl.collections.IF.SymbolicMap;

/**
 * A {@link Monomial} is the product of a constant and a {@link Monic}. The
 * constant is called the "constant factor" of the monomial; the monic is called
 * the "monic factor" of the monomial.
 * 
 * @author Stephen F. Siegel
 * 
 */
public interface Monomial extends RationalExpression {

	/**
	 * Returns the constant factor of this monomial.
	 * 
	 * @param factory
	 *            the ideal factory responsible for this monomial
	 * @return the constant factor of this monomial
	 */
	Constant monomialConstant(Ideal2Factory factory);

	/**
	 * Returns the monic factor of this monomial.
	 *
	 * @param factory
	 *            the ideal factory responsible for this monomial
	 * @return the monic factor of this monomial
	 */
	Monic monic(Ideal2Factory factory);

	/**
	 * Returns the degree of the monic where each factor is considered to have
	 * degree 1. For example, (X^2+Y^2)^3*Z^2 has monomial degree 5: it has two
	 * factors, one of degree 3 and one of degree 2.
	 * 
	 * @return the monomial degree with NO expansion
	 */
	int monomialDegree();

	/**
	 * The degree of this monomial if it were fully expanded to a polynomial in
	 * which the variables cannot be expressed as the sum, product, difference,
	 * or quotient of expressions. For example, (X^2+Y^2)^3*Z^2 has total degree
	 * 8.
	 * 
	 * @return total degree of this monomial after full expansion to a
	 *         polynomial
	 */
	int totalDegree();

	/**
	 * Returns the expansion of this monomial.
	 * 
	 * @see Ideal2Factory
	 * 
	 * @param factory
	 *            the ideal factory responsible for this monomial
	 * @return term map whose sum is equivalent to this but with no
	 *         {@link Polynomial}s.
	 */
	SymbolicMap<Monic, Monomial> expand(Ideal2Factory factory);

	/**
	 * Determines whether or not this monomial has a non-trivial expansion. A
	 * trivial expansion is one consisting of exactly one term.
	 * 
	 * @param factory
	 *            the ideal factory responsible for this monomial
	 * @return <code>true</code> iff this monomial has a non-trivial expansion
	 */
	boolean hasNontrivialExpansion(Ideal2Factory factory);

	/**
	 * Returns the term map of this monomial.
	 * 
	 * @see Ideal2Factory
	 * 
	 * @param factory
	 *            the ideal factory responsible for this monomial
	 * @return a term map whose sum is equivalent to this monomial
	 */
	SymbolicMap<Monic, Monomial> termMap(Ideal2Factory factory);

}
