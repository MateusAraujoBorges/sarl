package edu.udel.cis.vsl.sarl.ideal.IF;

import edu.udel.cis.vsl.sarl.collections.IF.SymbolicMap;

/**
 * A polynomial: an expression which is the sum of monomials.
 * 
 * 
 * @author siegel
 * 
 */
public interface Polynomial extends RationalExpression {

	/**
	 * Map from Monic to Monomial. The polynomial is sum of the monomials.
	 * 
	 * @return
	 */
	SymbolicMap<Monic, Monomial> termMap(IdealFactory factory);

	/**
	 * The leading term of this polynomial, or null if the polynomial is 0.
	 * 
	 * @return
	 */
	Monomial leadingTerm();

	/**
	 * The constant term of this polynomial, which may be 0.
	 * 
	 * @return constant term
	 */
	Constant constantTerm(IdealFactory factory);

	/**
	 * Returns a factorization of this polynomial expressed as a Monomial in
	 * which the "variables" are ReducedPolynomials as well as other standard
	 * NumericPrimitives, such as symbolic constants, etc.
	 */
	Monomial factorization(IdealFactory factory);

	/**
	 * Returns the degree of the polynomial, i.e., the maximum degree of a
	 * monomial term, or -1 if the polynomial is 0. A numeric primitive always
	 * has degree 1, even if it "wraps" a polynomial of higher degree.
	 * 
	 * @return the degree of the polynomial
	 */
	int degree();

}
