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

import java.util.Comparator;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicMap;
import edu.udel.cis.vsl.sarl.expr.IF.NumericExpressionFactory;
import edu.udel.cis.vsl.sarl.ideal2.common.One;

/**
 * <p>
 * An {@link IdealFactory} provides a few services beyond those guaranteed by an
 * arbitrary {@link NumericExpressionFactory}.
 * </p>
 * 
 * The ideal factory produces and manipulates the following kinds of numeric
 * expressions:
 * 
 * <p>
 * A {@link Constant} represents a concrete value. Each constant has either
 * integer or real type.
 * </p>
 * 
 * <p>
 * A {@link Primitive} expression is one which is not concrete and cannot be
 * expressed as a sum or product or quotient of other expressions. Examples:
 * symbolic constants, array read expressions of integer or real type, tuple
 * read expressions of integer or real types, function applications for
 * functions returning integer or real.
 * </p>
 * 
 * <p>
 * Any value which is the result of raising a primitive expression to a concrete
 * positive integer power is an instance of {@link PrimitivePower}. Any
 * {@link Primitive} is also a {@link PrimitivePower} by taking the exponent to
 * be 1.
 * </p>
 * 
 * <p>
 * A {@link Monic} is the product of {@link PrimitivePower}s. Any
 * {@link PrimitivePower} is also a {@link Monic}: it is the product of a single
 * primitive-power. The {@link Constant} 1 (integer or real) is also a
 * {@link Monic}: it is the empty product. The integer and real 1s are the only
 * constants which are also {@link Monic}s.
 * </p>
 * 
 * <p>
 * A {@link Monomial} is the product of a {@link Constant} and a {@link Monic}.
 * Any {@link Constant} is also a {@link Monomial} by taking 1 for the monic.
 * Any {@link Monic} is also a {@link Monomial} by taking 1 for the constant.
 * </p>
 * 
 * 
 * 
 * <p>
 * A <i>term map</i> is a map from {@link Monic} to {@link Monomial} with the
 * property that a monic <i>m</i> in the key set maps to a monomial of the form
 * <i>c</i>*<i>m</i> for some non-zero constant <i>c</i>. A term map is a
 * {@link SymbolicMap}, not a {@link SymbolicExpression}.
 * </p>
 * 
 * <p>
 * A {@link Polynomial} is a sum of the {@link Monomial} values of a term map.
 * {@link Polynomial} is also a subtype of {@link Primitive}, which is a subtype
 * of {@link PrimitivePower}, which is a subtype of {@link Monic}, which is a
 * subtype of {@link Monomial}. In this factory, each instance <code>p</code>of
 * {@link Polynomial} satisfies all of the following:
 * <ol>
 * <li><code>p</code> is the sum of at least 2 non-zero monomials</li>
 * <li>no term of <code>p</code> is a {@link Polynomial}</li>
 * <li>if <code>p</code> has integer type, the GCD of its coefficients is 1 and
 * the leading coefficient is positive</li>
 * <li>if <code>p</code> has real type, the leading coefficient is 1</li>
 * </ol>
 * </p>
 * 
 * <p>
 * The sum of two term maps is defined by combining the two maps by combining
 * two terms with the same monic by adding the coefficients. The product of two
 * term maps is defined in the usual way: by multiplying each element in one
 * with each element in the other, then combining terms with the same monic by
 * adding coefficients. The product of a {@link Constant} and a term map is
 * defined by multiplying that constant by each {@link Monomial} value in the
 * term map. The n-th power of a term map is the term map obtained by
 * multiplying the term map with itself n times.
 * </p>
 * 
 * <p>
 * Given any {@link Monomial} <i>m</i>, the <i>basic term map</i> of <i>m</i> is
 * defined as follows:
 * <ol>
 * <li>if <i>m</i> is a {@link Polynomial}, the basic term map is the term map
 * of that polynomial</li>
 * <li>if <i>m</i> is the product of a {@link Constant} and a {@link Polynomial}
 * , the basic term map is the product of the constant and the basic term map of
 * the polynomial</li>
 * <li>otherwise, the basic term map is the map with one entry with value
 * <i>m</i>.</li>
 * </ol>
 * </p>
 * 
 * <p>
 * The <i>fully expanded term map</i> of a {@link Monomial} <i>m</i> is the term
 * map defined recursively as follows:
 * <ul>
 * <li>If <i>m</i> is a {@link Primitive} which is not a {@link Polynomial}, the
 * fully expanded term map of <i>m</i> is the singleton map with value <i>m</i>.
 * </li>
 * <li>If <i>m</i> is a {@link Polynomial}, the fully expanded term map of
 * <i>m</i> is the sum of the fully expanded term maps of the terms of <i>m</i>.
 * </li>
 * <li>The fully expanded term map of the product of a {@link Constant} and a
 * {@link Monic} is the product of the constant with the fully expanded term map
 * of the {@link Monic}.</li>
 * <li>The fully expanded term map of a {@link PrimitivePower} <i>p</i>
 * <sup><i>n</i></sup> is the fully expanded term map of <i>p</i> raised to the
 * <i>n<sup>th</sup></i> power.</li>
 * </ul>
 * </p>
 * 
 * <p>
 * In the following examples, suppose <i>X</i> and <i>Y</i> are
 * {@link Primitive}s which are not {@link Polynomial}s.
 * </p>
 * 
 * <ul>
 * <li>the fully expanded term map of the {@link Monomial} <i>X</i> is {<i>X</i>
 * }</li>
 * <li>the fully expanded term map of the {@link Polynomial} <i>X</i>+<i>Y</i>
 * is {<i>X</i>, <i>Y</i>}</li>
 * <li>the fully expanded term map of the {@link Monomial} 2*(<i>X</i>+<i>Y</i>)
 * is {2*<i>X</i>, 2*<i>Y</i>}</li>
 * <li>the fully expanded term map of the {@link Polynomial} 2*(<i>X</i>+
 * <i>Y</i>) + <i>X</i> is {3*<i>X</i>, <i>Y</i>}</li>
 * <li>the fully expanded term map of the {@link Monomial} <i>X</i><sup>2</sup>
 * is {<i>X</i><sup>2</sup>}</li>
 * <li>the fully expanded term map of the {@link Monomial} (<i>X</i>+<i>Y</i>)
 * <sup>2</sup> is {<i>X</i><sup>2</sup>, 2*<i>XY</i>, <i>Y</i> <sup>2</sup>
 * </li>}</li>
 * </ul>
 * 
 * <p>
 * The product of two {@link Monomial}s is a {@link Monomial} and is defined in
 * the obvious way, by multiplying primitive powers.
 * </p>
 * 
 * <p>
 * Suppose <i>m</i><sub>1</sub> and <i>m</i><sub>2</sub> are two
 * {@link Monomial}s with no primitive factor in common. The sum <i>m</i>
 * <sub>1</sub> + <i>m</i><sub>2</sub> is defined as follows. First, there is
 * the option of using the basic or fully expanded term maps of the two
 * monomials. The choice of whether or not to expand can be made using some
 * heuristic. In any case, the two term maps are added. The resulting term map
 * is factored (if possible) to produce a {@link Monomial}; the result may be a
 * {@link Polynomial}.
 * </p>
 * 
 * <p>
 * The sum of two arbitrary {@link Monomial}s <i>m</i><sub>1</sub> and <i>m</i>
 * <sub>2</sub> is defined as follows. First, the greatest common factor is
 * factored out, so <i>m</i><sub>1</sub>=d*<i>r</i><sub>r</sub>, <i>m</i>
 * <sub>2</sub>=d*<i>r</i><sub>2</sub>, where <i>d</i> is a {@link Monomial} and
 * <i>r</i><sub>1</sub> and <i>r</i><sub>2</sub> are {@link Monomial}s which
 * have no primitive factor is common. Hence <i>m</i><sub>1</sub> + <i>m</i>
 * <sub>2</sub> = <i>d</i>*(<i>r</i><sub>1</sub>+<i>r</i><sub>2</sub>), where
 * the product is again monomial product and the sum <i>r</i><sub>1</sub>+
 * <i>r</i><sub>2</sub> is a {@link Monomial} computed as described above.
 * </p>
 * 
 * <p>
 * A {@link RationalExpression} is the quotient of two {@link Monomial}s. Any
 * {@link Monomial} is also a {@link RationalExpression} by taking the
 * denominator to be the (monomial) 1. Any {@link RationalExpression} of integer
 * type is also a {@link Monomial}. (The result of integer division of two
 * integer polynomials may be a {@link Primitive} expression with operator
 * {@link SymbolicOperator#INT_DIVIDE}.)
 * </p>
 * 
 * <p>
 * A relational numeric expression will always be in one of the following forms:
 * 
 * <ul>
 * <li><code>0&lt;m</code></li>
 * <li><code>0&le;m</code></li>
 * <li><code>0=m</code></li>
 * <li><code>0&ne;m</code></li>
 * </ul>
 * 
 * where <code>p</code> is a {@link Monomial}.
 * </p>
 * 
 * <p>
 * Reductions: 0&lt;<i>x</i><sup>2</sup><i>y</i> iff 0&lt;<i>y</i>. Hence we can
 * assume all powers are 1. Furthermore 0&lt;<i>xy</i> iff ((0&lt;<i>x</i> &and;
 * 0&lt;<i>y</i>) &or; (0&lt;&minus;<i>x</i> &and; 0&lt;&minus;<i>y</i>)). This
 * can be used to reduce everything to {@link Primitive}s, but unfortunately the
 * size of the formula is exponential in the number of factors. A heuristic
 * could be used to determine whether to expand.
 * </p>
 * 
 * <p>
 * Equality and inequality reductions are easier because <i>xy</i>=0 iff (
 * <i>x</i>=0 &or; <i>y</i>=0), which does not involve an expansion in formula
 * size. Similarly, <i>xy</i>&ne;0 iff (<i>x</i>&ne;0 &and; <i>y</i>&ne;0).
 * 
 * 
 * @author siegel
 * 
 */
public interface IdealFactory extends NumericExpressionFactory {
	
	Comparator<Monic> monicComparator();

	/**
	 * The empty map from Primitive to V, i.e., the map containing no entries.
	 *
	 * @return the empty map
	 */
	<V extends SymbolicExpression> SymbolicMap<Primitive, V> emptyPrimitiveMap();

	/**
	 * The empty map from Monic to V, i.e., the map containing no entries.
	 *
	 * @return the empty map
	 */
	<V extends SymbolicExpression> SymbolicMap<Monic, V> emptyMonicMap();

	/**
	 * The singleton map from Monic to V consisting of one entry (key,value).
	 * 
	 * @param key
	 *            a Monic
	 * @param value
	 *            an element of V
	 * @return symbolic map consisting of one entry (key,value)
	 */
	<V extends SymbolicExpression> SymbolicMap<Monic, V> monicSingletonMap(
			Monic key, V value);

	/**
	 * The singleton map from Primitive to V consisting of one entry
	 * (key,value).
	 * 
	 * @param key
	 *            a Primitive
	 * @param value
	 *            an element of V
	 * @return symbolic map consisting of one entry (key,value)
	 */
	<V extends SymbolicExpression> SymbolicMap<Primitive, V> primitiveSingletonMap(
			Primitive key, V value);

	/**
	 * Returns an int-object wrapping the int 1.
	 * 
	 * @return a value 1 of type IntObject
	 */
	IntObject oneIntObject();

	/**
	 * Creates an integer constant
	 * 
	 * @param value
	 *            - a normal integer value
	 * 
	 * @param type
	 *            Integer
	 * 
	 * @return an integer of type Constant
	 */
	Constant intConstant(int value);

	@Override
	/**
	 * Creates a zero integer constant
	 * 
	 * @return a zero integer of type Constant
	 */
	Constant zeroInt();

	@Override
	/**
	 * Creates a real zero constant
	 * 
	 * @return a real zero of type Constant
	 */
	Constant zeroReal();

	/**
	 * Creates a value zero for the type that is passed as an argument
	 * 
	 * @param type
	 *            - different data types of SymbolicType - real, Integer etc.
	 * 
	 * @param type
	 *            SymbolicType
	 * 
	 * @return a value zero of the specified type
	 */
	Constant zero(SymbolicType type);

	/**
	 * Returns a constant
	 * 
	 * @param number
	 *            - another form/representation of real number
	 * 
	 * @param type
	 *            Number
	 * 
	 * @return a constant of type Constant
	 */
	Constant constant(Number number);

	/**
	 * a Monic ONE
	 * 
	 * @param type
	 *            - different data types of SymbolicType - real, Integer etc.
	 * 
	 * @param type
	 *            SymbolicType
	 * 
	 * @return a value of 1 of type Monic
	 */
	One one(SymbolicType type);

	// Primitive Powers...

	PrimitivePower primitivePower(Primitive primitive, IntObject exponent);

	// Monomials...

	/**
	 * Creates a Monomial which is a Monic multiplied by a constant, integer or
	 * a real number.
	 * 
	 * @param constant
	 *            - a concrete number. Wraps a NumberObject, which wraps a
	 *            Number
	 * @param monic
	 *            - product of powers of primitive expressions
	 *            x_1^{i_1}*...*x_n^{i_n}, where the x_i are primitives and the
	 *            i_j are positive concrete integers.
	 * 
	 * @param type
	 *            Constant and Monic
	 * 
	 * @return a monomial by concatenating a constant of type Constant and a
	 *         monic of type Monic
	 */
	Monomial monomial(Constant constant, Monic monic);

	Monomial multiplyMonomials(Monomial m1, Monomial m2);

	Monomial addMonomials(Monomial m1, Monomial m2);

	Monomial multiplyConstantMonomial(Constant constant, Monomial monomial);

	// Term maps...

	SymbolicMap<Monic, Monomial> oneTermMap(SymbolicType type);

	SymbolicMap<Monic, Monomial> addTermMaps(SymbolicMap<Monic, Monomial> map1,
			SymbolicMap<Monic, Monomial> map2);

	SymbolicMap<Monic, Monomial> multiplyTermMaps(
			SymbolicMap<Monic, Monomial> map1,
			SymbolicMap<Monic, Monomial> map2);

	SymbolicMap<Monic, Monomial> multiplyConstantTermMap(Constant constant,
			SymbolicMap<Monic, Monomial> map);

	SymbolicMap<Monic, Monomial> powerTermMap(SymbolicType type,
			SymbolicMap<Monic, Monomial> map, IntObject exponent);

	/**
	 * <p>
	 * Computes a {@link Monomial} which is equivalent to the sum of the terms
	 * in the given term map. The goal is to attempt to factor the
	 * {@link Polynomial} as much as practical.
	 * </p>
	 * 
	 * <p>
	 * Pre-condition: <map> is non-empty.
	 * </p>
	 * 
	 * @param map
	 *            a term map, i.e., a map from {@link Monic} to {@link Monomial}
	 *            with the property that a {@link Monic} <i>m</i> maps to a
	 *            {@link Monomial} of the form <i>c</i>*<i>m</i>, for some non-0
	 *            {@link Constant} <i>c</i>
	 * @return a {@link Monomial} equivalent to the sum of the {@link Monomial}
	 *         values of <code>map</code>
	 */
	Monomial factorTermMap(SymbolicMap<Monic, Monomial> map);

	// Polynomials...

	Polynomial polynomial(SymbolicType type,
			SymbolicMap<Monic, Monomial> termMap);

	// /**
	// * Given a polynomial p with constant term c, returns p-c.
	// *
	// * @param polynomial
	// * a non-<code>null</code> instance of {@link Polynomial}
	// *
	// * @return result of subtracting the constant term from the polynomial
	// */
	// Polynomial subtractConstantTerm(Polynomial polynomial);

	// /**
	// * Divides each term in a polynomial with by a constant. The polynomial
	// and
	// * constant must have the same type. If the type is integer, this will
	// * perform integer division on each term; this is only equivalent to
	// integer
	// * division of the polynomial by the constant if the constant divides each
	// * term.
	// *
	// *
	// * @param polynomial
	// * a non-<code>null</code> instance of {@link Polynomial}
	// * @param constant
	// * a concrete number of the same type as the
	// * <code>polynomial</code>
	// *
	// * @return the polynomial that results from dividing the given polynomial
	// by
	// * the given constant
	// */
	// Polynomial dividePolynomialConstant(Polynomial polynomial,
	// Constant constant);

	// /**
	// * Given a numeric expression e of integer or real type, returns a
	// (possibly
	// * simpler) polynomial p of the same type which has the property that e=0
	// if
	// * and only if p=0. Example: e=x^5, p=x.
	// *
	// * @param expr
	// * a non-<code>null</code> numeric expression
	// * @return a polynomial of same type which is zero iff <code>expr</code>
	// is
	// */
	// Polynomial zeroEssence(NumericExpression expr);

}
