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
 * An {@link Ideal2Factory} provides a few services beyond those guaranteed by
 * an arbitrary {@link NumericExpressionFactory}.
 * </p>
 * 
 * <p>
 * The ideal factory produces and manipulates the following kinds of numeric
 * expressions:
 * </p>
 * 
 * <p>
 * A {@link Constant} represents a concrete value. Each constant has either
 * integer or real type.
 * </p>
 * 
 * <p>
 * A {@link Primitive} expression is one which is not concrete and which is to
 * be treated as an atomic expression, such as a variable, from the point of
 * view of ideal mathematical arithmetic. Examples: symbolic constants, array
 * read expressions of integer or real type, tuple read expressions of integer
 * or real types, function applications for functions returning integer or real
 * are all primitive expressions. In addition, in this factory a
 * {@link Polynomial} is a {@link Primitive} so that it can be treated as a
 * "variable" in a factorization.
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
 * <p>
 * A <i>term map</i> is a map from {@link Monic} to {@link Monomial} with the
 * property that a monic <i>m</i> in the key set maps to a monomial of the form
 * <i>c</i>*<i>m</i> for some non-zero constant <i>c</i>. A term map is a
 * {@link SymbolicMap}, not a {@link SymbolicExpression}.
 * </p>
 * 
 * <p>
 * A {@link Polynomial} is a sum of the {@link Monomial} values of a term map.
 * {@link Polynomial} is also a sub-type of {@link Primitive}, which is a
 * subtype of {@link PrimitivePower}, which is a sub-type of {@link Monic},
 * which is a sub-type of {@link Monomial}. In this factory, each instance
 * <code>p</code> of {@link Polynomial} satisfies all of the following:
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
 * </li>
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
 * <li><code>m&lt;0</code></li>
 * <li><code>m&le;0</code></li>
 * <li><code>0=p</code></li>
 * <li><code>0&ne;p</code></li>
 * </ul>
 * 
 * where <code>m</code> is a {@link Monic} and <code>p</code> is a
 * {@link Primitive}.
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
 * </p>
 * 
 * @author siegel
 */
public interface Ideal2Factory extends NumericExpressionFactory {

	/**
	 * The {@link Comparator} on {@link Monic}s. This places some well-defined
	 * total order on the set of all instances of {@link Monic}.
	 * 
	 * @return the comparator on {@link Monic}s
	 */
	Comparator<Monic> monicComparator();

	/**
	 * The empty map from {@link Primitive} to <code>V</code>, i.e., the map
	 * containing no entries.
	 *
	 * @return the empty map
	 */
	<V extends SymbolicExpression> SymbolicMap<Primitive, V> emptyPrimitiveMap();

	/**
	 * The empty map from {@link Monic} to <code>V</code>, i.e., the map
	 * containing no entries.
	 *
	 * @return the empty map
	 */
	<V extends SymbolicExpression> SymbolicMap<Monic, V> emptyMonicMap();

	/**
	 * The singleton map from {@link Monic} to <code>V</code> consisting of one
	 * entry <code>(key,value)</code>.
	 * 
	 * @param key
	 *            a non-<code>null</code> {@link Monic}
	 * @param value
	 *            an element of <code>V</code>
	 * @return symbolic map consisting of one entry <code>(key,value)</code>
	 */
	<V extends SymbolicExpression> SymbolicMap<Monic, V> monicSingletonMap(
			Monic key, V value);

	/**
	 * The singleton map from {@link Primitive} to <code>V</code> consisting of
	 * one entry <code>(key,value)</code>.
	 * 
	 * @param key
	 *            a non-<code>null</code> {@link Primitive}
	 * @param value
	 *            an element of <code>V</code>
	 * @return symbolic map consisting of one entry (key,value)
	 */
	<V extends SymbolicExpression> SymbolicMap<Primitive, V> primitiveSingletonMap(
			Primitive key, V value);

	/**
	 * Returns an {@link IntObject} wrapping the int 1.
	 * 
	 * @return the integer 1 as an {@link IntObject}
	 */
	IntObject oneIntObject();

	/**
	 * Returns an integer {@link Constant}.
	 * 
	 * @param value
	 *            any Java <code>int</code>
	 * 
	 * @return the integer {@link Constant} wrapping the given
	 *         <code>value</code>
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

	// Monics...

	/**
	 * Given a {@link Monic} returns the {@link Monic} obtained by removing some
	 * of the {@link PrimitivePower} factors according to the given
	 * <code>mask</code>. The <code>mask</code> is an array whose length is the
	 * number of {@link PrimitivePower} factors in <code>monic</code>. A
	 * <code>true</code> mask entry indicates the corresponding factor should be
	 * kept; a <code>false</code> entry indicates the corresponding factor
	 * should be removed.
	 * 
	 * @param monic
	 *            a non-<code>null</code> {@link Monic}
	 * @param mask
	 *            array of boolean whose length equals number of primitive power
	 *            factors in <code>monic</code>
	 * @return a {@link Monic} with same type as <code>monic</code> obtained
	 *         from <code>monic</code> by keeping only those factors for which
	 *         the corresponding bit in <code>mask</code> is <code>true</code>
	 */
	Monic monicMask(Monic monic, boolean[] mask);

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

	Monomial addMonomials(Monomial[] monomials);

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
	 * Pre-condition: <code>maps</code> is non-empty.
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

}
