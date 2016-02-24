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
package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import org.junit.After;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class IntegerArithmeticReasonTest {
	private SymbolicUniverse universe;
	private StringObject uobj; // "u"
	private SymbolicType integerType;
	private NumericSymbolicConstant u; // integer symbolic constant "u"
	private NumericExpression negOneInt;
	private NumericExpression threeInt;
	private NumericExpression fiveInt;
	private BooleanExpression trueExpr, falseExpr;
	private BooleanExpression assumption;
	private Reasoner reasoner;

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		uobj = universe.stringObject("u");
		integerType = universe.integerType();
		u = (NumericSymbolicConstant) universe.symbolicConstant(uobj,
				integerType);
		negOneInt = universe.integer(-1);
		threeInt = universe.integer(3);
		fiveInt = universe.integer(5);
		trueExpr = universe.bool(true);
		falseExpr = universe.bool(false);
	}

	@After
	public void tearDown() throws Exception {
	}

	/**
	 * u < 3 && u >=2: u -> 2
	 */
	@Test
	public void simplifyIntTight1() {
		BooleanExpression assumption = universe.and(
				universe.lessThan(u, universe.integer(3)),
				universe.lessThanEquals(universe.integer(2), u));
		Reasoner reasoner = universe.reasoner(assumption);

		assertEquals(universe.integer(2), reasoner.simplify(u));
		assertEquals(trueExpr, reasoner.getReducedContext());
	}

	/**
	 * u < 3 && u >1: u -> 2
	 */
	@Test
	public void simplifyIntTight2() {
		BooleanExpression assumption = universe.and(
				universe.lessThan(u, universe.integer(3)),
				universe.lessThan(universe.integer(1), u));
		Reasoner reasoner = universe.reasoner(assumption);

		assertEquals(universe.integer(2), reasoner.simplify(u));
		assertEquals(trueExpr, reasoner.getReducedContext());
	}

	/**
	 * u<3 && u>2 : contradiction
	 */
	@Test
	public void contradict1() {
		BooleanExpression assumption = universe.and(
				universe.lessThan(u, universe.integer(3)),
				universe.lessThan(universe.integer(2), u));
		Reasoner reasoner = universe.reasoner(assumption);

		assertEquals(u, reasoner.simplify(u));
		assertEquals(falseExpr, reasoner.getReducedContext());
	}

	/**
	 * u=2 : a{5,6,7}[u]->7
	 */
	@Test
	public void simplifyArrayRead() {
		SymbolicExpression a = universe.symbolicConstant(
				universe.stringObject("a"), universe.arrayType(integerType));

		a = universe.arrayWrite(a, universe.integer(0), universe.integer(5));
		a = universe.arrayWrite(a, universe.integer(1), universe.integer(6));
		a = universe.arrayWrite(a, universe.integer(2), universe.integer(7));

		SymbolicExpression read = universe.arrayRead(a, u);
		BooleanExpression assumption = universe.equals(u, universe.integer(2));
		Reasoner reasoner = universe.reasoner(assumption);

		assertEquals(universe.integer(7), reasoner.simplify(read));
		assertEquals(trueExpr, reasoner.getReducedContext());
	}

	/**
	 * Integer division. true : 2(u/2) -> 2(u/2)
	 */
	@Test
	public void simplifyIntDivNo() {
		SymbolicExpression e = universe.multiply(universe.integer(2),
				universe.divide(u, universe.integer(2)));
		Reasoner reasoner = universe.reasoner(trueExpr);

		assertEquals(e, reasoner.simplify(e));
	}

	/**
	 * Integer division. true : (2u)/2 -> u
	 */
	@Test
	public void simplifyIntDivYes() {
		SymbolicExpression e = universe.divide(
				universe.multiply(universe.integer(2), u), universe.integer(2));
		Reasoner reasoner = universe.reasoner(trueExpr);

		assertEquals(u, reasoner.simplify(e));
	}

	/**
	 * Integer modulus. true : 0 <= u/3 <=1 -> u <= 5
	 */
	@Ignore
	@Test
	public void simplifyIntDivTest() {
		assumption = universe.and(
				universe.lessThanEquals(universe.zeroInt(),
						universe.divide(u, threeInt)),
				universe.lessThanEquals(universe.divide(u, threeInt),
						universe.oneInt()));
		reasoner = universe.reasoner(assumption);
		SymbolicExpression e = universe.lessThanEquals(u, fiveInt);

		assertEquals(trueExpr, reasoner.simplify(e));
	}

	/**
	 * Integer modulus. true : (2u)%2 -> 0 for all u;
	 */
	@Test
	public void simplifyIntMod() {
		SymbolicExpression e = universe.modulo(
				universe.multiply(universe.integer(2), u), universe.integer(2));
		reasoner = universe.reasoner(trueExpr);

		assertEquals(universe.zeroInt(), reasoner.simplify(e));
	}

	// TODO: Possible approaches:
	// When evaluating x%constant: if x is a Monomial c*m,
	// (c*m)%d = ((c%d)*m)%d, and (c1*m1 + c2*m2)%d =...
	// (x^n)%d = ((x%d)^n)%d. In short, apply %d to all
	// constants...
	// (a*b)%d = ((a%d)*b)%d
	// (a+b)%d = ((a%d)+b)%d
	// sign?

	/**
	 * Integer modulus. true : (2u + 1) % 2 -> 1 only if u >= 0.
	 */
	@Test
	public void simplifyIntMod2() {
		assumption = universe.lessThanEquals(universe.zeroInt(), u);
		reasoner = universe.reasoner(assumption);
		SymbolicExpression e = universe
				.modulo(universe.add(universe.multiply(universe.integer(2), u),
						universe.oneInt()), universe.integer(2));

		assertEquals(universe.oneInt(), reasoner.simplify(e));
	}

	/**
	 * Integer modulus. true : (2u + 1) % 2 -> -1 only if u < 0.
	 */
	@Ignore
	@Test
	public void simplifyIntMod3() {
		assumption = universe.lessThan(u, universe.zeroInt());
		reasoner = universe.reasoner(assumption);
		SymbolicExpression e = universe
				.modulo(universe.add(universe.multiply(universe.integer(2), u),
						universe.oneInt()), universe.integer(2));

		assertEquals(negOneInt, reasoner.simplify(e));
	}

}
