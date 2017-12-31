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

/**
 * Tests reasoning about integer expressions.
 */
import static org.junit.Assert.assertEquals;

import java.io.PrintStream;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class IntegerArithmeticReasonTest {

	public static boolean debug = false;

	public static PrintStream out = System.out;

	private static SymbolicUniverse universe = SARL.newStandardUniverse();

	private static StringObject u_obj = universe.stringObject("u");

	private static StringObject x_obj = universe.stringObject("x");

	private static StringObject y_obj = universe.stringObject("y");

	private static StringObject z_obj = universe.stringObject("z");

	private static SymbolicType integerType = universe.integerType();

	private static NumericSymbolicConstant u = (NumericSymbolicConstant) universe
			.symbolicConstant(u_obj, integerType);

	private static NumericSymbolicConstant x = (NumericSymbolicConstant) universe
			.symbolicConstant(x_obj, integerType);

	private static NumericSymbolicConstant y = (NumericSymbolicConstant) universe
			.symbolicConstant(y_obj, integerType);

	private static NumericSymbolicConstant z = (NumericSymbolicConstant) universe
			.symbolicConstant(z_obj, integerType);

	private static NumericExpression threeInt = universe.integer(3);

	private static NumericExpression fiveInt = universe.integer(5);

	private static BooleanExpression trueExpr = universe.bool(true);

	private static BooleanExpression falseExpr = universe.bool(false);

	@BeforeClass
	public static void setUpClass() {
		if (debug)
			universe.setShowProverQueries(true);
	}

	@AfterClass
	public static void tearDownClass() {
		out = null;
		universe = null;
		u_obj = null;
		x_obj = null;
		y_obj = null;
		z_obj = null;
		integerType = null;
		u = null;
		x = null;
		y = null;
		z = null;
		threeInt = null;
		fiveInt = null;
		trueExpr = null;
		falseExpr = null;
	}

	private void debug(String msg) {
		if (debug)
			out.println(msg);
	}

	/**
	 * Does x/3 + y/z + 5/3 = 5 ? No. This shows you can form this expression
	 * even though it is not known whether z is 0.
	 */
	@Test
	public void divisionByZeroTest() {
		NumericExpression fiveDivThree = universe.divide(fiveInt, threeInt);
		NumericExpression xDiv3 = universe.divide(x, threeInt);
		NumericExpression yDivz = universe.divide(y, z);
		BooleanExpression predicate = universe.equals(
				universe.add(universe.add(xDiv3, yDivz), fiveDivThree),
				fiveInt);
		Reasoner r = universe.reasoner(trueExpr);
		ValidityResult result = r.valid(predicate);

		assertEquals(ResultType.NO, result.getResultType());
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
	 * Integer division. true : 0 <= u/3 <=1 -> u <= 5
	 */
	@Test
	public void intDivTest() {
		BooleanExpression assumption = universe.and(
				universe.lessThanEquals(universe.zeroInt(),
						universe.divide(u, threeInt)),
				universe.lessThanEquals(universe.divide(u, threeInt),
						universe.oneInt()));
		Reasoner reasoner = universe.reasoner(assumption);
		BooleanExpression e1 = universe.lessThanEquals(u, fiveInt);
		ValidityResult result1 = reasoner.valid(e1);

		assertEquals(ResultType.YES, result1.getResultType());
	}

	/**
	 * Integer division simplification. u/3<=1 -> u<=5.
	 */
	@Test
	public void simplifyIntDivTest() {
		BooleanExpression e1 = universe.lessThanEquals(
				universe.divide(u, threeInt), universe.oneInt());
		Reasoner reasoner = universe.reasoner(trueExpr);
		BooleanExpression e2 = reasoner.simplify(e1);
		BooleanExpression e3 = universe.lessThanEquals(u, fiveInt);

		debug("e2 = " + e2);
		assertEquals(e3, e2);
	}

	/**
	 * Integer modulus. true : (2u)%2 -> 0 for all u;
	 */
	@Test
	public void simplifyIntMod() {
		SymbolicExpression e = universe.modulo(
				universe.multiply(universe.integer(2), u), universe.integer(2));
		Reasoner reasoner = universe.reasoner(trueExpr);

		assertEquals(universe.zeroInt(), reasoner.simplify(e));
	}

	/**
	 * Multiply powers with the same base: (x^y)*(x^z)=x^(y+z)
	 */
	@Test
	public void multiplyPowerTest() {
		NumericExpression e1 = universe.multiply(universe.power(x, y),
				universe.power(x, z));
		NumericExpression e2 = universe.power(x, universe.add(y, z));
		Reasoner reasoner = universe.reasoner(trueExpr);

		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * Raise a power to a power: (x^y)^z=x^(y*z)
	 */
	@Test
	public void PowerToPowerTest() {
		NumericExpression e1 = universe.power(universe.power(x, y), z);
		NumericExpression e2 = universe.power(x, universe.multiply(y, z));
		Reasoner reasoner = universe.reasoner(trueExpr);

		debug("e1 is " + e1);
		debug("e2 is " + e2);
		assertEquals(reasoner.simplify(e2), reasoner.simplify(e1));
	}

	/**
	 * Assume x is an int, x>=3, and x div 2 <= 1. Prove x=3.
	 */
	@Test
	public void intDivBound() {
		NumericExpression two = universe.integer(2);
		SymbolicConstant X = universe.symbolicConstant(
				universe.stringObject("X"), universe.integerType());
		BooleanExpression clause1 = universe.lessThanEquals(
				universe.divide((NumericExpression) X, two), universe.oneInt());
		BooleanExpression clause2 = universe.lessThanEquals(threeInt,
				(NumericExpression) X);
		Reasoner r = universe.reasoner(universe.and(clause1, clause2));
		SymbolicExpression x_val = r.constantSubstitutionMap().get(X);

		assertEquals(threeInt, x_val);
		assertEquals(trueExpr, r.getReducedContext());
	}
}
