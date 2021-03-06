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
package edu.udel.cis.vsl.sarl.ideal;

import static org.junit.Assert.assertEquals;

import java.io.PrintStream;

import org.junit.After;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.object.NumberObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.ideal.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.preuniverse.IF.FactorySystem;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverses;
import edu.udel.cis.vsl.sarl.type.IF.SymbolicTypeFactory;

/**
 * The class IdealPowerTest tests methods found in the
 * edu.udel.cis.vsl.sarl.ideal.common package using exponentials
 * 
 * This class has a method bigPower which finds the result for [(x+y)^100] /
 * [(x+y)^99] as (x+y) by removing all the common factors This test method is
 * one of the good benchmarks by which we can evaluate the performance.
 *
 */
public class IdealPowerTest {

	private static PrintStream out = System.out;
	private ObjectFactory objectFactory;
	private SymbolicTypeFactory typeFactory;
	private IdealFactory idealFactory;
	private NumberFactory numberFactory;
	/**
	 * int constant -1
	 */
	private Constant intNegOne;
	/**
	 * int constant 0
	 */
	private Constant intZero;
	/**
	 * int constant 1
	 */
	private Constant intOne;
	/**
	 * int constant 2
	 */
	private Constant intTwo;
	/**
	 * "X"
	 */
	StringObject Xobj;
	/**
	 * int symbolic constant "X"
	 */
	NumericSymbolicConstant x;
	/**
	 * int symbolic constant "Y"
	 */
	NumericSymbolicConstant y;

	@Before
	public void setUp() throws Exception {
		FactorySystem system = PreUniverses.newIdealFactorySystem();
		objectFactory = system.objectFactory();
		typeFactory = system.typeFactory();
		idealFactory = (IdealFactory) system.numericFactory();
		numberFactory = idealFactory.numberFactory();
		intNegOne = idealFactory.intConstant(-1);
		intZero = idealFactory.zeroInt();
		intOne = idealFactory.intConstant(1);
		intTwo = idealFactory.intConstant(2);
		Xobj = objectFactory.stringObject("X");
		x = objectFactory.canonic(
				idealFactory.symbolicConstant(Xobj, typeFactory.integerType()));
		y = objectFactory.canonic(idealFactory.symbolicConstant(
				objectFactory.stringObject("Y"), typeFactory.integerType()));
	}

	@After
	public void tearDown() throws Exception {

	}

	/**
	 * a function - power() which has NumericExpression as base and IntObject as
	 * an exponent
	 * 
	 * @param a
	 *            - NumericExpression
	 * @param b
	 *            - NumberObject
	 * 
	 * @return the value of an expression consisting of numeric expression as
	 *         base and IntObject as power
	 */
	public NumericExpression power(NumericExpression a, NumberObject b) {
		NumericExpression ne = idealFactory.power(a, b);
		return ne;
	}

	/**
	 * Creates a numeric expression 0^0, which should raise a SARLException
	 */
	@Test(expected = SARLException.class)
	public void zeroToZero() {
		NumericExpression ztz = idealFactory.power(intZero, intZero);
		out.println("ztz= " + ztz);
	}

	/**
	 * Creates a numeric expression 1^-1, which should raise a SARLException
	 */
	@Test(expected = SARLException.class)
	public void negativeExponent() {
		NumericExpression negExp = idealFactory.power(intOne, intNegOne);
		out.println("negExp= " + negExp);
	}

	/**
	 * Asserts that (x+1)^2 = x^2 + 2*x + 1
	 * 
	 * @param type
	 *            SymbolicExpression of numeric type
	 */
	// ignoring for now because this now requires simplification
	@Test
	@Ignore
	public void xPlus1Squared() {
		NumericExpression xp1 = idealFactory.add(x, intOne);
		NumericExpression xp1squared = idealFactory.multiply(xp1, xp1);
		NumericExpression x2p2xp1 = idealFactory.add(
				idealFactory.multiply(x, x),
				idealFactory.add(idealFactory.multiply(intTwo, x), intOne));

		out.println("xplus1squared: " + xp1squared + " vs. " + x2p2xp1);

		NumericExpression diff = idealFactory.subtract(xp1squared, x2p2xp1);

		assertEquals(intZero, diff);
	}

	/**
	 * gives the result for [(x+y)^100] / [(x+y)^99] as (x+y). Will compute the
	 * values for [(x+y)^100] first and also compute the value for [(x+y)^99],
	 * divide both of them and remove the common factors which will be equal to
	 * (x + y).
	 * 
	 * @param type
	 *            SymbolicExpression of numeric type
	 */
	@Test
	public void bigPower() {
		int exponent = 100;
		NumberObject n = objectFactory.numberObject(numberFactory.integer(exponent));
		NumberObject m = objectFactory.numberObject(numberFactory.integer(exponent - 1));
		NumericExpression xpy = idealFactory.add(x, y);
		NumericExpression xpyen = power(xpy, n);
		NumericExpression xpyem = power(xpy, m);
		NumericExpression quotient = idealFactory.divide(xpyen, xpyem);

		out.println("bigPower: (X+Y)^" + n + " = " + xpyen);
		out.println("bigPower: (X+Y)^" + m + " = " + xpyem);
		out.println("bigPower: quotient : " + quotient);

		assertEquals(xpy, quotient);
	}
}