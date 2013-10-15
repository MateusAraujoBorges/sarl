/* Copyright 2013 Stephen F. Siegel, University of Delaware
 */
package edu.udel.cis.vsl.sarl.ideal.simplify;

import static edu.udel.cis.vsl.sarl.ideal.simplify.CommonObjects.*;
import static org.junit.Assert.*;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * @author danfried
 *
 */
public class SimplifyEqualsZeroTest {

	/**
	 * Calls the setUp() method in CommonObjects to make use of consolidated SARL object 
	 * declarations and initializations for testing of "Simplify" module.
	 * @throws java.lang.Exception
	 */
	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
		CommonObjects.setUp();
		//assumption = preUniv.lessThan(int0, xInt);
		assumption = preUniv.equals(xInt, int0);
		idealSimplifier = idealSimplifierFactory.newSimplifier(assumption);
	}

	/**
	 * @throws java.lang.Exception
	 */
	@Before
	public void setUp() throws Exception {
	}

	/**
	 * @throws java.lang.Exception
	 */
	@After
	public void tearDown() throws Exception {
	}

	/**
	 * Testing of polynomial simplification where factoring results in non-real terms
	 */
	@Test
	public void assumptionTest() {
		//out.println(xSqrLess1);
		//out.println(idealSimplifier.simplifyExpression(xSqrLess1));
		assertEquals(idealSimplifier.simplifyExpression(xSqrLess1), intNeg1);
		assertEquals(idealSimplifier.simplifyExpression(xSqrP1), int1);
		//out.println(idealSimplifier.apply(symbExpr_xpyInt));
		//out.println(idealSimplifier.simplifyExpression(symbExpr_xpyInt));
		//out.println("xx - 1 :  " + xSqrLess1.toString());
		//IdealSimplifier.
		out.println(mixedXYTermPoly);
		out.println(bigMixedXYTermPoly);
		
		assumption = preUniv.equals(x, rat0);
		idealSimplifier = idealSimplifierFactory.newSimplifier(assumption);
		
		//out.println(idealSimplifier.apply(bigMixedXYTermPoly));
		assertEquals(idealSimplifier.apply(bigMixedXYTermPoly).toString(), preUniv.multiply(y, preUniv.multiply(y, y)).toString());
		//out.println(idealSimplifier.simplifyExpression(mixedXYTermPoly));
		assertEquals(idealSimplifier.simplifyExpression(mixedXYTermPoly), y);
	}

}