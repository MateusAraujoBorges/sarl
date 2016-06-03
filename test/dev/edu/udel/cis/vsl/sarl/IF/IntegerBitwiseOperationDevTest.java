package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.io.PrintStream;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class IntegerBitwiseOperationDevTest {
	private final static PrintStream OUT = System.out;
	private final static boolean DEBUG = false;

	private SymbolicUniverse universe;
	private SymbolicType intType;
	private StringObject obj_x, obj_y;
	private NumericExpression x, y;

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		intType = universe.integerType();
		obj_x = universe.stringObject("x");
		obj_y = universe.stringObject("y");
		x = (NumericExpression) universe.symbolicConstant(obj_x, intType);
		y = (NumericExpression) universe.symbolicConstant(obj_y, intType);
	}

	@After
	public void tearDown() throws Exception {
	}

	/**
	 * Debugging printing function
	 * 
	 * @param o
	 *            Target {@link Object} should be printed.
	 */
	private void p(Object o) {
		if (DEBUG) {
			OUT.println(o);
		}
	}

	/**
	 * x & y | y = y
	 */
	@Test
	public void bitnot_xBITANDyBITORy() {
		SymbolicExpression actualResult = universe.bitor(
				universe.bitand(x, y), y);
		NumericExpression expectedResult = y;

		p("Expression: x & y | y");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}
}
