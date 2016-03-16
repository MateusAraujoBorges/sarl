package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class IntegerArithmeticDevTest {
	public final static PrintStream out = System.out;
	public final static boolean debug = false;
	private SymbolicUniverse universe;
	private NumericExpression negOneInt; // integer -1
	private NumericExpression twoInt; // integer 2
	private NumericExpression threeInt; // integer 3
	private NumericExpression negThreeInt;// integer -3
	private NumericExpression negFourInt; // integer -4
	private NumericExpression fourInt; // integer 4
	private NumericExpression x, y, z;
	private StringObject x_obj, y_obj, z_obj; // "x", "y", "z"
	private SymbolicType intType;

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		negOneInt = universe.integer(-1);
		twoInt = universe.integer(2);
		threeInt = universe.integer(3);
		negThreeInt = universe.integer(-3);
		fourInt = universe.integer(4);
		negFourInt = universe.integer(-4);
		x_obj = universe.stringObject("x");
		y_obj = universe.stringObject("y");
		z_obj = universe.stringObject("z");
		intType = universe.integerType();
		x = (NumericExpression) universe.symbolicConstant(x_obj, intType);
		y = (NumericExpression) universe.symbolicConstant(y_obj, intType);
		z = (NumericExpression) universe.symbolicConstant(z_obj, intType);
	}

	@After
	public void tearDown() throws Exception {
	}

	/**
	 * Negative exponent power test.
	 */
	@Test
	public void negativeExponentPowerTest() {
		NumericExpression e = universe.power(x, negOneInt);

		assertEquals(universe.divide(universe.oneInt(), x), e);
	}
}