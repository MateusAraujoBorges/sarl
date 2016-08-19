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

public class IntegerBitwiseOperationTest {
	private final static PrintStream OUT = System.out;
	private final static boolean DEBUG = true;

	private SymbolicUniverse universe;
	private SymbolicType intType;
	private NumericExpression intZero; // integer 0
	private NumericExpression intOne; // integer 1
	private NumericExpression intMax; // integer -4
	private StringObject obj_x, obj_y;
	private NumericExpression x, y;

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		intType = universe.integerType();
		intZero = universe.integer(0);
		intOne = universe.integer(1);
		intMax = universe.integer(Integer.MAX_VALUE);
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
	 * Expression: 0 & 1; [0x00000000] & [0x00000001] <br>
	 * Expected: 0; [0x00000000]
	 */
	@Test
	public void bitand_ConcreteNumbers_intZero_intOne() {
		SymbolicExpression actualResult = universe.bitand(intZero, intOne);
		NumericExpression expectedResult = universe.integer(0);

		p("\nExpression: 0 & 1");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitand_SymbolicExpression_x_y() {
		SymbolicExpression actualResult = universe.bitand(x, y);
		String actualStr = actualResult.toString();
		String expectedStr = "x & y";

		p("\nExpression: x & y");
		p("ActualResult  : " + actualStr);
		p("ExpectedResult  : " + expectedStr);
		assertEquals(expectedStr, actualStr);
	}

	/**
	 * Expression: x & 0; [x] & [0x00000000] <br>
	 * Expected: 0; [0x00000000]
	 */
	@Test
	public void bitand_Mixed_x_intZero() {
		SymbolicExpression actualResult = universe.bitand(x, intZero);
		NumericExpression expectedResult = universe.integer(0);

		p("\nExpression: x & 0");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitand_Mixed_x_intOne() {
		SymbolicExpression actualResult = universe.bitand(x, intOne);
		String actualStr = actualResult.toString();
		String expectedStr = "x & 1";

		p("\nExpression: x & 1");
		p("ActualResult  : " + actualStr);
		p("ExpectedResult  : " + expectedStr);
		assertEquals(expectedStr, actualStr);
	}

	/**
	 * Expression: x & ~0; [x] & ~[0x00000000] <br>
	 * Expected: x; [x]
	 */
	@Test
	public void bitand_Mixed_x_NotintZero() {
		SymbolicExpression actualResult = universe.bitand(x,
				universe.bitnot(intZero));
		NumericExpression expectedResult = x;

		p("\nExpression: x & ~0");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitand_Mixed_x_NotintOne() {
		SymbolicExpression actualResult = universe.bitand(x,
				universe.bitnot(intOne));
		String actualStr = actualResult.toString();
		String expectedStr = "x & 4294967294";
		// As an unsigned integer with 32bit, ~1 = 4294967294

		p("\nExpression: x & ~1");
		p("ActualResult  : " + actualStr);
		p("ExpectedResult  : " + expectedStr);
		assertEquals(expectedStr, actualStr);
	}

	/**
	 * Expression: 0 | 1; [0x00000000] | [0x00000001] <br>
	 * Expected: 1; [0x00000001]
	 */
	@Test
	public void bitor_ConcreteNumbers_intZero_intOne() {
		SymbolicExpression actualResult = universe.bitor(intZero, intOne);
		NumericExpression expectedResult = intOne;

		p("\nExpression: 0 | 1");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitor_SymbolicExpression_x_y() {
		SymbolicExpression actualResult = universe.bitor(x, y);
		String actualStr = actualResult.toString();
		String expectedStr = "x | y";

		p("\nExpression: x | y");
		p("ActualResult  : " + actualStr);
		p("ExpectedResult  : " + expectedStr);
		assertEquals(expectedStr, actualStr);
	}

	/**
	 * Expression: x | 0; [x] & [0x00000000] <br>
	 * Expected: x; [x]
	 */
	@Test
	public void bitor_Mixed_x_intZero() {
		SymbolicExpression actualResult = universe.bitor(x, intZero);
		NumericExpression expectedResult = x;

		p("\nExpression: x | 0");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitor_Mixed_x_intOne() {
		SymbolicExpression actualResult = universe.bitor(x, intOne);
		String actualStr = actualResult.toString();
		String expectedStr = "x | 1";

		p("\nExpression: x | 1");
		p("ActualResult  : " + actualStr);
		p("ExpectedResult  : " + expectedStr);
		assertEquals(expectedStr, actualStr);
	}

	/**
	 * Expression: x | ~0; [x] & ~[0x00000000] <br>
	 * Expected: ~0 = 4294967295 ; [0xffffffff]
	 */
	@Test
	public void bitor_Mixed_x_NotintZero() {
		long resLong = ((long) Integer.MAX_VALUE) * 2 + 1;
		SymbolicExpression actualResult = universe.bitor(x,
				universe.bitnot(intZero));
		NumericExpression expectedResult = universe.integer(resLong);

		p("\nExpression: x | ~0");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitor_Mixed_x_NotintOne() {
		NumericExpression actualResult = universe.bitor(x,
				universe.bitnot(intOne));
		String actualStr = actualResult.toString();
		String expectedStr = "x | 4294967294";
		// As an unsigned integer with 32bit, ~1 = 4294967294

		p("\nExpression: x | ~1");
		p("ActualResult  : " + actualStr);
		p("ExpectedResult  : " + expectedStr);
		assertEquals(expectedStr, actualStr);
	}

	/**
	 * Expression: 0 ^ 1; [0x00000000] & [0x00000001] <br>
	 * Expected: 1; [0x00000001]
	 */
	@Test
	public void bitxor_ConcreteNumbers_intZero_intOne() {
		NumericExpression actualResult = universe.bitxor(intZero, intOne);
		NumericExpression expectedResult = intOne;

		p("\nExpression: 0 ^ 1");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}
	
	/**
	 * Expression: 0 ^ 0; [0x00000000] & [0x00000000] <br>
	 * Expected: 0; [0x00000000]
	 */
	@Test
	public void bitxor_ConcreteNumbers_intZero_intZero() {
		NumericExpression actualResult = universe.bitxor(intZero, intZero);
		NumericExpression expectedResult = intZero;

		p("\nExpression: 0 ^ 1");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	/**
	 * Expression: 858993459 ^ 1431655765; [0x33333333] & [0x55555555] <br>
	 * Expected: 1717986918; [0x66666666]
	 */
	@Test
	public void bitxor_ConcreteNumbers_Extra() {
		NumericExpression actualResult = universe.bitxor(universe.integer(858993459), universe.integer(1431655765));
		NumericExpression expectedResult = universe.integer(1717986918);

		p("\nExpression: 858993459 ^ 1431655765");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitxor_SymbolicExpression_x_y() {
		SymbolicExpression actualResult = universe.bitxor(x, y);
		String actualStr = actualResult.toString();
		String expectedStr = "x ^ y";

		p("\nExpression: x ^ y");
		p("ActualResult  : " + actualStr);
		p("ExpectedResult  : " + expectedStr);
		assertEquals(expectedStr, actualStr);
	}

	/**
	 * Expression: x ^ 0; [x] & [0x00000000] <br>
	 * Expected: x; [x]
	 */
	@Test
	public void bitxor_Mixed_x_intZero() {
		SymbolicExpression actualResult = universe.bitxor(x, intZero);
		NumericExpression expectedResult = x;

		p("\nExpression: x ^ 0");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitxor_Mixed_x_intOne() {
		SymbolicExpression actualResult = universe.bitxor(x, intOne);
		String actualStr = actualResult.toString();
		String expectedStr = "x ^ 1";

		p("\nExpression: x ^ 1");
		p("ActualResult  : " + actualStr);
		p("ExpectedResult  : " + expectedStr);
		assertEquals(expectedStr, actualStr);
	}

	/**
	 * Expression: x ^ ~0; [x] & ~[0x00000000] <br>
	 * Expected: ~x; ~[x]
	 */
	@Test
	public void bitxor_Mixed_x_NotintZero() {
		SymbolicExpression actualResult = universe.bitxor(x,
				universe.bitnot(intZero));
		NumericExpression expectedResult = universe.bitnot(x);

		p("\nExpression: x ^ ~0");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitxor_Mixed_x_NotintOne() {
		SymbolicExpression actualResult = universe.bitxor(x,
				universe.bitnot(intOne));
		String actualStr = actualResult.toString();
		String expectedStr = "x ^ 4294967294";
		// As an unsigned integer with 32bit, ~1 = 4294967294

		p("\nExpression: x ^ ~1");
		p("ActualResult  : " + actualStr);
		p("ExpectedResult  : " + expectedStr);
		assertEquals(expectedStr, actualStr);
	}

	/**
	 * Expression: ~0; ~[0x00000000]<br>
	 * Expected: 2^32-1 = 4294967295; [0xffffffff]
	 */
	@Test
	public void bitnot_intZero() {
		long resLong = ((long) Integer.MAX_VALUE) * 2 + 1;
		SymbolicExpression actualResult = universe.bitnot(intZero);
		NumericExpression expectedResult = universe.integer(resLong);

		p("\nExpression: ~0");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	/**
	 * Expression: ~2147483647; ~[0x7fffffff]<br>
	 * Expected: 2147483648; [0x80000000]
	 */
	@Test
	public void bitnot_intMax() {
		SymbolicExpression actualResult = universe.bitnot(intMax);
		NumericExpression expectedResult = universe
				.integer(((long) Integer.MAX_VALUE) + 1);

		p("\nExpression: ~2147483647");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitnot_x() {
		SymbolicExpression actualResult = universe.bitnot(x);
		String actualStr = actualResult.toString();
		String expectedStr = "~x";
		// As an unsigned integer with 32bit, ~1 = 4294967294

		p("\nExpression: ~x");
		p("ActualResult  : " + actualStr);
		p("ExpectedResult  : " + expectedStr);
		assertEquals(expectedStr, actualStr);
	}

	/**
	 * Expression: ~(~x); ~(~[x])<br>
	 * Expected: x; [x]
	 */
	@Test
	public void bitnot_Notx() {
		SymbolicExpression actualResult = universe.bitnot(universe.bitnot(x));
		NumericExpression expectedResult = x;

		p("\nExpression: ~(~x)");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	/**
	 * Expression: ~ (x & y);<br>
	 * Expected: (~x | ~y);
	 */
	@Test
	public void bitnot_xBITANDy() {
		SymbolicExpression actualResult = universe
				.bitnot(universe.bitand(x, y));
		SymbolicExpression expectedResult = universe.bitor(universe.bitnot(x),
				universe.bitnot(y));

		p("\nExpression: ~ (x & y)");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	/**
	 * Expression: ~ (x | y);<br>
	 * Expected: (~x & ~y);
	 */
	@Test
	public void bitnot_xBITORy() {
		SymbolicExpression actualResult = universe.bitnot(universe.bitor(x, y));
		SymbolicExpression expectedResult = universe.bitand(universe.bitnot(x),
				universe.bitnot(y));

		p("\nExpression: ~ (x | y)");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void simplyficationTest() {
		NumericExpression x_or_4 = universe.bitand(universe.integer(15), universe.integer(8));
		SymbolicExpression actualResult = universe.bitor(x_or_4, y);
		SymbolicExpression expectedResult = universe.bitor(universe.integer(8),y);

		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}
}
