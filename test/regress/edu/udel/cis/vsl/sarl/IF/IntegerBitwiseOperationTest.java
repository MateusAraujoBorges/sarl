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
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class IntegerBitwiseOperationTest {
	private final static PrintStream OUT = System.out;
	private final static boolean DEBUG = false;
	private final static int INTEGER_BIT_LENGTH = 32;

	private SymbolicUniverse universe;
	private SymbolicType intType;
	private SymbolicCompleteArrayType bitVectorType;
	private NumericExpression intZero; // integer 0
	private NumericExpression intOne; // integer 1
	private NumericExpression intMax; // integer -4
	private StringObject obj_x, obj_y;
	private NumericExpression x, y;

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		intType = universe.integerType();
		bitVectorType = universe.bitVectorType(INTEGER_BIT_LENGTH);
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
		SymbolicExpression bv_intZero = universe.integer2Bitvector(intZero,
				bitVectorType);
		SymbolicExpression bv_intOne = universe.integer2Bitvector(intOne,
				bitVectorType);
		SymbolicExpression bitandResult = universe
				.bitand(bv_intZero, bv_intOne);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitandResult);
		NumericExpression expectedResult = universe.integer(0);

		p("Expression: 0 & 1");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitand_SymbolicExpression_x_y() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_y = universe.integer2Bitvector(y, bitVectorType);
		SymbolicExpression bitandResult = universe.bitand(bv_x, bv_y);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitandResult);
		// NumericExpression expectedResult = universe.integer(0);

		p("Expression: x & y");
		// p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
	}

	/**
	 * Expression: x & 0; [x] & [0x00000000] <br>
	 * Expected: 0; [0x00000000]
	 */
	@Test
	public void bitand_Mixed_x_intZero() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_intZero = universe.integer2Bitvector(intZero,
				bitVectorType);
		SymbolicExpression bitandResult = universe.bitand(bv_x, bv_intZero);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitandResult);
		NumericExpression expectedResult = universe.integer(0);

		p("Expression: x & 0");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitand_Mixed_x_intOne() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_intOne = universe.integer2Bitvector(intOne,
				bitVectorType);
		SymbolicExpression bitandResult = universe.bitand(bv_x, bv_intOne);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitandResult);
		// NumericExpression expectedResult = universe.integer(0);

		p("Expression: x & 1");
		// p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
	}

	/**
	 * Expression: x & ~0; [x] & ~[0x00000000] <br>
	 * Expected: x; [x]
	 */
	@Test
	public void bitand_Mixed_x_NotintZero() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_intZero = universe.integer2Bitvector(intZero,
				bitVectorType);
		SymbolicExpression bitandResult = universe.bitand(bv_x,
				universe.bitnot(bv_intZero));
		NumericExpression actualResult = universe
				.bitvector2Integer(bitandResult);
		NumericExpression expectedResult = universe.bitvector2Integer(bv_x);

		p("Expression: x & ~0");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitand_Mixed_x_NotintOne() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_intOne = universe.integer2Bitvector(intOne,
				bitVectorType);
		SymbolicExpression bitandResult = universe.bitand(bv_x,
				universe.bitnot(bv_intOne));
		NumericExpression actualResult = universe
				.bitvector2Integer(bitandResult);
		// NumericExpression expectedResult = universe.integer(0);

		p("Expression: x & ~1");
		// p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
	}

	/**
	 * Expression: 0 | 1; [0x00000000] | [0x00000001] <br>
	 * Expected: 1; [0x00000001]
	 */
	@Test
	public void bitor_ConcreteNumbers_intZero_intOne() {
		SymbolicExpression bv_intZero = universe.integer2Bitvector(intZero,
				bitVectorType);
		SymbolicExpression bv_intOne = universe.integer2Bitvector(intOne,
				bitVectorType);
		SymbolicExpression bitorResult = universe.bitor(bv_intZero, bv_intOne);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitorResult);
		NumericExpression expectedResult = universe.integer(1);

		p("Expression: 0 | 1");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitor_SymbolicExpression_x_y() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_y = universe.integer2Bitvector(y, bitVectorType);
		SymbolicExpression bitorResult = universe.bitor(bv_x, bv_y);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitorResult);
		// NumericExpression expectedResult = universe.integer(0);

		p("Expression: x | y");
		// p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
	}

	/**
	 * Expression: x | 0; [x] & [0x00000000] <br>
	 * Expected: x; [x]
	 */
	@Test
	public void bitor_Mixed_x_intZero() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_intZero = universe.integer2Bitvector(intZero,
				bitVectorType);
		SymbolicExpression bitorResult = universe.bitor(bv_x, bv_intZero);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitorResult);
		NumericExpression expectedResult = universe.bitvector2Integer(bv_x);

		p("Expression: x | 0");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitor_Mixed_x_intOne() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_intOne = universe.integer2Bitvector(intOne,
				bitVectorType);
		SymbolicExpression bitorResult = universe.bitor(bv_x, bv_intOne);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitorResult);
		// NumericExpression expectedResult = universe.integer(0);

		p("Expression: x | 1");
		// p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
	}

	/**
	 * Expression: x | ~0; [x] & ~[0x00000000] <br>
	 * Expected: ~0 = 4294967295 ; [0xffffffff]
	 */
	@Test
	public void bitor_Mixed_x_NotintZero() {
		long resLong = ((long) Integer.MAX_VALUE) * 2 + 1;
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_intZero = universe.integer2Bitvector(intZero,
				bitVectorType);
		SymbolicExpression bitorResult = universe.bitor(bv_x,
				universe.bitnot(bv_intZero));
		NumericExpression actualResult = universe
				.bitvector2Integer(bitorResult);
		NumericExpression expectedResult = universe.integer(resLong);

		p("Expression: x | ~0");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitor_Mixed_x_NotintOne() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_intOne = universe.integer2Bitvector(intOne,
				bitVectorType);
		SymbolicExpression bitorResult = universe.bitor(bv_x,
				universe.bitnot(bv_intOne));
		NumericExpression actualResult = universe
				.bitvector2Integer(bitorResult);
		// NumericExpression expectedResult = universe.integer(0);

		p("Expression: x | ~1");
		// p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
	}

	/**
	 * Expression: 0 ^ 1; [0x00000000] & [0x00000001] <br>
	 * Expected: 1; [0x00000001]
	 */
	@Test
	public void bitxor_ConcreteNumbers_intZero_intOne() {
		SymbolicExpression bv_intZero = universe.integer2Bitvector(intZero,
				bitVectorType);
		SymbolicExpression bv_intOne = universe.integer2Bitvector(intOne,
				bitVectorType);
		SymbolicExpression bitxorResult = universe
				.bitxor(bv_intZero, bv_intOne);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitxorResult);
		NumericExpression expectedResult = universe.integer(1);

		p("Expression: 0 ^ 1");
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
		SymbolicExpression bv_intZero = universe.integer2Bitvector(
				universe.integer(858993459), bitVectorType);
		SymbolicExpression bv_intOne = universe.integer2Bitvector(
				universe.integer(1431655765), bitVectorType);
		SymbolicExpression bitxorResult = universe
				.bitxor(bv_intZero, bv_intOne);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitxorResult);
		NumericExpression expectedResult = universe.integer(1717986918);

		p("Expression: 858993459 ^ 1431655765");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitxor_SymbolicExpression_x_y() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_y = universe.integer2Bitvector(y, bitVectorType);
		SymbolicExpression bitxorResult = universe.bitxor(bv_x, bv_y);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitxorResult);
		// NumericExpression expectedResult = universe.integer(0);

		p("Expression: x ^ y");
		// p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
	}

	/**
	 * Expression: x ^ 0; [x] & [0x00000000] <br>
	 * Expected: x; [x]
	 */
	@Test
	public void bitxor_Mixed_x_intZero() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_intZero = universe.integer2Bitvector(intZero,
				bitVectorType);
		SymbolicExpression bitxorResult = universe.bitxor(bv_x, bv_intZero);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitxorResult);
		NumericExpression expectedResult = universe.bitvector2Integer(bv_x);

		p("Expression: x ^ 0");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitxor_Mixed_x_intOne() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_intOne = universe.integer2Bitvector(intOne,
				bitVectorType);
		SymbolicExpression bitxorResult = universe.bitxor(bv_x, bv_intOne);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitxorResult);
		// NumericExpression expectedResult = universe.integer(0);

		p("Expression: x ^ 1");
		// p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
	}

	/**
	 * Expression: x ^ ~0; [x] & ~[0x00000000] <br>
	 * Expected: ~x; ~[x]
	 */
	@Test
	public void bitxor_Mixed_x_NotintZero() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_intZero = universe.integer2Bitvector(intZero,
				bitVectorType);
		SymbolicExpression bitxorResult = universe.bitxor(bv_x,
				universe.bitnot(bv_intZero));
		NumericExpression actualResult = universe
				.bitvector2Integer(bitxorResult);
		NumericExpression expectedResult = universe.bitvector2Integer(universe
				.bitnot(bv_x));

		p("Expression: x ^ ~0");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitxor_Mixed_x_NotintOne() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_intOne = universe.integer2Bitvector(intOne,
				bitVectorType);
		SymbolicExpression bitxorResult = universe.bitxor(bv_x,
				universe.bitnot(bv_intOne));
		NumericExpression actualResult = universe
				.bitvector2Integer(bitxorResult);
		// NumericExpression expectedResult = universe.integer(0);

		p("Expression: x ^ ~1");
		// p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
	}

	/**
	 * Expression: ~0; ~[0x00000000]<br>
	 * Expected: 2^32-1 = 4294967295; [0xffffffff]
	 */
	@Test
	public void bitnot_intZero() {
		long resLong = ((long) Integer.MAX_VALUE) * 2 + 1;
		SymbolicExpression bv_intZero = universe.integer2Bitvector(intZero,
				bitVectorType);
		SymbolicExpression bitnotResult = universe.bitnot(bv_intZero);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitnotResult);
		NumericExpression expectedResult = universe.integer(resLong);

		p("Expression: ~0");
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
		SymbolicExpression bv_intMax = universe.integer2Bitvector(intMax,
				bitVectorType);
		SymbolicExpression bitnotResult = universe.bitnot(bv_intMax);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitnotResult);
		NumericExpression expectedResult = universe
				.integer(((long) Integer.MAX_VALUE) + 1);

		p("Expression: ~2147483647");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void bitnot_x() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bitnotResult = universe.bitnot(bv_x);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitnotResult);
		// NumericExpression expectedResult = universe
		// .integer(((long) Integer.MAX_VALUE) + 1);

		p("Expression: ~x");
		// p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
	}

	/**
	 * Expression: ~(~x); ~(~[x])<br>
	 * Expected: x; [x]
	 */
	@Test
	public void bitnot_Notx() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bitnotResult = universe
				.bitnot(universe.bitnot(bv_x));
		NumericExpression actualResult = universe
				.bitvector2Integer(bitnotResult);
		NumericExpression expectedResult = universe.bitvector2Integer(bv_x);

		p("Expression: ~(~x)");
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
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_y = universe.integer2Bitvector(y, bitVectorType);
		SymbolicExpression bitwiseResult1 = universe.bitnot(universe.bitand(
				bv_x, bv_y));
		SymbolicExpression bitwiseResult2 = universe.bitor(
				universe.bitnot(bv_x), universe.bitnot(bv_y));
		NumericExpression actualResult = universe
				.bitvector2Integer(bitwiseResult1);
		NumericExpression expectedResult = universe
				.bitvector2Integer(bitwiseResult2);

		p("Expression: ~ (x & y)");
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
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_y = universe.integer2Bitvector(y, bitVectorType);
		SymbolicExpression bitwiseResult1 = universe.bitnot(universe.bitor(
				bv_x, bv_y));
		SymbolicExpression bitwiseResult2 = universe.bitand(
				universe.bitnot(bv_x), universe.bitnot(bv_y));
		NumericExpression actualResult = universe
				.bitvector2Integer(bitwiseResult1);
		NumericExpression expectedResult = universe
				.bitvector2Integer(bitwiseResult2);

		p("Expression: ~ (x | y)");
		p("ExpectedResult: " + expectedResult.atomString());
		p("ActualResult  : " + actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	@Test
	public void simplyficationTest() {
		SymbolicExpression bv_x = universe.integer2Bitvector(x, bitVectorType);
		SymbolicExpression bv_4 = universe.integer2Bitvector(
				universe.integer(4), bitVectorType);
		SymbolicExpression bv_x_and_4 = universe.bitand(bv_x, bv_4);
		SymbolicExpression x_and_4 = universe.bitvector2Integer(bv_x_and_4);
		SymbolicExpression resExpr = universe.neq(x_and_4, intZero);

		p(resExpr);
	}
}
