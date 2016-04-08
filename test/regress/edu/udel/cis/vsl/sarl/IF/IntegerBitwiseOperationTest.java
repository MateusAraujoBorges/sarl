package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.io.PrintStream;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;

public class IntegerBitwiseOperationTest {
	public final static PrintStream OUT = System.out;
	public final static boolean DEBUG = true;
	private SymbolicUniverse universe;
	// private SymbolicType intType;
	private SymbolicCompleteArrayType bitVectorType;
	private NumericExpression intNegFour; // integer -4
	private NumericExpression intNegOne; // integer -1
	private NumericExpression intZero; // integer 0
	private NumericExpression intPosOne; // integer 1

	// private NumericExpression x, y, z;
	// private StringObject x_obj, y_obj, z_obj; // "x", "y", "z"

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		// intType = universe.integerType();
		intNegFour = universe.integer(-4);
		intNegOne = universe.integer(-1);
		intZero = universe.integer(0);
		intPosOne = universe.integer(1);
		bitVectorType = universe.bitVectorType(32);

		// x_obj = universe.stringObject("x");
		// y_obj = universe.stringObject("y");
		// z_obj = universe.stringObject("z");
		// x = (NumericExpression) universe.symbolicConstant(x_obj, intType);
		// y = (NumericExpression) universe.symbolicConstant(y_obj, intType);
		// z = (NumericExpression) universe.symbolicConstant(z_obj, intType);
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
	 * Expression: 1 & 0; <br>
	 * Expected: 0;
	 */
	@Test
	public void bitand_concreteNumbers_intPosOne_intZero() {
		SymbolicExpression bv_intZero = universe.integer2Bitvector(intZero,
				bitVectorType);
		SymbolicExpression bv_intPosOne = universe.integer2Bitvector(intPosOne,
				bitVectorType);
		SymbolicExpression bitandResult = universe.bitand(bv_intZero,
				bv_intPosOne);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitandResult);
		NumericExpression expectedResult = universe.integer(0);

		p(actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	/**
	 * Expression: -1 & 1; <br>
	 * Expected: 1;
	 */
	@Test
	public void bitand_concreteNumbers_intNegOne_intPosOne() {
		SymbolicExpression bv_intPosOne = universe.integer2Bitvector(intPosOne,
				bitVectorType);
		SymbolicExpression bv_intNegOne = universe.integer2Bitvector(intNegOne,
				bitVectorType);
		SymbolicExpression bitandResult = universe.bitand(bv_intPosOne,
				bv_intNegOne);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitandResult);
		NumericExpression expectedResult = universe.integer(1);

		p(actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}

	/**
	 * Expression: -4 & 1; <br>
	 * Expected: -3;
	 */
	@Test
	public void bitor_concreteNumbers_intNegFour_intPosOne() {
		SymbolicExpression bv_intNegFour = universe.integer2Bitvector(
				intNegFour, bitVectorType);
		p(bv_intNegFour);
		SymbolicExpression bv_intPosOne = universe.integer2Bitvector(intPosOne,
				bitVectorType);
		p(bv_intPosOne);
		SymbolicExpression bitorResult = universe.bitor(bv_intNegFour,
				bv_intPosOne);
		p(bitorResult);
		NumericExpression actualResult = universe
				.bitvector2Integer(bitorResult);
		NumericExpression expectedResult = universe.integer(-3);

		p(actualResult.atomString());
		assertEquals(expectedResult, actualResult);
	}
}
