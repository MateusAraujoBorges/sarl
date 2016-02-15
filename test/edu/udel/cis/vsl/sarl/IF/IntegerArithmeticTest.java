package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class IntegerArithmeticTest {
	SymbolicUniverse universe = SARL.newStandardUniverse();
	private NumericExpression zero = universe.integer(0); 
	private NumericExpression oneInt = universe.integer(1); 
	private NumericExpression twoInt = universe.integer(2); 
	private NumericExpression threeInt = universe.integer(3);
	private StringObject x_obj = universe.stringObject("x");
	private StringObject y_obj = universe.stringObject("y");
	private SymbolicType intType = universe.integerType();

	/**
	 * Testing the add method for two IntegerNumbers.
	 */
	@Test
	public void addTwoIntTest() {
		/**
		 * concrete test: 1 + 2 = 3
		 */
		NumericExpression result = universe.add(oneInt, twoInt);
		assertEquals(threeInt, result);
		/**
		 * symbolic test: x + 0 = x;
		 */
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(x_obj, intType);
		NumericExpression result1 = universe.add(x, zero);
		assertEquals(x, result1);
	}

	/**
	 * Testing the add method for a sequence of IntegerNumbers.
	 */
	@Test
	public void addSeqTest() {
		List<NumericExpression> numList = new ArrayList<NumericExpression>();
		List<NumericExpression> numList2 = new ArrayList<NumericExpression>();
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(x_obj, intType);
		numList.add(zero);
		numList.add(oneInt);
		numList.add(twoInt);
		numList2.add(x);
		numList2.add(zero);
		NumericExpression result = universe.add(numList);
		NumericExpression result1 = universe.add(numList2);
		assertEquals(threeInt, result);
		assertEquals(x, result1);
	}

	/**
	 * Testing the subtract method for two IntegerNumbers.
	 */
	@Test
	public void substractIntTest() {
		/**
		 * concrete test: 3 - 2 = 1
		 */
		NumericExpression result = universe.subtract(threeInt, twoInt);
		assertEquals(oneInt, result);

		/**
		 * symbolic test: (x + y) - x = y;
		 */
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(x_obj, intType);
		NumericExpression y = (NumericExpression) universe
				.symbolicConstant(y_obj, intType);
		NumericExpression result2 = universe.subtract(universe.add(x, y), x);
		assertEquals(y, result2);
	}
}
