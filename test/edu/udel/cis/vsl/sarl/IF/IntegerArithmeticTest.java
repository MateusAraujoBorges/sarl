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
	 * Testing the add method for two concrete IntegerNumbers;test: 1 + 2 = 3
	 */
	@Test
	public void addTwoConcreteIntTest() {
		NumericExpression result = universe.add(oneInt, twoInt);

		assertEquals(threeInt, result);
	}

	/**
	 * Testing the add method for two symbolic IntegerNumbers;test: x + 0 = x;
	 */
	@Test
	public void addTwoSymbolicIntTest() {
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(x_obj, intType);
		NumericExpression result = universe.add(x, zero);

		assertEquals(x, result);
	}

	/**
	 * Testing the add method for a sequence of IntegerNumbers;test: 0 + 1 + 2 =
	 * 3; x + 0 = x;
	 */
	@Test
	public void addSeqIntTest() {
		List<NumericExpression> numList = new ArrayList<NumericExpression>();
		List<NumericExpression> numList2 = new ArrayList<NumericExpression>();
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(x_obj, intType);
		NumericExpression result, result1;

		numList.add(zero);
		numList.add(oneInt);
		numList.add(twoInt);
		numList2.add(x);
		numList2.add(zero);
		result = universe.add(numList);
		result1 = universe.add(numList2);
		assertEquals(threeInt, result);
		assertEquals(x, result1);
	}

	/**
	 * Testing the subtract method for two concrete IntegerNumbers;test: 3 - 2 =
	 * 1;
	 */
	@Test
	public void substractConcreteIntTest() {
		NumericExpression result = universe.subtract(threeInt, twoInt);

		assertEquals(oneInt, result);
	}

	/**
	 * Testing the subtract method for two symbolic IntegerNumbers;test: (x + y)
	 * - x = y;
	 */
	@Test
	public void substractSymbolicIntTest() {
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(x_obj, intType);
		NumericExpression y = (NumericExpression) universe
				.symbolicConstant(y_obj, intType);
		NumericExpression result = universe.subtract(universe.add(x, y), x);

		assertEquals(y, result);
	}

	/**
	 * Testing the multiply method for two concrete IntegerNumbers;test: 1 * 2 =
	 * 2;
	 */
	@Test
	public void multiplyTwoConcreteIntTest() {
		NumericExpression result = universe.multiply(oneInt, twoInt);

		assertEquals(twoInt, result);
	}

	/**
	 * Testing the multiply method for symbolic IntegerNumbers;test: x * 0 = 0;
	 */
	@Test
	public void multiplyTwoSymbolicIntTest() {
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(x_obj, intType);
		NumericExpression result = universe.multiply(x, zero);

		assertEquals(zero, result);
	}

	/**
	 * Testing the multiply method for a sequence of IntegerNumbers;test: 1 * 2
	 * = 2; test: x * y * 0 = 0;
	 */
	@Test
	public void multiplySeqIntTest() {
		List<NumericExpression> numList = new ArrayList<NumericExpression>();
		List<NumericExpression> numList2 = new ArrayList<NumericExpression>();
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(x_obj, intType);
		NumericExpression y = (NumericExpression) universe
				.symbolicConstant(y_obj, intType);
		NumericExpression result, result1;

		numList.add(oneInt);
		numList.add(twoInt);
		numList2.add(x);
		numList2.add(y);
		numList2.add(zero);
		result = universe.multiply(numList);
		result1 = universe.multiply(numList2);
		assertEquals(twoInt, result);
		assertEquals(zero, result1);
	}

	/**
	 * Testing the divide method for two concrete IntegerNumbers;test: 2 / 1 =
	 * 2;
	 */
	@Test
	public void divideConcreteIntTest() {
		NumericExpression result = universe.divide(twoInt, oneInt);

		assertEquals(twoInt, result);
	}

	/**
	 * Testing the divide method for symbolic IntegerNumbers;test: 0 / x = 0;
	 */
	@Test
	public void divideSymblicIntTest() {
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(x_obj, intType);
		NumericExpression result2 = universe.divide(zero, x);

		assertEquals(zero, result2);
	}
}
