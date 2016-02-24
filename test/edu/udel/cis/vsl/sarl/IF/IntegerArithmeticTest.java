package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;
import java.util.ArrayList;
import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class IntegerArithmeticTest {
	private SymbolicUniverse universe;
	private NumericExpression twoInt;
	private NumericExpression threeInt;
	private StringObject x_obj;
	private StringObject y_obj;
	private SymbolicType intType;

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		twoInt = universe.integer(2);
		threeInt = universe.integer(3);
		x_obj = universe.stringObject("x");
		y_obj = universe.stringObject("y");
		intType = universe.integerType();
	}

	@After
	public void tearDown() throws Exception {
	}

	/**
	 * Testing the add method for two concrete IntegerNumbers;test: 1 + 2 = 3
	 */
	@Test
	public void addTwoConcreteIntTest() {
		NumericExpression result = universe.add(universe.oneInt(), twoInt);

		assertEquals(threeInt, result);
	}

	/**
	 * Testing the add method for two symbolic IntegerNumbers;test: x + 0 = x;
	 */
	@Test
	public void addTwoSymbolicIntTest() {
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(x_obj, intType);
		NumericExpression result = universe.add(x, universe.zeroInt());

		assertEquals(x, result);
	}

	/**
	 * Testing the add method for a sequence of IntegerNumbers; test: 0 + 1 + 2
	 * = 3; x + 0 = x;
	 */
	@Test
	public void addSeqIntTest() {
		List<NumericExpression> numList = new ArrayList<NumericExpression>();
		List<NumericExpression> numList2 = new ArrayList<NumericExpression>();
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(x_obj, intType);
		NumericExpression result, result1;

		numList.add(universe.zeroInt());
		numList.add(universe.oneInt());
		numList.add(twoInt);
		numList2.add(x);
		numList2.add(universe.zeroInt());
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

		assertEquals(universe.oneInt(), result);
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
		NumericExpression result = universe.multiply(universe.oneInt(), twoInt);

		assertEquals(twoInt, result);
	}

	/**
	 * Testing the multiply method for symbolic IntegerNumbers;test: x * 0 = 0;
	 */
	@Test
	public void multiplyTwoSymbolicIntTest() {
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(x_obj, intType);
		NumericExpression result = universe.multiply(x, universe.zeroInt());

		assertEquals(universe.zeroInt(), result);
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

		numList.add(universe.oneInt());
		numList.add(twoInt);
		numList2.add(x);
		numList2.add(y);
		numList2.add(universe.zeroInt());
		result = universe.multiply(numList);
		result1 = universe.multiply(numList2);
		assertEquals(twoInt, result);
		assertEquals(universe.zeroInt(), result1);
	}

	/**
	 * Testing the divide method for two concrete IntegerNumbers;test: 2 / 1 =
	 * 2;
	 */
	@Test
	public void divideConcreteIntTest() {
		NumericExpression result = universe.divide(twoInt, universe.oneInt());

		assertEquals(twoInt, result);
	}

	/**
	 * Testing the divide method for symbolic IntegerNumbers;test: 0 / x = 0;
	 */
	@Test
	public void divideSymblicIntTest() {
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(x_obj, intType);
		NumericExpression result2 = universe.divide(universe.zeroInt(), x);

		assertEquals(universe.zeroInt(), result2);
	}

	/**
	 * n1 = (c^2 + c)/d d = c+1
	 * 
	 * n1 == c valid?
	 */
	// @Ignore
	// @Test
	// public void arrayReasonSimplifyTest2() {
	// NumericExpression n1 =
	// universe.divide(universe.add(universe.multiply(int_c, int_c), int_c),
	// int_d);// n1 = (c^2 + c)/d
	// NumericExpression n2 = universe.add(int_c, one);// n2 = c+1
	// Reasoner r = universe.reasoner(universe.equals(int_d, n2)); // d == n2
	// out.println(r.simplify(n1));
	//
	// BooleanExpression eq = universe.equals(n1, int_c); //n1 == c?
	// assertTrue(r.isValid(eq));
	// }
}
