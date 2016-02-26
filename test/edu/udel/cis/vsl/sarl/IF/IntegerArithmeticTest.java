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
	private NumericExpression negOneInt;  //integer -1
	private NumericExpression twoInt;     //integer  2
	private NumericExpression threeInt;   //integer  3
	private NumericExpression negThreeInt;//integer -3
	private NumericExpression negFourInt; //integer -4
	private NumericExpression fourInt;    //integer  4
	private NumericExpression x;
	private NumericExpression y;
	//private NumericExpression _x;   // -x
	private StringObject x_obj;		// "x"
	//private StringObject negX_obj;	// "-x"
	private StringObject y_obj;		// "y"
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
		//negX_obj = universe.stringObject("-x");
		y_obj = universe.stringObject("y");
		intType = universe.integerType();
		x = (NumericExpression) universe.symbolicConstant(x_obj, intType);
		y = (NumericExpression) universe.symbolicConstant(y_obj, intType);
		//_x = (NumericExpression) universe.symbolicConstant(negX_obj, intType);
	}

	@After
	public void tearDown() throws Exception {
	}

	/**
	 * Testing the add method for two concrete IntegerNumbers;test: 1 + (-4) = -3
	 */
	@Test
	public void addTwoConcreteIntTest() {
		NumericExpression result = universe.add(universe.oneInt(), negFourInt);

		assertEquals(negThreeInt, result);
	}

	/**
	 * Testing the add method for two symbolic IntegerNumbers;test: x + 0 = x;
	 */
	@Test
	public void addTwoSymbolicIntTest() {
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
	 * Testing the subtract method for two concrete IntegerNumbers;test: 3 - (-1) =
	 * 4;
	 */
	@Test
	public void substractConcreteIntTest() {
		NumericExpression result = universe.subtract(threeInt, negOneInt);

		assertEquals(fourInt, result);
	}

	/**
	 * Testing the subtract method for two symbolic IntegerNumbers;test: (x + y)
	 * - x = y;
	 */
	@Test
	public void substractSymbolicIntTest() {
		NumericExpression result = universe.subtract(universe.add(x, y), x);

		assertEquals(y, result);
	}

	/**
	 * Testing the multiply method for two concrete IntegerNumbers;test: (-1) * 3 =
	 * -3;
	 */
	@Test
	public void multiplyTwoConcreteIntTest() {
		NumericExpression result = universe.multiply(negOneInt, threeInt);

		assertEquals(negThreeInt, result);
	}

	/**
	 * Testing the multiply method for symbolic IntegerNumbers;test: x * 0 = 0;
	 */
	@Test
	public void multiplyTwoSymbolicIntTest() {
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
	 * Testing the divide method for two concrete IntegerNumbers;
	 * In C, a%b=a-(a/b)*b. test examples:
	 * a=4, b=3: a/b=1, a%b=4-3=1
	 * a=4, b=-3: a/b=-1, a%b=4-(-1)(-3)=1
	 * a=-4, b=3: a/b=-1, a%b=-4-(-1)3=-1
	 * a=-4, b=-3: a/b=1, a%b=-4-1(-3)=-1
	 */
	@Test
	public void divideConcreteIntTest() {
		NumericExpression result = universe.divide(fourInt, threeInt);
		NumericExpression result1 = universe.divide(fourInt, negThreeInt);
		NumericExpression result2 = universe.divide(negFourInt, threeInt);
		NumericExpression result3 = universe.divide(negFourInt, negThreeInt);

		assertEquals(universe.oneInt(), result);
		assertEquals(negOneInt, result1);
		assertEquals(negOneInt, result2);
		assertEquals(universe.oneInt(), result3);
	}

	/**
	 * Testing the divide method for symbolic IntegerNumbers;test: (x - x) / x =
	 * 0;
	 */
	@Test
	public void divideSymblicIntTest() {
		NumericExpression result = universe.divide(universe.subtract(x, x), x);

		assertEquals(universe.zeroInt(), result);
	}

	/**
	 * Testing the modulo method for IntegerNumbers;
	 * In C, a%b=a-(a/b)*b. test examples:
	 * a=4, b=3: a/b=1, a%b=4-3=1
	 * a=4, b=-3: a/b=-1, a%b=4-(-1)(-3)=1
	 * a=-4, b=3: a/b=-1, a%b=-4-(-1)3=-1
	 * a=-4, b=-3: a/b=1, a%b=-4-1(-3)=-1
	 */
	@Test
	public void moduloIntTest() { // positive divisor
		NumericExpression result = universe.modulo(fourInt, threeInt);
		NumericExpression result2 = universe.modulo(negFourInt, threeInt);

		assertEquals(universe.oneInt(), result);
		assertEquals(negOneInt, result2);
	}

	@Test
	public void moduloIntTest2() { // negative divisor
		NumericExpression result1 = universe.modulo(fourInt, negThreeInt);
		NumericExpression result3 = universe.modulo(negFourInt, negThreeInt);

		assertEquals(universe.oneInt(), result1);
		assertEquals(negOneInt, result3);
	}
	
	/**
	 * Testing the minus method for concrete IntegerNumbers;
	 */
	@Test
	public void minusConcreteIntTest() {
		NumericExpression result = universe.minus(negThreeInt);// negative int
		NumericExpression result1 = universe.minus(fourInt); // positive int
		NumericExpression result2 = universe.minus(universe.zeroInt()); // zero

		assertEquals(threeInt, result);
		assertEquals(negFourInt, result1);
		assertEquals(universe.zeroInt(), result2);
	}

	/**
	 * Testing the minus method for symbolic IntegerNumbers; x + (-x) = 0;
	 */
	@Test
	public void minusSymbolicIntTest() {
		NumericExpression result = universe.add(x, universe.minus(x));

		assertEquals(universe.zeroInt(), result);
	}

	/**
	 * Testing the power method for concrete IntegerNumbers; test: 3^1=2; 4^0=1;
	 */
	@Test
	public void powerConcreteIntTest() {
		NumericExpression result = universe.power(threeInt, universe.oneInt());
		NumericExpression result1 = universe.power(fourInt, universe.zeroInt());
		NumericExpression result2 = universe.power(x, universe.zeroInt());

		assertEquals(threeInt, result);
		assertEquals(universe.oneInt(), result1);
		assertEquals(universe.oneInt(), result2);
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
