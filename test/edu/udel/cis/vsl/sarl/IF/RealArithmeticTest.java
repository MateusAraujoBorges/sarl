package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class RealArithmeticTest {
	private SymbolicUniverse universe;
	/**
	 * 3/2
	 */
	private NumericExpression onePointFive;
	/**
	 * -.25
	 */
	private NumericExpression negPointTwoFive;
	/**
	 * 1.25
	 */
	private NumericExpression onePointTwoFive;
	/**
	 * 1/2
	 */
	private NumericExpression pointFive;
	private NumericExpression zero, one, three;
	/**
	 * "a"
	 */
	private StringObject a_obj;
	/**
	 * "b"
	 */
	private StringObject b_obj;
	private SymbolicType realType;
	BooleanExpression f;
	BooleanExpression t;
	
	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		realType = universe.realType();
		onePointFive = universe.rational(1.5);
		negPointTwoFive = universe.rational(-0.25);
		onePointTwoFive = universe.rational(1.25);
		pointFive = universe.rational(1, 2);
		zero = universe.rational(0);
		one = universe.rational(1);
		three = universe.rational(3);
		a_obj = universe.stringObject("a");
		b_obj = universe.stringObject("b");
		f = universe.bool(false);
		t = universe.bool(true);
	}
	
	@Test
	public void addTest(){
		List<NumericExpression> numArr = new ArrayList<NumericExpression>();
		numArr.add(onePointFive);
		numArr.add(negPointTwoFive);
		NumericExpression addResult1 = universe.add(onePointFive, negPointTwoFive);
		NumericExpression addResult2 = universe.add(one, pointFive);
		NumericExpression addResult3 = universe.add(numArr);
		
		assertEquals(onePointTwoFive, addResult1);
		assertEquals(onePointFive, addResult2);
		assertEquals(onePointTwoFive, addResult3);
		
		/**
		 * a+0 = a;
		 */
		NumericExpression a = (NumericExpression) universe
				.symbolicConstant(a_obj, realType);
		NumericExpression aPlusZero = universe.add(a, zero);
		
		assertEquals(a, aPlusZero);
	}
	
	/**
	 * (a+b) == (b+a)
	 */
	@Test
	public void addCommutativityTest(){
		NumericExpression a = (NumericExpression) universe
				.symbolicConstant(a_obj, realType);
		NumericExpression b = (NumericExpression) universe
				.symbolicConstant(b_obj, realType);
		SymbolicExpression apb = universe.add(a, b); // a + b
		SymbolicExpression bpa = universe.add(b, a); // b + a
		
		assertEquals(apb, bpa);
	}
	
	@Test
	public void substractTest(){
		/**
		 * 1.25 - (-.25) = 1.5
		 */
		NumericExpression result1 = universe.subtract(onePointTwoFive, negPointTwoFive);
		assertEquals(onePointFive, result1);
		
		/**
		 * (a+b)-a = b;
		 */
		NumericExpression a = (NumericExpression) universe
				.symbolicConstant(a_obj, realType);
		NumericExpression b = (NumericExpression) universe
				.symbolicConstant(b_obj, realType);
		NumericExpression result2 = universe.subtract(universe.add(a, b), a);
		assertEquals(b, result2);
	}
	
	/**
	 * 3 * .5 = 1.5
	 */
	@Test
	public void multiplyTest(){
		NumericExpression result1 = universe.multiply(three, pointFive);
		List<NumericExpression> numArr = new ArrayList<NumericExpression>();
		numArr.add(three);
		numArr.add(pointFive);
		NumericExpression result2 = universe.multiply(numArr);
		
		assertEquals(onePointFive, result1);
		assertEquals(onePointFive, result2);
	}
	
	/**
	 * (a*b) == (b*a)
	 */
	@Test 
	public void multiplyCommutativityTest(){
		NumericExpression a = (NumericExpression) universe
				.symbolicConstant(a_obj, realType);
		NumericExpression b = (NumericExpression) universe
				.symbolicConstant(b_obj, realType);
		NumericExpression result1 = universe.multiply(a, b); //a*b
		NumericExpression result2 = universe.multiply(b, a); //b*a
		
		assertEquals(result1, result2);
	}
	
	/**
	 * 1.5 / .5 == 3
	 */
	@Test 
	public void divideTest(){
		NumericExpression result = universe.divide(onePointFive, pointFive);
		
		assertEquals(three, result);
	}
	
	/**
	 * a + -a == 0
	 */
	@Test
	public void minusTest(){
		NumericExpression a = (NumericExpression) universe
				.symbolicConstant(a_obj, realType);
		NumericExpression negA = universe.minus(a);
		NumericExpression o = universe.add(a, negA);
		
		assertEquals(zero, o);
	}
	
	/**
	 * a^3 == a*a*a
	 */
	@Test
	public void powerTest(){
		NumericExpression a = (NumericExpression) universe
				.symbolicConstant(a_obj, realType);
		ArrayList<NumericExpression> numList = new ArrayList<NumericExpression>();
		numList.add(a);
		numList.add(a);
		numList.add(a);
		NumericExpression aCube1 = universe.power(a, 3);
		NumericExpression aCube2 = universe.multiply(numList);
		
		assertEquals(aCube1, aCube2);
	}
	
	/**
	 * a && a+1
	 */
	@Test
	public void lessThanTest(){
		NumericExpression a = (NumericExpression) universe
				.symbolicConstant(a_obj, realType);
		NumericExpression num = universe.add(a, one);
		BooleanExpression result1 = universe.lessThan(a, num);
		BooleanExpression result2 = universe.lessThan(num, a);
		BooleanExpression result3 = universe.lessThan(a, a);
		
		assertEquals(t, result1);
		assertEquals(f, result2);
		assertEquals(f, result3);
	}
	
	/**
	 * a && a+1 && a-1
	 */
	@Test
	public void lessThanEquals(){
		
		NumericExpression a = (NumericExpression) universe
				.symbolicConstant(a_obj, realType);
		NumericExpression num1 = universe.add(a, one);
		NumericExpression num2 = universe.subtract(a, one);
		BooleanExpression result1 = universe.lessThanEquals(a, num1);
		BooleanExpression result2 = universe.lessThanEquals(num2, a);
		BooleanExpression result3 = universe.lessThanEquals(a, a);
		
		assertEquals(t, result1);
		assertEquals(t, result2);
		assertEquals(t, result3);
	}
	
	/**
	 * (a+b)-b == (a*b)/b
	 */
	@Test
	public void equalsTest(){
		NumericExpression a = (NumericExpression) universe
				.symbolicConstant(a_obj, realType);
		NumericExpression b = (NumericExpression) universe
				.symbolicConstant(b_obj, realType);
		NumericExpression aPbMb = universe.subtract(universe.add(a, b), b); //(a+b)-b
		NumericExpression aMULbDb = universe.divide(universe.multiply(a, b), b); //(a*b)/b
		BooleanExpression result = universe.equals(aPbMb, aMULbDb);
		
		assertEquals(t, result);
	}
	
	/**
	 * a != a+1
	 */
	@Test
	public void notEqualsTest(){
		NumericExpression a = (NumericExpression) universe
				.symbolicConstant(a_obj, realType);
		NumericExpression aPlusOne = universe.add(a, one);
		BooleanExpression result = universe.neq(aPlusOne, a);
		
		assertEquals(t, result);
	}
	
}
