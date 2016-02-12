package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
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
	/**
	 * 1/4
	 */
	private NumericExpression pointTwoFive;
	private NumericExpression negTwo, one, two, three;
	/**
	 * "a"
	 */
	private StringObject a_obj;
	/**
	 * "b"
	 */
	private StringObject b_obj;
	private SymbolicType realType;
	
	
	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		realType = universe.realType();
		onePointFive = universe.rational(1.5);
		negPointTwoFive = universe.rational(-0.25);
		onePointTwoFive = universe.rational(1.25);
		pointFive = universe.rational(1, 2);
		pointTwoFive = universe.rational(1, 4);
		negTwo = universe.rational(-2);
		one = universe.rational(1);
		two = universe.rational(2);
		three = universe.rational(3);
		a_obj = universe.stringObject("a");
		b_obj = universe.stringObject("b");
	}
	
	@Test
	public void addTest(){
		List<NumericExpression> numArr = new ArrayList<NumericExpression>();
		numArr.add(onePointFive);
		numArr.add(negPointTwoFive);
		NumericExpression addResult1 = universe.add(onePointFive, negPointTwoFive);
		NumericExpression addResult2 = universe.add(one, pointFive);
		NumericExpression addResult3 = universe.add(numArr);
		
		assertEquals(addResult1, onePointTwoFive);
		assertEquals(addResult2, onePointFive);
		assertEquals(addResult3, onePointTwoFive);
	}
	
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
		NumericExpression result = universe.subtract(onePointTwoFive, negPointTwoFive);
		
		assertEquals(result, onePointFive);
	}
	
	@Test
	public void multiplyTest(){
		NumericExpression result1 = universe.multiply(three, pointFive);
		List<NumericExpression> numArr = new ArrayList<NumericExpression>();
		numArr.add(three);
		numArr.add(pointFive);
		NumericExpression result2 = universe.multiply(numArr);
		
		assertEquals(result1, onePointFive);
		assertEquals(result2, onePointFive);
	}
	
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
	
	@Test 
	public void divideTest(){
		NumericExpression result = universe.divide(onePointFive, pointFive);
		
		assertEquals(result, three);
	}
	
	@Test
	public void minusTest(){
		NumericExpression result = universe.minus(negPointTwoFive);
		
		assertEquals(result, pointTwoFive);
	}
	
	@Test
	public void powerTest(){
		NumericExpression result1 = universe.power(pointFive, two);
		NumericExpression result2 = universe.power(two, negTwo);
		
		assertEquals(result1, pointTwoFive);
		assertEquals(result2, pointTwoFive);
	}
}
