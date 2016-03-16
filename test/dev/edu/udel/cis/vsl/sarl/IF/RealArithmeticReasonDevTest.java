package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.io.PrintStream;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class RealArithmeticReasonDevTest {
	private static boolean debug = true;
	private static PrintStream out = System.out;
	private SymbolicUniverse universe;
	private NumericExpression negOne, one, two;
	private StringObject a_obj; // "a"
	private StringObject b_obj; // "b"
	private StringObject c_obj; // "c"
	private StringObject d_obj; // "d"
	private NumericExpression a;
	private NumericExpression b;
	private NumericExpression c;
	private NumericExpression d;
	private SymbolicType realType;
	
	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		realType = universe.realType();
		negOne = universe.rational(-1);
		one = universe.rational(1);
		two = universe.rational(2);
		a_obj = universe.stringObject("a");
		b_obj = universe.stringObject("b");
		c_obj = universe.stringObject("c");
		d_obj = universe.stringObject("d");
		a = (NumericExpression) universe
				.symbolicConstant(a_obj, realType);
		b = (NumericExpression) universe
				.symbolicConstant(b_obj, realType);
		c = (NumericExpression) universe
				.symbolicConstant(c_obj, realType);
		d = (NumericExpression) universe
				.symbolicConstant(d_obj, realType);
	}

	@After
	public void tearDown() throws Exception {
	}


	/**
	 * TODO under development
	 * ab = (c+1)*(c-1) &&
	 * a = c + 1
	 * ===>
	 * b = c - 1
	 * 
	 * c != -1
	 */
	@Test
	public void RealArithmeticReason1() {
		NumericExpression c2MinusOne = universe.multiply(universe.add(c, one), universe.subtract(c, one));
		NumericExpression cPlusOne = universe.add(c, one); // cPlusOne = c+1
		NumericExpression aTimesB = universe.multiply(a, b); // aTimesB = a*b
		NumericExpression cSubOne = universe.subtract(c, one); // cSubOne = c-1
		BooleanExpression assumption = universe.and(universe.neq(c, negOne), 
				universe.and(universe.equals(aTimesB, c2MinusOne), universe.equals(a, cPlusOne)));
		// a*b = c^2 -1 && a = c+1
		Reasoner r = universe.reasoner(assumption);
		BooleanExpression be = universe.equals(cSubOne, b);
		
		if(debug){
			out.println(aTimesB+"="+c2MinusOne);
			out.println(a+"="+cPlusOne);
			out.println(cSubOne+"=?"+b);
		}
//		assertEquals(true, r.isValid(be));
		ValidityResult result = r.valid(be);
		assertEquals(ResultType.MAYBE, result.getResultType());
	}

	/**
	 * TODO under development
	 * a = (b+1)*(c+2) &&
	 * d = a/(b+1)
	 * ===>
	 * d = c+2
	 */
	@Test
	public void RealArithmeticReason3() {
		NumericExpression bPlusOne = universe.add(b, one);
		NumericExpression cPlusTwo = universe.add(c, two);
		NumericExpression bAddOneTimescPlusTwo = universe.multiply(bPlusOne, cPlusTwo);
		NumericExpression aDivideBPlusOne = universe.divide(a, bPlusOne);
		BooleanExpression assumption = universe.and(universe.neq(b, negOne),
				universe.and(universe.equals(a, bAddOneTimescPlusTwo), universe.equals(d, aDivideBPlusOne)));
		Reasoner r = universe.reasoner(assumption);
		BooleanExpression eq = universe.equals(d, universe.add(c, two));
		ValidityResult result = r.valid(eq);
		
		if(debug){
			out.println(a+"="+bAddOneTimescPlusTwo);
			out.println(d+"="+aDivideBPlusOne);
		}
		
		assertEquals(ResultType.MAYBE, result.getResultType());
	}

	
	/**
	 * This is an integer test (need to be moved)
	 * <x,y> = 2^x * (2y + 1) -1
	 * x and y are integers
	 * x > 0 && y > 0
	 */
	@Test
	public void pairFucTest(){
//		NumericExpression int_zero = universe.integer(0);
		NumericExpression int_one = universe.integer(1);
		NumericExpression int_two = universe.integer(2);
		
		NumericExpression int_five = universe.integer(5);
		
//		NumericExpression int_ten = universe.integer(10);
		SymbolicType integerType = universe.integerType();
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("x"), integerType);
		NumericExpression y = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("y"), integerType);
		NumericExpression twoPowerX = universe.power(int_two, x);
		NumericExpression twoYPlusOne = universe.add(universe.multiply(int_two, y), int_one);
		NumericExpression xyPair = universe.subtract(universe.multiply(twoPowerX, twoYPlusOne), int_one);

		Reasoner r = universe.reasoner(universe.equals(xyPair, int_five));
		BooleanExpression e1 = universe.and(universe.equals(x, int_one), universe.equals(y, int_one));
		ValidityResult result1 = r.valid(e1);
		assertEquals(ResultType.YES, result1.getResultType());
//		
//		BooleanExpression pre = universe.and(universe.lessThanEquals(int_zero, x), universe.lessThanEquals(int_zero, y));
//		Reasoner r = universe.reasoner(universe.and(universe.equals(xyPair, int_ten), pre));
//		BooleanExpression e2 = universe.and(universe.equals(x, int_zero), universe.equals(y, int_five));
//		ValidityResult result2 = r.valid(e2);
//		assertEquals(ResultType.YES, result2.getResultType());
	}
	
	@Test
	public void powerTest(){
		SymbolicType integerType = universe.integerType();
		NumericExpression int_two = universe.integer(2);
		NumericExpression int_three = universe.integer(3);
		NumericExpression int_eight = universe.integer(8);
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("x"), integerType);
		NumericExpression twoPowerX = universe.power(int_two, x); // 2^x
		BooleanExpression assumption = universe.equals(twoPowerX, int_eight);// 2^x = 8
		System.out.println("assumption:"+assumption);
		Reasoner r = universe.reasoner(assumption);
		BooleanExpression deduction = universe.equals(x, int_three); // x == 3?
		ValidityResult result = r.valid(deduction);
		assertEquals(ResultType.YES, result.getResultType());
	}

}
