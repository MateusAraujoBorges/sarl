package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertEquals;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class RealArithmeticReasonTest {
	private static boolean debug = false;
	private static PrintStream out = System.out;
	private SymbolicUniverse universe;
	private NumericExpression one, two, five;
	private StringObject a_obj; // "a"
	private StringObject b_obj; // "b"
	private StringObject c_obj; // "c"
	private StringObject d_obj; // "d"
	private NumericExpression a;
	private NumericExpression b;
	private NumericExpression c;
	private NumericExpression d;
	private SymbolicType realType;
	private BooleanExpression t;
	private BooleanExpression f;
	
	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		realType = universe.realType();
		one = universe.rational(1);
		two = universe.rational(2);
		five = universe.rational(5);
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
		t = universe.bool(true);
		f = universe.bool(false);
	}

	@After
	public void tearDown() throws Exception {
	}
	
	/**
	 * n1 = (c^2 + c)/d
	 * d = c+1
	 * 
	 * n1 == c valid?
	 */
	@Test
	public void realDivideReason() {
		NumericExpression n1 = universe.divide(universe.add(universe.multiply(c, c), c), d);// n1 = (c^2 + c)/d
		NumericExpression n2 = universe.add(c, one);// n2 = c+1
		Reasoner r = universe.reasoner(universe.equals(d, n2)); // d == n2
		if(debug){
			out.println(r.simplify(n1)); 
		}
		BooleanExpression eq = universe.equals(n1, c); //n1 == c?
		ValidityResult result = r.valid(eq);
		assertEquals(ResultType.YES, result.getResultType());
	}
	
	/**
	 * (a+1) * (a-1) == a^2 - 1
	 */
	@Test
	public void xp1xm1test() {
		NumericExpression xp1 = universe.add(a, one);
		NumericExpression xm1 = universe.add(a, (NumericExpression) universe.minus(one));
		NumericExpression xp1xm1 = universe.multiply(xp1, xm1);		
		NumericExpression x2m1 = universe.subtract(universe.multiply(a, a),
				universe.multiply(one,one));
		
		BooleanExpression eq = universe.equals(xp1xm1, x2m1);
		if(debug){
			out.println("xp1xm1=" + xp1xm1);
			out.println("x2m1=" + x2m1);
			out.println("eq: "+eq);
		}
		
		assertTrue(universe.reasoner(t).isValid(eq));
	}

	/**
	 * TODO test fail
	 * ab = c^2 - 1 &&
	 * a = c + 1
	 * ===>
	 * b = c - 1
	 */
	@Test
	public void RealArithmeticReason1() {
		NumericExpression c2 = universe.multiply(c, c); //c2 = c^2
		NumericExpression c2MinusOne = universe.subtract(c2, one); //c2MinusOne = c^2 - 1
		NumericExpression cPlusOne = universe.add(c, one); // cPlusOne = c+1
		NumericExpression aTimesB = universe.multiply(a, b); // aTimesB = a*b
		NumericExpression cSubOne = universe.subtract(c, one); // cSubOne = c-1
		// a*b = c^2 -1 && a = c+1
		Reasoner r = universe.reasoner(universe.and(universe.equals(aTimesB, c2MinusOne), universe.equals(a, cPlusOne)));
		BooleanExpression be = universe.equals(cSubOne, b);
		
		if(debug){
			out.println(aTimesB+"="+c2MinusOne);
			out.println(a+"="+cPlusOne);
			out.println(cSubOne+"=?"+b);
		}

		ValidityResult result = r.valid(be);
		assertEquals(ResultType.YES, result.getResultType());
	}

	/**
	 * 
	 * a = b^2 + 2b + 1 &&
	 * c = b+1
	 * ===>
	 * a = c^2
	 */
	@Test
	public void RealArithmeticReason2() {
		NumericExpression b2 = universe.multiply(b, b);
		NumericExpression twoB = universe.multiply(two, b);
		List<NumericExpression> nums = new ArrayList<NumericExpression>();
		nums.add(b2);
		nums.add(twoB);
		nums.add(one);
		NumericExpression b2Plus2bPlusOne = universe.add(nums);
		NumericExpression bPlusOne = universe.add(b, one);
		NumericExpression c2 = universe.multiply(c, c);
		Reasoner r = universe.reasoner(universe.and(universe.equals(c, bPlusOne), universe.equals(a, b2Plus2bPlusOne)));
		BooleanExpression eq = universe.equals(a, c2);
		ValidityResult result = r.valid(eq);
		
		assertEquals(ResultType.YES, result.getResultType());
	}
	
	/**
	 * TODO test fail
	 * a = bc + 2 + c + 2b &&
	 * d = a/(b+1)
	 * ===>
	 * d = c+2
	 */
	@Test
	public void RealArithmeticReason3() {
		NumericExpression bTimesC = universe.multiply(b, c);
		NumericExpression bTimesCPlus2PlusCPlus2b = universe.add(universe.add(bTimesC, two), universe.add(c, universe.multiply(two, b)));
		NumericExpression aDivideBPlusOne = universe.divide(a, universe.add(b, one));
		Reasoner r = universe.reasoner(universe.and(universe.equals(a, bTimesCPlus2PlusCPlus2b), universe.equals(d, aDivideBPlusOne)));
		BooleanExpression eq = universe.equals(d, universe.add(c, two));
		ValidityResult result = r.valid(eq);
		
		if(debug){
			out.println(a+"="+bTimesCPlus2PlusCPlus2b);
			out.println(d+"="+aDivideBPlusOne);
		}
		
		assertEquals(ResultType.YES, result.getResultType());
	}
	
	/**
	 * a >= b
	 * c <= b
	 * ==>
	 * a >= c
	 * a^2 >= b^2 ?
	 */
	@Test
	public void RealLogicReason1() {
		NumericExpression a2 = universe.power(a, 2);
		NumericExpression b2 = universe.power(b, 2);
		Reasoner r = universe.reasoner(universe.and(universe.lessThanEquals(b, a), universe.lessThanEquals(c,b)));
		BooleanExpression lessThan1 = universe.lessThanEquals(c, a);
		BooleanExpression lessThan2 = universe.lessThanEquals(b2, a2);
		
		ValidityResult result1 = r.valid(lessThan1);
		ValidityResult result2 = r.valid(lessThan2);
		assertEquals(ResultType.YES, result1.getResultType());
		assertEquals(ResultType.NO, result2.getResultType());
	}
	
	/**
	 * 
	 * a < 2 V a >5
	 * b >2 && b < 5
	 * ==>
	 * a != b
	 * a > b?
	 * a < b?
	 * 
	 * (c > 5 && c < 2) == false
	 * 
	 */
	@Test
	public void RealLogicReason2() {
		BooleanExpression aRange = universe.or(universe.lessThan(a, two), universe.lessThan(five, a));
		BooleanExpression bRange = universe.and(universe.lessThan(two, b), universe.lessThan(b, five));
		BooleanExpression cRange = universe.and(universe.lessThan(five, c), universe.lessThan(c, two));
		Reasoner r = universe.reasoner(universe.and(aRange, bRange));
		BooleanExpression ne = universe.neq(a, b);
		BooleanExpression gt = universe.lessThan(b, a);
		BooleanExpression lt = universe.lessThan(a, b);
		BooleanExpression eq = universe.equals(cRange, f);
		ValidityResult result1 = r.valid(ne);
		ValidityResult result2 = r.valid(gt);
		ValidityResult result3 = r.valid(lt);
		ValidityResult result4 = r.valid(eq);
		
		assertEquals(ResultType.YES, result1.getResultType());
		assertEquals(ResultType.NO, result2.getResultType());
		assertEquals(ResultType.NO, result3.getResultType());
		assertEquals(ResultType.YES, result4.getResultType());
	}
	
}
