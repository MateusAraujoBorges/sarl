package edu.udel.cis.vsl.sarl.ideal.simplify;

import static org.junit.Assert.*;
import static edu.udel.cis.vsl.sarl.ideal.simplify.CommonObjects.*;

import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class IdealSimplifierSimpExprTest {
	
	private static IdealSimplifier idealSimp;
	
	private static BooleanExpression assumption;
	
	private static NumericExpression numExpr, numExpect, expr1, expr2, expr3, expr4;
	
	private static SymbolicExpression symExpr, expected;

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
		CommonObjects.setUp();
		
	}

	@After
	public void tearDown() throws Exception {
	}
	@Test
	public void simplifyExpression0(){
		numExpr = preUniv.multiply(rat0, x);
		symExpr = numExpr;
		
		assumption = preUniv.equals(rat0, x);
		
		idealSimp = idealSimplifierFactory.newSimplifier(assumption);
		
		assertEquals(rat0, idealSimp.simplifyExpression(symExpr));
	}
	
/*	@Test(expected=ArithmeticException.class)
	public void simplifyExpressionIllegalArg(){
		numExpr = preUniv.divide(x,rat0);
		symExpr = numExpr;
		
		assumption = preUniv.equals(rat0, x);
		
		idealSimp = idealSimplifierFactory.newSimplifier(assumption);
		
		assertEquals(rat0, idealSimp.simplifyExpression(symExpr));
	}*/
	
	@Test
	public void simplifyExpressionTrivial() {
		
		numExpr = preUniv.multiply(preUniv.divide(onePxPxSqdP3x4th, x), x);
		
		symExpr = numExpr;

		assumption = preUniv.equals(preUniv.multiply(rat5,x), preUniv.multiply(y, y));
		
		idealSimp = idealSimplifierFactory.newSimplifier(assumption);
		
		assertEquals(onePxPxSqdP3x4th, idealSimp.simplifyExpression(symExpr));
	}
	
	/*@Test
	public void simplifyExpressionAddition(){
		NumericExpression one;
		NumericExpression two;
		NumericExpression three;
		NumericExpression four;
		NumericExpression five;
		NumericExpression six;
		NumericExpression seven;
		NumericExpression eight;
		NumericExpression nine;
		NumericExpression ten;
		NumericExpression eleven;
		NumericExpression twelve;
		NumericExpression thirteen;
		NumericExpression fourteen;
		NumericExpression fifteen;
		expr1=	preUniv.add(one, preUniv.add(two, three));
		expr2=	preUniv.add(four, preUniv.add(five, six));
		expr3=	preUniv.add(seven, preUniv.add(eight, nine));
		expr4=	preUniv.add(ten,preUniv.add(eleven, twelve));
		NumericExpression expr5 = preUniv.add(thirteen, preUniv.add(fourteen, fifteen));
		
	}*/
	
	@Test
	public void simplifyExpressionSubtraction(){
		expr1 = preUniv.multiply(rat25, preUniv.multiply(preUniv.power(x, 4),preUniv.power(y,3)));
		out.println(expr1);
		expr2 = preUniv.multiply(ratNeg300, xx);
		out.println(expr2);
		expr3 = preUniv.multiply(rat20, preUniv.multiply(preUniv.power(x,4), preUniv.power(y, 3)));
		out.println(expr3);
		expr4 = preUniv.multiply(rat200, xx);
		out.println(expr4);
		
		numExpr = preUniv.subtract(preUniv.subtract(expr1, expr3), preUniv.subtract(expr2, expr4));
		
		symExpr = numExpr;
		
		assumption = preUniv.equals(x, rat5);
		
		idealSimp = idealSimplifierFactory.newSimplifier(assumption);
		
		numExpect = preUniv.add(preUniv.rational(12500), preUniv.multiply(preUniv.rational(3125), preUniv.power(y, 3)));
		
		expected = numExpect;
		// Step through the problem to see how it is breaking down the problem
		//should be 2500 not 12500
		
		assertEquals(expected, idealSimp.simplifyExpression(symExpr));
	}

	@Test
	public void simplifyExpressionDivide() {
		NumericExpression num = preUniv.add(preUniv.multiply(rat6, x), preUniv.multiply(preUniv.multiply(rat2,  x), preUniv.power(y, 2)));
		
		NumericExpression denom = preUniv.multiply(rat2, x);
		
		numExpr = preUniv.divide(num, denom);
		
		symExpr = numExpr;

		assumption = preUniv.equals(preUniv.multiply(rat5,x), preUniv.multiply(y, y));
		
		idealSimp = idealSimplifierFactory.newSimplifier(assumption);
		
		numExpect = preUniv.add(preUniv.power(y, 2), rat3);
		
		expected = numExpect;
		
		assertEquals(expected, idealSimp.simplifyExpression(symExpr));
		
	}
	
	@Test
	public void simplifyExpressionPoly() {
		NumericExpression num = 
				preUniv.add(
							preUniv.add(
									preUniv.multiply(rat4,
												preUniv.multiply(preUniv.power(x, 3),preUniv.power(y, 2))),
									preUniv.multiply(rat2, preUniv.multiply(xy, x))), 
						preUniv.multiply(rat3, xy));

		NumericExpression denom = preUniv.multiply(y, x);
		
		numExpr = preUniv.divide(num, denom);
		
		symExpr = numExpr;

		assumption = preUniv.equals(preUniv.multiply(rat5,x), preUniv.multiply(y, y));
		
		idealSimp = idealSimplifierFactory.newSimplifier(assumption);
		
		numExpect = preUniv.add(preUniv.multiply(preUniv.multiply(rat4,preUniv.power(x, 2)), y), 
											preUniv.add(preUniv.multiply(rat2,x),
												rat3));
		
		expected = numExpect;
		
		assertEquals(expected, idealSimp.simplifyExpression(symExpr));
	}
	
	/*@Test
	public void simplifyExprLarge(){
		
	}*/
}
