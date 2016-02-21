package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.PrintStream;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class RealArithmeticTest {
	private SymbolicUniverse universe;
	private static PrintStream out = System.out;
	/**
	 * -.25
	 */
	private NumericExpression negPointTwoFive;
	/**
	 * 0
	 */
	private NumericExpression zero;
	/**
	 * 1
	 */
	private NumericExpression one;
	/**
	 * 1.25
	 */
	private NumericExpression onePointTwoFive;
	/**
	 * 3/2
	 */
	private NumericExpression onePointFive;
	/**
	 * 2
	 */
	private NumericExpression two;
	/**
	 * 3
	 */
	private NumericExpression three;
	/**
	 * 5
	 */
	private NumericExpression five;
	/**
	 * 10
	 */
	private NumericExpression ten;
	/**
	 * 20
	 */
	private NumericExpression twenty;
	/**
	 * "a"
	 */
	private StringObject a_obj;
	/**
	 * "b"
	 */
	private StringObject b_obj;
	/**
	 * "c"
	 */
	private StringObject c_obj;
	private NumericExpression a;
	private NumericExpression b;
	private NumericExpression c;
	private NumericExpression aDBb;
	private BooleanExpression f;
	private BooleanExpression t;
	private SymbolicType realType;
	
	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		negPointTwoFive = universe.rational(-0.25);
		zero = universe.rational(0);
		one = universe.rational(1);
		onePointTwoFive = universe.rational(1.25);
		onePointFive = universe.rational(1.5);
		two = universe.rational(2);
		three = universe.rational(3);
		five = universe.rational(5);
		ten = universe.rational(10);
		twenty = universe.rational(20);
		a_obj = universe.stringObject("a");
		b_obj = universe.stringObject("b");
		c_obj = universe.stringObject("c");
		realType = universe.realType();
		a = (NumericExpression) universe
				.symbolicConstant(a_obj, realType);
		b = (NumericExpression) universe
				.symbolicConstant(b_obj, realType);
		c = (NumericExpression) universe
				.symbolicConstant(c_obj, realType);
		aDBb = universe.divide(a, b);
		f = universe.bool(false);
		t = universe.bool(true);
	}
	
	/**************************add test******************************/
	
	/**
	 * Adds two constants of real type.
	 * 
	 * @param type
	 * 				Real Numbers
	 */
	@Test
	public void constantAdd() {
		NumericExpression c3 = (NumericExpression) universe.add(onePointFive, negPointTwoFive);
				
		assertEquals(onePointTwoFive, c3);
	}
	
	/**
	 * Shows that the commutative property holds for two Numeric Symbolic 
	 * 
	 * @param type
	 * 				NumericSymbolicConstant
	 */
	@Test
	public void commutativity1() { 
		SymbolicExpression apb = universe.add(a, b); // a + b
		SymbolicExpression bpa = universe.add(b, a); // b + a

		assertEquals(apb, bpa);
	}
	
	/**
	 * Adds two polynomials by forming the factorization and by factoring out 
	 * the common factors that are produced from the two factorizations.
	 * 
	 * @param p1 = a^2 + 1
	 * 
	 * @param p2 = 2*a^2 + 1
	 * 
	 * @param p3 = 0 * a
	 * 
	 * @param p4 = 3*a^2 + 2
	 * 
	 * @param b1 = a^2 + 1 + 2*a^2 + 1
	 * 
	 * @param b2 = 0*a + 2*a^2 + 1
	 * 
	 * @param type NumericExpression
	 * 
	 */
	@Test
	public void addPolyToPoly(){
		NumericExpression p1 = universe.add(universe.multiply(a, a), one);
		NumericExpression p2 = universe.add(universe.multiply(two, universe.multiply(a, a)), one);
		NumericExpression p3 = universe.multiply(zero, a);
		NumericExpression p4 = universe.add(universe.multiply(three, universe.multiply(a, a)), two);
		
		NumericExpression b1 = universe.add(p1, p2);
		NumericExpression b2 = universe.add(p3, p2);
		
		assertEquals(p4, b1);
		assertEquals(p2, b2);
	}
	
	/**
	 * Adds a monomial and a polynomial by forming the factorization and by 
	 * factoring out the common factors that are produced from the two factorizations.
	 * 
	 * @param p1 = 2a^2 + 1
	 * 
	 * @param p2 = 10a
	 * 
	 * @param p3 = 10a + 2a^2 + 1
	 * 
	 * @param type
	 * 				NumericExpression
	 * 
	 */
	@Test
	public void addPolyToMonomial() {
		NumericExpression p1 = universe.add(universe.multiply(two, universe.multiply(a, a)), one);
		NumericExpression p2 = universe.multiply(ten, a);
		NumericExpression p3 = universe.add(universe.multiply(ten, a), universe.add(universe.multiply(
						two, universe.multiply(a, a)), one));
				
		NumericExpression b1 = universe.add(p1, p2);
		
		assertEquals(p3, b1);
	}
	
	/**
	 * Adds two monomials by forming the factorization and by 
	 * factoring out the common factors that are produced from the two factorizations.
	 * 
	 * @param p1 = 10a
	 * 
	 * @param p2 = 20a
	 * 
	 * @param type
	 * 				NumericExpression
	 * 
	 */
	@Test
	public void addMonomialToMonomial() {
		NumericExpression p1 = universe.multiply(ten, a);
		NumericExpression p2 = universe.multiply(twenty, a);
				
		NumericExpression b1 = universe.add(p1, p1);
		
		assertEquals(p2, b1);
	}
	
	/**
	 * Adds a monomial and a primitive power by forming the factorization and by 
	 * factoring out the common factors that are produced from the two factorizations.
	 * 
	 * @param p1 = 10a
	 * 
	 * @param p2 = a^2
	 * 
	 * @param p3 = a * (10 + a)
	 * 
	 * @param type
	 * 				NumericExpression
	 */
	@Test
	public void addMonomialToPrimitivePower() {
		NumericExpression p1 = universe.multiply(ten, a);
		NumericExpression p2 = universe.multiply(a, a);
		NumericExpression p3 = universe.multiply(a, universe.add(ten, a));
		
		NumericExpression b1 = universe.add(p1, p2);
		
		assertEquals(p3, b1);
	}
	
	/**
	 * Adds a monomial and a monic by forming the factorization and by 
	 * factoring out the common factors that are produced from the two factorizations.
	 * 
	 * @param p1 = 10a
	 * 
	 * @param p2 = ab
	 * 
	 * @param p3 = a * (10 + b)
	 * 
	 * @param type
	 * 				NumericExpression
	 */
	@Test
	public void addMonomialToMonic() {
		NumericExpression p1 = universe.multiply(ten, a);
		NumericExpression p2 = universe.multiply(a, b);
		NumericExpression p3 = universe.multiply(a, universe.add(ten, b));
		
		NumericExpression b1 = universe.add(p1, p2);
		
		assertEquals(p3, b1);
	}
	
	/**************************substract test******************************/
	
	/**
	 * Subtracts a rational expression and a polynomial by forming the factorization and by factoring out 
	 * the common factors that are produced from the two factorizations.
	 * 
	 * @param x2 = a^2
	 * 
	 * @param monic = a^2 * b
	 * 
	 * @param monomial = 3a^2 * b
	 * 
	 * @param polynomial = 3a^2 * b + a^2
	 * 
	 * @param result = (-(3a^2 + x^2)*y + x)/y
	 * 
	 * @param subPolynomial = x/y - polynomial
	 * 
	 * @param type
	 * 				NumericExpression
	 */
	@Test
	public void subRationalToPolynomial() {
		NumericExpression a2 = (NumericExpression) universe.multiply(a, a); 
		NumericExpression monic = (NumericExpression) universe.multiply(a2, b); 
		NumericExpression monomial = (NumericExpression) universe.multiply(three, 
				monic); 
		NumericExpression polynomial = (NumericExpression) universe.add(monomial, a2); 
		NumericExpression result = universe.divide(universe.
				add(universe.minus(universe.multiply(polynomial, b)),
						a), b); 
		
		NumericExpression subPolynomial = universe.subtract(aDBb, polynomial);
		
		assertEquals(result, subPolynomial);
	}
	
	/**
	 * Subtracts a rational expression and a monomial by forming the factorization and by factoring out 
	 * the common factors that are produced from the two factorizations.
	 * 
	 * @param x2 = a^2
	 * 
	 * @param monic = a^2 * b
	 * 
	 * @param monomial = 3a^2 * b
	 * 
	 * @param result = ((3*a^2*y^2)+x)/y
	 * 
	 * @param subMonomial = (a - 3*a^2*a^2)/b
	 * 
	 * @param type
	 * 				NumericExpression
	 * 
	 */
	@Test
	public void subRationalToMonomial() {
		NumericExpression a2 = (NumericExpression) universe.multiply(a, a);
		NumericExpression monic = (NumericExpression) universe.multiply(a2, b);
		NumericExpression monomial = (NumericExpression) universe.multiply(three, 
				monic); 
		NumericExpression result = universe.divide(universe.
				subtract(a, universe.multiply(monomial, b)), b); 
		
		NumericExpression subMonomial = universe.subtract(aDBb, monomial);
		
		assertEquals(result, subMonomial);
	}
	
	/**************************multiply test******************************/
	
	/**
	 * Multiplies two Constants of type real and returns a Constant with 
	 * the same type
	 * 
	 * @param type
	 * 				NumericExpression
	 */	
	@Test
	public void constantMultiply() {
		NumericExpression result = (NumericExpression) universe.multiply(onePointFive, negPointTwoFive);
		NumericExpression expected = universe.rational(-.375);
		out.println("numeric multilpy: " + onePointFive + " * " + negPointTwoFive + " = " + result);
		
		assertEquals(expected, result);
	}
	
	/**
	 * Multiplies two polynomials by forming the factorization and by 
	 * factoring out the common factors that are produced from the two factorizations.
	 * 
	 * @param p1 = a^2 + 1
	 * 
	 * @param p2 = 2*a^2 + 1
	 * 
	 * @param p3 = 0 * a
	 * 
	 * @param p4 = 3 * a^2 + 1
	 * 
	 * @param p5 = 2a^4 +p4
	 * 
	 * @param b1 = (a^2 + 1) * (2*a^2 + 1)
	 * 
	 * @param b2 = (a^2 + 1)* (0 * a)
	 * 
	 * @param type
	 * 				NumericExpression
	 * 
	 */
	@Test
	@Ignore
    public void mulPolyToPoly() {
		NumericExpression p1 = universe.add(universe.multiply(a, a), one); // a^2 + 1
		NumericExpression p2 = universe.add(universe.multiply(two,
				universe.multiply(a, a)), one); // 2*a^2 + 1
		NumericExpression p3 = universe.multiply(zero, a);
        NumericExpression a2 = universe.multiply(a, a);
        NumericExpression a4 = universe.multiply(a2, a2);
        NumericExpression p4 = universe.add(universe.multiply(three, universe.multiply(a, a)), one);
        NumericExpression p5 = universe.add(universe.
                multiply(two, a4), p4);
               
        NumericExpression b1 = universe.multiply(p1, p2);
        NumericExpression b2 = universe.multiply(p1, p3);
       
        assertEquals(p5, b1);
        assertEquals(zero, b2);
    }
	
	/**
	 * Multiplies a polynomial with a monomial by forming the factorization 
	 * and by factoring out the common factors that are produced from the two factorizations.
	 * 
	 * @param p1 = a^2 + 1
	 * 
	 * @param p2 = 10a
	 * 
	 * @param p3 = 10a^3 + 10a
	 * 
	 * @param b1 = 10a * (a^2+1)
	 * 
	 * @param type
	 * 				NumericExpression
	 * 
	 */
	@Test
	public void mulPolyToMonomial() {
		NumericExpression p1 = universe.add(universe.multiply(a, a), one);
		NumericExpression p2 = universe.multiply(ten, a);
		NumericExpression a2 = universe.multiply(a, a);
		NumericExpression p3 = universe.add(universe.multiply(ten, 
				universe.multiply(a2, a)), p2);
		
		NumericExpression b1 = universe.multiply(p2, p1);
		
		assertEquals(p3, b1);
	}
	
	/**
	 * Multiplies a monomial with a primitive power by forming the factorization 
	 * and by factoring out the common factors that are produced from the two factorizations.
	 * 
	 * @param p1 = 10a
	 * 
	 * @param p2 = 10 * (a^2 * a)
	 * 
	 * @param b1 = 10a * a^2
	 * 
	 * @param type
	 * 				NumericExpression
	 * 
	 */
	@Test
	public void mulMonomialToPrimitivePower() {
		NumericExpression p1 = universe.multiply(ten, a);
		NumericExpression a2 = universe.multiply(a, a);
		NumericExpression p2 = universe.multiply(ten, universe.multiply(a2, a));
		
		NumericExpression b1 = universe.multiply(p1, a2);
		
		assertEquals(p2, b1);
	}
	
	/**
	 * (a+1) * (a-1) == a^2 - 1
	 * 
	 */
	@Test
	public void xp1xm1() {
		NumericExpression xp1 = universe.add(a, one);
		NumericExpression xm1 = universe.add(a, (NumericExpression) universe.minus(one));
		NumericExpression xp1xm1 = universe.multiply(xp1, xm1);		
		NumericExpression x2m1 = universe.subtract(universe.multiply(a, a),
				universe.multiply(one,one));
		
		out.println("xp1xm1=" + xp1xm1);
		out.println("x2m1=" + x2m1);
		
		BooleanExpression eq = universe.equals(xp1xm1, x2m1);
		
		out.println("eq: "+eq);
		
		assertTrue(universe.reasoner(t).isValid(eq));
		
		//assertEquals(x2m1, xp1xm1);
	}
	
	/**************************divide test******************************/
	
	/**
	 * Divides two polynomials by forming the factorization and by factoring 
	 * out the common factors that are produced from the two factorizations.
	 * 
	 * @param p01 = 10 + 10a
	 * 
	 * @param p02 = 2 + 2a
	 * 
	 * 5 == p01/p02 ?
	 * 
	 * @param type
	 * 				NumericExpression
	 * 
	 */
	@Test
	public void dividePolyByPoly() {
		NumericExpression p01 = universe.add(ten, universe.multiply(ten, a));
		NumericExpression p02 = universe.add(two, universe.multiply(two, a));
		NumericExpression b1 = universe.divide(p01, p02);
		
		assertEquals(five, b1);
	}
	
	/**
	 * Divides a polynomial with a monomial by forming the factorization and 
	 * by factoring out the common factors that are produced from the two factorizations.
	 * 
	 * @param p01 = a^2
	 * 
	 * @param p02 = 10a
	 * 
	 * @param p03 = 10a + 10a^2
	 * 
	 * @param p04 = a+1
	 * 
	 * @param b1 = p03/p02
	 * 
	 * @param type
	 * 				NumericExpression
	 * 
	 */
	@Test
	public void dividePolyToMonomial() {
		NumericExpression p01 = universe.multiply(a, a);
		NumericExpression p02 = universe.multiply(ten, a);
		NumericExpression p03 = universe.add(p02, universe.multiply(ten, p01));
		NumericExpression p04 = universe.add(a, one);
		
		NumericExpression b1 = universe.divide(p03, p02);
		
		assertEquals(p04, b1);
	}
	
	/**
	 * Divides two monomials by forming the factorization 
	 * and by factoring out the common factors that are produced from the two factorizations.
	 * 
	 * @param p1 = 10a
	 * 
	 * @param p2 = 2a
	 * 
	 * @param type
	 * 				NumericExpression
	 *
	 */
	@Test
	public void divideMonomialToMonomial() {
		NumericExpression p01 = universe.multiply(ten, a);
		NumericExpression p02 = universe.multiply(two, a);
		
		NumericExpression b1 = universe.divide(p01, p02);
		
		assertEquals(five, b1);
	}
	
	/**
	 * Divides a monomial with a primitive power by forming the factorization 
	 * and by factoring out the common factors that are produced from the two factorizations.
	 * 
	 * @param p01 = a^2
	 * 
	 * @param p02 = a^2*b
	 * 
	 * @param b1 = p02/p01
	 * 
	 * @param type
	 * 				NumericExpression
	 * 
	 */
	@Test
	public void divideMonicToPrimitivePower() {
		NumericExpression p01 = universe.multiply(a, a);
		NumericExpression p02 = universe.multiply(universe.multiply(a, a), b);
		
		NumericExpression b1 = universe.divide(p02, p01);
		
		assertEquals(b, b1);
	}
	
	/**
	 * Divides a primitive with a constant by forming the factorization and 
	 * by factoring out the common factors that are produced from the two factorizations.
	 * 
	 * @param p01 = a^2
	 * 
	 * @param p02 = 10a
	 * 
	 * @param p03 = p01/p02
	 * 
	 * @param b3 = a/10
	 * 
	 * p03 == b3 ?
	 * 
	 * @param type
	 * 				NumericExpression
	 * 
	 */
	@Test
	public void dividePrimitiveToConstant() {
		NumericExpression p01 = universe.multiply(a, a);
		NumericExpression p02 = universe.multiply(ten, a);
		NumericExpression p03 = universe.divide(p01, p02);
		
		NumericExpression b3 = universe.divide(a, ten);
		
		assertEquals(p03, b3);
	}
	
	/**
	 * Divides two polynomials by removing the common factors between them
	 * 
	 * @param p01 = ((a-1)*(a+1))*(ab+2)
	 * 
	 * @param p02 = ((a-1)*c)*(ab+3)
	 * 
	 * @param p03 = (a+1)*(ab+2)
	 * 
	 * @param p04 = (c)*(ab+3)
	 * 
	 * @param p05 = p03/p04
	 * 
	 * @param b1 = p01/p02
	 * 
	 * p05 == b1 ?
	 * 
	 * @param type
	 * 				NumericExpression
	 * 
	 */
	@Test
	public void factorization() {
		NumericExpression p01 = universe.multiply(universe.multiply((NumericExpression) universe.
				subtract(a, one),universe.add(a, one)), universe.add(universe.multiply(
						a, b), two));
		NumericExpression p02 = universe.multiply(universe.multiply((NumericExpression) universe.
				subtract(a, one), c), universe.add(universe.multiply(a, 
						b), three));
		NumericExpression p03 = universe.multiply(universe.add(a, one), universe.add(universe.multiply(
				a, b), two));
		NumericExpression p04 = universe.multiply(c, universe.add(universe.multiply(a, b), 
				three));
		NumericExpression p05 = universe.divide(p03, p04);
		
		NumericExpression b1 = universe.divide(p01, p02);
		
		assertEquals(p05, b1);
	}
	
	/**************************boolean test******************************/
	
	/**
	 * Returns true if the first argument is 'less than' the second 
	 * argument and vice-versa.
	 * 
	 * @param n1 = a-1
	 * 
	 * @param n2 = a+1
	 * 
	 * r1 := (n2 < n1)
	 * 
	 * r2 := (n1 < n2)
	 * 
	 * @param type
	 * 				NumericExpression
	 * 
	 */
	@Test
	public void lessThan() {
		NumericExpression n1 = universe.subtract(a,one);
		NumericExpression n2 = universe.add(a, one);
		
		BooleanExpression r1 = universe.lessThan(n2, n1);
		BooleanExpression r2 = universe.lessThan(n1, n2);
		
		assertEquals(r1, f);
		assertEquals(r2, t);
	}
	
	/**
	 * @param num1 = a+1
	 * 
	 * @param num2 = a-1
	 * 
	 * @param result1 := a <= a+1 ?
	 * 
	 * @param result2 := a-1 <= a ?
	 * 
	 * @param result3 := a <= a ?
	 */
	@Test
	public void lessThanEquals(){
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
	 * Returns true if the first argument is 'equal' 
	 * to the second argument and returns false otherwise.
	 * 
	 * @param n1 = a+1
	 * 
	 * @param n2 = (1*a^2)+a
	 * 
	 * @param n3 = 2ab + a
	 * 
	 * @param r1 = (a+b)/a
	 * @param type
	 * 				NumericExpression
	 * 
	 */
	@Test
	public void equals() {
		NumericExpression n1 = universe.add(a, one);
		NumericExpression n2 = universe.add(universe.
				multiply(one, universe.multiply(a, a)), a);
		NumericExpression n3 = universe.add(universe.
				multiply(two, universe.multiply(a, b)), a);
		NumericExpression r1 = universe.
				divide(universe.add(a, b), a);	// (x-y)/y	
		
		BooleanExpression b0 = universe.equals(a, n1);
		BooleanExpression b1 = universe.equals(a, n2);
		BooleanExpression b2 = universe.equals(a, n3);
		BooleanExpression b3 = universe.equals(a, a);
		BooleanExpression b4 = universe.equals(one, r1);
		
		
		out.println("b1=" +b1);
		out.println("b2=" +b2);
		out.println("b4=" +b4);
		assertEquals(f, b0);
		assertEquals(t, b3);
	}
	
	
	
}
