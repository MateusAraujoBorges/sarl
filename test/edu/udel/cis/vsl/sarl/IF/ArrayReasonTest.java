package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.PrintStream;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class ArrayReasonTest {
	private static PrintStream out = System.out;
	
	private SymbolicUniverse universe;
	private StringObject a_obj; // "a"
	private StringObject c_obj; // "c"
	private StringObject d_obj; // "d"
	private NumericExpression one, two, six;
	private SymbolicType integerType;
	private SymbolicExpression intArr_a;
	private NumericExpression int_c;
	private NumericExpression int_d;

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		one = universe.integer(1);
		two = universe.integer(2);
		six = universe.integer(6);
		integerType = universe.integerType();
		a_obj = universe.stringObject("a");
		c_obj = universe.stringObject("c");
		d_obj = universe.stringObject("d");
		intArr_a = universe.symbolicConstant(
				a_obj, universe.arrayType(integerType));
		int_c = (NumericExpression) universe
				.symbolicConstant(c_obj, integerType);
		int_d = (NumericExpression) universe
				.symbolicConstant(d_obj, integerType);
	}

	@After
	public void tearDown() throws Exception {
	}

	@Test
	public void arrayAccessReason() {
		NumericExpression i = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("i"), integerType);
		SymbolicExpression a2 = universe.arrayWrite(intArr_a, i, six);
		SymbolicExpression x = universe.arrayRead(a2, two);
		Reasoner r = universe.reasoner(universe.equals(i, two));

		out.println("x=" + x);

		assertEquals(six, r.simplify(x));
	}

	/**
	 * n1 = (c^2 + c)/d
	 * d = c+1
	 * 
	 * n1 == c valid?
	 */
	@Test
	public void arrayReasonSimplifyTest2() {
		NumericExpression n1 = universe.divide(universe.add(universe.multiply(int_c, int_c), int_c), int_d);// n1 = (c^2 + c)/d
		NumericExpression n2 = universe.add(int_c, one);// n2 = c+1
		Reasoner r = universe.reasoner(universe.equals(int_d, n2)); // d == n2
		
		out.println(r.simplify(n1)); 
		
		BooleanExpression eq = universe.equals(n1, int_c); //n1 == c?
		assertTrue(r.isValid(eq));
	}

	/**
	 * 
	 * ab = c^2 - 1 &&
	 * a = c + 1
	 * ===>
	 * b = c - 1
	 */
	@Test
	public void arrayReasonValidTest1() {
		
	}

	/**
	 * 
	 * a = b^2 + 2b + 1 &&
	 * c = b+1
	 * ===>
	 * a = c^2
	 */
	@Test
	public void arrayReasonValidTest2() {
		
	}
	
	/**
	 * 
	 * a = bc + 2 + c + 2b &&
	 * d = a/(b+1)
	 * ===>
	 * a = c+2
	 */
	@Test
	public void arrayReasonValidTest3() {
		
	}

}
