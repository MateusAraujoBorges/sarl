package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.PrintStream;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class ArrayReasonTest {
	private static PrintStream out = System.out;
	
	private SymbolicUniverse universe;
	private StringObject a_obj; // "a"
	private NumericExpression two, six;
	private SymbolicType integerType;
	private SymbolicExpression intArr_a;

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		two = universe.integer(2);
		six = universe.integer(6);
		integerType = universe.integerType();
		a_obj = universe.stringObject("a");
		intArr_a = universe.symbolicConstant(
				a_obj, universe.arrayType(integerType));
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

}
