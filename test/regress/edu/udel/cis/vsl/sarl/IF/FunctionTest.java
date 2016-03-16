package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class FunctionTest {
	public final static PrintStream out = System.out;
	public final static boolean debug = true;
	private SymbolicUniverse universe;
	private SymbolicType integerType;
	private SymbolicCompleteArrayType arrayType;
	private NumericSymbolicConstant x, a, b;
	private NumericExpression one, two, four;
	
	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		integerType = universe.integerType();
		x = (NumericSymbolicConstant) universe.symbolicConstant(
				universe.stringObject("x"), integerType);
		arrayType = universe.arrayType(integerType, x);
		a = (NumericSymbolicConstant) universe.symbolicConstant(
				universe.stringObject("a"), integerType);
		b = (NumericSymbolicConstant) universe.symbolicConstant(
				universe.stringObject("b"), integerType);
		one = universe.integer(1);
		two = universe.integer(2);
		four = universe.integer(4);
	}
	
	@After
	public void tearDown() throws Exception {
	}
	
	@Test
	public void arrayLambdaTest() {
		SymbolicExpression function1;
		SymbolicExpression arrayL1;
		SymbolicExpression function2;
		SymbolicExpression arrayL2;
		
		function1 = universe.lambda(a, universe.multiply(a, a));
		arrayL1 = universe.arrayLambda(arrayType, function1);
		function2 = universe.lambda(b, universe.add(b, one));
		arrayL2 = universe.arrayLambda(arrayType, function2);

		assertEquals(universe.multiply(two, two), universe.arrayRead(arrayL1, two));
		assertEquals(universe.add(two, one), universe.arrayRead(arrayL2, universe.integer(2)));
	}
	
	@Test
	public void applyTest(){
		SymbolicExpression function1;
		function1 = universe.lambda(a, universe.multiply(a, a));
		SymbolicExpression function2;
		List<SymbolicExpression> args1 = new ArrayList<SymbolicExpression>();
		args1.add(two);
		function2 = universe.lambda(b, universe.multiply(b, (NumericExpression)universe.apply(function1, args1)));
		List<SymbolicExpression> args2 = new ArrayList<SymbolicExpression>();
		args2.add(four);
		SymbolicExpression r = universe.apply(function2, args2);
		if(debug){
			out.println(r);
		}
		assertEquals(universe.multiply(four, universe.multiply(two, two)), r);
	}
	
	/**
	 * test function type
	 */
	@Test
	public void applyTest2(){
		
	}
}
