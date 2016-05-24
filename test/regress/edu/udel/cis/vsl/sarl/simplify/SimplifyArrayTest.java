package edu.udel.cis.vsl.sarl.simplify;

import static org.junit.Assert.assertTrue;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class SimplifyArrayTest {

	private static SymbolicUniverse universe = SARL.newIdealUniverse();

	private static SymbolicType realType = universe.realType();

	private static SymbolicType integerType = universe.integerType();

	private static NumericExpression zero = universe.integer(0), one = universe
			.integer(1), two = universe.integer(2),
			three = universe.integer(3);

	private static NumericSymbolicConstant N = (NumericSymbolicConstant) universe
			.symbolicConstant(universe.stringObject("N"), integerType);

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@Before
	public void setUp() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}

	@Test
	public void test() {
		BooleanExpression claim = universe.equals(N, three);
		SymbolicArrayType arrayType1 = universe.arrayType(realType, N);
		SymbolicConstant a1 = universe.symbolicConstant(
				universe.stringObject("a"), arrayType1);
		SymbolicExpression x1 = universe.add(universe.add(
				(NumericExpression) universe.arrayRead(a1, zero),
				(NumericExpression) universe.arrayRead(a1, one)),
				(NumericExpression) universe.arrayRead(a1, two));
		Reasoner reasoner = universe.reasoner(claim);
		SymbolicExpression x2 = reasoner.simplify(x1);
		SymbolicExpression x3 = reasoner.simplify(x1);

		System.out.println(x1.toStringBufferLong());
		System.out.println(x2.toStringBufferLong());
		System.out.println(x3.toStringBufferLong());
	}

	/**
	 * define an array of type int[n] and initialize it as A: int[n] array=A
	 * 
	 * then define my array and use array lambda to initialize it:
	 * myArray=lambda i. A[i]
	 * 
	 * specify quantified expression: forall j: 0 .. n-1. myArray[j]== array[j]
	 */
	@Test
	public void arrayLambda() {
		SymbolicConstant i = universe.symbolicConstant(
				universe.stringObject("i"), integerType);
		NumericExpression n = (NumericExpression) universe.symbolicConstant(
				universe.stringObject("n"), integerType);
		SymbolicCompleteArrayType arrayType = universe
				.arrayType(integerType, n);
		SymbolicExpression array = universe.symbolicConstant(
				universe.stringObject("A"), arrayType);
		SymbolicExpression lambda = universe.lambda(i,
				universe.arrayRead(array, (NumericExpression) i));
		SymbolicExpression myArray = universe.arrayLambda(arrayType, lambda);
		NumericSymbolicConstant j = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("j"), integerType);
		SymbolicExpression quantified = universe.forallInt(
				j,
				zero,
				universe.subtract(n, one),
				universe.equals(universe.arrayRead(myArray, j),
						universe.arrayRead(array, j))), simplified;
		Reasoner reasoner = universe.reasoner(universe.trueExpression());

		// System.out.println(quantified);
		simplified = reasoner.simplify(quantified);
		// System.out.println(simplified);
		assertTrue(simplified.isTrue());
	}
}
