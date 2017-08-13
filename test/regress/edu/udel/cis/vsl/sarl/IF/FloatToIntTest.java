package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

import java.io.PrintStream;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class FloatToIntTest {

	public final static PrintStream out = System.out;

	private static SymbolicUniverse universe = SARL.newStandardUniverse();

	private static SymbolicType realType = universe.realType();

	private static SymbolicType integerType = universe.integerType();

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
	public void castTest() {
		StringObject xname = universe.stringObject("x");
		// $real floatX; (a real number)
		SymbolicExpression floatX = universe.symbolicConstant(xname, realType);
		// intY = (int) x;
		SymbolicExpression intY = universe.cast(integerType, floatX);
		// floatY = ($real) intY;
		SymbolicExpression floatY = universe.cast(realType, intY);
		BooleanExpression xEqualsY = universe.equals(floatX, floatY);
		Reasoner reasoner = universe.reasoner(universe.trueExpression());
		// checks if floatX equals floatY?
		ValidityResult result = reasoner.valid(xEqualsY);

		// the result should NOT be YES
		assertFalse(result.getResultType() == ResultType.YES);
	}

	@Test
	public void floor1() {
		NumericExpression x = universe.rational(3, 2);

		assertEquals(universe.integer(1), universe.floor(x));
	}

	@Test
	public void floor2() {
		NumericExpression x = universe.minus(universe.rational(3, 2));

		assertEquals(universe.integer(-2), universe.floor(x));
	}

	@Test
	public void ceil1() {
		NumericExpression x = universe.rational(3, 2);

		assertEquals(universe.integer(2), universe.ceil(x));
	}

	@Test
	public void ceil2() {
		NumericExpression x = universe.minus(universe.rational(3, 2));

		assertEquals(universe.integer(-1), universe.ceil(x));
	}

	@Test
	public void roundToZero1() {
		NumericExpression x = universe.rational(3, 2);

		assertEquals(universe.integer(1), universe.roundToZero(x));
	}

	@Test
	public void roundToZero2() {
		NumericExpression x = universe.minus(universe.rational(3, 2));

		assertEquals(universe.integer(-1), universe.roundToZero(x));
	}

	@Test
	public void realInts() {
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("x"), integerType);
		NumericExpression y = (NumericExpression) universe.cast(realType, x);

		assertEquals(x, universe.ceil(y));
		assertEquals(x, universe.floor(y));
		assertEquals(x, universe.roundToZero(y));
	}

	@Test
	public void noSimp() {
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("x"), realType);

		out.println("floor(x) = " + universe.floor(x));
		out.println("ceil(x) = " + universe.ceil(x));
		out.println("roundToZero(x) = " + universe.roundToZero(x));
		out.println("(int)x = " + universe.cast(integerType, x));
		out.flush();
	}
}
