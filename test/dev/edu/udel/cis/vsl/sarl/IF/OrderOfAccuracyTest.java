package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.io.PrintStream;
import java.util.Arrays;

import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class OrderOfAccuracyTest {

	private static PrintStream out = System.out;

	private static SymbolicUniverse universe = SARL.newStandardUniverse();

	private static SymbolicType real = universe.realType();

	private static SymbolicFunctionType r2 = universe
			.functionType(Arrays.asList(real, real), real);
	private static SymbolicConstant f = universe
			.symbolicConstant(universe.stringObject("f"), r2);

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@Test
	public void deriv1() {
		SymbolicExpression df0 = universe.derivative(f, universe.intObject(0),
				universe.intObject(1));

		out.println(df0);
		assertEquals(f, df0.argument(0));
		assertEquals(universe.intObject(0), df0.argument(1));
		assertEquals(universe.intObject(1), df0.argument(2));
		assertEquals(3, df0.numArguments());
	}

	@Test
	public void diff1() {
		BooleanExpression diff = universe.differentiable(f,
				universe.intObject(4),
				Arrays.asList(universe.rational(1.0), universe.rational(2.0)),
				Arrays.asList(universe.rational(2.0), universe.rational(3.0)));

		out.println(diff);
		assertEquals(f, diff.argument(0));
		assertEquals(universe.intObject(4), diff.argument(1));
	}

	@Test
	public void taylor1() {
		// f(x0+h0,y0) = 
	}

}
