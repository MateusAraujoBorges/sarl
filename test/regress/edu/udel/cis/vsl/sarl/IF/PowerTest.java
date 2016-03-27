package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.io.PrintStream;

import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicRealType;

public class PowerTest {

	public final static boolean debug = true;

	public final static PrintStream out = System.out;

	public final static SymbolicUniverse universe = SARL.newStandardUniverse();

	public final static Reasoner reasoner = universe
			.reasoner(universe.trueExpression());

	public final static SymbolicRealType real = universe.realType();

	public final static NumericExpression x = (NumericExpression) universe
			.symbolicConstant(universe.stringObject("x"), real);

	public final static NumericExpression y = (NumericExpression) universe
			.symbolicConstant(universe.stringObject("y"), real);

	public final static NumericExpression z = (NumericExpression) universe
			.symbolicConstant(universe.stringObject("z"), real);

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	public final static void debug(String msg) {
		if (debug) {
			out.println(msg);
			out.flush();
		}
	}

	@Test
	public void sqaureRootOfSquare() {
		NumericExpression x2 = universe.power(x, 2);
		NumericExpression x3 = universe.power(x2, universe.rational(1, 2));

		debug("x2 = " + x2);
		debug("x2^(1/2) = " + x3);
		assertEquals(x, x3);
	}

	@Test
	public void powerOfPower() {
		NumericExpression xy = universe.power(x, y);
		NumericExpression xyz = universe.power(xy, z);

		debug("x^y = " + xy);
		debug("(x^y)^z = " + xyz);

		NumericExpression expected = universe.power(x, universe.multiply(y, z));

		debug("expected = " + expected);
		assertEquals(expected, xyz);
	}

	@Test
	public void neg1Exp() {
		NumericExpression xToNeg1 = universe.power(x, universe.integer(-1));
		NumericExpression expected = universe.divide(universe.rational(1), x);

		debug("xToNeg1 = " + xToNeg1);
		debug("expected = " + expected);
		assertEquals(expected, xToNeg1);
	}

	@Test
	public void intInExp() {
		NumericExpression x2y = universe.power(x,
				universe.multiply(universe.rational(2), y));
		NumericExpression expected = universe.power(universe.power(x, y),
				universe.intObject(2));

		debug("x^(2y) = " + x2y);
		assertEquals(expected, x2y);
	}

	@Test
	public void simpProd1() {
		NumericExpression sqrtx = universe.power(x, universe.rational(1, 2));
		NumericExpression x32 = universe.multiply(x, sqrtx);
		NumericExpression x32s = reasoner.simplify(x32);
		NumericExpression expected = universe.power(x, universe.rational(3, 2));

		debug("sqrt(x) = " + sqrtx);
		debug("x*sqrt(x) = " + x32);
		debug("simplified x*sqrt(x) = " + x32s);
		debug("x^(3/2) = " + expected);
		assertEquals(expected, x32s);
	}

	@Test
	public void sqrtxsq() {
		NumericExpression sqrtx = universe.power(x, universe.rational(1, 2));
		NumericExpression y = universe.multiply(sqrtx, sqrtx);
		NumericExpression ys = reasoner.simplify(y);

		assertEquals(x, ys);
	}

}
