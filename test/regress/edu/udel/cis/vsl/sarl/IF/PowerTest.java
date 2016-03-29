package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.io.PrintStream;
import java.util.Arrays;

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

	private NumericExpression sqrt(NumericExpression expr) {
		return universe.power(expr, universe.rational(1, 2));
	}

	@Test
	public void sqaureRootOfSquare() {
		NumericExpression x2 = universe.power(x, 2);
		NumericExpression x3 = sqrt(x2);

		debug("x2 = " + x2);
		debug("x2^(1/2) = " + x3);
		assertEquals(x, x3);
	}
	
	/**
	 * Expression = ((-x)^2)^(1/2)
	 * Actual = Pow(Pow(-x, 2), (1/2));
	 * Expected = x;
	 */
	@Test
	public void squareRootOfSquare_NegBase_EvenExp(){
		NumericExpression neg_x = universe.minus(x);
		NumericExpression pow2_neg_x = universe.power(neg_x, 2);
		NumericExpression actualResult = sqrt(pow2_neg_x); 
		NumericExpression expectedResult = x;
		
		debug("Actual: " + actualResult);
		debug("Expected: " + expectedResult);
		assertEquals(expectedResult, actualResult);
	}

	/**
	 * Expression = ((-x)^3)^(1/3)
	 * Actual = Pow(Pow(-x, 3), (1/3));
	 * Expected = -x;
	 */
	@Test
	public void squareRootOfSquare_NegBase_OddExp(){
		NumericExpression neg_x = universe.minus(x);
		NumericExpression pow3_neg_x = universe.power(neg_x, 3);
		NumericExpression actualResult = universe.power(pow3_neg_x, universe.rational(1, 3)); 
		NumericExpression expectedResult = neg_x;

		debug("Actual: " + actualResult);
		debug("Expected: " + expectedResult);
		assertEquals(expectedResult, actualResult);
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
		NumericExpression sqrtx = sqrt(x);
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
		NumericExpression sqrtx = sqrt(x);
		NumericExpression y = universe.multiply(sqrtx, sqrtx);
		NumericExpression ys = reasoner.simplify(y);

		assertEquals(x, ys);
	}

	@Test
	public void sqrtx_y_sqrtx() {
		NumericExpression sqrtx = sqrt(x);
		NumericExpression w = universe.multiply(Arrays.asList(sqrtx, y, sqrtx));

		debug("w = " + w);

		NumericExpression ws = reasoner.simplify(w);

		debug("ws = " + ws);
		assertEquals(universe.multiply(x, y), ws);
	}

	@Test
	public void x_div_sqrtx() {
		NumericExpression sqrtx = sqrt(x);
		NumericExpression w = universe.divide(x, sqrtx);

		debug("w = " + w);

		NumericExpression ws = reasoner.simplify(w);

		debug("ws = " + ws);
		assertEquals(sqrtx, ws);
	}

	/**
	 * Multiply powers with the same base: (x^y)*(x^z)=x^(y+z)
	 */
	@Test
	public void multiplyPower() {
		NumericExpression e1 = universe.multiply(universe.power(x, y),
				universe.power(x, z));
		NumericExpression e2 = universe.power(x, universe.add(y, z));

		debug("left " + e1);
		debug("left simplied " + reasoner.simplify(e1));
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * Divide powers with the same base: (x^y)/(x^z) =x^(y-z).
	 */
	@Test
	public void dividePower() {
		NumericExpression e1 = universe.divide(universe.power(x, y),
				universe.power(x, z));
		NumericExpression e2 = universe.power(x, universe.subtract(y, z));

		debug("left " + e1);
		debug("left simplied " + reasoner.simplify(e1));
		debug("right " + e2);
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * When raising a product to a power, raise each factor with a power:
	 * 
	 * <pre>
	 * (xy)^z = (x^z)(y^z)
	 * </pre>
	 */
	@Test
	public void productToPower() {
		NumericExpression e1 = universe.power(universe.multiply(x, y), z);
		NumericExpression e2 = universe.multiply(universe.power(x, z),
				universe.power(y, z));

		debug("left " + e1);
		debug("right" + e2);
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * When raising a quotient to a power, raise both the numerator and the
	 * denominator to the power.
	 * 
	 * <pre>
	 * (x/y)^z = (x^z)/(y^z)
	 * </pre>
	 */
	@Test
	public void quotientToPower() {
		NumericExpression e1 = universe.power(universe.divide(x, y), z);
		NumericExpression e2 = universe.divide(universe.power(x, z),
				universe.power(y, z));

		debug("left " + e1);
		debug("right" + e2);
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * Raise any number(except 0 itself) to a zero power you'll always get 1
	 */
	@Test
	public void zeroExponent() {
		NumericExpression e1 = universe.power(universe.power(x, y),
				universe.zeroReal());
		NumericExpression e2 = universe.power(z, universe.zeroReal());

		debug("left " + e1);
		debug("right " + e2);
		assertEquals(universe.oneReal(), reasoner.simplify(e1));
		assertEquals(universe.oneReal(), reasoner.simplify(e2));
	}

	/**
	 * 0^0 exception
	 */
	@Test(expected = SARLException.class)
	public void zeroExponentZero() {
		NumericExpression e1 = universe.power(universe.zeroReal(),
				universe.zeroReal());

		debug("left " + e1);
		assertEquals(universe.oneReal(), reasoner.simplify(e1));
	}

	/**
	 * x^1 = x
	 */
	@Test
	public void powerOne() {
		NumericExpression e1 = universe.power(x, universe.oneReal());

		debug("left " + e1);
		assertEquals(x, reasoner.simplify(e1));
	}

	/**
	 * x^(-y) = 1/(x^y)
	 */
	@Test
	public void negativeExponent() {
		NumericExpression e1 = universe.power(x, universe.minus(y));
		NumericExpression e2 = universe.divide(universe.oneReal(),
				universe.power(x, y));

		debug("left " + e1);
		debug("right " + e2);
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e1));
	}
}
