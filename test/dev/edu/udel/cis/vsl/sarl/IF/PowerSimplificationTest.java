package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;

public class PowerSimplificationTest {
	private static SymbolicUniverse universe = SARL.newStandardUniverse();
	private NumericExpression NUM_0 = universe.rational(0.0);
	private NumericExpression NUM_1 = universe.rational(1.0);
	private NumericExpression NUM_2 = universe.rational(2.0);
	private NumericExpression NUM_3 = universe.rational(3.0);
	private NumericExpression NUM_4 = universe.rational(4.0);
	private NumericExpression NUM_1D2 = universe.divide(NUM_1, NUM_2);

	/**
	 * baseMonic = -1/3 <br>
	 * baseMonomial = 1-sqrt(2) <br>
	 * base = (-1/3)*(1-sqrt(2)) <br>
	 * expr = sqrt( (-1/3)*(1-sqrt(2)) ) <br>
	 * pred: 0 < sqrt( (-1/3)*(1-sqrt(2)) ) <br>
	 * <p>
	 * The <code>pred</code> should be <code>true</code>, because the square
	 * root of a positive number should be positive.
	 * </p>
	 * <strong>Note: this expression CAN be simplified but the pred returns a
	 * WRONG answer</strong>
	 */
	@Test
	public void power_simple() {
		NumericExpression baseMonic = universe
				.minus(universe.divide(NUM_1, NUM_3));
		NumericExpression baseMonomial = universe.subtract(NUM_1,
				universe.power(NUM_2, NUM_1D2));
		NumericExpression base = universe.multiply(baseMonic, baseMonomial);
		NumericExpression expr = universe.power(base, NUM_1D2);
		BooleanExpression pred = universe.lessThan(NUM_0, expr);
		pred.printCompressedTree(System.out);
		assertTrue(pred.isTrue());
	}

	/**
	 * baseMonic = -4/3 <br>
	 * baseMonomial = sqrt(2)-3 <br>
	 * base = (-4/3)*(sqrt(2)-3) <br>
	 * expr = sqrt( (-4/3)*(sqrt(2)-3) ) <br>
	 * pred: 0 < sqrt( (-4/3)*(sqrt(2)-3) ) <br>
	 * <p>
	 * The <code>pred</code> should be <code>true</code>, because the square
	 * root of a positive number should be positive.
	 * </p>
	 * <strong>Note: this expression can NOT be simplified so that the base for
	 * the method nthRoot is negative and an exception is thrown</strong>
	 */
	@Test
	public void power_complex1() {
		NumericExpression baseMonic = universe
				.minus(universe.divide(NUM_4, NUM_3));
		NumericExpression baseMonomial = universe
				.subtract(universe.power(NUM_2, NUM_1D2), NUM_3);
		NumericExpression base = universe.multiply(baseMonic, baseMonomial);
		NumericExpression expr = universe.power(base, NUM_1D2);
		BooleanExpression pred = universe.lessThan(NUM_0, expr);
		expr.printCompressedTree(System.out);
		assertTrue(pred.isTrue());
	}
}
