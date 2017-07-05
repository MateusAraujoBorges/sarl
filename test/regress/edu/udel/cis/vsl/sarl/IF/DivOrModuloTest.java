package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class DivOrModuloTest {
	private SymbolicUniverse universe;
	private SymbolicType integerType;
	private NumericExpression x;
	private NumericExpression y;
	private NumericExpression z;
	private NumericExpression a;
	private NumericExpression b;
	private NumericExpression c;
	private NumericExpression d;
	private NumericExpression two;
	private NumericExpression zero;
	private NumericExpression one;

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		universe.setShowProverQueries(true);
		integerType = universe.integerType();
		x = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("x"), integerType);
		y = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("y"), integerType);
		z = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("z"), integerType);
		a = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("a"), integerType);
		b = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("b"), integerType);
		c = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("c"), integerType);
		d = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("d"), integerType);
		two = universe.integer(2);
		zero = universe.integer(0);
		one = universe.integer(1);
	}

	/**
	 * Note: cvc4 can not solve this problem without translation TODO: z3 is not
	 * used?
	 * 
	 * assumption: x/y = 2 predicate: x != y
	 * 
	 * result true;
	 */
	@Test
	public void divisionTest1() {
		BooleanExpression constraints = universe.and(
				universe.lessThanEquals(zero, x), universe.lessThan(zero, y));
		BooleanExpression assumption = universe.and(constraints,
				universe.equals(two, universe.divide(x, y)));
		BooleanExpression predicate = universe.neq(x, y);
		Reasoner r = universe.reasoner(assumption);

		ValidityResult result = r.valid(predicate);
		assertEquals(ResultType.YES, result.getResultType());
	}

	/**
	 * Assumption: x^2 + y = 1, x^2 - y = 1. Conclusion: y=0.
	 * 
	 * predicate: y = 0
	 */
	@Test
	public void divisionTest2() {
		BooleanExpression x2py = universe.equals(one,
				universe.add(y, universe.multiply(x, x)));
		BooleanExpression x2my = universe.equals(one,
				universe.subtract(universe.multiply(x, x), y));
		BooleanExpression assumption = universe.and(x2py, x2my);
		BooleanExpression predicate = universe.equals(y, zero);
		Reasoner r = universe.reasoner(assumption);

		ValidityResult result = r.valid(predicate);
		assertEquals(ResultType.YES, result.getResultType());
	}

	/**
	 * assumption: x/y=z predicate: x!=z
	 * 
	 * expected result: no
	 */
	@Test
	public void divisionTest3() {
		BooleanExpression assumption = universe.and(
				universe.equals(z, universe.divide(x, y)),
				universe.neq(y, zero));
		BooleanExpression predicate = universe.neq(x, z);
		Reasoner r = universe.reasoner(assumption);

		ValidityResult result = r.valid(predicate);
		assertEquals(ResultType.NO, result.getResultType());
	}

	/**
	 * assumption: x%y = 2 predicate: x != y
	 * 
	 * expected result true;
	 */
	@Test
	public void moduloTest1() {
		BooleanExpression assumption = universe.and(
				universe.equals(two, universe.modulo(x, y)),
				universe.neq(y, zero));
		BooleanExpression predicate = universe.neq(x, y);
		Reasoner r = universe.reasoner(assumption);

		ValidityResult result = r.valid(predicate);
		assertEquals(ResultType.YES, result.getResultType());
	}

	@Test
	public void divisionTest4() {
		BooleanExpression assumption1 = universe.equals(two,
				universe.add(universe.divide(a, b), universe.divide(c, d)));
		BooleanExpression assumption2 = universe.and(universe.lessThan(zero, b),
				universe.lessThan(zero, d));
		BooleanExpression assumption3 = universe.and(
				universe.lessThanEquals(zero, a),
				universe.lessThanEquals(zero, c));
		BooleanExpression assumption = universe
				.and(universe.and(assumption1, assumption2), assumption3);
		BooleanExpression predicate = universe.equals(two,
				universe.divide(a, c));
		Reasoner r = universe.reasoner(assumption);

		ValidityResult result = r.valid(predicate);
		assertEquals(ResultType.NO, result.getResultType());
	}

}
