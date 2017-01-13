package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.PrintStream;
import java.util.Arrays;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicIntegerType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class SimplifyTest {

	static PrintStream out = System.out;

	static SymbolicUniverse universe = SARL.newStandardUniverse();

	static SymbolicIntegerType intType = universe.integerType();

	static NumericExpression zero = universe.integer(0);

	static NumericExpression one = universe.integer(1);

	static NumericExpression two = universe.integer(2);

	static NumericExpression three = universe.integer(3);

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
	}

	@Before
	public void setUp() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}

	@Test
	public void invalidInterval() {
		SymbolicUniverse universe = SARL.newStandardUniverse();
		SymbolicConstant X = (SymbolicConstant) universe
				.canonic(universe.symbolicConstant(universe.stringObject("X"),
						universe.integerType()));
		// context: X<1 && 1<X
		BooleanExpression context = (BooleanExpression) universe.and(
				universe.lessThan((NumericExpression) X, universe.oneInt()),
				universe.lessThan(universe.oneInt(), (NumericExpression) X));
		Reasoner reasoner = universe.reasoner(context);
		// SARL crashes here
		Interval interval = reasoner.assumptionAsInterval(X);

		assertTrue(interval == null);
	}

	@Test
	public void simplify() {
		SymbolicUniverse univ = SARL.newStandardUniverse();
		SymbolicConstant X1 = (SymbolicConstant) univ.canonic(univ
				.symbolicConstant(univ.stringObject("X1"), univ.integerType()));
		SymbolicConstant X2 = (SymbolicConstant) univ.canonic(univ
				.symbolicConstant(univ.stringObject("X2"), univ.integerType()));
		BooleanExpression contex = (BooleanExpression) univ
				.canonic(univ.equals(univ.integer(4),
						univ.canonic(univ.multiply((NumericExpression) X1,
								(NumericExpression) X2))));
		Reasoner reasoner;

		contex = (BooleanExpression) univ
				.canonic(univ.and(contex, (BooleanExpression) univ
						.canonic(univ.equals(X1, univ.integer(1)))));
		reasoner = univ.reasoner(contex);
		System.out.println(contex.toString());
		contex = reasoner.getReducedContext();
		System.out.println(contex.toString());
	}

	@Test
	public void test() {
		NumericExpression x = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("x"), intType);
		SymbolicCompleteArrayType arrayType = universe.arrayType(intType, x);
		NumericSymbolicConstant index = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("i"), intType);
		SymbolicExpression arrayLambda = universe.arrayLambda(arrayType,
				universe.lambda(index, index));

		// out.println(arrayLambda);
		out.println(universe);

		BooleanExpression context = universe.equals(x, three);
		Reasoner reasoner = universe.reasoner(context);
		SymbolicExpression simplifiedArrayLambda = reasoner
				.simplify(arrayLambda);
		SymbolicExpression concreteArray = universe.array(intType,
				Arrays.asList(zero, one, two));

		out.println(simplifiedArrayLambda);
		out.flush();

		assertEquals(concreteArray, simplifiedArrayLambda);
	}

	@Test
	public void divideTest() {
		NumericExpression a = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("a"), intType);
		NumericExpression b = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("a"), intType);
		BooleanExpression precon = universe.equals(universe.integer(3),
				universe.divide(a, b));
		BooleanExpression predicate = universe.equals(a,
				universe.multiply(b, universe.integer(3)));
		BooleanExpression e = universe.forall((SymbolicConstant) a,
				universe.implies(precon, predicate));
		Reasoner r = universe.reasoner(universe.bool(true));
		r.isValid(e);
	}

	/**
	 * Assumption: 0==(sigma(0,Y1*Y2 - 1,lambda k : int . (Y8[k]*Y9[k])) -
	 * 1*Y12) && 0==(Y1*Y2 - 1*Y11) <br>
	 * <br>
	 * Predicate: 0==(sigma(0,Y11 - 1,lambda t : int . (Y8[t]*Y9[t])) - 1*Y12)
	 * 
	 * cvc3 required
	 */
	@Test
	public void sigmaReasoning() {
		// 0==(sigma(0,Y1*Y2 - 1,lambda k : int . (Y8[k]*Y9[k])) -
		// 1*Y12)
		NumericSymbolicConstant Y1 = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("Y1"),
						universe.integerType());
		NumericSymbolicConstant Y2 = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("Y2"),
						universe.integerType());
		NumericSymbolicConstant Y11 = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("Y11"),
						universe.integerType());
		NumericSymbolicConstant Y12 = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("Y12"),
						universe.realType());
		SymbolicType arrayType = universe.arrayType(universe.realType(),
				universe.integer(10));
		SymbolicExpression Y8 = universe
				.symbolicConstant(universe.stringObject("Y8"), arrayType);
		SymbolicExpression Y9 = universe
				.symbolicConstant(universe.stringObject("Y9"), arrayType);
		NumericSymbolicConstant k = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("k"),
						universe.integerType());
		SymbolicExpression Y8_k_times_Y9_k = universe.multiply(
				(NumericExpression) universe.arrayRead(Y8, k),
				(NumericExpression) universe.arrayRead(Y9, k));
		SymbolicExpression lambda = universe.lambda(k,
				Y8_k_times_Y9_k);
		NumericExpression Y1_times_Y2_minus_1 = universe
				.subtract(universe.multiply(Y1, Y2), universe.oneInt());
		NumericExpression Y11_minus_1 = universe.subtract(Y11,
				universe.oneInt());
		SymbolicExpression sigma = universe.sigma(universe.zeroInt(),
				Y1_times_Y2_minus_1, lambda);
		BooleanExpression pred_sigma_eq_Y12 = universe.equals(sigma, Y12);
		// 0==(Y1*Y2 - 1*Y11)
		BooleanExpression Y1_times_Y2_eq_Y11 = universe
				.equals(universe.multiply(Y1, Y2), Y11);
		// 0==(sigma(0,Y11 - 1,lambda t : int . (Y8[t]*Y9[t])) - 1*Y12)

		lambda = universe.lambda(k, Y8_k_times_Y9_k);
		// sigma = universe.sigma(universe.zeroInt(), Y11_minus_1, lambda);
		sigma = universe.sigma(universe.zeroInt(), Y11_minus_1, lambda);
		BooleanExpression assu_sigma_eq_Y12 = universe.equals(Y12, sigma);
		BooleanExpression assumptions = universe
				.and(Arrays.asList(Y1_times_Y2_eq_Y11, assu_sigma_eq_Y12));

		universe.setShowProverQueries(true);
		Reasoner reasoner = universe.reasoner(assumptions);

		ResultType resultType = reasoner.valid(pred_sigma_eq_Y12)
				.getResultType();
		assertEquals(resultType, ResultType.YES);
	}

}
