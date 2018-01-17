package edu.udel.cis.vsl.sarl.ideal.simplify;

import static edu.udel.cis.vsl.sarl.ideal.simplify.CommonObjects.idealSimplifier;
import static edu.udel.cis.vsl.sarl.ideal.simplify.CommonObjects.idealSimplifierFactory;
import static edu.udel.cis.vsl.sarl.ideal.simplify.CommonObjects.preUniv;
import static edu.udel.cis.vsl.sarl.ideal.simplify.CommonObjects.rat0;
import static edu.udel.cis.vsl.sarl.ideal.simplify.CommonObjects.rat2;
import static edu.udel.cis.vsl.sarl.ideal.simplify.CommonObjects.rat25;
import static edu.udel.cis.vsl.sarl.ideal.simplify.CommonObjects.ratNeg25;
import static edu.udel.cis.vsl.sarl.ideal.simplify.CommonObjects.trueExpr;
import static edu.udel.cis.vsl.sarl.ideal.simplify.CommonObjects.x;
import static edu.udel.cis.vsl.sarl.ideal.simplify.CommonObjects.xeq5;
import static org.junit.Assert.assertEquals;

import java.util.Arrays;

import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.CoreUniverse.ForallStructure;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.simplify.IF.Simplifier;

/**
 * Testing on IdealSimplifier based on Polynomials using methods -
 * getFullContext() - getReducedContext()
 * 
 * 
 * @author mbrahma
 */

public class IdealSimplifierTest {

	private final static boolean useBackwardSubstitution = true;

	private static BooleanExpression boolArg1, boolArg2;

	/**
	 * Calls the setUp() method in CommonObjects to make use of consolidated
	 * SARL object declarations and initializations for testing of "Simplify"
	 * module. Also initialized objects in the CommonObjects class that are used
	 * often and therefore not given an initial value.
	 * 
	 * @throws java.lang.Exception
	 */

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
		CommonObjects.setUp();

	}

	/**
	 * @throws java.lang.Exception
	 */

	@After
	public void tearDown() throws Exception {
	}

	/**
	 * Test on IdealSimplifier to check if a exception is thrown and if it is
	 * the correct one.
	 */
	@Test(expected = NullPointerException.class)
	public void getFullContextTextTestnull() {

		idealSimplifier = idealSimplifierFactory.newSimplifier(null,
				useBackwardSubstitution);
		BooleanExpression boolNull = idealSimplifier.getFullContext();
		assertEquals(null, boolNull);

	}

	/**
	 * Test on IdealSimplifier to get full context
	 */
	public void getFullContextTextTestTrivial() {

		idealSimplifier = idealSimplifierFactory.newSimplifier(xeq5,
				useBackwardSubstitution);
		BooleanExpression boolXEq5 = idealSimplifier.getFullContext();
		assertEquals(xeq5, boolXEq5);

	}

	/**
	 * Test on IdealSimplifier to get full context
	 */
	public void getFullContextTestTrivial1() {
		boolArg1 = preUniv.lessThanEquals(rat25, preUniv.multiply(x, x));
		Simplifier simpEq1 = idealSimplifierFactory.newSimplifier(boolArg1,
				useBackwardSubstitution);
		BooleanExpression boolSimpEq1 = simpEq1.getFullContext();
		assertEquals(
				preUniv.lessThanEquals(rat0,
						preUniv.add(ratNeg25, preUniv.multiply(x, x))),
				boolSimpEq1);
	}

	/**
	 * Test on IdealSimplifier to get full context
	 */
	public void getFullContextTestTrivial2() {
		boolArg2 = preUniv.lessThanEquals(rat2, preUniv.multiply(x, x));
		Simplifier simpEq2 = idealSimplifierFactory.newSimplifier(boolArg2,
				useBackwardSubstitution);
		BooleanExpression boolSimpEq2 = simpEq2.getFullContext();
		assertEquals(boolArg2, boolSimpEq2);
	}
	/*
	 * @Test public void getFullReducedQuadTest(){ boolArg1 =
	 * preUniv.lessThanEquals(twenty_five, xpyInt); boolArg2 =
	 * preUniv.lessThan(five, yInt);
	 * 
	 * //IdealSimplifier idealSimp1 =
	 * idealSimplifierFactory.newSimplifier(boolArg1); //IdealSimplifier
	 * idealSimp2 = idealSimplifierFactory.newSimplifier(boolArg2);
	 * 
	 * 
	 * //BooleanExpression boolExpr1 = idealSimp1.getReducedContext();
	 * //BooleanExpression boolExpr2 = idealSimp2.getReducedContext();
	 * 
	 * assumption = preUniv.equals(boolArg1, boolArg2); idealSimplifier =
	 * idealSimplifierFactory.newSimplifier(assumption); BooleanExpression
	 * boolExpr = idealSimplifier.getFullContext();
	 * 
	 * assertEquals(boolArg1,boolExpr);
	 * 
	 * }
	 */

	/**
	 * Test on IdealSimplifier to get reduced context
	 */

	@Test
	public void getReducedContextTest() {
		CommonObjects.setUp();
		idealSimplifier = idealSimplifierFactory.newSimplifier(trueExpr,
				useBackwardSubstitution);
		BooleanExpression boolTrue = idealSimplifier.getReducedContext();
		assertEquals(trueExpr, boolTrue);

		boolArg2 = preUniv.lessThanEquals(rat2, preUniv.multiply(x, x));
		Simplifier simpEq2 = idealSimplifierFactory.newSimplifier(boolArg2,
				useBackwardSubstitution);
		BooleanExpression boolSimpEq2 = simpEq2.getReducedContext();
		assertEquals(boolArg2, boolSimpEq2);
	}

	@Test
	public void getForallStructure() {
		SymbolicUniverse universe = SARL.newIdealUniverse();

		NumericSymbolicConstant i = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("i"),
						universe.integerType());
		NumericSymbolicConstant j = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("j"),
						universe.integerType());
		BooleanExpression body = universe.equals(i, j);
		NumericSymbolicConstant low = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("low"),
						universe.integerType());
		NumericSymbolicConstant high = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("high"),
						universe.integerType());

		BooleanExpression forall0 = universe.forallInt(j, low, high, body);

		forall0 = universe.forallInt(i, low, high, forall0);

		ForallStructure structure0 = universe.getForallStructure(forall0);

		assert structure0 != null;
		// another way of constructing forall-predicate causes the failure of
		// find the pattern ...
		body = universe.implies(universe.and(universe.lessThanEquals(low, j),
				universe.lessThan(j, high)), body);
		body = universe.implies(universe.and(universe.lessThanEquals(low, i),
				universe.lessThan(i, high)), body);
		BooleanExpression forall1 = universe.forall(j, body);

		forall1 = universe.forall(i, forall1);

		ForallStructure structure1 = universe.getForallStructure(forall1);

		assert structure1 != null;
	}

	/**
	 * context: 0 <= x && x < 5 && 0 <= y && y < 5 && $forall (int i | i == 0 ||
	 * i == x) ($forall (int j | j == 0 || j == y) a[i][j] == 0)
	 * 
	 * the program "stuck" at when using a reasoner of this context simplifies
	 * not(context).
	 */
	@Test
	public void verySlowSimplification() {
		SymbolicUniverse universe = SARL.newIdealUniverse();

		universe.setUseBackwardSubstitution(true);

		NumericSymbolicConstant i = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("i"),
						universe.integerType());
		NumericSymbolicConstant j = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("j"),
						universe.integerType());
		NumericSymbolicConstant x = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("X_x"),
						universe.integerType());
		NumericSymbolicConstant y = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("X_y"),
						universe.integerType());
		NumericExpression five = universe.integer(5);
		SymbolicExpression array = universe.symbolicConstant(
				universe.stringObject("X_a"),
				universe.arrayType(
						universe.arrayType(universe.integerType(), five),
						five));

		BooleanExpression outerRestrict = universe.or(
				universe.equals(i, universe.zeroInt()), universe.equals(i, x));
		BooleanExpression innerRestrict = universe.or(
				universe.equals(j, universe.zeroInt()), universe.equals(j, y));
		BooleanExpression assumption = universe.and(
				Arrays.asList(universe.lessThanEquals(universe.zeroInt(), x),
						universe.lessThan(x, five),
						universe.lessThanEquals(universe.zeroInt(), y),
						universe.lessThan(y, five)));
		BooleanExpression pred = universe.equals(
				universe.arrayRead(universe.arrayRead(array, i), j),
				universe.zeroInt());

		pred = universe.implies(innerRestrict, pred);
		pred = universe.implies(outerRestrict, pred);
		pred = universe.forall(j, pred);
		pred = universe.forall(i, pred);

		BooleanExpression context = universe.and(assumption, pred);
		Reasoner reasoner = universe.reasoner(context);

		System.out.println(reasoner.getReducedContext());
		reasoner.isValid(universe.not(reasoner.getReducedContext()));
	}

	/*
	 * @Test public void assumptionAsIntervalTest(){ boolArg1 =
	 * preUniv.lessThanEquals(twenty_five, preUniv.multiply(x, x)); boolArg2 =
	 * preUniv.lessThan(x, two_hund); assumption = preUniv.and(boolArg1,
	 * boolArg2);
	 * 
	 * idealSimplifier = idealSimplifierFactory.newSimplifier(assumption);
	 * Interval interval = idealSimplifier.assumptionAsInterval(xsqd);
	 * 
	 * assertEquals(x,interval);
	 * 
	 * }
	 */
}
