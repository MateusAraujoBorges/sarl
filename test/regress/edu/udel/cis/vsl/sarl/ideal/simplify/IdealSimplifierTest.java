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
import static org.junit.Assert.assertTrue;

import java.io.PrintStream;
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
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.simplify.IF.Simplifier;

/**
 * Testing on IdealSimplifier based on Polynomials using methods -
 * getFullContext() - getReducedContext()
 * 
 * 
 * @author mbrahma
 */

public class IdealSimplifierTest {

	public final static PrintStream out = System.out;

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
	 * Context:
	 * 
	 * <pre>
	 * 0 <= x && x < 5 && 0 <= y && y < 5 &&
	 * $forall (int i | i == 0 || i == x)
	 *    ($forall (int j | j == 0 || j == y) a[i][j] == 0)
	 * </pre>
	 */
	// @Ignore
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
		BooleanExpression p = reasoner.getReducedContext();
		out.println("p  : " + p);
		BooleanExpression neg = universe.not(p);
		out.println("!p : " + neg);
		out.println(reasoner.isValid(neg));
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

	@Test
	public void negationCacheError() {
		SymbolicUniverse universe = SARL.newStandardUniverse();
		// at one state:
		NumericExpression old_Y2 = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("Y2"),
						universe.integerType());
		NumericExpression old_Y3 = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("Y3"),
						universe.integerType());
		BooleanExpression falseExpr;

		// Y2 <= 0 && 0 <= Y2 - 1 && 0 <= Y3 - 1
		falseExpr = universe.and(
				universe.lessThanEquals(old_Y2, universe.zeroInt()),
				universe.lessThanEquals(universe.oneInt(), old_Y3));
		falseExpr = universe.and(falseExpr,
				universe.lessThanEquals(universe.oneInt(), old_Y2));
		falseExpr = universe.reasoner(universe.not(falseExpr))
				.getReducedContext();
		System.err.println("!" + falseExpr + " = " + universe.not(falseExpr));
		// at another state:
		/*
		 * NumericSymbolicConstant N, Y1, t, ccbv5; SymbolicConstant Y2, Y3;
		 * 
		 * N = (NumericSymbolicConstant) universe.symbolicConstant(
		 * universe.stringObject("X_N"), universe.integerType()); Y1 =
		 * (NumericSymbolicConstant) universe.symbolicConstant(
		 * universe.stringObject("Y1"), universe.integerType()); t =
		 * (NumericSymbolicConstant) universe.symbolicConstant(
		 * universe.stringObject("t"), universe.integerType()); Y2 =
		 * universe.symbolicConstant(universe.stringObject("Y2"),
		 * universe.arrayType(universe.integerType(), N)); Y3 =
		 * universe.symbolicConstant(universe.stringObject("Y3"),
		 * universe.arrayType(universe.integerType(), N)); ccbv5 =
		 * (NumericSymbolicConstant) universe.symbolicConstant(
		 * universe.stringObject("_cc_bv_5"), universe.integerType()); // 0 == N
		 * - Y1: BooleanExpression cxt = universe.equals(N, Y1);
		 * 
		 * // ((forall t : int . ((0 == Y2[t] - 1*t) || (Y1 - 1*t <= 0) || (t +
		 * 1 // <= 0))) || (0 <= Y2 - 1)) && cxt = universe.and(cxt,
		 * universe.forallInt(t, universe.zeroInt(), Y1,
		 * universe.equals(universe.arrayRead(Y2, t), t))); // N >= 2 && Y1 >= 0
		 * cxt = universe.and(cxt, universe.lessThanEquals(universe.integer(2),
		 * N)); cxt = universe.and(cxt,
		 * universe.lessThanEquals(universe.integer(0), Y1)); // forall _cc_bv_5
		 * : int . ((0 == Y2[_cc_bv_5] - 1*Y3[_cc_bv_5]) || (0 // <= X_N -
		 * 1*_cc_bv_5 - 1)) && // forall _cc_bv_5 : int . ((0 == Y2[_cc_bv_5] -
		 * 1*Y3[_cc_bv_5]) || (0 // <= _cc_bv_5)) &&
		 */
		/*
		 * cxt = universe.and(cxt, universe.forall(ccbv5, universe.or(
		 * universe.equals(universe.arrayRead(Y2, ccbv5), universe.arrayRead(Y3,
		 * ccbv5)), universe.lessThan(ccbv5, N)))); cxt = universe.and(cxt,
		 * universe.forall(ccbv5, universe.or(
		 * universe.equals(universe.arrayRead(Y2, ccbv5), universe.arrayRead(Y3,
		 * ccbv5)), universe.lessThanEquals(universe.zeroInt(), ccbv5))));
		 * System.out.println(cxt); universe.reasoner(cxt);
		 */
	}

	@Test
	public void simplifyNotEqualToZero() {
		SymbolicUniverse universe = SARL.newIdealUniverse();
		NumericExpression x = (NumericExpression) universe.symbolicConstant(
				universe.stringObject("X"), universe.integerType());
		NumericExpression y = (NumericExpression) universe.symbolicConstant(
				universe.stringObject("Y"), universe.integerType());
		// xy = 3 * (x + x/y)
		NumericExpression xy = universe.multiply(universe.integer(3),
				universe.add(x, universe.divide(x, y)));
		// context : xy > 1
		BooleanExpression context = universe.lessThan(universe.oneInt(), xy);
		// query : xy != 1
		BooleanExpression neq0 = universe.neq(xy, universe.oneInt());

		assertTrue(universe.reasoner(context).simplify(neq0).isTrue());
	}

	@Test
	public void simplifyPolyEqualToZero() {
		// (c - 1)*(c + 1) - 1*a*b != 0
		SymbolicUniverse u = SARL.newIdealUniverse();
		NumericExpression a = (NumericExpression) u
				.symbolicConstant(u.stringObject("a"), u.integerType());
		NumericExpression b = (NumericExpression) u
				.symbolicConstant(u.stringObject("b"), u.integerType());
		NumericExpression c = (NumericExpression) u
				.symbolicConstant(u.stringObject("c"), u.integerType());

		NumericExpression expr0 = u.multiply(u.subtract(c, u.oneInt()),
				u.add(c, u.oneInt()));
		NumericExpression expr1 = u.multiply(a, b);

		BooleanExpression context = u.and(
				u.lessThan(u.number(u.numberFactory().number("2")),
						u.multiply(c, c)),
				u.lessThan(expr1, u.number(u.numberFactory().number("1"))));
		Reasoner reasoner = u.reasoner(context);
		BooleanExpression p = u.equals(u.zeroInt(),
				u.add(u.oneInt(), u.subtract(expr1, expr0)));
		BooleanExpression pSimp = reasoner.simplify(p);

		out.println("Original Assumption: " + context);
		out.println("Full Context       : " + reasoner.getFullContext());
		out.println("p                  : " + p);
		out.println("pSimp              : " + pSimp);

		assertEquals(u.falseExpression(), pSimp);
	}

	/**
	 * <code> forall i0 : int . ((Y13[i0] == Y10[i0]) || (_uf_$mpi_sizeof(Y3)*Y2 - 1*i0 &lt= 0) || (i0 + 1 &lt== 0))</code>
	 * <code> forall i0 : int . ((Y4[i0] == Y10[i0]) || (2*_uf_$mpi_sizeof(Y3)*Y2 - 1*i0 &lt= 0) || (i0 + 1 &lt== 0))</code>
	 * <code> forall i0 : int . ((Y14[_uf_$mpi_sizeof(Y9)*Y8 + i0] == Y4[_uf_$mpi_sizeof(Y9)*Y8 + i0]) || (_uf_$mpi_sizeof(Y9)*Y8 - 1*i0 &lt== 0) || (i0 + 1 &lt== 0))</code>
	 */
	@Test
	public void simplifyArraySliceAssumptions() {
		SymbolicUniverse u = SARL.newIdealUniverse();
		NumericExpression Y2 = (NumericExpression) u
				.symbolicConstant(u.stringObject("Y2"), u.integerType());
		NumericExpression Y3 = (NumericExpression) u
				.symbolicConstant(u.stringObject("Y3"), u.integerType());
		NumericExpression Y8 = (NumericExpression) u
				.symbolicConstant(u.stringObject("Y8"), u.integerType());
		NumericExpression Y9 = (NumericExpression) u
				.symbolicConstant(u.stringObject("Y9"), u.integerType());
		NumericExpression Y2Y3 = u.multiply(Y2, Y3);
		NumericExpression Y8Y9 = u.multiply(Y8, Y9);

		NumericExpression arraySizeY2Y3 = u.multiply(Y2Y3, u.integer(2));
		SymbolicArrayType arrayTypeY2Y3 = u.arrayType(u.characterType(),
				arraySizeY2Y3);
		NumericExpression arraySizeY8Y9 = u.multiply(Y8Y9, u.integer(2));
		SymbolicArrayType arrayTypeY8Y9 = u.arrayType(u.characterType(),
				arraySizeY8Y9);

		SymbolicExpression Y4 = u.symbolicConstant(u.stringObject("Y4"),
				arrayTypeY2Y3);
		SymbolicExpression Y10 = u.symbolicConstant(u.stringObject("Y10"),
				arrayTypeY8Y9);
		SymbolicExpression Y13 = u.symbolicConstant(u.stringObject("Y13"),
				arrayTypeY2Y3);
		SymbolicExpression Y14 = u.symbolicConstant(u.stringObject("Y14"),
				arrayTypeY8Y9);
		NumericSymbolicConstant i = (NumericSymbolicConstant) u
				.symbolicConstant(u.stringObject("i0"), u.integerType());
		BooleanExpression clauses[] = new BooleanExpression[3];

		// Y13 == Y10 for the first half:
		clauses[0] = u.forallInt(i, u.zeroInt(), Y2Y3,
				u.equals(u.arrayRead(Y13, i), u.arrayRead(Y10, i)));
		// Y4 == Y10 for all:
		clauses[1] = u.forallInt(i, u.zeroInt(), arraySizeY2Y3,
				u.equals(u.arrayRead(Y4, i), u.arrayRead(Y10, i)));
		// Y14 == Y4 for the second half:
		clauses[2] = u.forallInt(i, u.zeroInt(), Y8Y9,
				u.equals(u.arrayRead(Y14, u.add(Y8Y9, i)),
						u.arrayRead(Y4, u.add(Y8Y9, i))));

		BooleanExpression ctx = u.and(u.equals(Y2Y3, Y8Y9),
				u.and(Arrays.asList(clauses)));
		Reasoner reasoner = u.reasoner(ctx);

		// System.out.println(ctx);
		// System.out.println(reasoner.getReducedContext());

		// if symbolic constant Y4 is simplified away then the reduce the
		// context shall not contain Y4 neither:
		if (!reasoner.simplify(Y4).getFreeVars().contains(Y4)) {
			assertTrue(
					!reasoner.getReducedContext().getFreeVars().contains(Y4));
		}

	}
}
