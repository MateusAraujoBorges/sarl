package edu.udel.cis.vsl.sarl.prove;

import static org.junit.Assert.assertEquals;

import java.io.PrintStream;
import java.util.Collection;
import java.util.LinkedList;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.config.Configurations;
import edu.udel.cis.vsl.sarl.IF.config.ProverInfo;
import edu.udel.cis.vsl.sarl.IF.config.ProverInfo.ProverKind;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.preuniverse.IF.FactorySystem;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverses;
import edu.udel.cis.vsl.sarl.prove.IF.Prove;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProver;

@RunWith(JUnit4.class)
public class BitwiseProveTest {
	private final static PrintStream OUT = System.out;
	private final static boolean DEBUG = false;

	// Static fields: instantiated once and used for all tests...
	private static FactorySystem factorySystem = PreUniverses
			.newIdealFactorySystem();

	private static PreUniverse universe = PreUniverses
			.newPreUniverse(factorySystem);

	private static SymbolicType integerType = universe.integerType();

	private static NumericExpression intZero = universe.integer(0);

	private static NumericExpression intOne = universe.integer(1);

	private static NumericExpression intTwo = universe.integer(2);

	//private static NumericExpression intThree = universe.integer(3);

	private static NumericExpression intFive = universe.integer(5);

	private static NumericExpression intSeven = universe.integer(7);

	private static NumericExpression intEight = universe.integer(8);

	private static NumericExpression intSixteen = universe.integer(16);

	private static long intMax_signed = 214748367;

	private static long intMax_unsigned = intMax_signed * 2 + 1;

	private static NumericExpression intMax32bit = universe
			.integer(intMax_unsigned);

	private static NumericSymbolicConstant intX = (NumericSymbolicConstant) universe
			.symbolicConstant(universe.stringObject("x"), integerType);

	private static NumericSymbolicConstant intY = (NumericSymbolicConstant) universe
			.symbolicConstant(universe.stringObject("y"), integerType);

	private static NumericSymbolicConstant intEven = (NumericSymbolicConstant) universe
			.symbolicConstant(universe.stringObject("even"), integerType);

	private static BooleanExpression context = universe.and(
			universe.and(
					universe.and(universe.lessThan(intZero, intX),
							universe.lessThan(intZero, intY)),
					universe.and(universe.lessThan(intX, intMax32bit),
							universe.lessThan(intY, intMax32bit))),
			universe.and(
					universe.and(universe.lessThan(intX, intMax32bit),
							universe.lessThan(intY, intMax32bit)),
					universe.equals(universe.modulo(intEven, intTwo),
							intZero)));

	private static Collection<TheoremProver> provers;

	private static ResultType resN = ResultType.NO;

	private static ResultType resY = ResultType.YES;

	private static ResultType resM = ResultType.MAYBE;

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
		universe.setShowProverQueries(false);
		provers = new LinkedList<TheoremProver>();
		for (ProverInfo info : Configurations.getDefaultConfiguration()
				.getProvers()) {
			if (info.getKind().equals(ProverKind.Z3))
				provers.add(Prove.newProverFactory(universe, info)
						.newProver(context));
		}
	}

	@Before
	public void setUp() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}

	/**
	 * Debugging printing function
	 * 
	 * @param o
	 *            Target {@link Object} should be printed.
	 */
	private void p(Object o) {
		if (DEBUG) {
			OUT.println(o);
		}
	}

	/**
	 * Debugging printing function
	 * 
	 * @param o
	 *            Target {@link Object} should be printed.
	 */
	private void p(String s) {
		if (DEBUG) {
			OUT.println(s);
		}
	}

	/**
	 * Checks that the result of applying the prover to the given predicate is
	 * as expected.
	 * 
	 * @param expected
	 *            expected result type (YES, NO, or MAYBE)
	 * @param predicate
	 *            boolean expression to be checked for validity
	 */
	private void check(ResultType expected, BooleanExpression predicate) {
		for (TheoremProver prover : provers) {
			p("Predicate: ");
			p(predicate);
			assertEquals(prover.toString(), expected,
					prover.valid(predicate).getResultType());
		}
	}

	/**
	 * Context: 0 < x < 2^32 - 1, 0 < y < 2^32 - 1; <br>
	 * Query: 7 & 5 | 2 == 7; <br>
	 * Expected: Yes
	 */
	@Test
	public void prove_bitand_intSeven_intFive() {
		BooleanExpression bExpr = universe.equals(
				universe.bitor(universe.bitand(intSeven, intFive), intTwo),
				intSeven);
		check(resY, bExpr);
	}

	/**
	 * Context: 0 < x < 2^32 - 1, 0 < y < 2^32 - 1; <br>
	 * Query: 0 & 1 < 1; <br>
	 * Expected: Yes
	 */
	@Test
	public void prove_bitand_intZero_intOne() {
		BooleanExpression bExpr = universe
				.lessThan(universe.bitand(intZero, intOne), intOne);

		check(resY, bExpr);
	}

	/**
	 * Context: 0 < x < 2^32 - 1, 0 < y < 2^32 - 1; <br>
	 * Query: 0 & x > 0 (0 < 0 & x); <br>
	 * Expected: No
	 */
	@Test
	public void prove_bitand_intZero_intX() {
		BooleanExpression bExpr = universe.lessThan(intZero,
				universe.bitand(intZero, intX));

		check(resN, bExpr);
	}

	/**
	 * Context: 0 < x < 2^32 - 1, 0 < y < 2^32 - 1; <br>
	 * Query: x & y >= 0 (0 <= x & y); <br>
	 * Expected: Yes
	 */
	@Test
	public void prove_bitand_intX_intY() {
		BooleanExpression bExpr = universe.lessThanEquals(intZero,
				universe.bitand(intX, intY));

		check(resY, bExpr);
	}

	/**
	 * Context: 0 < x < 2^32 - 1, 0 < y < 2^32 - 1; <br>
	 * Query: 8 >= y & 4 (y & 4 <= 8); <br>
	 * Expected: Yes
	 */
	@Test
	public void prove_bitand_intX_and_intEight_LT_intFive() {
		BooleanExpression bExpr = universe
				.lessThan(universe.bitand(intY, intFive), intEight);

		check(resY, bExpr);
	}

	/**
	 * Context: 0 < x < 2^32 - 1, 0 < y < 2^32 - 1; <br>
	 * Query: x % 8 == x & 7; <br>
	 * Expected: Yes
	 */
	@Ignore
	@Test
	public void prove_bitand_intX_bitand_intSeven() {
		BooleanExpression bExpr = universe.equals(
				universe.modulo(intX, intEight),
				universe.bitand(intX, intSeven));

		check(resM, bExpr);
		// Expected: Yes, but Time out.
	}

	/**
	 * Context: 0 < x < 2^32 - 1, 0 < y < 2^32 - 1; <br>
	 * Query: x | y > 0 (0 < x | y); <br>
	 * Expected: Yes
	 */
	@Test
	public void prove_bitand_intX_bitor_intY_GT_intZero() {
		BooleanExpression bExpr = universe.lessThan(intZero,
				universe.bitor(intX, intY));

		check(resY, bExpr);
	}

	/**
	 * Context: 0 < x < 2^32 - 1, 0 < y < 2^32 - 1; <br>
	 * Query: x | y > 1 (1 < x | y); <br>
	 * Expected: No
	 */
	@Test
	public void prove_bitor_intX_intY_GT_intOne() {
		BooleanExpression bExpr = universe.lessThan(intOne,
				universe.bitor(intX, intY));

		check(resN, bExpr);
	}

	/**
	 * Context: 0 < x < 2^32 - 1, 0 < y < 2^32 - 1; <br>
	 * Query: ((x & y) | y) == y; <br>
	 * Expected: Yes
	 */
	@Ignore
	@Test
	public void prove_bitor_0bitand_intX_intY0_intY() {
		BooleanExpression bExpr = universe.equals(intY,
				universe.bitor(universe.bitand(intX, intY), intY));

		check(resM, bExpr);
	}

	/**
	 * Context: 0 < x < 2^32 - 1, 0 < y < 2^32 - 1; <br>
	 * Query: [(x & 8) + (y & 8)] <= 16; <br>
	 * Expected: Yes
	 */
	@Test
	public void prove_bitwise_complex1() {
		NumericExpression sum = universe.add(universe.bitand(intX, intEight),
				universe.bitand(intY, intEight));
		BooleanExpression bExpr = universe.lessThanEquals(sum, intSixteen);

		check(resY, bExpr);
	}

	@Test
	public void translateBitPred() {
		check(resN,
				universe.lessThan(universe.bitand(intFive, intFive), intFive));
	}

}
