package edu.udel.cis.vsl.sarl.prove.translation;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

import java.util.LinkedList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.config.Configurations;
import edu.udel.cis.vsl.sarl.IF.config.ProverInfo;
import edu.udel.cis.vsl.sarl.IF.config.SARLConfig;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUninterpretedType;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverses;
import edu.udel.cis.vsl.sarl.prove.IF.Prove;
import edu.udel.cis.vsl.sarl.prove.IF.ProverFunctionInterpretation;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProver;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProverFactory;
import performance.PerformanceTest;

public class Why3TranslationTest {
	PreUniverse universe;

	private TheoremProverFactory proverFactory = null;

	@Before
	public void setUp() throws Exception {
		universe = PreUniverses
				.newPreUniverse(PreUniverses.newIdealFactorySystem());

		ProverInfo why3 = Configurations.getDefaultConfiguration()
				.getWhy3ProvePlatform();

		if (why3 != null)
			proverFactory = Prove.newWhy3ProvePlatformFactory(universe,
					Configurations.getDefaultConfiguration()
							.getWhy3ProvePlatform());
		else {
			System.err.println(
					"Why3 translation tests are not executed because no Why3 was found by SARL.");
			proverFactory = Prove.newMultiProverFactory(universe,
					Configurations.getDefaultConfiguration());
		}

	}

	@Test
	public void unionTest() {
		if (proverFactory == null) {
			System.err.println("Warning: no why3 installed.");
			return;
		}
		List<SymbolicType> unionTypes = new LinkedList<>();

		unionTypes.add(universe.integerType());
		unionTypes.add(universe.realType());

		SymbolicExpression union = universe.unionInject(
				universe.unionType(universe.stringObject("_u"), unionTypes),
				universe.intObject(0), universe.zeroInt());

		SymbolicConstant realX = universe.symbolicConstant(
				universe.stringObject("X"), universe.realType());

		assertEquals(
				proverFactory.newProver(universe.trueExpression())
						.valid(universe.equals(universe.unionExtract(
								universe.intObject(1), union), realX))
						.getResultType(),
				ResultType.MAYBE);

		union = universe.unionInject(
				universe.unionType(universe.stringObject("_u"), unionTypes),
				universe.intObject(1), universe.zeroReal());
		assertEquals(
				proverFactory
						.newProver(universe.equals(realX, universe.zeroReal()))
						.valid(universe.equals(universe.unionExtract(
								universe.intObject(1), union), realX))
						.getResultType(),
				ResultType.YES);
	}

	/**
	 * Test why3 translation of uninterpreted type objects
	 */
	@Test
	public void testUninterpretedTypeNCCompare() {
		SymbolicUninterpretedType type = universe
				.symbolicUninterpretedType("test");
		SymbolicConstant X = universe
				.symbolicConstant(universe.stringObject("X"), type);
		SymbolicConstant Y = universe
				.symbolicConstant(universe.stringObject("Y"), type);
		SymbolicConstant Z = universe
				.symbolicConstant(universe.stringObject("Z"), type);
		BooleanExpression context = universe.and(universe.equals(X, Y),
				universe.equals(Z, Y));
		BooleanExpression comparison = universe.equals(X, Z);

		assertEquals(proverFactory.newProver(context).valid(comparison)
				.getResultType(), ResultType.YES);
	}

	/**
	 * Test why3 translation of uninterpreted type objects
	 */
	@Test
	public void testUninterpretedTypeNCCompare2() {
		SymbolicUninterpretedType type = universe
				.symbolicUninterpretedType("test");
		SymbolicExpression k0 = universe.concreteValueOfUninterpretedType(type,
				universe.intObject(0));
		SymbolicExpression k1 = universe.concreteValueOfUninterpretedType(type,
				universe.intObject(1));
		SymbolicConstant X = universe
				.symbolicConstant(universe.stringObject("X"), type);
		BooleanExpression comparison = universe.and(universe.equals(X, k0),
				universe.equals(X, k1));

		assertEquals(
				proverFactory.newProver(universe.trueExpression())
						.valid(universe.not(comparison)).getResultType(),
				ResultType.YES);
	}

	/**
	 * Test why3 translation of uninterpreted type objects
	 */
	@Test
	public void testUninterpretedTypeNCCompare3() {
		SymbolicUninterpretedType type = universe
				.symbolicUninterpretedType("test");
		SymbolicExpression k0 = universe.concreteValueOfUninterpretedType(type,
				universe.intObject(0));
		SymbolicExpression k1 = universe.concreteValueOfUninterpretedType(type,
				universe.intObject(1));
		SymbolicConstant X = universe
				.symbolicConstant(universe.stringObject("X"), type);
		SymbolicConstant Y = universe
				.symbolicConstant(universe.stringObject("Y"), type);
		BooleanExpression context = universe.and(universe.equals(Y, k0),
				universe.equals(X, k1));
		BooleanExpression comparison = universe.neq(X, Y);

		universe.setShowProverQueries(true);
		assertEquals(proverFactory.newProver(context).valid(comparison)
				.getResultType(), ResultType.YES);

		context = universe.and(universe.equals(Y, k0), universe.equals(X, k0));
		comparison = universe.equals(X, Y);
		assertEquals(proverFactory.newProver(context).valid(comparison)
				.getResultType(), ResultType.YES);
	}

	@Test
	public void testPermutConcArraySwap() {
		SymbolicExpression array = universe.array(universe.integerType(),
				new SymbolicExpression[] { universe.zeroInt(),
						universe.oneInt(), universe.integer(2) });
		SymbolicExpression swapped = universe.arrayWrite(array,
				universe.zeroInt(), universe.integer(2));

		swapped = universe.arrayWrite(swapped, universe.integer(2),
				universe.zeroInt());

		BooleanExpression permut = universe.permut(array, swapped,
				universe.zeroInt(), universe.integer(3));

		universe.setShowProverQueries(true);
		assertEquals(proverFactory.newProver(universe.trueExpression())
				.valid(permut).getResultType(), ResultType.YES);
	}

	@Test
	public void testPermutConcArrayCycle() {
		SymbolicExpression array = universe.array(universe.integerType(),
				new SymbolicExpression[] { universe.zeroInt(),
						universe.oneInt(), universe.integer(2),
						universe.integer(3) });
		SymbolicExpression swapped = universe.arrayWrite(array,
				universe.zeroInt(), universe.integer(2));

		swapped = universe.arrayWrite(swapped, universe.integer(1),
				universe.zeroInt());
		swapped = universe.arrayWrite(swapped, universe.integer(2),
				universe.oneInt());

		BooleanExpression permut = universe.permut(array, swapped,
				universe.zeroInt(), universe.integer(3));

		universe.setShowProverQueries(true);
		assertEquals(proverFactory.newProver(universe.trueExpression())
				.valid(permut).getResultType(), ResultType.YES);
	}

	@Test
	public void testPermutSymArraySwap() {
		SymbolicExpression array = universe.symbolicConstant(
				universe.stringObject("X"),
				universe.arrayType(universe.integerType()));
		NumericExpression zero = universe.zeroInt();
		NumericExpression two = universe.integer(2);

		SymbolicExpression swapped = universe.arrayWrite(array, zero,
				universe.arrayRead(array, two));

		swapped = universe.arrayWrite(swapped, two,
				universe.arrayRead(array, zero));

		BooleanExpression permut = universe.permut(array, swapped,
				universe.zeroInt(), universe.integer(3));

		universe.setShowProverQueries(true);
		assertEquals(proverFactory.newProver(universe.trueExpression())
				.valid(permut).getResultType(), ResultType.YES);
	}

	@Test
	public void testPermutSymArrayCycle() {
		SymbolicExpression array = universe.symbolicConstant(
				universe.stringObject("X"),
				universe.arrayType(universe.integerType()));
		NumericExpression b = (NumericExpression) universe.symbolicConstant(
				universe.stringObject("x"), universe.integerType());
		NumericExpression bOne = universe.add(b, universe.oneInt());
		NumericExpression bTwo = universe.add(bOne, universe.oneInt());
		NumericExpression lower = (NumericExpression) universe.symbolicConstant(
				universe.stringObject("lower"), universe.integerType());
		NumericExpression higher = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("higher"),
						universe.integerType());

		SymbolicExpression swapped = universe.arrayWrite(array, b,
				universe.arrayRead(array, bOne));

		swapped = universe.arrayWrite(swapped, bOne,
				universe.arrayRead(array, bTwo));
		swapped = universe.arrayWrite(swapped, bTwo,
				universe.arrayRead(array, b));

		BooleanExpression permut = universe.permut(array, swapped, lower,
				higher);
		BooleanExpression validB = universe.lessThanEquals(lower, b);

		validB = universe.and(validB, universe.lessThan(bTwo, higher));
		universe.setShowProverQueries(true);
		assertEquals(
				proverFactory.newProver(validB).valid(permut).getResultType(),
				ResultType.YES);
	}

	@Test
	public void testPermutSymArrayCycleBad() {
		SymbolicExpression array = universe.symbolicConstant(
				universe.stringObject("X"),
				universe.arrayType(universe.integerType()));
		NumericExpression b = (NumericExpression) universe.symbolicConstant(
				universe.stringObject("x"), universe.integerType());
		NumericExpression bOne = universe.add(b, universe.oneInt());
		NumericExpression bTwo = universe.add(bOne, universe.oneInt());
		NumericExpression lower = (NumericExpression) universe.symbolicConstant(
				universe.stringObject("lower"), universe.integerType());
		NumericExpression higher = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("higher"),
						universe.integerType());

		SymbolicExpression swapped = universe.arrayWrite(array, b,
				universe.arrayRead(array, bOne));

		swapped = universe.arrayWrite(swapped, bOne,
				universe.arrayRead(array, bTwo));
		swapped = universe.arrayWrite(swapped, bTwo,
				universe.arrayRead(array, bTwo));

		BooleanExpression permut = universe.permut(array, swapped, lower,
				higher);
		BooleanExpression validB = universe.lessThanEquals(lower, b);

		validB = universe.and(validB, universe.lessThan(bTwo, higher));
		universe.setShowProverQueries(true);
		assertFalse(proverFactory.newProver(validB).valid(permut)
				.getResultType() == ResultType.YES);
	}

	/**
	 * permut(a, a[1:=a[2], 2:=a[1], 1, 3), valid
	 */
	@Test
	public void testPermutArraySlice() {
		SymbolicExpression array = universe.symbolicConstant(
				universe.stringObject("X"),
				universe.arrayType(universe.integerType()));
		NumericExpression one = universe.oneInt();
		NumericExpression two = universe.integer(2);

		SymbolicExpression swapped = universe.arrayWrite(array, one,
				universe.arrayRead(array, two));

		swapped = universe.arrayWrite(swapped, two,
				universe.arrayRead(array, one));

		BooleanExpression permut = universe.permut(array, swapped,
				universe.oneInt(), universe.integer(3));

		universe.setShowProverQueries(true);
		assertEquals(ResultType.YES,
				proverFactory.newProver(universe.trueExpression()).valid(permut)
						.getResultType());
	}

	/**
	 * permut(a, a[0:=a[2], 2:=a[0], 1, 3), cannot prove validity
	 */
	@Test
	public void testPermutArraySliceBad() {
		SymbolicExpression array = universe.symbolicConstant(
				universe.stringObject("X"),
				universe.arrayType(universe.integerType()));
		NumericExpression zero = universe.zeroInt();
		NumericExpression two = universe.integer(2);

		SymbolicExpression swapped = universe.arrayWrite(array, zero,
				universe.arrayRead(array, two));

		swapped = universe.arrayWrite(swapped, two,
				universe.arrayRead(array, zero));

		BooleanExpression permut = universe.permut(array, swapped,
				universe.oneInt(), universe.integer(3));

		universe.setShowProverQueries(true);
		assertFalse(ResultType.YES == proverFactory
				.newProver(universe.trueExpression()).valid(permut)
				.getResultType());
	}

	@Test
	public void testNoUnsatWhy3() {
		SARLConfig config = Configurations.getDefaultConfiguration();
		ProverInfo why3 = config.getWhy3ProvePlatform();

		assertEquals("Why3 must be installed for passing this " + "test", true,
				why3 != null);
		SymbolicUniverse su = SARL.newStandardUniverse(config, null);
		BooleanExpression unsatFormula = PerformanceTest
				.slowNegationFormula(false, su);

		su.setShowProverQueries(true);
		assertEquals(true,
				su.why3Reasoner(su.trueExpression(),
						new ProverFunctionInterpretation[0]).unsat(unsatFormula)
						.getResultType() != ResultType.YES);
	}

	@Test
	public void testUnsatWhy3NoSimplify() {
		SARLConfig config = Configurations.getDefaultConfiguration();
		ProverInfo why3 = config.getWhy3ProvePlatform();

		assertEquals("Why3 must be installed for passing this " + "test", true,
				why3 != null);
		SymbolicUniverse su = SARL.newStandardUniverse(config, null);
		BooleanExpression unsatFormula = PerformanceTest
				.slowNegationFormula(true, su);

		su.setShowProverQueries(true);

		TheoremProver prover = Prove
				.newWhy3ProvePlatformFactory((PreUniverse) su,
						(ProverInfo) why3)
				.newProver(su.trueExpression(),
						new ProverFunctionInterpretation[0]);

		assertEquals(ResultType.YES,
				prover.unsat(unsatFormula).getResultType());
	}
}
