package edu.udel.cis.vsl.sarl.prove.translation;

import static org.junit.Assert.assertEquals;

import java.util.LinkedList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.config.Configurations;
import edu.udel.cis.vsl.sarl.IF.config.ProverInfo;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUninterpretedType;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverses;
import edu.udel.cis.vsl.sarl.prove.IF.Prove;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProverFactory;

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
}
