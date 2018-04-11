package edu.udel.cis.vsl.sarl.prove;

import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.config.Configurations;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUninterpretedType;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverses;
import edu.udel.cis.vsl.sarl.prove.IF.Prove;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProverFactory;

public class ProveTest {

	PreUniverse universe;

	private TheoremProverFactory proverFactory;

	@Before
	public void setUp() throws Exception {
		universe = PreUniverses
				.newPreUniverse(PreUniverses.newIdealFactorySystem());
		proverFactory = Prove.newMultiProverFactory(universe,
				Configurations.getDefaultConfiguration());
	}

	@Test
	public void testValidityResult() {
		ResultType r = ValidityResult.ResultType.YES;
		ValidityResult v = Prove.validityResult(r);
		assertEquals(Prove.RESULT_YES, v);

		r = ValidityResult.ResultType.NO;
		v = Prove.validityResult(r);
		assertEquals(Prove.RESULT_NO, v);

		r = ValidityResult.ResultType.MAYBE;
		v = Prove.validityResult(r);
		assertEquals(Prove.RESULT_MAYBE, v);
	}

	/**
	 * Test translation of uninterpreted type objects
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

		universe.setShowProverQueries(true);
		assertEquals(proverFactory.newProver(context).valid(comparison)
				.getResultType(), ResultType.YES);
	}

	/**
	 * Test translation of uninterpreted type objects
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

		universe.setShowProverQueries(true);
		assertEquals(
				proverFactory.newProver(universe.trueExpression())
						.valid(universe.not(comparison)).getResultType(),
				ResultType.YES);
	}

	/**
	 * Test translation of uninterpreted type objects
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
