package edu.udel.cis.vsl.sarl.prove.translation;

import static org.junit.Assert.assertEquals;

import java.util.LinkedList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.config.Configurations;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverses;
import edu.udel.cis.vsl.sarl.prove.IF.Prove;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProverFactory;

public class Why3TranslationTest {
	PreUniverse universe;

	private TheoremProverFactory proverFactory;

	@Before
	public void setUp() throws Exception {
		universe = PreUniverses
				.newPreUniverse(PreUniverses.newIdealFactorySystem());
		proverFactory = Prove.newWhy3ProvePlatformFactory(universe,
				Configurations.getDefaultConfiguration()
						.getWhy3ProvePlatform());
	}

	@Test
	public void unionTest() {
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
}
