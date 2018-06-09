package edu.udel.cis.vsl.sarl.prove;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;

import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.config.Configurations;
import edu.udel.cis.vsl.sarl.IF.config.ProverInfo;
import edu.udel.cis.vsl.sarl.IF.config.ProverInfo.ProverKind;
import edu.udel.cis.vsl.sarl.IF.config.SARLConfig;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUninterpretedType;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverses;
import edu.udel.cis.vsl.sarl.prove.IF.Prove;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProverFactory;
import edu.udel.cis.vsl.sarl.prove.z3.RobustZ3TheoremProverFactory;

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

	/**
	 * Test summation expression
	 * {@link PreUniverse#sigma(edu.udel.cis.vsl.sarl.IF.expr.NumericExpression, edu.udel.cis.vsl.sarl.IF.expr.NumericExpression, SymbolicExpression)}
	 */
	@Test
	public void testSummationExpansion() {
		SymbolicUniverse su = SARL.newStandardUniverse();

		SymbolicType intType = su.integerType();
		NumericExpression x = (NumericExpression) su
				.symbolicConstant(su.stringObject("X"), intType);
		NumericExpression y = (NumericExpression) su
				.symbolicConstant(su.stringObject("Y"), intType);
		SymbolicExpression f = su.symbolicConstant(su.stringObject("f"), su
				.functionType(Arrays.asList(su.integerType()), su.realType()));
		SymbolicConstant i = su.symbolicConstant(su.stringObject("i"),
				su.integerType());

		f = su.lambda(i, su.apply(f, Arrays.asList(i)));

		NumericExpression f_x_y = (NumericExpression) su.sigma(x, y, f);
		NumericExpression f_x_yPLUS1 = (NumericExpression) su.sigma(x,
				su.add(y, su.oneInt()), f);
		NumericExpression f_xMINUS1_y = (NumericExpression) su
				.sigma(su.subtract(x, su.oneInt()), y, f);

		BooleanExpression rightExpansion = su.equals(f_x_yPLUS1,
				su.add(f_x_y, (NumericExpression) su.apply(f,
						Arrays.asList(su.add(y, su.oneInt())))));
		BooleanExpression leftExpansion = su.equals(f_xMINUS1_y,
				su.add(f_x_y, (NumericExpression) su.apply(f,
						Arrays.asList(su.subtract(x, su.oneInt())))));
		Reasoner reasoner = su.reasoner(su.trueExpression());

		su.setShowProverQueries(true);
		assertEquals(ResultType.YES,
				reasoner.valid(rightExpansion).getResultType());
		assertEquals(ResultType.YES,
				reasoner.valid(leftExpansion).getResultType());
	}

	@Test
	public void testSummationTransitive() {
		SymbolicUniverse su = SARL.newStandardUniverse();

		SymbolicType intType = su.integerType();
		NumericExpression x = (NumericExpression) su
				.symbolicConstant(su.stringObject("X"), intType);
		NumericExpression y = (NumericExpression) su
				.symbolicConstant(su.stringObject("Y"), intType);
		NumericExpression z = (NumericExpression) su
				.symbolicConstant(su.stringObject("Z"), intType);
		SymbolicExpression f = su.symbolicConstant(su.stringObject("f"), su
				.functionType(Arrays.asList(su.integerType()), su.realType()));
		SymbolicConstant i = su.symbolicConstant(su.stringObject("i"),
				su.integerType());

		f = su.lambda(i, su.apply(f, Arrays.asList(i)));

		NumericExpression f_x_y = (NumericExpression) su.sigma(x, y, f);
		NumericExpression f_y_z = (NumericExpression) su.sigma(y, z, f);
		NumericExpression f_x_z = (NumericExpression) su.sigma(x, z, f);

		ResultType result = su.reasoner(su.trueExpression())
				.valid(su.equals(su.add(f_x_y, f_y_z), f_x_z)).getResultType();

		assertEquals(ResultType.YES, result);
	}

	// (X.0).0 != 0 ==> (X.0).0 == 0
	// Expected: NO
	@Test
	public void testProverTranslationForSymbolicTuple() {
		SARLConfig config = Configurations.getDefaultConfiguration();
		ProverInfo z3 = config.getProverWithKind(ProverKind.Z3);

		assertEquals("Z3 must be installed for passing this " + "test", true,
				z3 != null);

		SymbolicUniverse su = SARL.newStandardUniverse(config, z3);
		SymbolicTupleType innerTupleType = su.tupleType(
				su.stringObject("tuple_inn"), Arrays.asList(su.integerType()));
		SymbolicTupleType tupleType = su.tupleType(su.stringObject("tuple"),
				Arrays.asList(innerTupleType));
		SymbolicConstant myTuple = su.symbolicConstant(su.stringObject("X"),
				tupleType);

		BooleanExpression equation = su
				.equals(su.tupleRead(su.tupleRead(myTuple, su.intObject(0)),
						su.intObject(0)), su.zeroInt());
		BooleanExpression assumption = su.not(equation);
		ResultType result = new RobustZ3TheoremProverFactory((PreUniverse) su, z3)
				.newProver(assumption).valid(equation).getResultType();

		assertEquals(ResultType.NO, result);
	}

	// (X.0).0 == 1 ==> 0 <= (X.0).0 <= 2
	// Expected: YES
	@Test
	public void testProverTranslationForSymbolicTuple2() {
		SARLConfig config = Configurations.getDefaultConfiguration();
		ProverInfo z3 = config.getProverWithKind(ProverKind.Z3);

		assertEquals("Z3 must be installed for passing this " + "test", true,
				z3 != null);

		SymbolicUniverse su = SARL.newStandardUniverse(config, z3);
		SymbolicTupleType innerTupleType = su.tupleType(
				su.stringObject("tuple_inn"), Arrays.asList(su.integerType()));
		SymbolicTupleType tupleType = su.tupleType(su.stringObject("tuple"),
				Arrays.asList(innerTupleType));
		SymbolicConstant myTuple = su.symbolicConstant(su.stringObject("X"),
				tupleType);

		NumericExpression read = (NumericExpression) su.tupleRead(
				su.tupleRead(myTuple, su.intObject(0)), su.intObject(0));
		BooleanExpression assumption = su.equals(read, su.oneInt());
		ResultType result = new RobustZ3TheoremProverFactory(
				(PreUniverse) su, z3)
						.newProver(assumption)
						.valid(su.and(su.lessThan(su.zeroInt(), read),
								su.lessThan(read, su.integer(2))))
						.getResultType();

		assertEquals(ResultType.YES, result);
	}
}
