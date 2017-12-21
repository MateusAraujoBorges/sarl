package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

import java.util.Arrays;

import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class QuantifierTest {

	private SymbolicUniverse universe;

	private SymbolicType integerType;

	SymbolicFunctionType intToInt;

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		universe.setShowProverQueries(true);
		universe.setShowQueries(true);
		integerType = universe.integerType();
		intToInt = universe.functionType(Arrays.asList(integerType),
				integerType);
	}

	/**
	 * 
	 * forall i : (2<=i && i<B) => (A%i = 0)
	 */
	@Test
	public void divideOrModuleWithQuantifierTest1() {
		BooleanExpression t = universe.trueExpression();
		NumericExpression A = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("A"), integerType);
		NumericExpression B = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("B"), integerType);
		SymbolicConstant i = universe
				.symbolicConstant(universe.stringObject("i"), integerType);
		NumericExpression zero = universe.integer(0);
		NumericExpression two = universe.integer(2);
		BooleanExpression predicate = universe
				.neq(universe.modulo(A, (NumericExpression) i), zero);
		BooleanExpression preCondition1 = universe.and(
				universe.lessThanEquals(two, (NumericExpression) i),
				universe.lessThan((NumericExpression) i, B));
		BooleanExpression query = universe.implies(preCondition1, predicate);
		Reasoner r = universe.reasoner(t);
		BooleanExpression be = universe.forall(i, query);
		ValidityResult result = r.valid(be);
		assertEquals(ResultType.NO, result.getResultType());
	}

	@Test
	public void quantifiedTest() {
		BooleanExpression t = universe.trueExpression();
		SymbolicConstant i = universe
				.symbolicConstant(universe.stringObject("i"), integerType);
		SymbolicConstant j = universe
				.symbolicConstant(universe.stringObject("j"), integerType);
		BooleanExpression predicate = universe.lessThan((NumericExpression) i,
				(NumericExpression) j);
		BooleanExpression be = universe.forall(i, predicate);
		Reasoner r = universe.reasoner(t);
		ValidityResult result = r.valid(be);
		assertEquals(ResultType.NO, result.getResultType());
	}

	/**
	 * forall (i>1) : ( exists (j,k) : j/k=i )
	 * 
	 * result should be YES
	 */
	@Test
	public void divideOrModuleWithQuantifierTest2() {
		BooleanExpression t = universe.trueExpression();
		SymbolicType integerType = universe.integerType();
		SymbolicConstant i = universe
				.symbolicConstant(universe.stringObject("i"), integerType);
		SymbolicConstant j = universe
				.symbolicConstant(universe.stringObject("j"), integerType);
		SymbolicConstant k = universe
				.symbolicConstant(universe.stringObject("k"), integerType);
		NumericExpression one = universe.integer(1);
		BooleanExpression precon = universe.lessThan(one,
				(NumericExpression) i);
		BooleanExpression equality = universe.equals(
				universe.divide((NumericExpression) j, (NumericExpression) k),
				i);
		BooleanExpression predicate = universe.exists(j,
				universe.exists(k, equality));
		BooleanExpression query = universe.implies(precon, predicate);
		BooleanExpression forall = universe.forall(i, query);
		Reasoner r = universe.reasoner(t);
		ValidityResult result = r.valid(forall);
		assertEquals(ResultType.YES, result.getResultType());
	}

	/**
	 * forall 0 < i <B : A/i + B%i = 5
	 * 
	 * should return NO
	 */
	@Test
	public void divideOrModuleWithQuantifierTest3() {
		BooleanExpression t = universe.trueExpression();
		SymbolicType integerType = universe.integerType();
		NumericExpression zero = universe.integer(0);
		NumericExpression five = universe.integer(5);
		NumericExpression A = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("A"), integerType);
		NumericExpression B = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("B"), integerType);
		SymbolicConstant i = universe
				.symbolicConstant(universe.stringObject("i"), integerType);
		BooleanExpression precon = universe.and(
				universe.lessThan((NumericExpression) i, B),
				universe.lessThan(zero, (NumericExpression) i));
		BooleanExpression predicate = universe
				.equals(universe.add(universe.divide(A, (NumericExpression) i),
						universe.modulo(B, (NumericExpression) i)), five);
		BooleanExpression query = universe.implies(precon, predicate);
		BooleanExpression forall = universe.forall(i, query);
		Reasoner r = universe.reasoner(t);
		ValidityResult result = r.valid(forall);
		assertEquals(ResultType.NO, result.getResultType());
	}

	/**
	 * for bug #618
	 * 
	 * $assert( ($forall {int i | i > 0 && i < n1} X1[i] == X2[i]) && ($forall
	 * {int i | i > 0 && i < n1} X1[i] == X2[i]) );
	 */
	@Test
	public void quantifierTest() {
		NumericExpression zero = universe.integer(0);
		BooleanExpression t = universe.trueExpression();
		SymbolicType integerType = universe.integerType();
		NumericExpression n1 = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("n1"), integerType);// n1
		SymbolicType arrayType = universe.arrayType(integerType, n1);
		SymbolicConstant X1 = universe
				.symbolicConstant(universe.stringObject("X1"), arrayType); // X1[n1]
		SymbolicConstant X2 = universe
				.symbolicConstant(universe.stringObject("X2"), arrayType); // X2[n1]
		NumericExpression i = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("i"), integerType);
		BooleanExpression precon = universe.and(universe.lessThan(zero, i),
				universe.lessThan(i, n1)); // 0 < i < n1
		BooleanExpression predicate = universe.equals(universe.arrayRead(X1, i),
				universe.arrayRead(X2, i)); // X1[i] = X2[i];
		BooleanExpression forall = universe.forall((SymbolicConstant) i,
				universe.implies(precon, predicate)); // forall i : 0 < i < n1
														// ==> X[n1] = X[n2]
		BooleanExpression expression = universe.and(forall, forall); // forall
																		// and
																		// forall
		Reasoner r = universe.reasoner(t);

		r.isValid(expression);
	}

	@Test
	public void boundUnbound() {
		SymbolicConstant f = universe
				.symbolicConstant(universe.stringObject("f"), intToInt);
		NumericSymbolicConstant x = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("X"), integerType);
		// forall x . f(x)>0
		BooleanExpression context = universe.forall(x, universe.lessThan(
				universe.zeroInt(),
				(NumericExpression) universe.apply(f, Arrays.asList(x))));
		// f(x) > 999
		BooleanExpression pred = universe.lessThan(universe.integer(999),
				(NumericExpression) universe.apply(f, Arrays.asList(x)));
		Reasoner r = universe.reasoner(context);

		assertFalse(r.isValid(pred));
	}

}
