package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class QuantifierDevTest {
	private SymbolicUniverse universe;
	
	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
	}
	
	/**
	 * 
	 * forall i : (2<=i && i<B) => (A%i = 0)
	 */
	@Test
	public void divideOrModuleWithQuantifierTest1(){
		BooleanExpression t = universe.trueExpression();
		SymbolicType integerType = universe.integerType();
		NumericExpression A = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("A"), integerType);
		NumericExpression B = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("B"), integerType);
		SymbolicConstant i = universe
				.symbolicConstant(universe.stringObject("i"), integerType);
		NumericExpression zero = universe.integer(0);
		NumericExpression two = universe.integer(2);
		BooleanExpression predicate = universe.equals(universe.modulo(A, (NumericExpression)i), zero);
		BooleanExpression preCondition1 = universe.and(universe.lessThanEquals(two, (NumericExpression)i), 
				universe.lessThan((NumericExpression)i, B));
		BooleanExpression query = universe.implies(preCondition1, predicate);
		Reasoner r = universe.reasoner(t);
		BooleanExpression be = universe.forall(i, query);
		ValidityResult result = r.valid(be);
		assertEquals(ResultType.NO, result.getResultType());
	}
	
	/**
	 * forall (i>1) : ( exists (j,k) : j/k=i )
	 * 
	 * result should be YES
	 */
	@Test
	public void divideOrModuleWithQuantifierTest2(){
		BooleanExpression t = universe.trueExpression();
		SymbolicType integerType = universe.integerType();
		SymbolicConstant i = universe
				.symbolicConstant(universe.stringObject("i"), integerType);
		SymbolicConstant j = universe
				.symbolicConstant(universe.stringObject("j"), integerType);
		SymbolicConstant k = universe
				.symbolicConstant(universe.stringObject("k"), integerType);
		NumericExpression one = universe.integer(1);
		BooleanExpression precon = universe.lessThan(one, (NumericExpression)i);
		BooleanExpression equality = universe.equals(universe.divide((NumericExpression)j
				, (NumericExpression)k), i);
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
	public void divideOrModuleWithQuantifierTest3(){
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
		BooleanExpression precon = universe.and(universe.lessThan((NumericExpression)i, B)
				, universe.lessThan(zero, (NumericExpression)i));
		BooleanExpression predicate = universe.equals(universe.add(
				universe.divide(A, (NumericExpression)i)
				, universe.modulo(B, (NumericExpression)i)), five);
		BooleanExpression query = universe.implies(precon, predicate);
		BooleanExpression forall = universe.forall(i, query);
		Reasoner r = universe.reasoner(t);
		ValidityResult result = r.valid(forall);
		assertEquals(ResultType.NO, result.getResultType());
	}
}
