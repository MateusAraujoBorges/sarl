package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class DivOrModuloTest {
	private SymbolicUniverse universe;
	private SymbolicType integerType;
	private NumericExpression x; 
	private NumericExpression y;
	private NumericExpression two;
	
	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		universe.setShowProverQueries(true);
		integerType = universe.integerType();
		x = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("x"), integerType);
		y = (NumericExpression) universe
				.symbolicConstant(universe.stringObject("y"), integerType);
		two = universe.integer(2);
	}
	
	/**
	 * Note: cvc4 can not solve this problem without translation
	 * TODO: z3 is not used?
	 * 
	 * assumption: x/y = 2
	 * predicate: x != y
	 * 
	 * result true;
	 */
	@Test
	public void divisionTest1(){
		BooleanExpression assumption = universe.equals(two, 
				universe.divide(x, y));
		BooleanExpression predicate = universe.neq(x, y);
		Reasoner r = universe.reasoner(assumption);
		
		ValidityResult result = r.valid(predicate);
		assertEquals(ResultType.YES, result.getResultType());
	}
	
	/**
	 * 
	 * assumption: x%y = 2
	 * predicate: x != y
	 * 
	 * result true;
	 */
	@Test
	public void moduloTest1(){
		BooleanExpression assumption = universe.equals(two, 
				universe.modulo(x, y));
		BooleanExpression predicate = universe.neq(x, y);
		Reasoner r = universe.reasoner(assumption);
		
		ValidityResult result = r.valid(predicate);
		assertEquals(ResultType.YES, result.getResultType());
	}
}
