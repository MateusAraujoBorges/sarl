package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.universe.IF.Universes;

public class ArrayReasonTest {
	private SymbolicUniverse universe;
	private BooleanExpression t;
	private List<NumericExpression> list1; // {5,6}
	private StringObject a_obj; // "a"
	private NumericExpression zero, one, two, five, six;
	private ReferenceExpression identityReference;
	private SymbolicType integerType;
	private Reasoner reasoner;
	
	@Before
	public void setUp() throws Exception {
		universe = Universes.newIdealUniverse();
		t = universe.trueExpression();
		reasoner = universe.reasoner(t);
		zero = universe.integer(0);
		one = universe.integer(1);
		two = universe.integer(2);
		five = universe.integer(5);
		six = universe.integer(6);
		list1 = Arrays.asList(new NumericExpression[] { five, six });
		identityReference = universe.identityReference();
		integerType = universe.integerType();
		a_obj = universe.stringObject("a");
	}
	
	@After
	public void tearDown() throws Exception {
	}
	
	 /**
	  * context: 
	  * 	b = {a,a,a,a,a,a}
	  * a <== simplify(a[5])
	  */
	@Test
	public void arrayReasonSimplifyTest1(){
		ArrayElementReference reference;
		SymbolicExpression a = universe.symbolicConstant(a_obj, integerType);
		SymbolicExpression b = universe.constantArray(integerType, six, a);
		reference = universe.arrayElementReference(identityReference, five);
		
		SymbolicExpression result = reasoner.simplify(universe.dereference(b, reference));
		assertEquals(result, a);
		
	}
	
	/**
	 * context: 
	 * 		b = {a,a,a,a,a,a}
	 * 		c = {5,6}
	 * a <== simplify(b[c[0]]) 
	 * 
	 */
	@Test
	public void arrayReasonSimplifyTest2(){
		ArrayElementReference reference;
		SymbolicExpression a = universe.symbolicConstant(a_obj, integerType);
		SymbolicExpression b = universe.constantArray(integerType, six, a);
		SymbolicExpression c = universe.array(integerType, list1);
		
		reference = universe.arrayElementReference(identityReference, zero);
		SymbolicExpression c1 = universe.dereference(c, reference); // c[0]
		reference = universe.arrayElementReference(identityReference, (NumericExpression)c1);
		SymbolicExpression result = reasoner.simplify(universe.dereference(b, reference)); //b[c[0]]
		
		assertEquals(result, a);
	}
	
	/**
	 * context:
	 * 		b = {a,a,a,a,a,a}
	 * valid(b[5] == a)
	 */
	@Test
	public void arrayReasonValidTest1(){
		SymbolicExpression a = universe.symbolicConstant(a_obj, integerType);
		SymbolicExpression b = universe.constantArray(integerType, six, a);
		BooleanExpression p = universe.equals(a,
				(NumericExpression) universe.arrayRead(b, five));
		ValidityResult result = reasoner.valid(p);
		
		assertEquals(ResultType.YES, result.getResultType());
	}
	
	/**
	 * context:
	 * 		a = {1,1,1,1,1,1}
	 * 		b[i] = a[i] + 1 forall i=0..6
	 * valid(b[i] == 2 for all i=0..6)
	 */
	@Test
	public void arrayReasonValidTest2(){
		SymbolicExpression a = universe.constantArray(integerType, six, one);
		SymbolicExpression b = universe.emptyArray(integerType);
		int len = Integer.parseInt(universe.length(a).toString());
		for(int i=0; i<len; i++){
			// b[i] = a[i] +1
			b = universe.append(b, universe.add((NumericExpression)universe.arrayRead(a, universe.integer(i)), one));
		}
		
		for(int i=0; i<len; i++){
			assertEquals(universe.arrayRead(b, universe.integer(i)), two);
		}
	}
	
}
