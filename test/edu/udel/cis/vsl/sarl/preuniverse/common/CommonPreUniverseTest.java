package edu.udel.cis.vsl.sarl.preuniverse.common;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.BooleanObject;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType.SymbolicTypeKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTypeSequence;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;
import edu.udel.cis.vsl.sarl.expr.IF.BooleanExpressionFactory;
import edu.udel.cis.vsl.sarl.expr.IF.ExpressionFactory;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.preuniverse.PreUniverses;
import edu.udel.cis.vsl.sarl.preuniverse.IF.FactorySystem;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.type.IF.SymbolicTypeFactory;

public class CommonPreUniverseTest {

	// Universe
	private static PreUniverse universe;
	// SymbolicTypes
	private static SymbolicType integerType;
	private static SymbolicType realType;
	private static SymbolicType arrayType;
	private static SymbolicType doubleArrayType;
	// Factories
	private static ObjectFactory objectFactory;
	private static ExpressionFactory expressionFactory;
	private static BooleanExpressionFactory booleanFactory;
	private static SymbolicTypeFactory typeFactory;
	// SymbolicObjects
	private static Comparator<SymbolicObject> objectComparator;
	private static SymbolicExpression nullExpression;
	private static NumericExpression two, four;
	private static SymbolicCompleteArrayType symbolicCompleteArrayType;
	// Collections
	private static Collection<SymbolicObject> objectCollection;
	private static ArrayList<NumericExpression> emptyNumericList;

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
		FactorySystem system = PreUniverses.newIdealFactorySystem();
		universe = PreUniverses.newPreUniverse(system);
		
		// Types
		integerType = universe.integerType();
		realType = universe.realType();
		arrayType = universe.arrayType(integerType); //creates an array of ints
		doubleArrayType = universe.arrayType(arrayType); //creates an array of int[]s
		
		// NumberExpressions
		two = universe.integer(2);
		four = universe.integer(4);
		
		// For testing comparator() method
		objectFactory = system.objectFactory();
		objectComparator = objectFactory.comparator();
		
		// For testing nullExpression() method
		expressionFactory = system.expressionFactory();
		nullExpression = expressionFactory.nullExpression();
		
		booleanFactory = system.booleanFactory();
		
		// For testing objects() method
		objectCollection = objectFactory.objects();
		
		emptyNumericList = new ArrayList<NumericExpression>();
		
		typeFactory = system.typeFactory();
		
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
	}

	@Before
	public void setUp() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}

	@Test
	@Ignore
	public void testCommonPreUniverse() {
		fail("Not yet implemented");
	}
	
	@Test
	@Ignore
	public void testErr() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testIerr() {
		
	}

	@Test
	@Ignore
	public void testCanonicSymbolicExpression() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testExpressionSymbolicOperatorSymbolicTypeSymbolicObjectArray() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testExpressionSymbolicOperatorSymbolicTypeSymbolicObject() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testExpressionSymbolicOperatorSymbolicTypeSymbolicObjectSymbolicObject() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testExpressionSymbolicOperatorSymbolicTypeSymbolicObjectSymbolicObjectSymbolicObject() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testZero() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testHashSet() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testCompatible() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testIncompatible() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testForallIntConcrete() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testExistsIntConcrete() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testTupleUnsafe() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testNumericExpressionFactory() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testCanonicSymbolicObject() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testMake() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testNumberFactory() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testAddIterableOfQextendsNumericExpression() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testAndIterableOfQextendsBooleanExpression() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testAndBooleanExpressionBooleanExpression() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testPureType() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testBooleanType() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testIntegerType() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testHerbrandIntegerType() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testRealType() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testBoundedIntegerType() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testHerbrandRealType() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testCharacterType() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testArrayTypeSymbolicTypeNumericExpression() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testArrayTypeSymbolicType() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testTypeSequenceSymbolicTypeArray() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testTypeSequenceIterableOfQextendsSymbolicType() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testTupleTypeStringObjectSymbolicTypeSequence() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testTupleTypeStringObjectIterableOfQextendsSymbolicType() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testFunctionTypeSymbolicTypeSequenceSymbolicType() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testFunctionTypeIterableOfQextendsSymbolicTypeSymbolicType() {
		fail("Not yet implemented");
	}

	@Test
	// Written by Jeff DiMarco(jdimarco) 9/20/13
	public void testUnionTypeStringObjectSymbolicTypeSequence() {
		LinkedList<SymbolicType> memberTypes = new LinkedList<SymbolicType>();
		SymbolicUnionType unionType;
		SymbolicTypeSequence sequence;
		CommonPreUniverse commonUniverse = (CommonPreUniverse)universe;

		memberTypes.add(integerType);
		memberTypes.add(realType);
		sequence = universe.typeSequence(memberTypes);
		
		unionType = commonUniverse.unionType(universe.stringObject("MyUnion"),
				sequence);
		
		assertEquals(SymbolicTypeKind.UNION, unionType.typeKind());
		sequence = unionType.sequence();
		assertEquals(integerType, sequence.getType(0));
		assertEquals(realType, sequence.getType(1));
		assertEquals(2, sequence.numTypes());
		assertEquals(universe.stringObject("MyUnion"), unionType.name());
	}

	@Test
	public void testUnionType() {
		LinkedList<SymbolicType> memberTypes = new LinkedList<SymbolicType>();
		SymbolicUnionType unionType;
		SymbolicTypeSequence sequence;

		memberTypes.add(integerType);
		memberTypes.add(realType);
		unionType = universe.unionType(universe.stringObject("MyUnion"),
				memberTypes);
		assertEquals(SymbolicTypeKind.UNION, unionType.typeKind());
		sequence = unionType.sequence();
		assertEquals(integerType, sequence.getType(0));
		assertEquals(realType, sequence.getType(1));
		assertEquals(2, sequence.numTypes());
		assertEquals(universe.stringObject("MyUnion"), unionType.name());
	}

	@Test
	@Ignore
	public void testUnionTypeStringObjectIterableOfQextendsSymbolicType() {
		fail("Not yet implemented");
	}

	@Test
	// Written by Marlin Blue
	public void testNumObjects() {
		// Testing universe against factory
		int object = universe.numObjects();		
		assertEquals(object, objectFactory.numObjects());
	}

	@Test
	@Ignore
	public void testObjectWithId() {
		fail("Not yet implemented");
	}

	@Test
	// Written by Marlin Blue
	public void testObjects() {
		Collection<SymbolicObject> testCollection = 
				universe.objects();
		assertEquals(objectCollection, testCollection);
	}

	@Test
	@Ignore
	public void testBooleanObject() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testCharObject() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testIntObject() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testNumberObject() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testStringObject() {
		fail("Not yet implemented");
	}

	@Test
	//written by Chris Heider
	public void testSymbolicConstant() {
		//create two symbolicConstants to see if they are equal
		StringObject name = universe.stringObject("name");
		SymbolicType type = universe.booleanType();  //need to test for bool type. the other has been done.
		SymbolicConstant scA = universe.symbolicConstant(name, type);
		SymbolicConstant scB = universe.symbolicConstant(name, type);
		
		assertEquals(scA,scB);
	}

	@Test
	// Written by Jordan Saints on 9/16/13
	// These nullExpression objects will be the same because they were generated by a factory
	public void testNullExpression() {
		SymbolicExpression resultNullExpression = universe.nullExpression();
		
		assertEquals(nullExpression, resultNullExpression); //test for equality
	}

	@Test
	@Ignore
	public void testNumberNumberObject() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testIntegerInt() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testRationalDouble() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testRationalIntInt() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testZeroInt() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testZeroReal() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testOneInt() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testOneReal() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testCharacter() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testExtractCharacter() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testStringExpression() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testAddNumericExpressionNumericExpression() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testSubtract() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testMultiplyNumericExpressionNumericExpression() {
		fail("Not yet implemented");
	}

	@Test(expected=SARLException.class)	
	public void testEmptyMultiply() {
		universe.multiply(emptyNumericList);
			
	}

	@Test
	@Ignore
	public void testDivide() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testModulo() {
		fail("Not yet implemented");
	}

	@Test
	// Test written by Jeff DiMarco (jdimarco) 9/17/13
	public void testMinus() {
		NumericExpression seventeen = universe.integer(17);
		NumericExpression negativeSeventeen = universe.integer(-17);
		assertEquals(universe.minus(seventeen), negativeSeventeen); // test -( 17) = -17
		assertEquals(universe.minus(negativeSeventeen), seventeen); // test -(-17) =  17
	}

	@Test
	@Ignore
	public void testPowerNumericExpressionIntObject() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testPowerNumericExpressionInt() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testPowerNumericExpressionNumericExpression() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testExtractNumber() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testSubstituteSymbolicConstants() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testSubstituteSymbolicExpressionMapOfSymbolicExpressionSymbolicExpression() {
		fail("Not yet implemented");
	}

	@Test
	// Test written by Jeff DiMarco (jdimarco) 9/17/13
	public void testBoolBooleanObject() {
		BooleanObject booleanObj = universe.booleanObject(true);
		BooleanExpression booleanExpr = booleanFactory.symbolic(booleanObj);
		assertEquals(universe.bool(booleanObj), booleanExpr); // trivial check of return type
	}

	@Test
	@Ignore
	public void testBoolBoolean() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testOrBooleanExpressionBooleanExpression() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testOrIterableOfQextendsBooleanExpression() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testNot() {
		fail("Not yet implemented");
	}

	@Test
	//Test written by Chris Heider 9/16/13
	public void testImplies() {
		//setup BooleanExpressions for running in equiv()
		BooleanExpression boolA = universe.bool(true);
		BooleanExpression boolB = universe.bool(true);
		BooleanExpression boolC = universe.bool(false);
		BooleanExpression boolD = universe.bool(false);
		BooleanExpression testTrue = universe.bool(true);
		BooleanExpression testFalse = universe.bool(false);
		
		assertEquals(universe.implies(boolA, boolB), testTrue); //test for 2 true
		assertEquals(universe.implies(boolA, boolC), testFalse); //test for a failure
		assertEquals(universe.implies(boolC, boolD), testTrue); //test for 2 false
		assertEquals(universe.implies(boolA, boolA), testTrue); //test for identical
	}

	@Test
	//Test written by Chris Heider 9/16/13
	public void testEquiv() {
		//setup BooleanExpressions for running in equiv()
		BooleanExpression boolA = universe.bool(true);
		BooleanExpression boolB = universe.bool(true);
		BooleanExpression boolC = universe.bool(false);
		BooleanExpression boolD = universe.bool(false);
		BooleanExpression testTrue = universe.bool(true);
		BooleanExpression testFalse = universe.bool(false);
		
		assertEquals(universe.equiv(boolA, boolB), testTrue); //test for 2 true
		assertEquals(universe.equiv(boolA, boolC), testFalse); //test for a failure
		assertEquals(universe.equiv(boolC, boolD), testTrue); //test for 2 false
		assertEquals(universe.equiv(boolA, boolA), testTrue); //test for identical
	}

	@Test
	@Ignore
	public void testSubstituteSymbolicExpressionSymbolicConstantSymbolicExpression() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testForallInt() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testExistsInt() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testLessThan() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testLessThanEquals() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testEqualsSymbolicExpressionSymbolicExpression() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testNeq() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testDivides() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testForall() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testExists() {
		fail("Not yet implemented");
	}

	@Test
	// Test written by Jeff DiMarco(jdimarco) 9/20/13
	public void testExtractBoolean() {
		BooleanExpression trueExpr;
		BooleanExpression falseExpr;
		BooleanExpression nullExpr;
		
		trueExpr = universe.bool(true);
		falseExpr = universe.bool(false);
		nullExpr = null;
		
		assertEquals(universe.extractBoolean(trueExpr), true);
		assertEquals(universe.extractBoolean(falseExpr), false);
		assertEquals(universe.extractBoolean(nullExpr), null);
			
	}

	@Test
	@Ignore
	public void testLambda() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testApply() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testUnionInject() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testUnionTest() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testUnionExtract() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testArray() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testAppend() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testEmptyArray() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testLength() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testArrayRead() {
		fail("Not yet implemented");
	}
	

	/*
	 * Main function that tests for successful completion of denseArrayWrite()
	 * Written by Jordan Saints on 9/16/13
	 */
	@Test
	public void testDenseArrayWrite_success() {
		// The SymbolicExpression, of type ARRAY(int) (array of ints), that we will be writing to
		SymbolicExpression arrayTypeExpression = universe.symbolicConstant(universe.stringObject("arrayTypeExpression"), arrayType);
		
		// A List of expressions to write to new array (in dense format),
		// where, after calling denseArrayWrite(), an element's index in this List == index in resulting expressions sequence
		List<SymbolicExpression> expressionsToWrite = Arrays.asList(new SymbolicExpression[] { null, null, two, null, two, null, null });
		
		// Call denseArrayWrite()!
		SymbolicExpression denseResult = universe.denseArrayWrite(arrayTypeExpression, expressionsToWrite);
		
		// Test by comparing to normal write operation in arrayWrite()
		// USAGE: universe.arrayWrite(array to write to, index in array to write at, value to write @ that index)
		SymbolicExpression writeResult = universe.arrayWrite(arrayTypeExpression, two, two); //adds a 2 at index 2 in arrayTypeExpression array
		writeResult = universe.arrayWrite(writeResult, four, two); //replace writeResult's entry at index 4 (NumExpr four) with a 2 (NumExpr two) 
		assertEquals(writeResult, denseResult); //test if arrays are equal
		
		// Test denseResult's type
		assertEquals(universe.arrayType(integerType), arrayType); //check that arrayType is actually correct type to begin with
		assertEquals(arrayType, denseResult.type()); //check that denseResult is of arrayType

		// Test denseResult's arguments
		assertEquals(2, denseResult.numArguments()); //test total numArguments
		@SuppressWarnings("unchecked")
		SymbolicSequence<SymbolicExpression> expressions = (SymbolicSequence<SymbolicExpression>) denseResult.argument(1); //get sequence of expressions
		assertEquals(5, expressions.size()); //the 2 trailing null SymExprs will be chopped off ("made dense")
		
		// Test denseResult's expressions sequence against known values in expressionsToWrite List
		assertEquals(nullExpression, expressions.get(0));
		assertEquals(nullExpression, expressions.get(1));
		assertEquals(two, expressions.get(2));
		assertEquals(nullExpression, expressions.get(3));
		assertEquals(two, expressions.get(4));
	}
	
	/*
	 * Auxiliary function #1 that tests failure branch (1 of 2) of denseArrayWrite()
	 * Written by Jordan Saints on 9/16/13
	 */
	@Test(expected=SARLException.class)
	public void testDenseArrayWrite_param1Exception() {
		// Create SymbolicExpression of type INTEGER (no array at all)
		SymbolicExpression integerTypeExpression = universe.symbolicConstant(universe.stringObject("integerTypeExpression"), integerType);
		
		// A List of expressions to write to new array (in dense format)
		List<SymbolicExpression> expressionsToWrite = Arrays.asList(new SymbolicExpression[] { null, null, two, null, two, null, null });
		
		// Will throw a SARLException because input param #1 (SymbolicExpression) must be of type ARRAY
		// "Argument 0 of denseArrayWrite must have array type but had type int"
		universe.denseArrayWrite(integerTypeExpression, expressionsToWrite);
	}
	
	/*
	 * Auxiliary function #2 that tests failure branch (2 of 2) of denseArrayWrite()
	 * Written by Jordan Saints on 9/16/13
	 */
	@Test(expected=SARLException.class)
	public void testDenseArrayWrite_param2Exception() {
		// Create SymbolicExpression of type ARRAY(int[]) (an array of int arrays) to fill with new values
		SymbolicExpression doubleArrayTypeExpression = universe.symbolicConstant(universe.stringObject("doubleArrayTypeExpression"), doubleArrayType);
		
		// A List of expressions to write to new array (in dense format)
		List<SymbolicExpression> expressionsToWrite = Arrays.asList(new SymbolicExpression[] { null, null, two, null, two, null, null });
		
		// Will throw a SARLException because input param #2 (List<SymbolicExpressions>) must be of type ARRAY
		// "Element 2 of values argument to denseArrayWrite has incompatible type.\nExpected: int[]\nSaw: int"
		universe.denseArrayWrite(doubleArrayTypeExpression, expressionsToWrite);
	}

	@Test
	@Ignore
	public void testDenseTupleWrite() {
		fail("Not yet implemented");
	}

	@Test
	public void testArrayLambda() {
		assertEquals(null, universe.arrayLambda(symbolicCompleteArrayType, nullExpression)); //Simple test for coverage.
	}

	@Test
	@Ignore
	public void testTuple() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testTupleRead() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testTupleWrite() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testCast() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testCond() {
		fail("Not yet implemented");
	}

	@Test
	/*
	 * Tests the comparator() factory method.
	 * Written by Jordan Saints on 9/16/13
	 */
	public void testComparator() {
		Comparator<SymbolicObject> resultComparator = universe.comparator();
		
		//the comparator objects objectComparator and resultComparator
		//will be the same because they are generated by a factory
		assertEquals(objectComparator, resultComparator); //generic test for equality
		assertTrue(resultComparator.equals(objectComparator)); //test if same attributes
		assertTrue(resultComparator == objectComparator); //test if same instance
	}

	@Test
	@Ignore
	public void testIntegerLong() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testIntegerBigInteger() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testRationalInt() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testRationalLong() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testRationalBigInteger() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testRationalFloat() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testRationalLongLong() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testRationalBigIntegerBigInteger() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testNumberNumber() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testTrueExpression() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testFalseExpression() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testNumValidCalls() {
		fail("Not yet implemented");
	}

	@Test
	public void testNumProverValidCalls() {
		assertEquals(universe.numProverValidCalls(), 0); //at the time of tests, universe.proverValidCount should be 0;
	}

	@Test
	@Ignore
	public void testIncrementValidCount() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testIncrementProverValidCount() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testBasicCollection() {
		fail("Not yet implemented");
	}

	@Test
	/*
	 * Tests the referenceType() method.
	 * Written by Jordan Saints on 9/16/13
	 */
	public void testReferenceType() {
		// Setup
		SymbolicType refType = universe.referenceType(); //call referenceType() method
		SymbolicTupleType refTuple = (SymbolicTupleType) refType; //cast to TUPLE SymbolicType
		SymbolicTypeSequence refTupleSequence = refTuple.sequence(); //pull out the tuple's SymbolicTypeSequence
		
		// Tests
		assertEquals(SymbolicTypeKind.TUPLE, refType.typeKind()); //test that the refType is a TUPLE kind
		assertEquals(universe.stringObject("Ref"), refTuple.name()); //test the name of the tuple
		//assertEquals("Ref", refTuple.name().getString()); //test the name of the tuple // ALSO WORKS
		assertEquals(1, refTupleSequence.numTypes()); //test the number of types available in this tuple's sequence
		assertEquals(integerType, refTupleSequence.getType(0)); //test sequence type
	}

	@Test
	@Ignore
	public void testNullReference() {
		fail("Not yet implemented");
	}

	@Test
	public void testDereference() {
		SymbolicType doubleArrayType = universe.arrayType(arrayType); //int[]
		SymbolicExpression arrayTypeExpression = universe.symbolicConstant(universe.stringObject("arrayTypeExpression"), doubleArrayType);
		
		try
		{
			universe.dereference(arrayTypeExpression, null);
		}
		catch(Exception e)
		{
			assertEquals(e.getClass(), SARLException.class); //test class name of thrown exception	
			assertEquals(e.getMessage(), "dereference given null reference");
		}
		
		try
		{
			universe.dereference(null, null);
		}
		catch(Exception e)
		{
			assertEquals(e.getClass(), SARLException.class); //test class name of thrown exception	
			assertEquals(e.getMessage(), "dereference given null value");
		}
	}

	@Test
	@Ignore
	public void testReferencedType() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testIdentityReference() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testArrayElementReference() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testTupleComponentReference() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testUnionMemberReference() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testOffsetReference() {
		fail("Not yet implemented");
	}

	@Test
	@Ignore
	public void testAssign() {
		fail("Not yet implemented");
	}
	
	@Test
	@Ignore
	public void testInteger() { //tests cannot have any parameters
		fail("Not yet implemented");
//		value = 50;
//		BigInteger N1= number(numberFactory.integer(value));
//		assertEquals(N1,50);
	}
	
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void tupleExceptionTest1(){
		
		SymbolicTupleType tupleType1 = universe.tupleType(universe.stringObject("tupleType1"), Arrays.asList(new SymbolicType[]{integerType,integerType,realType}));
		SymbolicExpression tuple = universe.tuple(tupleType1, Arrays.asList(new SymbolicExpression[]{universe.integer(1),universe.integer(2)}));
	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void tupleExceptionTest2(){
		SymbolicTupleType tupleType1 = universe.tupleType(universe.stringObject("tupleType1"), Arrays.asList(new SymbolicType[]{integerType,integerType,realType}));
		
		SymbolicExpression tuple = universe.tuple(tupleType1, Arrays.asList(new SymbolicExpression[]{universe.rational(1),universe.integer(2),universe.integer(2)}));

		
	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void testLengthExceptions(){
		
		NumericExpression[] arrayMembers = new NumericExpression[2] ;
		SymbolicExpression array;
		NumericExpression length;
		
		arrayMembers[0] = universe.integer(1);
		arrayMembers[1] = universe.integer(2);
		array = universe .array(integerType, Arrays.asList(arrayMembers));
		array = null;
		// exception for null array
		length = universe.length(array);

		
	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void testLengthExceptions2(){
		// exception for non array type
		SymbolicTupleType tupleType1;
		SymbolicExpression tuple;
		NumericExpression length;
		tupleType1 = universe.tupleType(universe.stringObject("tupleType1"), Arrays.asList(new SymbolicType[]{integerType,integerType}));
		tuple = universe.tuple(tupleType1, Arrays.asList(new SymbolicExpression[]{universe.integer(1),universe.integer(2)}));
		length = universe.length(tuple);	


	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void tupleWriteTest(){
		SymbolicTupleType tupleType1;
		SymbolicExpression tuple, resultedTuple;
		IntObject i1;
		i1 = universe.intObject(1);
		tupleType1 = universe.tupleType(universe.stringObject("tupleType1"), Arrays.asList(new SymbolicType[]{integerType,integerType}));
		tuple = universe.tuple(tupleType1, Arrays.asList(new SymbolicExpression[]{universe.integer(1),universe.integer(2)}));

		resultedTuple = universe.tupleWrite(tuple, i1, universe.integer(2));
		assertEquals(tuple, resultedTuple);
		
		
		// exception
		tuple = universe.tupleWrite(tuple, i1, universe.rational(3));
		
			
	}
	// written by Mohammad Alsulmi
	@Test
	public void emptyArrayTest(){
		// get an empty array with size 0
		SymbolicExpression array = universe.emptyArray(integerType);
		NumericExpression zero = universe.integer(0);
		assertEquals(zero,universe.length(array));
	}
	@Test(expected= SARLException.class)
	public void testModuloWithExceptions(){
		NumericExpression fiveInt, threeInt;
		NumericExpression fiveReal;
		NumericExpression fiveModthree;
		
		fiveInt = universe.integer(5);
		threeInt = universe.integer(3);
		fiveModthree = universe.modulo(fiveInt, threeInt);
		assertEquals(universe.integer(2),fiveModthree);
		
		//exception first arg is realtype
		
		fiveReal = universe.rational(5.0);
		fiveModthree = universe.modulo(fiveReal, threeInt);
		
		


	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void testModuloWithExceptions2(){
		NumericExpression fiveInt, threeInt;
		NumericExpression threeReal;
		NumericExpression fiveModthree;
		
		fiveInt = universe.integer(5);
		threeInt = universe.integer(3);
		fiveModthree = universe.modulo(fiveInt, threeInt);
		assertEquals(universe.integer(2),fiveModthree);
		threeReal = universe.rational(3.0);
		
		//exception second arg is realtype
		
		fiveModthree = universe.modulo(fiveInt, threeReal);

	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void testPowerException(){
		NumericExpression base = universe.integer(3);
		NumericExpression result = universe.power(base, 2);
		assertEquals(universe.integer(9), result);
		
		// exception when the exponent is negative
		
		result = universe.power(base, -2);
	}
	// written by Mohammad Alsulmi
	@Test
	public void testRemoveElementAt(){
		SymbolicExpression array, expected, resultedArray;
		NumericExpression one,two, three;
		
		
		one = universe.integer(1);
		two = universe.integer(2);
		three = universe.integer(3);
		array = universe.array(integerType, Arrays.asList(new NumericExpression[]{one,two,three}));
		expected = universe.array(integerType, Arrays.asList(new NumericExpression[]{one,three}));
		resultedArray = universe.removeElementAt(array, 1);
		
		assertEquals(expected, resultedArray);
		
		
	}
	// written by Mohammad Alsulmi
	@Test (expected= SARLException.class)
	public void testRemoveElementAtException(){
		
		SymbolicTupleType tupleType1;
		SymbolicExpression tuple, resultedArray;
		
		tupleType1 = universe.tupleType(universe.stringObject("tupleType1"), Arrays.asList(new SymbolicType[]{integerType,integerType}));
		tuple = universe.tuple(tupleType1, Arrays.asList(new SymbolicExpression[]{universe.integer(1),universe.integer(2)}));
		// passing an argument from type other than array
		resultedArray = universe.removeElementAt(tuple, 0);
				
	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void testRemoveElementAtException2(){
		SymbolicExpression array, expected, resultedArray;
		NumericExpression one,two, three;
		
		one = universe.integer(1);
		two = universe.integer(2);
		three = universe.integer(3);
		array = universe.array(integerType, Arrays.asList(new NumericExpression[]{one,two,three}));
		expected = universe.array(integerType, Arrays.asList(new NumericExpression[]{one,three}));
		// index out of range exception
		resultedArray = universe.removeElementAt(array, 3);
		
	}
	// written by Mohammad Alsulmi
	@Test
	public void testArrayWrite()
	{
		SymbolicExpression array, resultedArray, expected;
		NumericExpression one,two, three, five;
		
		one = universe.integer(1);
		two = universe.integer(2);
		three = universe.integer(3);
		five = universe.integer(5);
		
		array = universe.array(integerType, Arrays.asList(new NumericExpression[]{two,three,five}));
		expected = universe.array(integerType, Arrays.asList(new NumericExpression[]{two,two,five}));
		
		resultedArray = universe.arrayWrite(array, one, two);
		assertEquals(expected, resultedArray);
	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void testArrayWriteException()
	{
		// testing the fail when pass a null array to arrayWrite()
		SymbolicExpression array, resultedArray;
		NumericExpression one,two, three, five;
		
		one = universe.integer(1);
		two = universe.integer(2);
		three = universe.integer(3);
		five = universe.integer(5);
		
		array = universe.array(integerType, Arrays.asList(new NumericExpression[]{two,three,five}));
		array = null;
		resultedArray = universe.arrayWrite(array, one, two);
	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void testArrayWriteException2()
	{
		// testing the fail when pass a null index to arrayWrite()
		SymbolicExpression array, resultedArray;
		NumericExpression one,two, three, five;
		
		one = universe.integer(1);
		two = universe.integer(2);
		three = universe.integer(3);
		five = universe.integer(5);
		
		one = null;
		
		array = universe.array(integerType, Arrays.asList(new NumericExpression[]{two,three,five}));
		resultedArray = universe.arrayWrite(array, one, two);
	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void testArrayWriteException3()
	{
		// testing the fail when pass a null value to arrayWrite()
		SymbolicExpression array, resultedArray;
		NumericExpression one,two, three, five;
		
		one = universe.integer(1);
		two = universe.integer(2);
		three = universe.integer(3);
		five = universe.integer(5);
		
		
		array = universe.array(integerType, Arrays.asList(new NumericExpression[]{two,three,five}));
		two = null;
		resultedArray = universe.arrayWrite(array, one, two);
	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void testArrayWriteException4()
	{
		// testing the fail when pass a non array type to arrayWrite()
		// here we use a tuple instead of array
		SymbolicExpression  resultedArray,tuple;
		NumericExpression one,two,five;
		SymbolicTupleType tupleType1;
		
		tupleType1 = universe.tupleType(universe.stringObject("tupleType1"), Arrays.asList(new SymbolicType[]{integerType,integerType}));
		tuple = universe.tuple(tupleType1, Arrays.asList(new SymbolicExpression[]{universe.integer(1),universe.integer(2)}));
		
		one = universe.integer(1);
		two = universe.integer(2);
		
		resultedArray = universe.arrayWrite(tuple, one, two);
	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void testArrayWriteException5()
	{
		// testing the fail when pass a non integer index to arrayWrite()
		SymbolicExpression array, resultedArray;
		NumericExpression one,two, three, five;
		
		one = universe.rational(1);
		two = universe.integer(2);
		three = universe.integer(3);
		five = universe.integer(5);
		
		array = universe.array(integerType, Arrays.asList(new NumericExpression[]{two,three,five}));
		resultedArray = universe.arrayWrite(array, one, two);
	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void testArrayWriteException6()
	{
		// testing the fail when passing an incompatible value to arrayWrite()
		// here the array has integer type, so we pass real type instead of integer
		SymbolicExpression array, resultedArray;
		NumericExpression one,two, three, five;
		
		one = universe.integer(1);
		two = universe.integer(2);
		three = universe.integer(3);
		five = universe.integer(5);
		
		array = universe.array(integerType, Arrays.asList(new NumericExpression[]{two,three,five}));
		two = universe.rational(2.0);
		resultedArray = universe.arrayWrite(array, one, two);
	}
	// written by Mohammad Alsulmi
	@Test
	public void testRational(){
		// here we cover the remaining cases of using rational()
		long value1, num1,den1 ;
		float value2;
		NumericExpression result;

		num1 = 3;
		den1 = 2;
		value1 = 5;
		value2 = 5;
		result = universe.rational(value1); // long case
		assertEquals(universe.rational(5), result);
		result = universe.rational(value2); // float case
		assertEquals(universe.rational(5), result); 
		result = universe.rational(BigInteger.TEN); // BigInteger case
		assertEquals(universe.rational(10), result);
		result = universe.rational(num1, den1); // long numerator and denominator
		assertEquals(universe.rational(1.5), result);
		result = universe.rational(BigInteger.ONE, BigInteger.TEN); // BigInteger numerator and denominator
		assertEquals(universe.rational(.1), result);
		
	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)	
	public void TestArrayReadException(){
		// testing the fail when pass a null array to arrayRead()
		SymbolicExpression array, resultedArray;
		NumericExpression one,two, three, five;
				
		one = universe.integer(1);
		two = universe.integer(2);
		three = universe.integer(3);
		five = universe.integer(5);
		array = universe.array(integerType, Arrays.asList(new NumericExpression[]{two,three,five}));
		array = null;	// null array
		resultedArray = universe.arrayRead(array, one);
	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void TestArrayReadException2(){
		// testing the fail when pass a null index to arrayRead()
				
		SymbolicExpression array, resultedArray;
		NumericExpression one,two, three, five;

		one = universe.integer(1);
		two = universe.integer(2);
		three = universe.integer(3);
		five = universe.integer(5);		
		array = universe.array(integerType, Arrays.asList(new NumericExpression[]{two,three,five}));

		two = null; // null index
		resultedArray = universe.arrayRead(array, two);
	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void TestArrayReadException3(){
		// testing the fail when pass a non array type to arrayRead()
		// here we use a tuple instead of array
		SymbolicExpression  resultedArray,tuple;
		NumericExpression one,two,five;
		SymbolicTupleType tupleType1;

		tupleType1 = universe.tupleType(universe.stringObject("tupleType1"), Arrays.asList(new SymbolicType[]{integerType,integerType}));
		tuple = universe.tuple(tupleType1, Arrays.asList(new SymbolicExpression[]{universe.integer(1),universe.integer(2)}));
		one = universe.integer(1);
		two = universe.integer(2);
		
		resultedArray = universe.arrayRead(tuple, two);
	}
	// written by Mohammad Alsulmi
	@Test(expected= SARLException.class)
	public void TestArrayReadException4(){
		// testing the fail when pass a negative index to arrayRead()
		SymbolicExpression array, resultedArray;
		NumericExpression negativeOne,two, three, five;
		
		negativeOne = universe.integer(-1); // negative number
		two = universe.integer(2);
		three = universe.integer(3);
		five = universe.integer(5);
		
		array = universe.array(integerType, Arrays.asList(new NumericExpression[]{two,three,five}));
		resultedArray = universe.arrayRead(array, negativeOne);
	}








}
