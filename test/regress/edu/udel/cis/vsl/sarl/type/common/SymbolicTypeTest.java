package edu.udel.cis.vsl.sarl.type.common;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicIntegerType.IntegerKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicRealType.RealKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType.SymbolicTypeKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUninterpretedType;
import edu.udel.cis.vsl.sarl.number.IF.Numbers;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.object.IF.Objects;
import edu.udel.cis.vsl.sarl.type.IF.SymbolicTypeFactory;

/**
 * 
 * Testing CommonSymbolicType A SymbolicType could be of different kinds: Real,
 * Array, Tuple, Boolean, Char, Function, Union, or Integer.
 * 
 * 
 * @author alali
 *
 */
public class SymbolicTypeTest {

	/**
	 * creating different SymbolicTypes
	 */
	CommonSymbolicType realType, realType2, integerType, arrayType,
			functionType, tupleType, booleanType;

	ObjectFactory objectFactory;
	SymbolicTypeFactory typeFactory;
	SymbolicUniverse universe;

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {

	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
	}

	@Before
	public void setUp() throws Exception {
		realType = new CommonSymbolicRealType(RealKind.IDEAL);
		realType2 = new CommonSymbolicRealType(RealKind.FLOAT);
		integerType = new CommonSymbolicIntegerType(IntegerKind.IDEAL);
		objectFactory = Objects.newObjectFactory(Numbers.REAL_FACTORY);
		booleanType = new CommonSymbolicPrimitiveType(SymbolicTypeKind.BOOLEAN);
		this.universe = SARL.newStandardUniverse();
	}

	@After
	public void tearDown() throws Exception {
	}

	/**
	 * Tests the equality of two types by calling typeEquals()
	 * 
	 */
	@Test
	public void testIntrinsicEquals() {
		assertTrue(realType.intrinsicEquals(realType));
		assertFalse(realType.intrinsicEquals(realType2));
		assertFalse(realType.intrinsicEquals(integerType));
		assertFalse(realType.intrinsicEquals(null));
	}

	/**
	 * Testing the kind of a SymbolicType
	 */
	@Test
	public void testTypeKind() {
		assertEquals(realType.typeKind(), SymbolicTypeKind.REAL);
	}

	/**
	 * testing a type if it is INTEGER kind.
	 */
	@Test
	public void testIsInteger() {
		assertTrue(integerType.isInteger());
		assertFalse(realType.isInteger());
	}

	/**
	 * testing a type if it is REAL kind.
	 */
	@Test
	public void testIsReal() {
		assertTrue(realType.isReal());
		assertFalse(integerType.isReal());
	}

	/**
	 * testing a type if it is a BOOLEAN kind.
	 */
	@Test
	public void testIsBoolean() {
		assertTrue(booleanType.isBoolean());
		assertFalse(realType.isBoolean());
	}

	/**
	 * testing a type if it is numeric, i.e. INTEGER or REAL
	 */
	@Test
	public void testIsNumeric() {
		assertTrue(integerType.isNumeric());
		assertTrue(realType.isNumeric());
		assertFalse(booleanType.isNumeric());
	}

	/**
	 * tests if a type is HERBRAND in CommonSymbolicType, it is assumed that all
	 * types are NOT herbrand. it is overridden in the concrete classes.
	 */
	@Test
	public void testIsHerbrand() {
		assertFalse(booleanType.isHerbrand());
	}

	/**
	 * tests if a type is IDEAL in CommonSymbolicType, it is assumed that all
	 * types are NOT ideal so, the method must be overridden by the concrete
	 * classes that are ideal
	 */
	@Test
	public void testIsIdeal() {
		assertFalse(booleanType.isIdeal());
	}

	/**
	 * tests a string representation of the type
	 */
	@Test
	public void testToStringBufferLong() {
		assertEquals(realType.toStringBufferLong().toString(), "real");
	}

	/**
	 * tests the returned pureType of this type
	 */
	@Test
	public void testGetPureType() {
		assertTrue(realType.getPureType() instanceof CommonSymbolicRealType);
	}

	/**
	 * tests creation of uninterpreted type expressions
	 */
	@Test
	public void testUninterpretedTypeExpressionCreation() {
		SymbolicUninterpretedType type = universe
				.symbolicUninterpretedType("test");
		SymbolicUninterpretedType typeAgain = universe
				.symbolicUninterpretedType("test");

		assertTrue(type == typeAgain);

		SymbolicExpression expr = universe
				.concreteValueOfUninterpretedType(type, universe.intObject(0));

		assertTrue(type instanceof CommonSymbolicUninterpretedType);
		assertTrue(expr.operator() == SymbolicOperator.CONCRETE);
	}

	/**
	 * tests comparison of concrete uninterpreted type expressions
	 */
	@Test
	public void testUninterpretedTypeExpressionComparison() {
		SymbolicUninterpretedType type = universe
				.symbolicUninterpretedType("test");
		SymbolicExpression expr0 = universe
				.concreteValueOfUninterpretedType(type, universe.intObject(0));
		SymbolicExpression expr1 = universe
				.concreteValueOfUninterpretedType(type, universe.intObject(0));
		SymbolicExpression expr2 = universe
				.concreteValueOfUninterpretedType(type, universe.intObject(1));

		assertTrue(expr0 == expr1);
		assertTrue(universe.equals(expr0, expr1).isTrue());
		assertTrue(universe.equals(expr0, expr2).isFalse());
		assertTrue(universe.neq(expr0, expr2).isTrue());
	}

	/**
	 * tests comparison of non-concrete uninterpreted type expressions
	 */
	@Test
	public void testUninterpretedTypeNCExpressionComparison() {
		SymbolicUninterpretedType type = universe
				.symbolicUninterpretedType("test");
		SymbolicConstant ncExpr = universe
				.symbolicConstant(universe.stringObject("X"), type);
		SymbolicExpression expr0 = universe
				.concreteValueOfUninterpretedType(type, universe.intObject(0));
		BooleanExpression comparison = universe.equals(ncExpr, expr0);

		assertFalse(comparison.isTrue());
		assertFalse(comparison.isFalse());
	}

	/*
	
	
		
	*/

}
