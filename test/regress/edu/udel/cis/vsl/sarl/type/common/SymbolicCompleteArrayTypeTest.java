package edu.udel.cis.vsl.sarl.type.common;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicIntegerType.IntegerKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.ideal.common.NumericPrimitive;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.preuniverse.IF.FactorySystem;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverses;

/**
 * @author alali
 *
 *         Testing CommonSymbolicCompleteArrayType: this type of array is
 *         complete, i.e. you have to specify the length of the array when
 *         creating a new object of this type.
 *
 *         int computeHashCode() String extentString() NumericExpression
 *         extent() canonizeChildren(CommonObjectFactory factory) // no need to
 *         test because this class has not children isComplete()
 * 
 */
public class SymbolicCompleteArrayTypeTest {

	/**
	 * Declaring variables to be used in the test
	 */

	CommonSymbolicCompleteArrayType completeArray2, completeArray3,
			completeArray33;
	NumberFactory numberFactory;
	ObjectFactory objectFactory;
	SymbolicObject symbolicObject2, symbolicObject3;
	NumericExpression number2, number3;
	TypeComparator typeComparator;

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
	}

	/**
	 * instantiating variables that are used in the test
	 * 
	 * @throws Exception
	 */
	@Before
	public void setUp() throws Exception {
		FactorySystem system = PreUniverses.newIdealFactorySystem();

		typeComparator = system.typeFactory().typeComparator();
		numberFactory = system.numberFactory();
		objectFactory = system.objectFactory();
		symbolicObject3 = objectFactory.numberObject(numberFactory.integer(3));
		symbolicObject2 = objectFactory.numberObject(numberFactory.integer(2));

		SymbolicType intType = new CommonSymbolicIntegerType(IntegerKind.IDEAL);
		SymbolicType arrayType = new CommonSymbolicArrayType(intType);

		number3 = new NumericPrimitive(SymbolicOperator.CONCRETE, intType,
				symbolicObject3);
		number2 = new NumericPrimitive(SymbolicOperator.CONCRETE, intType,
				symbolicObject3);
		completeArray2 = new CommonSymbolicCompleteArrayType(arrayType,
				number2);
		completeArray3 = new CommonSymbolicCompleteArrayType(arrayType,
				number3);
		completeArray33 = new CommonSymbolicCompleteArrayType(arrayType,
				number3);
	}

	/**
	 * testing computeHashCode() two objects have the same hashCode if they're
	 * identical i.e. they've the same properties.
	 */
	@Test
	public void testComputeHashCode() {
		assertEquals(completeArray3.computeHashCode(),
				completeArray33.computeHashCode());

	}

	/**
	 * testing isComplete() all objects of this type must be complete
	 */
	@Test
	public void testIsComplete() {
		assertTrue(completeArray3.isComplete());
		assertTrue(completeArray33.isComplete());

	}

	/**
	 * testing if two CommonSymbolicCompleteArrayType objects have the same type
	 */
	@Test
	public void testTypeEquals() {
		assertTrue(completeArray3.typeEquals(completeArray33));
		assertTrue(completeArray2.typeEquals(completeArray3));
	}

	/**
	 * testing extendString(), checking if it prints those square parentheses
	 */
	@Test
	public void testExtentString() {
		assertEquals(completeArray2.extentString(),
				"[" + completeArray2.extent() + "]");
	}

	// typeComparator test is done in SymbolicTypeFactoryTest

}
