package edu.udel.cis.vsl.sarl.object.common;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.number.real.RealNumberFactory;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverses;
import edu.udel.cis.vsl.sarl.type.common.TypeComparator;
import edu.udel.cis.vsl.sarl.type.common.TypeSequenceComparator;

/**
 * Test class for CommonObjectFactory
 * 
 * @author jtirrell
 *
 */
public class CommonObjectFactoryTest {

	/**
	 * CommonObjectFactory that is instantiated during setUp
	 */
	ObjectFactory fac;

	/**
	 * Instantiates this.fac to a CommonObjectFactory
	 * 
	 * @throws Exception
	 */
	@Before
	public void setUp() {
		this.fac = PreUniverses.newIdealFactorySystem().objectFactory();
	}

	/**
	 * Method to test CommonObjectFactory.CommonObjectFactory
	 */
	@Test
	public void testCommonObjectFactory() {
		assertTrue(fac instanceof CommonObjectFactory);
	}

	/**
	 * Method to test CommonObjectFactory.NumberFactory
	 */
	@Test
	public void testNumberFactory() {
		assertTrue(this.fac.numberFactory() instanceof RealNumberFactory);
	}

	/**
	 * Method to test CommonObjectFactory.init
	 */
	@Test
	public void testInit() {
		this.fac.setExpressionComparator(new ExpressionComparatorStub());
		this.fac.setTypeComparator(new TypeComparator(fac.comparator()));
		this.fac.setTypeSequenceComparator(new TypeSequenceComparator());

		try {
			this.fac.init();
			assertTrue(true);
		} catch (Exception e) {
			assertTrue(false);
		}
	}

	/**
	 * Method to test CommonObjectFactory.trueObj
	 */
	@Test
	public void testTrueObj() {
		assertEquals(true, this.fac.trueObj().getBoolean());
	}

	/**
	 * Method to test CommonObjectFactory.falseObj
	 */
	@Test
	public void testFalseObj() {
		assertEquals(false, this.fac.falseObj().getBoolean());
	}

	/**
	 * Method to test CommonObjectFactory.zeroIntObj
	 */
	@Test
	public void testZeroIntObj() {
		assertEquals(0, this.fac.zeroIntObj().getInt());
	}

	/**
	 * Method to test CommonObjectFactory.oneIntObj
	 */
	@Test
	public void testOneIntObj() {
		assertEquals(1, this.fac.oneIntObj().getInt());
	}

	/**
	 * Method to test CommonObjectFactory.zeroIntegerObj
	 */
	@Test
	public void testZeroIntegerObj() {
		assertEquals("0", this.fac.zeroIntegerObj().toString());
	}

	/**
	 * Method to test CommonObjectFactory.oneIntegerObj
	 */
	@Test
	public void testOneIntegerObj() {
		assertEquals("1", this.fac.oneIntegerObj().toString());
	}

	/**
	 * Method to test CommonObjectFactory.zeroRealObj
	 */
	@Test
	public void testZeroRealObj() {
		assertEquals("0", this.fac.zeroRealObj().toString());
	}

	/**
	 * Method to test CommonObjectFactory.oneRealObj
	 */
	@Test
	public void testOneRealObj() {
		assertEquals("1", this.fac.oneRealObj().toString());
	}

	/**
	 * Method to test CommonObjectFactory.numberObject
	 */
	@Test
	public void testNumberObject() {
		assertEquals("1", this.fac
				.numberObject(this.fac.numberFactory().integer(1)).toString());
	}

	/**
	 * Method to test thrown exception for CommonObjectFactory.numberObject()
	 */
	@Test(expected = SARLException.class)
	public void testNumberObjectException() {
		this.fac.numberObject(null);
	}

	/**
	 * Method to test CommonObjectFactory.stringObject
	 */
	@Test
	public void testStringObject() {
		assertEquals("string", this.fac.stringObject("string").toString());
	}

	/**
	 * Method to test thrown exception for CommonObjectFactory.stringObject()
	 */
	@Test(expected = SARLException.class)
	public void testStringObjectException() {
		this.fac.stringObject(null);
	}

	/**
	 * Method to test CommonObjectFactory.intObject
	 */
	@Test
	public void testIntObject() {
		assertEquals(1, this.fac.intObject(1).getInt());
	}

	/**
	 * Method to test CommonObjectFactory.charObject
	 */
	@Test
	public void testCharObject() {
		assertEquals('A', this.fac.charObject('A').getChar());
	}

	/**
	 * Method to test CommonObjectFactory.booleanObject
	 */
	@Test
	public void testBooleanObject() {
		assertEquals(true, this.fac.booleanObject(true).getBoolean());
		assertEquals(false, this.fac.booleanObject(false).getBoolean());
	}

	/**
	 * Method to test thrown exception for CommonObjectFactory.canonic()
	 */
	@Test(expected = SARLException.class)
	public void testCanonicException() {
		this.fac.canonic(null);
	}

}
