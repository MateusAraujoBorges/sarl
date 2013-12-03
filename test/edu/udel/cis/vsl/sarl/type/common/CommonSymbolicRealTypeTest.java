package edu.udel.cis.vsl.sarl.type.common;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.type.SymbolicRealType.RealKind;

public class CommonSymbolicRealTypeTest {
	/* Testing CommonSymbolicRealType by Team3
	 * Three realKinds: ideal, herbrand, and float;
	 */
		CommonSymbolicRealType idealRealKind, idealRealKind2, herbrandRealKind, floatRealKind;
		TypeComparator typeComparator;
	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
	}

	@Before
	public void setUp() throws Exception {
		typeComparator = new TypeComparator();
		idealRealKind = new CommonSymbolicRealType(RealKind.IDEAL);
		idealRealKind2 = new CommonSymbolicRealType(RealKind.IDEAL);
		floatRealKind = new CommonSymbolicRealType(RealKind.FLOAT);
		herbrandRealKind = new CommonSymbolicRealType(RealKind.HERBRAND);
	}

	@After
	public void tearDown() throws Exception {
	}


	@Test
	public void testRealKind() {
		assertEquals(herbrandRealKind.realKind(), RealKind.HERBRAND);
		assertEquals(floatRealKind.realKind(), RealKind.FLOAT);
		assertEquals(idealRealKind.realKind(), RealKind.IDEAL);
	}
	
	@Test
	public void testTypeEquals() {
		assertTrue(idealRealKind.typeEquals(idealRealKind2));
	}
	
	@Test
	public void testComputeHashCode() {
		assertEquals(idealRealKind.computeHashCode(), idealRealKind2.computeHashCode());
	}

	

	@Test
	public void testIsHerbrand() {
		assertTrue(herbrandRealKind.isHerbrand());
		
	}
	
	@Test
	public void testIsIdeal() {
		assertTrue(idealRealKind.isIdeal());
		assertTrue(idealRealKind2.isIdeal());
	}
	
	/*
	 * testing if two realTypes are equal using the compareTo in TypeComparator;
	 */
	@Test
	public void testTypeComparator(){
		assertEquals(typeComparator.compare(idealRealKind, idealRealKind2), 0);
	}

	/**
	 * this test checks whether the variables are canonizable or not,
	 * here they are not and return false.
	 */
	@Test
	public void testCanonizeChildren() 
	{
//		System.out.println(idealRealKind.isCanonic());
//		System.out.println(idealRealKind2.isCanonic());
//		System.out.println(herbrandRealKind.isCanonic());
//		System.out.println(floatRealKind.isCanonic());
		assertEquals(idealRealKind.isCanonic(), floatRealKind.isCanonic());
		assertEquals(idealRealKind2.isCanonic(), herbrandRealKind.isCanonic());
	}

	/**
	 * this test aims check the output for the method getPureType and the PureType for 
 		different kind of variables should be different.
	 */
	@Test
	public void testGetPureType() 
	{
//		System.out.println(idealRealKind.getPureType());
//		System.out.println(idealRealKind2.getPureType());
//		System.out.println(floatRealKind.getPureType());
//		System.out.println(herbrandRealKind.getPureType());
		assertEquals(idealRealKind.getPureType(), idealRealKind2.getPureType());
		assertNotEquals(floatRealKind.getPureType(), herbrandRealKind.getPureType());		
	}
	

	


	@Test
	public void testToStringBuffer() {
        CommonSymbolicRealType ideal1 = new CommonSymbolicRealType(RealKind.IDEAL);
        assertEquals(
            "IDEAL type should be 'real'",
            ideal1.toStringBuffer(true).toString(),
            "real");

        CommonSymbolicRealType herbrand1 = new CommonSymbolicRealType(RealKind.HERBRAND);
        assertEquals(
            "HERBRAND type should be 'hreal'",
            herbrand1.toStringBuffer(true).toString(),
            "hreal");

        CommonSymbolicRealType float1 = new CommonSymbolicRealType(RealKind.FLOAT);
        assertEquals(
            "FLOAT type should be 'float'",
            float1.toStringBuffer(true).toString(),
            "float");
	}


}
