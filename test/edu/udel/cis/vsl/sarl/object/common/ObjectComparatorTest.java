package edu.udel.cis.vsl.sarl.object.common;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;
import edu.udel.cis.vsl.sarl.collections.IF.ExpressionComparatorStub;

public class ObjectComparatorTest {

	ObjectComparator com;
	
	@Before
	public void setUp() throws Exception {
		this.com = new ObjectComparator();
	}

	/**
	 * Tests expressionComparator() and setExpressionComparator()
	 */
	@Test
	public void testExpressionComparator() {
		this.com.setExpressionComparator(new ExpressionComparatorStub());
		assertTrue(this.com.expressionComparator() instanceof ExpressionComparatorStub);
	}
/*
	@Test
	public void testCollectionComparator() {
		fail("Not yet implemented");
	}

	@Test
	public void testTypeComparator() {
		fail("Not yet implemented");
	}

	@Test
	public void testTypeSequenceComparator() {
		fail("Not yet implemented");
	}

	@Test
	public void testCompare() {
		CommonNumberObject ex1 = new CommonNumberObject(new RealInteger(new BigInteger("1")));
		CommonNumberObject ex2 = new CommonNumberObject(new RealInteger(new BigInteger("1")));
		System.out.println(this.com.compare(ex1, ex2));
	}
*/
}
