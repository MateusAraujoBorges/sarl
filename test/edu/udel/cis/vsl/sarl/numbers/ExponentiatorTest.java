package edu.udel.cis.vsl.sarl.numbers;

import static org.junit.Assert.assertEquals;

//import java.math.BigInteger;



import org.junit.Before;
import org.junit.BeforeClass;
//import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.number.Numbers;
import edu.udel.cis.vsl.sarl.number.real.Exponentiator;
//import edu.udel.cis.vsl.sarl.util.BinaryOperator;
import edu.udel.cis.vsl.sarl.util.BinaryOperator;

public class ExponentiatorTest {
	
	private static NumberFactory factory = Numbers.REAL_FACTORY;
	//private static BigInteger bigTwo = new BigInteger("2");
	//private static BigInteger bigThree = new BigInteger("3");
	private static IntegerNumber inOne = factory.integer(1);
	private static IntegerNumber inZero = factory.integer(0);
	//private static IntegerNumber inNegativeOne = factory.integer(-1);
	private static IntegerNumber inTwo = factory.integer(2);
	//private static IntegerNumber inThree = factory.integer(3);
	//private static IntegerNumber inEight = factory.integer(8);
	private static IntegerNumber inResult = factory.integer(9);

	//private static Exponentiator<IntegerNumber> myXpo;
	
	
	private BinaryOperator<IntegerNumber> multiplier;
	private Exponentiator<IntegerNumber> myXpo = new Exponentiator<IntegerNumber>(multiplier , inOne);
	
	
	
	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@Before
	public void setUp() throws Exception {
	}
	
	@Test
	public void OneExpTest(){
		inResult = myXpo.exp( inTwo , inOne );
		assertEquals( inResult , inTwo );
	}
	
	/*
	//need to catch illegalArgumentException
	@Test
	public void NegativeExpTest(){
		inResult = myXpo.exp( inTwo , inNegativeOne );
		assertEquals( inResult , inTwo );
	}
	*/	
	
	@Test
	public void ZeroExpTest(){
		inResult = myXpo.exp( inTwo , inZero );
		assertEquals( inResult , inOne );
	}
	
}
