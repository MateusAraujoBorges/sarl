package edu.udel.cis.vsl.sarl.numbers;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.number.IF.Numbers;

public class IntervalTest {

	private static NumberFactory numFactory = Numbers.REAL_FACTORY;
	private static IntegerNumber INT_ZERO = numFactory.zeroInteger();
	private static IntegerNumber INT_POS_ONE = numFactory.integer(1);
	private static IntegerNumber INT_POS_TWO = numFactory.integer(2);
	private static IntegerNumber INT_POS_FIVE = numFactory.integer(5);
	private static IntegerNumber INT_POS_TEN = numFactory.integer(10);
	private static IntegerNumber INT_NEG_ONE = numFactory.negate(INT_POS_ONE);
	private static IntegerNumber INT_NEG_TWO = numFactory.negate(INT_POS_TWO);
	private static IntegerNumber INT_NEG_FIVE = numFactory.negate(INT_POS_FIVE);
	private static IntegerNumber INT_NEG_TEN = numFactory.negate(INT_POS_TEN);
	private static RationalNumber RAT_ZERO = numFactory.fraction(INT_ZERO,
			INT_POS_ONE);
	private static RationalNumber RAT_POS_ONE = numFactory.fraction(
			INT_POS_ONE, INT_POS_ONE);
	private static RationalNumber RAT_POS_TWO = numFactory.fraction(
			INT_POS_TWO, INT_POS_ONE);
	private static RationalNumber RAT_POS_FIVE = numFactory.fraction(
			INT_POS_FIVE, INT_POS_ONE);
	private static RationalNumber RAT_POS_TEN = numFactory.fraction(
			INT_POS_TEN, INT_POS_ONE);
	private static RationalNumber RAT_NEG_ONE = numFactory.fraction(
			INT_NEG_ONE, INT_POS_ONE);
	private static RationalNumber RAT_NEG_TWO = numFactory.fraction(
			INT_NEG_TWO, INT_POS_ONE);
	private static RationalNumber RAT_NEG_FIVE = numFactory.fraction(
			INT_NEG_FIVE, INT_POS_ONE);
	private static RationalNumber RAT_NEG_TEN = numFactory.fraction(
			INT_NEG_TEN, INT_POS_ONE);

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
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

	private void p(String input){
		System.out.println(input);
	}

	private void p(Object input){
		System.out.println(input.toString());
	}
	
	// ADD
	@Test
	public void add_Interval_Univ() {
		Interval interval_neg1_pos1 = numFactory.newInterval(true, INT_NEG_ONE,
				false, INT_POS_ONE, false);
		Interval univInterval1 = numFactory.newInterval(true, null, true, null,
				true);
		Interval univInterval2 = numFactory.newInterval(true, null, true, null,
				true);
		Interval actualResult1 = numFactory.add(univInterval1, univInterval2);
		Interval actualResult2 = numFactory.add(interval_neg1_pos1,
				univInterval2);
		Interval actualResult3 = numFactory.add(univInterval1,
				interval_neg1_pos1);

		assert actualResult1.isUniversal() && actualResult2.isUniversal()
				&& actualResult3.isUniversal();
	}

	@Test
	public void add_Interval_Infi() {
		Interval interval_left_infi = numFactory.newInterval(false, null, true,
				RAT_NEG_ONE, true);
		Interval interval_right_infi = numFactory.newInterval(false,
				RAT_POS_ONE, false, null, true);
		Interval interval_neg10_pos10 = numFactory.newInterval(false,
				RAT_NEG_TWO, false, RAT_POS_TWO, false);
		Interval actualResult1 = numFactory.add(interval_left_infi,
				interval_left_infi);
		Interval actualResult2 = numFactory.add(interval_right_infi,
				interval_right_infi);
		Interval actualResult3 = numFactory.add(interval_left_infi,
				interval_right_infi);
		Interval actualResult4 = numFactory.add(interval_left_infi,
				interval_neg10_pos10);
		Interval actualResult5 = numFactory.add(interval_neg10_pos10,
				interval_right_infi);
		Interval expectedResult1 = numFactory.newInterval(false, null, true,
				RAT_NEG_TWO, true);
		Interval expectedResult2 = numFactory.newInterval(false, RAT_POS_TWO,
				false, null, true);
		Interval expectedResult4 = numFactory.newInterval(false, null, true,
				RAT_POS_ONE, true);
		Interval expectedResult5 = numFactory.newInterval(false, RAT_NEG_ONE,
				false, null, true);

		assert numFactory.compare(actualResult1, expectedResult1) == 0;
		assert numFactory.compare(actualResult2, expectedResult2) == 0;
		assert actualResult3.isUniversal();
		assert numFactory.compare(actualResult4, expectedResult4) == 0;
		assert numFactory.compare(actualResult5, expectedResult5) == 0;
	}

	@Test
	public void add_Interval_Zero() {
		Interval interval_int_zero = numFactory.newInterval(true, INT_ZERO,
				false, INT_ZERO, false);
		Interval interval_rat_zero = numFactory.newInterval(false, RAT_ZERO,
				false, RAT_ZERO, false);
		Interval interval_int_neg1_pos1 = numFactory.newInterval(true,
				INT_NEG_ONE, false, INT_POS_ONE, false);
		Interval interval_rat_neg1_pos1_1 = numFactory.newInterval(false,
				RAT_NEG_ONE, true, RAT_POS_ONE, true);
		Interval interval_rat_neg1_pos1_2 = numFactory.newInterval(false,
				RAT_NEG_ONE, false, RAT_POS_ONE, false);
		Interval actualResult1 = numFactory.add(interval_int_zero,
				interval_int_neg1_pos1);
		Interval actualResult2 = numFactory.add(interval_rat_zero,
				interval_rat_neg1_pos1_1);
		Interval actualResult3 = numFactory.add(interval_rat_zero,
				interval_rat_neg1_pos1_2);

		assert numFactory.compare(actualResult1, interval_int_neg1_pos1) == 0;
		assert numFactory.compare(actualResult2, interval_rat_neg1_pos1_1) == 0;
		assert numFactory.compare(actualResult3, interval_rat_neg1_pos1_2) == 0;
	}

	@Test
	public void add_Interval_Single_Number() {
		Interval interval_int_pos1 = numFactory.newInterval(true, INT_POS_ONE,
				false, INT_POS_ONE, false);
		Interval interval_rat_neg1 = numFactory.newInterval(false, RAT_NEG_ONE,
				false, RAT_NEG_ONE, false);
		Interval actualResult1 = numFactory.add(interval_int_pos1,
				interval_int_pos1);
		Interval actualResult2 = numFactory.add(interval_rat_neg1,
				interval_rat_neg1);
		Interval expectedResult1 = numFactory.newInterval(true, INT_POS_TWO,
				false, INT_POS_TWO, false);
		Interval expectedResult2 = numFactory.newInterval(false, RAT_NEG_TWO,
				false, RAT_NEG_TWO, false);

		assert numFactory.compare(actualResult1, expectedResult1) == 0;
		assert numFactory.compare(actualResult2, expectedResult2) == 0;
	}

	// MULTIPLY
	@Test
	public void multiply_Interval_Univ() {
		Interval interval_neg1_pos1 = numFactory.newInterval(true, INT_NEG_ONE,
				false, INT_POS_ONE, false);
		Interval univInterval1 = numFactory.newInterval(true, null, true, null,
				true);
		Interval univInterval2 = numFactory.newInterval(true, null, true, null,
				true);
		Interval actualResult1 = numFactory.multiply(univInterval1,
				univInterval2);
		Interval actualResult2 = numFactory.multiply(interval_neg1_pos1,
				univInterval2);
		Interval actualResult3 = numFactory.multiply(univInterval1,
				interval_neg1_pos1);

		assert actualResult1.isUniversal() && actualResult2.isUniversal()
				&& actualResult3.isUniversal();
	}

	// POWER
}
