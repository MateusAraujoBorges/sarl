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
	private static IntegerNumber INT_POS_FOUR = numFactory.integer(4);
	private static IntegerNumber INT_POS_TEN = numFactory.integer(10);
	private static IntegerNumber INT_NEG_ONE = numFactory.negate(INT_POS_ONE);
	private static IntegerNumber INT_NEG_TWO = numFactory.negate(INT_POS_TWO);
	private static IntegerNumber INT_NEG_FOUR = numFactory.negate(INT_POS_FOUR);
	private static IntegerNumber INT_NEG_TEN = numFactory.negate(INT_POS_TEN);
	private static RationalNumber RAT_ZERO = numFactory.fraction(INT_ZERO,
			INT_POS_ONE);
	private static RationalNumber RAT_POS_ONE = numFactory.fraction(
			INT_POS_ONE, INT_POS_ONE);
	private static RationalNumber RAT_POS_TWO = numFactory.fraction(
			INT_POS_TWO, INT_POS_ONE);
	private static RationalNumber RAT_POS_FOUR = numFactory.fraction(
			INT_POS_FOUR, INT_POS_ONE);
	private static RationalNumber RAT_POS_TEN = numFactory.fraction(
			INT_POS_TEN, INT_POS_ONE);
	private static RationalNumber RAT_NEG_ONE = numFactory.fraction(
			INT_NEG_ONE, INT_POS_ONE);
	private static RationalNumber RAT_NEG_TWO = numFactory.fraction(
			INT_NEG_TWO, INT_POS_ONE);
	private static RationalNumber RAT_NEG_FOUR = numFactory.fraction(
			INT_NEG_FOUR, INT_POS_ONE);
	private static RationalNumber RAT_NEG_TEN = numFactory.fraction(
			INT_NEG_TEN, INT_POS_ONE);
	private static RationalNumber RAT_POS_HALF = numFactory.fraction(
			INT_POS_ONE, INT_POS_TWO);
	private static RationalNumber RAT_NEG_HALF = numFactory.fraction(
			INT_NEG_ONE, INT_POS_TWO);
	private static RationalNumber RAT_POS_QUART = numFactory.fraction(
			INT_POS_ONE, INT_POS_FOUR);
	private static RationalNumber RAT_NEG_QUART = numFactory.fraction(
			INT_NEG_ONE, INT_POS_FOUR);

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

	private void p(String input) {
		System.out.println(input);
	}

	private void p(Object input) {
		System.out.println(input.toString());
	}

	// ADD
	@Test
	public void add_Univ() {
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
	public void add_Infi() {
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
	public void add_Zero() {
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
	public void add_Single_Number() {
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
	public void multiply_Zero() {
		Interval interval_zero = numFactory.newInterval(false, RAT_ZERO, false,
				RAT_ZERO, false);
		Interval univInterval = numFactory.newInterval(false, null, true, null,
				true);
		Interval interval_neg1_pos1 = numFactory.newInterval(false,
				RAT_NEG_ONE, false, RAT_POS_ONE, false);
		Interval actualResult1 = numFactory.multiply(interval_zero,
				univInterval);
		Interval actualResult2 = numFactory.multiply(interval_zero,
				interval_neg1_pos1);

		assert actualResult1.isZero() && actualResult2.isZero();
	}

	@Test
	public void multiply_Univ() {
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

	@Test
	public void multiply_Two_Infinity() {
		Interval univInterval = numFactory.newInterval(false, null, true, null,
				true);
		Interval interval_left_infi1 = numFactory.newInterval(false, null,
				true, RAT_NEG_ONE, true);
		Interval interval_left_infi2 = numFactory.newInterval(false, null,
				true, RAT_ZERO, false);
		Interval interval_left_infi3 = numFactory.newInterval(false, null,
				true, RAT_POS_ONE, true);
		Interval interval_right_infi1 = numFactory.newInterval(false,
				RAT_POS_ONE, false, null, true);
		Interval interval_right_infi2 = numFactory.newInterval(false, RAT_ZERO,
				false, null, true);
		Interval interval_right_infi3 = numFactory.newInterval(false,
				RAT_NEG_ONE, true, null, true);
		// L1
		Interval actualResult_l1l1 = numFactory.multiply(interval_left_infi1,
				interval_left_infi1);
		Interval actualResult_l1l2 = numFactory.multiply(interval_left_infi1,
				interval_left_infi2);
		Interval actualResult_l1l3 = numFactory.multiply(interval_left_infi1,
				interval_left_infi3);
		Interval actualResult_l1r1 = numFactory.multiply(interval_left_infi1,
				interval_right_infi1);
		Interval actualResult_l1r2 = numFactory.multiply(interval_left_infi1,
				interval_right_infi2);
		Interval actualResult_l1r3 = numFactory.multiply(interval_left_infi1,
				interval_right_infi3);
		// L2
		Interval actualResult_l2l1 = numFactory.multiply(interval_left_infi2,
				interval_left_infi1);
		Interval actualResult_l2l2 = numFactory.multiply(interval_left_infi2,
				interval_left_infi2);
		Interval actualResult_l2l3 = numFactory.multiply(interval_left_infi2,
				interval_left_infi3);
		Interval actualResult_l2r1 = numFactory.multiply(interval_left_infi2,
				interval_right_infi1);
		Interval actualResult_l2r2 = numFactory.multiply(interval_left_infi2,
				interval_right_infi2);
		Interval actualResult_l2r3 = numFactory.multiply(interval_left_infi2,
				interval_right_infi3);
		// L3
		Interval actualResult_l3l1 = numFactory.multiply(interval_left_infi3,
				interval_left_infi1);
		Interval actualResult_l3l2 = numFactory.multiply(interval_left_infi3,
				interval_left_infi2);
		Interval actualResult_l3l3 = numFactory.multiply(interval_left_infi3,
				interval_left_infi3);
		Interval actualResult_l3r1 = numFactory.multiply(interval_left_infi3,
				interval_right_infi1);
		Interval actualResult_l3r2 = numFactory.multiply(interval_left_infi3,
				interval_right_infi2);
		Interval actualResult_l3r3 = numFactory.multiply(interval_left_infi3,
				interval_right_infi3);
		// R1
		Interval actualResult_r1l1 = numFactory.multiply(interval_right_infi1,
				interval_left_infi1);
		Interval actualResult_r1l2 = numFactory.multiply(interval_right_infi1,
				interval_left_infi2);
		Interval actualResult_r1l3 = numFactory.multiply(interval_right_infi1,
				interval_left_infi3);
		Interval actualResult_r1r1 = numFactory.multiply(interval_right_infi1,
				interval_right_infi1);
		Interval actualResult_r1r2 = numFactory.multiply(interval_right_infi1,
				interval_right_infi2);
		Interval actualResult_r1r3 = numFactory.multiply(interval_right_infi1,
				interval_right_infi3);
		// R2
		Interval actualResult_r2l1 = numFactory.multiply(interval_right_infi2,
				interval_left_infi1);
		Interval actualResult_r2l2 = numFactory.multiply(interval_right_infi2,
				interval_left_infi2);
		Interval actualResult_r2l3 = numFactory.multiply(interval_right_infi2,
				interval_left_infi3);
		Interval actualResult_r2r1 = numFactory.multiply(interval_right_infi2,
				interval_right_infi1);
		Interval actualResult_r2r2 = numFactory.multiply(interval_right_infi2,
				interval_right_infi2);
		Interval actualResult_r2r3 = numFactory.multiply(interval_right_infi2,
				interval_right_infi3);
		// R3
		Interval actualResult_r3l1 = numFactory.multiply(interval_right_infi3,
				interval_left_infi1);
		Interval actualResult_r3l2 = numFactory.multiply(interval_right_infi3,
				interval_left_infi2);
		Interval actualResult_r3l3 = numFactory.multiply(interval_right_infi3,
				interval_left_infi3);
		Interval actualResult_r3r1 = numFactory.multiply(interval_right_infi3,
				interval_right_infi1);
		Interval actualResult_r3r2 = numFactory.multiply(interval_right_infi3,
				interval_right_infi2);
		Interval actualResult_r3r3 = numFactory.multiply(interval_right_infi3,
				interval_right_infi3);
		// Expected
		// L1
		Interval expectedResult_l1l1 = numFactory.newInterval(false,
				RAT_POS_ONE, true, null, true);
		Interval expectedResult_l1l2 = numFactory.newInterval(false, RAT_ZERO,
				false, null, true);
		Interval expectedResult_l1l3 = univInterval;
		Interval expectedResult_l1r1 = interval_left_infi1;
		Interval expectedResult_l1r2 = interval_left_infi2;
		Interval expectedResult_l1r3 = univInterval;
		// L2
		Interval expectedResult_l2l2 = interval_right_infi2;
		Interval expectedResult_l2l3 = univInterval;
		Interval expectedResult_l2r1 = interval_left_infi2;
		Interval expectedResult_l2r2 = interval_left_infi2;
		Interval expectedResult_l2r3 = univInterval;
		// L3
		Interval expectedResult_l3l3 = univInterval;
		Interval expectedResult_l3r1 = univInterval;
		Interval expectedResult_l3r2 = univInterval;
		Interval expectedResult_l3r3 = univInterval;
		// R1
		Interval expectedResult_r1r1 = interval_right_infi1;
		Interval expectedResult_r1r2 = interval_right_infi2;
		Interval expectedResult_r1r3 = univInterval;
		// R2
		Interval expectedResult_r2r2 = interval_right_infi2;
		Interval expectedResult_r2r3 = univInterval;
		// R3
		Interval expectedResult_r3r3 = univInterval;

		// L1
		assert numFactory.compare(actualResult_l1l1, expectedResult_l1l1) == 0;
		assert numFactory.compare(actualResult_l1l2, expectedResult_l1l2) == 0;
		assert numFactory.compare(actualResult_l1l3, expectedResult_l1l3) == 0;
		assert numFactory.compare(actualResult_l1r1, expectedResult_l1r1) == 0;
		assert numFactory.compare(actualResult_l1r2, expectedResult_l1r2) == 0;
		assert numFactory.compare(actualResult_l1r3, expectedResult_l1r3) == 0;
		// L2
		assert numFactory.compare(actualResult_l2l1, expectedResult_l1l2) == 0;
		assert numFactory.compare(actualResult_l2l2, expectedResult_l2l2) == 0;
		assert numFactory.compare(actualResult_l2l3, expectedResult_l2l3) == 0;
		assert numFactory.compare(actualResult_l2r1, expectedResult_l2r1) == 0;
		assert numFactory.compare(actualResult_l2r2, expectedResult_l2r2) == 0;
		assert numFactory.compare(actualResult_l2r3, expectedResult_l2r3) == 0;
		// L3
		assert numFactory.compare(actualResult_l3l1, expectedResult_l1l3) == 0;
		assert numFactory.compare(actualResult_l3l2, expectedResult_l2l3) == 0;
		assert numFactory.compare(actualResult_l3l3, expectedResult_l3l3) == 0;
		assert numFactory.compare(actualResult_l3r1, expectedResult_l3r1) == 0;
		assert numFactory.compare(actualResult_l3r2, expectedResult_l3r2) == 0;
		assert numFactory.compare(actualResult_l3r3, expectedResult_l3r3) == 0;
		// R1
		assert numFactory.compare(actualResult_r1l1, expectedResult_l1r1) == 0;
		assert numFactory.compare(actualResult_r1l2, expectedResult_l2r1) == 0;
		assert numFactory.compare(actualResult_r1l3, expectedResult_l3r1) == 0;
		assert numFactory.compare(actualResult_r1r1, expectedResult_r1r1) == 0;
		assert numFactory.compare(actualResult_r1r2, expectedResult_r1r2) == 0;
		assert numFactory.compare(actualResult_r1r3, expectedResult_r1r3) == 0;
		// R2
		assert numFactory.compare(actualResult_r2l1, expectedResult_l1r2) == 0;
		assert numFactory.compare(actualResult_r2l2, expectedResult_l2r2) == 0;
		assert numFactory.compare(actualResult_r2l3, expectedResult_l3r2) == 0;
		assert numFactory.compare(actualResult_r2r1, expectedResult_r1r2) == 0;
		assert numFactory.compare(actualResult_r2r2, expectedResult_r2r2) == 0;
		assert numFactory.compare(actualResult_r2r3, expectedResult_r2r3) == 0;
		// R3
		assert numFactory.compare(actualResult_r3l1, expectedResult_l1r3) == 0;
		assert numFactory.compare(actualResult_r3l2, expectedResult_l2r3) == 0;
		assert numFactory.compare(actualResult_r3l3, expectedResult_l3r3) == 0;
		assert numFactory.compare(actualResult_r3r1, expectedResult_r1r3) == 0;
		assert numFactory.compare(actualResult_r3r2, expectedResult_r2r3) == 0;
		assert numFactory.compare(actualResult_r3r3, expectedResult_r3r3) == 0;
	}

	@Test
	public void multiply_One_Infinity1() {
		Interval univInterval = numFactory.newInterval(false, null, true, null,
				true);
		Interval interval_left_infi1 = numFactory.newInterval(false, null,
				true, RAT_NEG_ONE, true);
		Interval interval_left_infi2 = numFactory.newInterval(false, null,
				true, RAT_ZERO, false);
		Interval interval_left_infi3 = numFactory.newInterval(false, null,
				true, RAT_POS_ONE, true);
		Interval interval_right_infi1 = numFactory.newInterval(false,
				RAT_POS_ONE, false, null, true);
		Interval interval_right_infi2 = numFactory.newInterval(false, RAT_ZERO,
				false, null, true);
		Interval interval_right_infi3 = numFactory.newInterval(false,
				RAT_NEG_ONE, true, null, true);
		Interval interval_neg_neg = numFactory.newInterval(false, RAT_NEG_TWO,
				true, RAT_NEG_ONE, true);
		Interval interval_neg_zero = numFactory.newInterval(false, RAT_NEG_TWO,
				true, RAT_ZERO, false);
		Interval interval_neg_pos = numFactory.newInterval(false, RAT_NEG_ONE,
				false, RAT_POS_ONE, false);
		Interval interval_zero_pos = numFactory.newInterval(false, RAT_ZERO,
				false, RAT_POS_TWO, true);
		Interval interval_pos_pos = numFactory.newInterval(false, RAT_POS_ONE,
				false, RAT_POS_TWO, false);
		// L1
		Interval actualResult_l1nn = numFactory.multiply(interval_left_infi1,
				interval_neg_neg);
		Interval actualResult_l1nz = numFactory.multiply(interval_left_infi1,
				interval_neg_zero);
		Interval actualResult_l1np = numFactory.multiply(interval_left_infi1,
				interval_neg_pos);
		Interval actualResult_l1zp = numFactory.multiply(interval_left_infi1,
				interval_zero_pos);
		Interval actualResult_l1pp = numFactory.multiply(interval_left_infi1,
				interval_pos_pos);
		// L2
		Interval actualResult_l2nn = numFactory.multiply(interval_left_infi2,
				interval_neg_neg);
		Interval actualResult_l2nz = numFactory.multiply(interval_left_infi2,
				interval_neg_zero);
		Interval actualResult_l2np = numFactory.multiply(interval_left_infi2,
				interval_neg_pos);
		Interval actualResult_l2zp = numFactory.multiply(interval_left_infi2,
				interval_zero_pos);
		Interval actualResult_l2pp = numFactory.multiply(interval_left_infi2,
				interval_pos_pos);
		// L3
		Interval actualResult_l3nn = numFactory.multiply(interval_left_infi3,
				interval_neg_neg);
		Interval actualResult_l3nz = numFactory.multiply(interval_left_infi3,
				interval_neg_zero);
		Interval actualResult_l3np = numFactory.multiply(interval_left_infi3,
				interval_neg_pos);
		Interval actualResult_l3zp = numFactory.multiply(interval_left_infi3,
				interval_zero_pos);
		Interval actualResult_l3pp = numFactory.multiply(interval_left_infi3,
				interval_pos_pos);
		// R1
		Interval actualResult_r1nn = numFactory.multiply(interval_right_infi1,
				interval_neg_neg);
		Interval actualResult_r1nz = numFactory.multiply(interval_right_infi1,
				interval_neg_zero);
		Interval actualResult_r1np = numFactory.multiply(interval_right_infi1,
				interval_neg_pos);
		Interval actualResult_r1zp = numFactory.multiply(interval_right_infi1,
				interval_zero_pos);
		Interval actualResult_r1pp = numFactory.multiply(interval_right_infi1,
				interval_pos_pos);
		// R2
		Interval actualResult_r2nn = numFactory.multiply(interval_right_infi2,
				interval_neg_neg);
		Interval actualResult_r2nz = numFactory.multiply(interval_right_infi2,
				interval_neg_zero);
		Interval actualResult_r2np = numFactory.multiply(interval_right_infi2,
				interval_neg_pos);
		Interval actualResult_r2zp = numFactory.multiply(interval_right_infi2,
				interval_zero_pos);
		Interval actualResult_r2pp = numFactory.multiply(interval_right_infi2,
				interval_pos_pos);
		// R3
		Interval actualResult_r3nn = numFactory.multiply(interval_right_infi3,
				interval_neg_neg);
		Interval actualResult_r3nz = numFactory.multiply(interval_right_infi3,
				interval_neg_zero);
		Interval actualResult_r3np = numFactory.multiply(interval_right_infi3,
				interval_neg_pos);
		Interval actualResult_r3zp = numFactory.multiply(interval_right_infi3,
				interval_zero_pos);
		Interval actualResult_r3pp = numFactory.multiply(interval_right_infi3,
				interval_pos_pos);
		// L1
		Interval expectedResult_l1nn = numFactory.newInterval(false,
				RAT_POS_ONE, true, null, true);
		Interval expectedResult_l1nz = interval_right_infi2;
		Interval expectedResult_l1np = univInterval;
		Interval expectedResult_l1zp = interval_left_infi2;
		Interval expectedResult_l1pp = interval_left_infi1;
		// L2
		Interval expectedResult_l2nn = interval_right_infi2;
		Interval expectedResult_l2nz = interval_right_infi2;
		Interval expectedResult_l2np = univInterval;
		Interval expectedResult_l2zp = interval_left_infi2;
		Interval expectedResult_l2pp = interval_left_infi2;
		// L3
		Interval expectedResult_l3nn = numFactory.newInterval(false,
				RAT_NEG_TWO, true, null, true);
		Interval expectedResult_l3nz = expectedResult_l3nn;
		Interval expectedResult_l3np = univInterval;
		Interval expectedResult_l3zp = numFactory.newInterval(false, null,
				true, RAT_POS_TWO, true);
		Interval expectedResult_l3pp = expectedResult_l3zp;
		// R1
		Interval expectedResult_r1nn = interval_left_infi1;
		Interval expectedResult_r1nz = interval_left_infi2;
		Interval expectedResult_r1np = univInterval;
		Interval expectedResult_r1zp = interval_right_infi2;
		Interval expectedResult_r1pp = interval_right_infi1;
		// R2
		Interval expectedResult_r2nn = interval_left_infi2;
		Interval expectedResult_r2nz = interval_left_infi2;
		Interval expectedResult_r2np = univInterval;
		Interval expectedResult_r2zp = interval_right_infi2;
		Interval expectedResult_r2pp = interval_right_infi2;
		// R3
		Interval expectedResult_r3nn = numFactory.newInterval(false, null,
				true, RAT_POS_TWO, true);
		Interval expectedResult_r3nz = expectedResult_r3nn;
		Interval expectedResult_r3np = univInterval;
		Interval expectedResult_r3zp = numFactory.newInterval(false,
				RAT_NEG_TWO, true, null, true);
		Interval expectedResult_r3pp = expectedResult_r3zp;

		assert numFactory.compare(actualResult_l1nn, expectedResult_l1nn) == 0;
		assert numFactory.compare(actualResult_l1nz, expectedResult_l1nz) == 0;
		assert numFactory.compare(actualResult_l1np, expectedResult_l1np) == 0;
		assert numFactory.compare(actualResult_l1zp, expectedResult_l1zp) == 0;
		assert numFactory.compare(actualResult_l1pp, expectedResult_l1pp) == 0;
		assert numFactory.compare(actualResult_l2nn, expectedResult_l2nn) == 0;
		assert numFactory.compare(actualResult_l2nz, expectedResult_l2nz) == 0;
		assert numFactory.compare(actualResult_l2np, expectedResult_l2np) == 0;
		assert numFactory.compare(actualResult_l2zp, expectedResult_l2zp) == 0;
		assert numFactory.compare(actualResult_l2pp, expectedResult_l2pp) == 0;
		assert numFactory.compare(actualResult_l3nn, expectedResult_l3nn) == 0;
		assert numFactory.compare(actualResult_l3nz, expectedResult_l3nz) == 0;
		assert numFactory.compare(actualResult_l3np, expectedResult_l3np) == 0;
		assert numFactory.compare(actualResult_l3zp, expectedResult_l3zp) == 0;
		assert numFactory.compare(actualResult_l3pp, expectedResult_l3pp) == 0;
		assert numFactory.compare(actualResult_r1nn, expectedResult_r1nn) == 0;
		assert numFactory.compare(actualResult_r1nz, expectedResult_r1nz) == 0;
		assert numFactory.compare(actualResult_r1np, expectedResult_r1np) == 0;
		assert numFactory.compare(actualResult_r1zp, expectedResult_r1zp) == 0;
		assert numFactory.compare(actualResult_r1pp, expectedResult_r1pp) == 0;
		assert numFactory.compare(actualResult_r2nn, expectedResult_r2nn) == 0;
		assert numFactory.compare(actualResult_r2nz, expectedResult_r2nz) == 0;
		assert numFactory.compare(actualResult_r2np, expectedResult_r2np) == 0;
		assert numFactory.compare(actualResult_r2zp, expectedResult_r2zp) == 0;
		assert numFactory.compare(actualResult_r2pp, expectedResult_r2pp) == 0;
		assert numFactory.compare(actualResult_r3nn, expectedResult_r3nn) == 0;
		assert numFactory.compare(actualResult_r3nz, expectedResult_r3nz) == 0;
		assert numFactory.compare(actualResult_r3np, expectedResult_r3np) == 0;
		assert numFactory.compare(actualResult_r3zp, expectedResult_r3zp) == 0;
		assert numFactory.compare(actualResult_r3pp, expectedResult_r3pp) == 0;
	}

	@Test
	public void multiply_One_Infinity2() {
		Interval univInterval = numFactory.newInterval(false, null, true, null,
				true);
		Interval interval_left_infi1 = numFactory.newInterval(false, null,
				true, RAT_NEG_ONE, true);
		Interval interval_left_infi2 = numFactory.newInterval(false, null,
				true, RAT_ZERO, false);
		Interval interval_left_infi3 = numFactory.newInterval(false, null,
				true, RAT_POS_ONE, true);
		Interval interval_right_infi1 = numFactory.newInterval(false,
				RAT_POS_ONE, false, null, true);
		Interval interval_right_infi2 = numFactory.newInterval(false, RAT_ZERO,
				false, null, true);
		Interval interval_right_infi3 = numFactory.newInterval(false,
				RAT_NEG_ONE, true, null, true);
		Interval interval_neg_neg = numFactory.newInterval(false, RAT_NEG_TWO,
				true, RAT_NEG_ONE, true);
		Interval interval_neg_zero = numFactory.newInterval(false, RAT_NEG_TWO,
				true, RAT_ZERO, false);
		Interval interval_neg_pos = numFactory.newInterval(false, RAT_NEG_ONE,
				false, RAT_POS_ONE, false);
		Interval interval_zero_pos = numFactory.newInterval(false, RAT_ZERO,
				false, RAT_POS_TWO, true);
		Interval interval_pos_pos = numFactory.newInterval(false, RAT_POS_ONE,
				false, RAT_POS_TWO, false);
		// L1
		Interval actualResult_nnl1 = numFactory.multiply(interval_neg_neg,
				interval_left_infi1);
		Interval actualResult_nzl1 = numFactory.multiply(interval_neg_zero,
				interval_left_infi1);
		Interval actualResult_npl1 = numFactory.multiply(interval_neg_pos,
				interval_left_infi1);
		Interval actualResult_zpl1 = numFactory.multiply(interval_zero_pos,
				interval_left_infi1);
		Interval actualResult_ppl1 = numFactory.multiply(interval_pos_pos,
				interval_left_infi1);
		// L2
		Interval actualResult_nnl2 = numFactory.multiply(interval_neg_neg,
				interval_left_infi2);
		Interval actualResult_nzl2 = numFactory.multiply(interval_neg_zero,
				interval_left_infi2);
		Interval actualResult_npl2 = numFactory.multiply(interval_neg_pos,
				interval_left_infi2);
		Interval actualResult_zpl2 = numFactory.multiply(interval_zero_pos,
				interval_left_infi2);
		Interval actualResult_ppl2 = numFactory.multiply(interval_pos_pos,
				interval_left_infi2);
		// L3
		Interval actualResult_nnl3 = numFactory.multiply(interval_neg_neg,
				interval_left_infi3);
		Interval actualResult_nzl3 = numFactory.multiply(interval_neg_zero,
				interval_left_infi3);
		Interval actualResult_npl3 = numFactory.multiply(interval_neg_pos,
				interval_left_infi3);
		Interval actualResult_zpl3 = numFactory.multiply(interval_zero_pos,
				interval_left_infi3);
		Interval actualResult_ppl3 = numFactory.multiply(interval_pos_pos,
				interval_left_infi3);
		// R1
		Interval actualResult_nnr1 = numFactory.multiply(interval_neg_neg,
				interval_right_infi1);
		Interval actualResult_nzr1 = numFactory.multiply(interval_neg_zero,
				interval_right_infi1);
		Interval actualResult_npr1 = numFactory.multiply(interval_neg_pos,
				interval_right_infi1);
		Interval actualResult_zpr1 = numFactory.multiply(interval_zero_pos,
				interval_right_infi1);
		Interval actualResult_ppr1 = numFactory.multiply(interval_pos_pos,
				interval_right_infi1);
		// R2
		Interval actualResult_nnr2 = numFactory.multiply(interval_neg_neg,
				interval_right_infi2);
		Interval actualResult_nzr2 = numFactory.multiply(interval_neg_zero,
				interval_right_infi2);
		Interval actualResult_npr2 = numFactory.multiply(interval_neg_pos,
				interval_right_infi2);
		Interval actualResult_zpr2 = numFactory.multiply(interval_zero_pos,
				interval_right_infi2);
		Interval actualResult_ppr2 = numFactory.multiply(interval_pos_pos,
				interval_right_infi2);
		// R3
		Interval actualResult_nnr3 = numFactory.multiply(interval_neg_neg,
				interval_right_infi3);
		Interval actualResult_nzr3 = numFactory.multiply(interval_neg_zero,
				interval_right_infi3);
		Interval actualResult_npr3 = numFactory.multiply(interval_neg_pos,
				interval_right_infi3);
		Interval actualResult_zpr3 = numFactory.multiply(interval_zero_pos,
				interval_right_infi3);
		Interval actualResult_ppr3 = numFactory.multiply(interval_pos_pos,
				interval_right_infi3);
		// L1
		Interval expectedResult_l1nn = numFactory.newInterval(false,
				RAT_POS_ONE, true, null, true);
		Interval expectedResult_l1nz = interval_right_infi2;
		Interval expectedResult_l1np = univInterval;
		Interval expectedResult_l1zp = interval_left_infi2;
		Interval expectedResult_l1pp = interval_left_infi1;
		// L2
		Interval expectedResult_l2nn = interval_right_infi2;
		Interval expectedResult_l2nz = interval_right_infi2;
		Interval expectedResult_l2np = univInterval;
		Interval expectedResult_l2zp = interval_left_infi2;
		Interval expectedResult_l2pp = interval_left_infi2;
		// L3
		Interval expectedResult_l3nn = numFactory.newInterval(false,
				RAT_NEG_TWO, true, null, true);
		Interval expectedResult_l3nz = expectedResult_l3nn;
		Interval expectedResult_l3np = univInterval;
		Interval expectedResult_l3zp = numFactory.newInterval(false, null,
				true, RAT_POS_TWO, true);
		Interval expectedResult_l3pp = expectedResult_l3zp;
		// R1
		Interval expectedResult_r1nn = interval_left_infi1;
		Interval expectedResult_r1nz = interval_left_infi2;
		Interval expectedResult_r1np = univInterval;
		Interval expectedResult_r1zp = interval_right_infi2;
		Interval expectedResult_r1pp = interval_right_infi1;
		// R2
		Interval expectedResult_r2nn = interval_left_infi2;
		Interval expectedResult_r2nz = interval_left_infi2;
		Interval expectedResult_r2np = univInterval;
		Interval expectedResult_r2zp = interval_right_infi2;
		Interval expectedResult_r2pp = interval_right_infi2;
		// R3
		Interval expectedResult_r3nn = numFactory.newInterval(false, null,
				true, RAT_POS_TWO, true);
		Interval expectedResult_r3nz = expectedResult_r3nn;
		Interval expectedResult_r3np = univInterval;
		Interval expectedResult_r3zp = numFactory.newInterval(false,
				RAT_NEG_TWO, true, null, true);
		Interval expectedResult_r3pp = expectedResult_r3zp;

		assert numFactory.compare(actualResult_nnl1, expectedResult_l1nn) == 0;
		assert numFactory.compare(actualResult_nzl1, expectedResult_l1nz) == 0;
		assert numFactory.compare(actualResult_npl1, expectedResult_l1np) == 0;
		assert numFactory.compare(actualResult_zpl1, expectedResult_l1zp) == 0;
		assert numFactory.compare(actualResult_ppl1, expectedResult_l1pp) == 0;
		assert numFactory.compare(actualResult_nnl2, expectedResult_l2nn) == 0;
		assert numFactory.compare(actualResult_nzl2, expectedResult_l2nz) == 0;
		assert numFactory.compare(actualResult_npl2, expectedResult_l2np) == 0;
		assert numFactory.compare(actualResult_zpl2, expectedResult_l2zp) == 0;
		assert numFactory.compare(actualResult_ppl2, expectedResult_l2pp) == 0;
		assert numFactory.compare(actualResult_nnl3, expectedResult_l3nn) == 0;
		assert numFactory.compare(actualResult_nzl3, expectedResult_l3nz) == 0;
		assert numFactory.compare(actualResult_npl3, expectedResult_l3np) == 0;
		assert numFactory.compare(actualResult_zpl3, expectedResult_l3zp) == 0;
		assert numFactory.compare(actualResult_ppl3, expectedResult_l3pp) == 0;
		assert numFactory.compare(actualResult_nnr1, expectedResult_r1nn) == 0;
		assert numFactory.compare(actualResult_nzr1, expectedResult_r1nz) == 0;
		assert numFactory.compare(actualResult_npr1, expectedResult_r1np) == 0;
		assert numFactory.compare(actualResult_zpr1, expectedResult_r1zp) == 0;
		assert numFactory.compare(actualResult_ppr1, expectedResult_r1pp) == 0;
		assert numFactory.compare(actualResult_nnr2, expectedResult_r2nn) == 0;
		assert numFactory.compare(actualResult_nzr2, expectedResult_r2nz) == 0;
		assert numFactory.compare(actualResult_npr2, expectedResult_r2np) == 0;
		assert numFactory.compare(actualResult_zpr2, expectedResult_r2zp) == 0;
		assert numFactory.compare(actualResult_ppr2, expectedResult_r2pp) == 0;
		assert numFactory.compare(actualResult_nnr3, expectedResult_r3nn) == 0;
		assert numFactory.compare(actualResult_nzr3, expectedResult_r3nz) == 0;
		assert numFactory.compare(actualResult_npr3, expectedResult_r3np) == 0;
		assert numFactory.compare(actualResult_zpr3, expectedResult_r3zp) == 0;
		assert numFactory.compare(actualResult_ppr3, expectedResult_r3pp) == 0;
	}

	@Test
	public void multiply_No_Infinity() {
		Interval interval_neg_neg = numFactory.newInterval(false, RAT_NEG_TWO,
				true, RAT_NEG_ONE, true);
		Interval interval_neg_zero = numFactory.newInterval(false, RAT_NEG_TWO,
				true, RAT_ZERO, false);
		Interval interval_neg_pos1 = numFactory.newInterval(false, RAT_NEG_TWO,
				false, RAT_POS_ONE, false);
		Interval interval_pos_pos = numFactory.newInterval(false, RAT_POS_ONE,
				false, RAT_POS_TWO, false);
		Interval interval_zero_pos = numFactory.newInterval(false, RAT_ZERO,
				false, RAT_POS_TWO, true);
		Interval interval_neg_pos2 = numFactory.newInterval(false, RAT_NEG_ONE,
				true, RAT_POS_TWO, true);
		// L1
		Interval actualResult_nnnn = numFactory.multiply(interval_neg_neg,
				interval_neg_neg);
		Interval actualResult_nnnz = numFactory.multiply(interval_neg_neg,
				interval_neg_zero);
		Interval actualResult_nnnp1 = numFactory.multiply(interval_neg_neg,
				interval_neg_pos1);
		Interval actualResult_nnpp = numFactory.multiply(interval_neg_neg,
				interval_pos_pos);
		Interval actualResult_nnzp = numFactory.multiply(interval_neg_neg,
				interval_zero_pos);
		Interval actualResult_nnnp2 = numFactory.multiply(interval_neg_neg,
				interval_neg_pos2);
		// L2
		Interval actualResult_nznn = numFactory.multiply(interval_neg_zero,
				interval_neg_neg);
		Interval actualResult_nznz = numFactory.multiply(interval_neg_zero,
				interval_neg_zero);
		Interval actualResult_nznp1 = numFactory.multiply(interval_neg_zero,
				interval_neg_pos1);
		Interval actualResult_nzpp = numFactory.multiply(interval_neg_zero,
				interval_pos_pos);
		Interval actualResult_nzzp = numFactory.multiply(interval_neg_zero,
				interval_zero_pos);
		Interval actualResult_nznp2 = numFactory.multiply(interval_neg_zero,
				interval_neg_pos2);
		// L3
		Interval actualResult_np1nn = numFactory.multiply(interval_neg_pos1,
				interval_neg_neg);
		Interval actualResult_np1nz = numFactory.multiply(interval_neg_pos1,
				interval_neg_zero);
		Interval actualResult_np1np1 = numFactory.multiply(interval_neg_pos1,
				interval_neg_pos1);
		Interval actualResult_np1pp = numFactory.multiply(interval_neg_pos1,
				interval_pos_pos);
		Interval actualResult_np1zp = numFactory.multiply(interval_neg_pos1,
				interval_zero_pos);
		Interval actualResult_np1np2 = numFactory.multiply(interval_neg_pos1,
				interval_neg_pos2);
		// R1
		Interval actualResult_ppnn = numFactory.multiply(interval_pos_pos,
				interval_neg_neg);
		Interval actualResult_ppnz = numFactory.multiply(interval_pos_pos,
				interval_neg_zero);
		Interval actualResult_ppnp1 = numFactory.multiply(interval_pos_pos,
				interval_neg_pos1);
		Interval actualResult_pppp = numFactory.multiply(interval_pos_pos,
				interval_pos_pos);
		Interval actualResult_ppzp = numFactory.multiply(interval_pos_pos,
				interval_zero_pos);
		Interval actualResult_ppnp2 = numFactory.multiply(interval_pos_pos,
				interval_neg_pos2);
		// R2
		Interval actualResult_zpnn = numFactory.multiply(interval_zero_pos,
				interval_neg_neg);
		Interval actualResult_zpnz = numFactory.multiply(interval_zero_pos,
				interval_neg_zero);
		Interval actualResult_zpnp1 = numFactory.multiply(interval_zero_pos,
				interval_neg_pos1);
		Interval actualResult_zppp = numFactory.multiply(interval_zero_pos,
				interval_pos_pos);
		Interval actualResult_zpzp = numFactory.multiply(interval_zero_pos,
				interval_zero_pos);
		Interval actualResult_zpnp2 = numFactory.multiply(interval_zero_pos,
				interval_neg_pos2);
		// R3
		Interval actualResult_np2nn = numFactory.multiply(interval_neg_pos2,
				interval_neg_neg);
		Interval actualResult_np2nz = numFactory.multiply(interval_neg_pos2,
				interval_neg_zero);
		Interval actualResult_np2np1 = numFactory.multiply(interval_neg_pos2,
				interval_neg_pos1);
		Interval actualResult_np2pp = numFactory.multiply(interval_neg_pos2,
				interval_pos_pos);
		Interval actualResult_np2zp = numFactory.multiply(interval_neg_pos2,
				interval_zero_pos);
		Interval actualResult_np2np2 = numFactory.multiply(interval_neg_pos2,
				interval_neg_pos2);
		// Expected
		// L1
		Interval expectedResult_nnnn = numFactory.newInterval(false,
				RAT_POS_ONE, true, RAT_POS_FOUR, true);
		Interval expectedResult_nnnz = numFactory.newInterval(false, RAT_ZERO,
				false, RAT_POS_FOUR, true);
		Interval expectedResult_nnnp1 = numFactory.newInterval(false,
				RAT_NEG_TWO, true, RAT_POS_FOUR, true);
		Interval expectedResult_nnpp = numFactory.newInterval(false,
				RAT_NEG_FOUR, true, RAT_NEG_ONE, true);
		Interval expectedResult_nnzp = numFactory.newInterval(false,
				RAT_NEG_FOUR, true, RAT_ZERO, false);
		Interval expectedResult_nnnp2 = numFactory.newInterval(false,
				RAT_NEG_FOUR, true, RAT_POS_TWO, true);
		// L2
		Interval expectedResult_nznz = numFactory.newInterval(false, RAT_ZERO,
				false, RAT_POS_FOUR, true);
		Interval expectedResult_nznp1 = numFactory.newInterval(false,
				RAT_NEG_TWO, true, RAT_POS_FOUR, true);
		Interval expectedResult_nzpp = numFactory.newInterval(false,
				RAT_NEG_FOUR, true, RAT_ZERO, false);
		Interval expectedResult_nzzp = expectedResult_nzpp;
		Interval expectedResult_nznp2 = numFactory.newInterval(false,
				RAT_NEG_FOUR, true, RAT_POS_TWO, true);
		// L3
		Interval expectedResult_np1np1 = numFactory.newInterval(false,
				RAT_NEG_TWO, false, RAT_POS_FOUR, false);
		Interval expectedResult_np1pp = numFactory.newInterval(false,
				RAT_NEG_FOUR, false, RAT_POS_TWO, false);
		Interval expectedResult_np1zp = numFactory.newInterval(false,
				RAT_NEG_FOUR, true, RAT_POS_TWO, true);
		Interval expectedResult_np1np2 = expectedResult_np1zp;
		// R1
		Interval expectedResult_pppp = numFactory.newInterval(false,
				RAT_POS_ONE, false, RAT_POS_FOUR, false);
		Interval expectedResult_ppzp = numFactory.newInterval(false, RAT_ZERO,
				false, RAT_POS_FOUR, true);
		Interval expectedResult_ppnp2 = numFactory.newInterval(false,
				RAT_NEG_TWO, true, RAT_POS_FOUR, true);
		// R2
		Interval expectedResult_zpzp = expectedResult_ppzp;
		Interval expectedResult_zpnp2 = expectedResult_ppnp2;
		// R3
		Interval expectedResult_np2np2 = expectedResult_ppnp2;

		// L1
		assert numFactory.compare(actualResult_nnnn, expectedResult_nnnn) == 0;
		assert numFactory.compare(actualResult_nnnz, expectedResult_nnnz) == 0;
		assert numFactory.compare(actualResult_nnnp1, expectedResult_nnnp1) == 0;
		assert numFactory.compare(actualResult_nnpp, expectedResult_nnpp) == 0;
		assert numFactory.compare(actualResult_nnzp, expectedResult_nnzp) == 0;
		assert numFactory.compare(actualResult_nnnp2, expectedResult_nnnp2) == 0;
		// L2
		assert numFactory.compare(actualResult_nznn, expectedResult_nnnz) == 0;
		assert numFactory.compare(actualResult_nznz, expectedResult_nznz) == 0;
		assert numFactory.compare(actualResult_nznp1, expectedResult_nznp1) == 0;
		assert numFactory.compare(actualResult_nzpp, expectedResult_nzpp) == 0;
		assert numFactory.compare(actualResult_nzzp, expectedResult_nzzp) == 0;
		assert numFactory.compare(actualResult_nznp2, expectedResult_nznp2) == 0;
		// L3
		assert numFactory.compare(actualResult_np1nn, expectedResult_nnnp1) == 0;
		assert numFactory.compare(actualResult_np1nz, expectedResult_nznp1) == 0;
		assert numFactory.compare(actualResult_np1np1, expectedResult_np1np1) == 0;
		assert numFactory.compare(actualResult_np1pp, expectedResult_np1pp) == 0;
		assert numFactory.compare(actualResult_np1zp, expectedResult_np1zp) == 0;
		assert numFactory.compare(actualResult_np1np2, expectedResult_np1np2) == 0;
		// R1
		assert numFactory.compare(actualResult_ppnn, expectedResult_nnpp) == 0;
		assert numFactory.compare(actualResult_ppnz, expectedResult_nzpp) == 0;
		assert numFactory.compare(actualResult_ppnp1, expectedResult_np1pp) == 0;
		assert numFactory.compare(actualResult_pppp, expectedResult_pppp) == 0;
		assert numFactory.compare(actualResult_ppzp, expectedResult_ppzp) == 0;
		assert numFactory.compare(actualResult_ppnp2, expectedResult_ppnp2) == 0;
		// R2
		assert numFactory.compare(actualResult_zpnn, expectedResult_nnzp) == 0;
		assert numFactory.compare(actualResult_zpnz, expectedResult_nzzp) == 0;
		assert numFactory.compare(actualResult_zpnp1, expectedResult_np1zp) == 0;
		assert numFactory.compare(actualResult_zppp, expectedResult_ppzp) == 0;
		assert numFactory.compare(actualResult_zpzp, expectedResult_zpzp) == 0;
		assert numFactory.compare(actualResult_zpnp2, expectedResult_zpnp2) == 0;
		// R3
		assert numFactory.compare(actualResult_np2nn, expectedResult_nnnp2) == 0;
		assert numFactory.compare(actualResult_np2nz, expectedResult_nznp2) == 0;
		assert numFactory.compare(actualResult_np2np1, expectedResult_np1np2) == 0;
		assert numFactory.compare(actualResult_np2pp, expectedResult_ppnp2) == 0;
		assert numFactory.compare(actualResult_np2zp, expectedResult_zpnp2) == 0;
		assert numFactory.compare(actualResult_np2np2, expectedResult_np2np2) == 0;
	}

	// POWER
	@Test
	public void power_Zero_Interval() {
		Interval interval_int_zero = numFactory.newInterval(true, INT_ZERO,
				false, INT_ZERO, false);
		Interval interval_rat_zero = numFactory.newInterval(false, RAT_ZERO,
				false, RAT_ZERO, false);
		Interval actualResult_int_zero = numFactory.power(interval_int_zero, 1);
		Interval actualResult_rat_zero = numFactory.power(interval_rat_zero, 1);

		assert actualResult_int_zero.isZero();
		assert actualResult_rat_zero.isZero();
	}

	@Test
	public void power_ONE_Interval() {
		Interval interval_int_neg_one = numFactory.newInterval(true,
				INT_NEG_ONE, false, INT_NEG_ONE, false);
		Interval interval_int_pos_one = numFactory.newInterval(true,
				INT_POS_ONE, false, INT_POS_ONE, false);
		Interval interval_rat_neg_one = numFactory.newInterval(false,
				RAT_NEG_ONE, false, RAT_NEG_ONE, false);
		Interval interval_rat_pos_one = numFactory.newInterval(false,
				RAT_POS_ONE, false, RAT_POS_ONE, false);
		Interval actualResult_int_neg_one1 = numFactory.power(
				interval_int_neg_one, 1);
		Interval actualResult_rat_neg_one1 = numFactory.power(
				interval_rat_neg_one, 1);
		Interval actualResult_int_pos_one1 = numFactory.power(
				interval_int_pos_one, 1);
		Interval actualResult_rat_pos_one1 = numFactory.power(
				interval_rat_pos_one, 1);
		Interval actualResult_int_neg_one2 = numFactory.power(
				interval_int_neg_one, 2);
		Interval actualResult_rat_neg_one2 = numFactory.power(
				interval_rat_neg_one, 2);
		Interval actualResult_int_pos_one2 = numFactory.power(
				interval_int_pos_one, 2);
		Interval actualResult_rat_pos_one2 = numFactory.power(
				interval_rat_pos_one, 2);
		Interval expectedResult_int_neg_one1 = interval_int_neg_one;
		Interval expectedResult_rat_neg_one1 = interval_rat_neg_one;
		Interval expectedResult_int_pos_one1 = interval_int_pos_one;
		Interval expectedResult_rat_pos_one1 = interval_rat_pos_one;
		Interval expectedResult_int_neg_one2 = interval_int_pos_one;
		Interval expectedResult_rat_neg_one2 = interval_rat_pos_one;
		Interval expectedResult_int_pos_one2 = interval_int_pos_one;
		Interval expectedResult_rat_pos_one2 = interval_rat_pos_one;

		assert numFactory.compare(actualResult_int_neg_one1,
				expectedResult_int_neg_one1) == 0;
		assert numFactory.compare(actualResult_rat_neg_one1,
				expectedResult_rat_neg_one1) == 0;
		assert numFactory.compare(actualResult_int_pos_one1,
				expectedResult_int_pos_one1) == 0;
		assert numFactory.compare(actualResult_rat_pos_one1,
				expectedResult_rat_pos_one1) == 0;
		assert numFactory.compare(actualResult_int_neg_one2,
				expectedResult_int_neg_one2) == 0;
		assert numFactory.compare(actualResult_rat_neg_one2,
				expectedResult_rat_neg_one2) == 0;
		assert numFactory.compare(actualResult_int_pos_one2,
				expectedResult_int_pos_one2) == 0;
		assert numFactory.compare(actualResult_rat_pos_one2,
				expectedResult_rat_pos_one2) == 0;
	}

	@Test
	public void power_Zero_Exponet_Interval() {
		Interval interval_int_pos_two = numFactory.newInterval(true,
				INT_POS_TWO, false, INT_POS_TWO, false);
		Interval interval_rat_neg_two = numFactory.newInterval(false,
				RAT_NEG_TWO, false, RAT_NEG_TWO, false);
		Interval actualResult_int = numFactory.power(interval_int_pos_two, 0);
		Interval actualResult_rat = numFactory.power(interval_rat_neg_two, 0);
		Interval expectedResult_int = numFactory.newInterval(true, INT_POS_ONE,
				false, INT_POS_ONE, false);
		Interval expectedResult_rat = numFactory.newInterval(false,
				RAT_POS_ONE, false, RAT_POS_ONE, false);

		assert numFactory.compare(actualResult_int, expectedResult_int) == 0;
		assert numFactory.compare(actualResult_rat, expectedResult_rat) == 0;
	}

	@Test
	public void power_Zero_Exponet_Number() {
		IntegerNumber int_power_zero = numFactory.power(INT_POS_TWO, 0);
		RationalNumber rat_power_zero = numFactory.power(RAT_NEG_TWO, 0);

		assert numFactory.compare(int_power_zero, INT_POS_ONE) == 0;
		assert numFactory.compare(rat_power_zero, RAT_POS_ONE) == 0;
	}

	@Test
	public void power_Neg_Exponet_Number() {
		RationalNumber rat_power_neg1 = numFactory.power(RAT_POS_TWO, -1);
		RationalNumber rat_power_neg2 = numFactory.power(RAT_POS_HALF, -1);

		assert numFactory.compare(rat_power_neg1, RAT_POS_HALF) == 0;
		assert numFactory.compare(rat_power_neg2, RAT_POS_TWO) == 0;
	}

	@Test
	public void power_Univ() {
		Interval interval_int_univ = numFactory.newInterval(true, null, true,
				null, true);
		Interval interval_rat_univ = numFactory.newInterval(false, null, true,
				null, true);
		Interval actualResult_int = numFactory.power(interval_int_univ, 1);
		Interval actualResult_rat = numFactory.power(interval_rat_univ, 2);

		assert numFactory.compare(actualResult_int, interval_int_univ) == 0;
		assert numFactory.compare(actualResult_rat, interval_rat_univ) == 0;
	}

	@Test
	public void power_One_Infinity() {
		Interval interval_left_infi1 = numFactory.newInterval(false, null,
				true, RAT_NEG_ONE, true);
		Interval interval_left_infi2 = numFactory.newInterval(false, null,
				true, RAT_ZERO, false);
		Interval interval_left_infi3 = numFactory.newInterval(false, null,
				true, RAT_POS_ONE, true);
		Interval interval_right_infi1 = numFactory.newInterval(false,
				RAT_POS_ONE, false, null, true);
		Interval interval_right_infi2 = numFactory.newInterval(false, RAT_ZERO,
				false, null, true);
		Interval interval_right_infi3 = numFactory.newInterval(false,
				RAT_NEG_ONE, true, null, true);
		Interval actualResult_l1_pow_neg1 = numFactory.power(
				interval_left_infi1, -1);
		Interval actualResult_l1_pow_neg2 = numFactory.power(
				interval_left_infi1, -2);
		Interval actualResult_l1_pow_pos1 = numFactory.power(
				interval_left_infi1, 1);
		Interval actualResult_l1_pow_pos2 = numFactory.power(
				interval_left_infi1, 2);
		Interval actualResult_l2_pow_pos1 = numFactory.power(
				interval_left_infi2, 1);
		Interval actualResult_l2_pow_pos2 = numFactory.power(
				interval_left_infi2, 2);
		Interval actualResult_l3_pow_pos1 = numFactory.power(
				interval_left_infi3, 1);
		Interval actualResult_l3_pow_pos2 = numFactory.power(
				interval_left_infi3, 2);
		Interval actualResult_r1_pow_neg1 = numFactory.power(
				interval_right_infi1, -1);
		Interval actualResult_r1_pow_neg2 = numFactory.power(
				interval_right_infi1, -2);
		Interval actualResult_r1_pow_pos1 = numFactory.power(
				interval_right_infi1, 1);
		Interval actualResult_r1_pow_pos2 = numFactory.power(
				interval_right_infi1, 2);
		Interval actualResult_r2_pow_pos1 = numFactory.power(
				interval_right_infi2, 1);
		Interval actualResult_r2_pow_pos2 = numFactory.power(
				interval_right_infi2, 2);
		Interval actualResult_r3_pow_pos1 = numFactory.power(
				interval_right_infi3, 1);
		Interval actualResult_r3_pow_pos2 = numFactory.power(
				interval_right_infi3, 2);
		//
		Interval expectedResult_l1_pow_neg1 = numFactory.newInterval(false,
				RAT_NEG_ONE, true, RAT_ZERO, true);
		Interval expectedResult_l1_pow_neg2 = numFactory.newInterval(false,
				RAT_ZERO, true, RAT_POS_ONE, true);
		Interval expectedResult_l1_pow_pos1 = interval_left_infi1;
		Interval expectedResult_l1_pow_pos2 = numFactory.newInterval(false,
				RAT_POS_ONE, true, null, true);
		Interval expectedResult_l2_pow_pos1 = interval_left_infi2;
		Interval expectedResult_l2_pow_pos2 = interval_right_infi2;
		Interval expectedResult_l3_pow_pos1 = interval_left_infi3;
		Interval expectedResult_l3_pow_pos2 = interval_right_infi2;
		Interval expectedResult_r1_pow_neg1 = numFactory.newInterval(false,
				RAT_ZERO, true, RAT_POS_ONE, false);
		Interval expectedResult_r1_pow_neg2 = expectedResult_r1_pow_neg1;
		Interval expectedResult_r1_pow_pos1 = interval_right_infi1;
		Interval expectedResult_r1_pow_pos2 = interval_right_infi1;
		Interval expectedResult_r2_pow_pos1 = interval_right_infi2;
		Interval expectedResult_r2_pow_pos2 = interval_right_infi2;
		Interval expectedResult_r3_pow_pos1 = interval_right_infi3;
		Interval expectedResult_r3_pow_pos2 = interval_right_infi2;

		assert numFactory.compare(actualResult_l1_pow_neg1,
				expectedResult_l1_pow_neg1) == 0;
		assert numFactory.compare(actualResult_l1_pow_neg2,
				expectedResult_l1_pow_neg2) == 0;
		assert numFactory.compare(actualResult_l1_pow_pos1,
				expectedResult_l1_pow_pos1) == 0;
		assert numFactory.compare(actualResult_l1_pow_pos2,
				expectedResult_l1_pow_pos2) == 0;
		assert numFactory.compare(actualResult_l2_pow_pos1,
				expectedResult_l2_pow_pos1) == 0;
		assert numFactory.compare(actualResult_l2_pow_pos2,
				expectedResult_l2_pow_pos2) == 0;
		assert numFactory.compare(actualResult_l3_pow_pos1,
				expectedResult_l3_pow_pos1) == 0;
		assert numFactory.compare(actualResult_l3_pow_pos2,
				expectedResult_l3_pow_pos2) == 0;
		assert numFactory.compare(actualResult_r1_pow_neg1,
				expectedResult_r1_pow_neg1) == 0;
		assert numFactory.compare(actualResult_r1_pow_neg2,
				expectedResult_r1_pow_neg2) == 0;
		assert numFactory.compare(actualResult_r1_pow_pos1,
				expectedResult_r1_pow_pos1) == 0;
		assert numFactory.compare(actualResult_r1_pow_pos2,
				expectedResult_r1_pow_pos2) == 0;
		assert numFactory.compare(actualResult_r2_pow_pos1,
				expectedResult_r2_pow_pos1) == 0;
		assert numFactory.compare(actualResult_r2_pow_pos2,
				expectedResult_r2_pow_pos2) == 0;
		assert numFactory.compare(actualResult_r3_pow_pos1,
				expectedResult_r3_pow_pos1) == 0;
		assert numFactory.compare(actualResult_r3_pow_pos2,
				expectedResult_r3_pow_pos2) == 0;
	}

	@Test
	public void power_No_Infinity() {
		Interval interval_neg_neg = numFactory.newInterval(false, RAT_NEG_TWO,
				true, RAT_NEG_ONE, true);
		Interval interval_neg_zero = numFactory.newInterval(false, RAT_NEG_ONE,
				true, RAT_ZERO, false);
		Interval interval_neg_pos = numFactory.newInterval(false, RAT_NEG_ONE,
				false, RAT_POS_ONE, false);
		Interval interval_zero_pos = numFactory.newInterval(false, RAT_ZERO,
				false, RAT_POS_ONE, true);
		Interval interval_pos_pos = numFactory.newInterval(false, RAT_POS_ONE,
				false, RAT_POS_TWO, false);
		Interval actualResult_nn_pow_neg1 = numFactory.power(interval_neg_neg,
				-1);
		Interval actualResult_nn_pow_neg2 = numFactory.power(interval_neg_neg,
				-2);
		Interval actualResult_nn_pow_pos1 = numFactory.power(interval_neg_neg,
				1);
		Interval actualResult_nn_pow_pos2 = numFactory.power(interval_neg_neg,
				2);
		Interval actualResult_nz_pow_pos1 = numFactory.power(interval_neg_zero,
				1);
		Interval actualResult_nz_pow_pos2 = numFactory.power(interval_neg_zero,
				2);
		Interval actualResult_np_pow_pos1 = numFactory.power(interval_neg_pos,
				1);
		Interval actualResult_np_pow_pos2 = numFactory.power(interval_neg_pos,
				2);
		Interval actualResult_zp_pow_pos1 = numFactory.power(interval_zero_pos,
				1);
		Interval actualResult_zp_pow_pos2 = numFactory.power(interval_zero_pos,
				2);
		Interval actualResult_pp_pow_neg1 = numFactory.power(interval_pos_pos,
				-1);
		Interval actualResult_pp_pow_neg2 = numFactory.power(interval_pos_pos,
				-2);
		Interval actualResult_pp_pow_pos1 = numFactory.power(interval_pos_pos,
				1);
		Interval actualResult_pp_pow_pos2 = numFactory.power(interval_pos_pos,
				2);
		//
		Interval expectedResult_nn_pow_neg1 = numFactory.newInterval(false,
				RAT_NEG_ONE, true, RAT_NEG_HALF, true);
		Interval expectedResult_nn_pow_neg2 = numFactory.newInterval(false,
				RAT_POS_QUART, true, RAT_POS_ONE, true);
		Interval expectedResult_nn_pow_pos1 = interval_neg_neg;
		Interval expectedResult_nn_pow_pos2 = numFactory.newInterval(false,
				RAT_POS_ONE, true, RAT_POS_FOUR, true);
		Interval expectedResult_nz_pow_pos1 = interval_neg_zero;
		Interval expectedResult_nz_pow_pos2 = numFactory.newInterval(false,
				RAT_ZERO, false, RAT_POS_ONE, true);
		Interval expectedResult_np_pow_pos1 = interval_neg_pos;
		Interval expectedResult_np_pow_pos2 = numFactory.newInterval(false,
				RAT_ZERO, false, RAT_POS_ONE, false);
		Interval expectedResult_zp_pow_pos1 = interval_zero_pos;
		Interval expectedResult_zp_pow_pos2 = interval_zero_pos;
		Interval expectedResult_pp_pow_neg1 = numFactory.newInterval(false,
				RAT_POS_HALF, false, RAT_POS_ONE, false);
		Interval expectedResult_pp_pow_neg2 = numFactory.newInterval(false,
				RAT_POS_QUART, false, RAT_POS_ONE, false);
		Interval expectedResult_pp_pow_pos1 = interval_pos_pos;
		Interval expectedResult_pp_pow_pos2 = numFactory.newInterval(false,
				RAT_POS_ONE, false, RAT_POS_FOUR, false);

		assert numFactory.compare(actualResult_nn_pow_neg1,
				expectedResult_nn_pow_neg1) == 0;
		assert numFactory.compare(actualResult_nn_pow_neg2,
				expectedResult_nn_pow_neg2) == 0;
		assert numFactory.compare(actualResult_nn_pow_pos1,
				expectedResult_nn_pow_pos1) == 0;
		assert numFactory.compare(actualResult_nn_pow_pos2,
				expectedResult_nn_pow_pos2) == 0;
		assert numFactory.compare(actualResult_nz_pow_pos1,
				expectedResult_nz_pow_pos1) == 0;
		assert numFactory.compare(actualResult_nz_pow_pos2,
				expectedResult_nz_pow_pos2) == 0;
		assert numFactory.compare(actualResult_np_pow_pos1,
				expectedResult_np_pow_pos1) == 0;
		assert numFactory.compare(actualResult_np_pow_pos2,
				expectedResult_np_pow_pos2) == 0;
		assert numFactory.compare(actualResult_zp_pow_pos1,
				expectedResult_zp_pow_pos1) == 0;
		assert numFactory.compare(actualResult_zp_pow_pos2,
				expectedResult_zp_pow_pos2) == 0;
		assert numFactory.compare(actualResult_pp_pow_neg1,
				expectedResult_pp_pow_neg1) == 0;
		assert numFactory.compare(actualResult_pp_pow_neg2,
				expectedResult_pp_pow_neg2) == 0;
		assert numFactory.compare(actualResult_pp_pow_pos1,
				expectedResult_pp_pow_pos1) == 0;
		assert numFactory.compare(actualResult_pp_pow_pos2,
				expectedResult_pp_pow_pos2) == 0;
	}
	
	@Test
	public void power_No_Infinity2(){
		Interval interval1 = numFactory.newInterval(false, RAT_NEG_TWO,
				true, RAT_POS_ONE, true);
		Interval interval2 = numFactory.newInterval(false, RAT_NEG_ONE,
				false, RAT_POS_TWO, false);
		Interval actualResult1 = numFactory.power(interval1, 2);
		Interval actualResult2 = numFactory.power(interval2, 2);
		Interval expectedResult1 = numFactory.newInterval(false,
				RAT_ZERO, false, RAT_POS_FOUR, true);
		Interval expectedResult2 = numFactory.newInterval(false,
				RAT_ZERO, false, RAT_POS_FOUR, false);

		assert numFactory.compare(actualResult1,
				expectedResult1) == 0;
		assert numFactory.compare(actualResult2,
				expectedResult2) == 0;
	}
}
