/*
 * Copyright 2013 Stephen F. Siegel, University of Delaware
 */
package edu.udel.cis.vsl.sarl.simplify.common;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.PrintStream;
import java.util.Arrays;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.number.IF.Numbers;
import edu.udel.cis.vsl.sarl.preuniverse.IF.FactorySystem;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverses;
import edu.udel.cis.vsl.sarl.simplify.IF.Range;
import edu.udel.cis.vsl.sarl.simplify.IF.RangeFactory;

/**
 * @author WenhaoWu
 *
 */
public class IntervalUnionSetTest {
	// Declarations:
	private static PrintStream OUT = System.out;
	private static boolean DEBUG = false;
	private static boolean ASSERTION_ENABLED = false;

	private static int ARR_SIZE = 15;
	private static PreUniverse universe;
	private static NumberFactory numberFactory = Numbers.REAL_FACTORY;
	private static RangeFactory rangeFactory = new IntervalUnionFactory();
	private static Interval INT_EMPTY = numberFactory.emptyIntegerInterval();
	private static Interval RAT_EMPTY = numberFactory.emptyRealInterval();
	private static Interval INT_UNIV = numberFactory.universalIntegerInterval();
	private static Interval RAT_UNIV = numberFactory.universalRealInterval();
	private static IntegerNumber INT_POS_INF = numberFactory
			.infiniteInteger(true);
	private static IntegerNumber INT_NEG_INF = numberFactory
			.infiniteInteger(false);
	private static IntegerNumber INT_ZERO = numberFactory.zeroInteger();
	private static IntegerNumber INT_ONE = numberFactory.integer(1);
	private static IntegerNumber INT_TWO = numberFactory.integer(2);
	private static IntegerNumber INT_THREE = numberFactory.integer(3);
	private static IntegerNumber INT_FOUR = numberFactory.integer(4);
	private static IntegerNumber INT_FIVE = numberFactory.integer(5);
	private static IntegerNumber INT_SIX = numberFactory.integer(6);
	private static IntegerNumber INT_SEVEN = numberFactory.integer(7);
	private static IntegerNumber INT_EIGHT = numberFactory.integer(8);
	private static IntegerNumber INT_NINE = numberFactory.integer(9);
	private static IntegerNumber INT_TEN = numberFactory.integer(10);
	private static IntegerNumber INT_N_ONE = numberFactory.integer(-1);
	private static IntegerNumber INT_N_TWO = numberFactory.integer(-2);
	private static IntegerNumber INT_N_THREE = numberFactory.integer(-3);
	private static IntegerNumber INT_N_FOUR = numberFactory.integer(-4);
	private static IntegerNumber INT_N_FIVE = numberFactory.integer(-5);
	private static IntegerNumber INT_N_SIX = numberFactory.integer(-6);
	private static IntegerNumber INT_N_SEVEN = numberFactory.integer(-7);
	private static IntegerNumber INT_N_EIGHT = numberFactory.integer(-8);
	private static IntegerNumber INT_N_NINE = numberFactory.integer(-9);
	private static IntegerNumber INT_N_TEN = numberFactory.integer(-10);
	private static RationalNumber RAT_POS_INF = numberFactory
			.infiniteRational(true);
	private static RationalNumber RAT_NEG_INF = numberFactory
			.infiniteRational(false);
	private static RationalNumber RAT_ZERO = numberFactory.rational(INT_ZERO);
	private static RationalNumber RAT_ONE = numberFactory.rational(INT_ONE);
	private static RationalNumber RAT_TWO = numberFactory.rational(INT_TWO);
	private static RationalNumber RAT_THREE = numberFactory.rational(INT_THREE);
	private static RationalNumber RAT_FOUR = numberFactory.rational(INT_FOUR);
	private static RationalNumber RAT_FIVE = numberFactory.rational(INT_FIVE);
	private static RationalNumber RAT_SIX = numberFactory.rational(INT_SIX);
	private static RationalNumber RAT_SEVEN = numberFactory.rational(INT_SEVEN);
	private static RationalNumber RAT_EIGHT = numberFactory.rational(INT_EIGHT);
	private static RationalNumber RAT_NINE = numberFactory.rational(INT_NINE);
	private static RationalNumber RAT_TEN = numberFactory.rational(INT_TEN);
	private static RationalNumber RAT_N_ONE = numberFactory.rational(INT_N_ONE);
	private static RationalNumber RAT_N_TWO = numberFactory.rational(INT_N_TWO);
	private static RationalNumber RAT_N_THREE = numberFactory
			.rational(INT_N_THREE);
	private static RationalNumber RAT_N_FOUR = numberFactory
			.rational(INT_N_FOUR);
	private static RationalNumber RAT_N_FIVE = numberFactory
			.rational(INT_N_FIVE);
	private static RationalNumber RAT_N_SIX = numberFactory.rational(INT_N_SIX);
	private static RationalNumber RAT_N_SEVEN = numberFactory
			.rational(INT_N_SEVEN);
	private static RationalNumber RAT_N_EIGHT = numberFactory
			.rational(INT_N_EIGHT);
	private static RationalNumber RAT_N_NINE = numberFactory
			.rational(INT_N_NINE);
	private static RationalNumber RAT_N_TEN = numberFactory.rational(INT_N_TEN);
	private static NumericSymbolicConstant RAT_X;
	private static NumericSymbolicConstant INT_X;
	private Range actual;
	private Range actual1;
	private Range actual2;
	private Range expected;
	private Range expected1;
	private Range expected2;

	private void p(boolean isDebug, String s) {
		if (isDebug) {
			OUT.println(s);
		}
	}

	private void p(boolean isDebug, Interval... intervals) {
		if (isDebug) {
			if (intervals != null) {
				StringBuilder sb = new StringBuilder();

				sb.append("{");
				for (int i = 0; i < intervals.length; i++) {
					if (intervals[i] != null) {
						sb.append(intervals[i].toString());
					} else {
						sb.append("null");
					}
					if (i == intervals.length - 1) {
						sb.append("}\n");
					} else {
						sb.append(", ");
					}
				}
				OUT.print(sb.toString());
			}
		}
	}

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
		FactorySystem system = PreUniverses.newIdealFactorySystem();

		assert ASSERTION_ENABLED = true;
		universe = PreUniverses.newPreUniverse(system);
		RAT_X = (NumericSymbolicConstant) universe.symbolicConstant(
				universe.stringObject("X"), universe.realType());
		INT_X = (NumericSymbolicConstant) universe.symbolicConstant(
				universe.stringObject("X"), universe.integerType());
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {

	}

	/**
	 * @throws java.lang.Exception
	 */
	@Before
	public void setUp() throws Exception {
	}

	/**
	 * @throws java.lang.Exception
	 */
	@After
	public void tearDown() throws Exception {
		if (actual != null) {
			assert ((IntervalUnionSet) actual).checkInvariants();
		}
		if (actual1 != null) {
			assert ((IntervalUnionSet) actual1).checkInvariants();
		}
		if (actual2 != null) {
			assert ((IntervalUnionSet) actual2).checkInvariants();
		}
	}

	// Tests
	// Constructor Testings
	@Test
	public void constructIntervalUnionSet_Int_Empty() {
		actual = new IntervalUnionSet(true);

		assertTrue(actual.isEmpty());
		assertTrue(actual.isIntegral());
		p(DEBUG, actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_Rat_Empty() {
		actual = new IntervalUnionSet(false);

		assertTrue(actual.isEmpty());
		assertTrue(!actual.isIntegral());
		p(DEBUG, actual.toString());
	}

	@Test(expected = AssertionError.class)
	public void constructIntervalUnionSet_Number_Int_Null() {
		if (ASSERTION_ENABLED) {
			IntegerNumber nullNum = null;
			actual = new IntervalUnionSet(nullNum);
		} else {
			throw new AssertionError();
		}
	}

	@Test(expected = AssertionError.class)
	public void constructIntervalUnionSet_Number_Rat_Null() {
		if (ASSERTION_ENABLED) {
			RationalNumber nullNum = null;
			actual = new IntervalUnionSet(nullNum);
		} else {
			throw new AssertionError();
		}
	}

	@Test
	public void constructIntervalUnionSet_Number_Int_Zero() {
		actual = new IntervalUnionSet(INT_ZERO);

		assertTrue(!actual.isEmpty());
		assertTrue(actual.isIntegral());
		p(DEBUG, actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_Number_Rat_Zero() {
		actual = new IntervalUnionSet(RAT_ZERO);

		assertTrue(!actual.isEmpty());
		assertTrue(!actual.isIntegral());
		p(DEBUG, actual.toString());
	}

	@Test(expected = AssertionError.class)
	public void constructIntervalUnionSet_Interval_Null() {
		if (ASSERTION_ENABLED) {
			Interval nullInterval = null;
			actual = new IntervalUnionSet(nullInterval);
		} else {
			throw new AssertionError();
		}
	}

	@Test
	public void constructIntervalUnionSet_Interval_Rat_Empty() {
		expected = new IntervalUnionSet(false);
		Interval emptyInterval = RAT_EMPTY;
		actual = new IntervalUnionSet(emptyInterval);

		assertTrue(actual.isEmpty());
		assertTrue(!actual.isIntegral());
		assertEquals(expected.toString(), actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_Interval_Int_Single() {
		expected = new IntervalUnionSet(INT_TEN);
		Interval singleInterval = numberFactory.newInterval(true, INT_TEN,
				false, INT_TEN, false);
		actual = new IntervalUnionSet(singleInterval);

		assertTrue(!actual.isEmpty());
		assertTrue(actual.isIntegral());
		assertEquals(expected.toString(), actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_Interval_Rat_Single() {
		Interval singleInterval = numberFactory.newInterval(false, RAT_N_ONE,
				false, RAT_ONE, true);
		actual = new IntervalUnionSet(singleInterval);

		assertTrue(!actual.isEmpty());
		assertTrue(!actual.isIntegral());
		p(DEBUG, actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_Interval_CorrectForm1() {
		Interval singleInterval = numberFactory.newInterval(true, INT_ZERO,
				false, INT_POS_INF, true);
		actual = new IntervalUnionSet(singleInterval);

		assertTrue(!actual.isEmpty());
		assertTrue(actual.isIntegral());
		p(DEBUG, actual.toString());
	}

	@Test(expected = AssertionError.class)
	public void constructIntervalUnionSet_IntervalList_NullList() {
		if (ASSERTION_ENABLED) {
			Interval[] nullList = null;
			actual = new IntervalUnionSet(nullList);
		} else {
			throw new AssertionError();
		}
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_EmptyList() {
		Interval[] emptyList = new Interval[0];
		actual = new IntervalUnionSet(emptyList);
		assertTrue(actual.isEmpty());
	}

	@Test(expected = AssertionError.class)
	public void constructIntervalUnionSet_IntervalList_Int_mismatchedType() {
		if (ASSERTION_ENABLED) {
			Interval int_zeroInterval = numberFactory.newInterval(true,
					INT_ZERO, false, INT_ZERO, false);
			Interval rat_zeroInterval = numberFactory.newInterval(false,
					INT_ZERO, false, INT_ZERO, false);

			Interval[] intList = { int_zeroInterval, rat_zeroInterval };
			actual = new IntervalUnionSet(intList);
		} else {
			throw new AssertionError();
		}
	}

	@Test(expected = AssertionError.class)
	public void constructIntervalUnionSet_IntervalList_Rat_mismatchedType() {
		if (ASSERTION_ENABLED) {
			Interval int_zeroInterval = numberFactory.newInterval(true,
					INT_ZERO, false, INT_ZERO, false);
			Interval rat_zeroInterval = numberFactory.newInterval(false,
					INT_ZERO, false, INT_ZERO, false);

			Interval[] intList = { rat_zeroInterval, int_zeroInterval };
			actual = new IntervalUnionSet(intList);
		} else {
			throw new AssertionError();
		}
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_NullIntervals() {
		// All of intervals in the array are non-<code>null</code> intervals.
		expected = new IntervalUnionSet(false);
		Interval[] nullIntervalList = new Interval[ARR_SIZE];
		actual = new IntervalUnionSet(nullIntervalList);

		assertTrue(actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_EpmtyIntervals() {
		// All of intervals in the array are non-<code>null</code> intervals.
		expected = new IntervalUnionSet(true);
		Interval[] emptyIntervalList = new Interval[ARR_SIZE];
		for (int i = 0; i < ARR_SIZE; i++) {
			emptyIntervalList[i] = INT_EMPTY;
		}
		actual = new IntervalUnionSet(emptyIntervalList);

		assertTrue(actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_UnivIntervals() {
		// All of intervals in the array are non-<code>null</code> intervals.
		expected = new IntervalUnionSet(RAT_UNIV);
		Interval[] univIntervalList = new Interval[ARR_SIZE];
		for (int i = 0; i < ARR_SIZE; i++) {
			univIntervalList[i] = RAT_UNIV;
		}
		actual = new IntervalUnionSet(univIntervalList);

		// assertFalse(actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_SomeUnivIntervals() {
		// All of intervals in the array are non-<code>null</code> intervals.
		expected = new IntervalUnionSet(RAT_UNIV);
		Interval[] univIntervalList = new Interval[ARR_SIZE];
		for (int i = 0; i < ARR_SIZE; i++) {
			if (i % 5 == 3) {
				univIntervalList[i] = RAT_UNIV;
			} else {
				univIntervalList[i] = numberFactory.newInterval(false,
						RAT_N_ONE, true, RAT_ONE, true);
			}
		}
		actual = new IntervalUnionSet(univIntervalList);

		// assertFalse(actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Rat_SomeNull() {
		// All of intervals in the array are non-<code>null</code> intervals.
		Interval[] expectedList = new Interval[ARR_SIZE];
		Interval[] list = new Interval[ARR_SIZE];

		for (int i = 0; i * 3 < ARR_SIZE && i < 7; i += 2) {
			RationalNumber rat_i = numberFactory
					.rational(numberFactory.integer(i));
			RationalNumber rat_j = numberFactory
					.rational(numberFactory.integer(i + 1));

			expectedList[i] = numberFactory.newInterval(false, rat_i, true,
					rat_j, true);
			list[i * 3] = numberFactory.newInterval(false, rat_i, true, rat_j,
					true);
		}

		expected = new IntervalUnionSet(expectedList);
		actual = new IntervalUnionSet(list);

		assertTrue(!actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Int_SomeNull() {
		// All of intervals in the array are non-<code>null</code> intervals.
		Interval[] expectedList = new Interval[ARR_SIZE];
		Interval[] list = new Interval[ARR_SIZE];

		for (int i = 0; i * 3 < ARR_SIZE && i < 7; i += 2) {
			IntegerNumber int_i = numberFactory.integer(i);
			IntegerNumber int_j = numberFactory.integer(i + 1);

			expectedList[i] = numberFactory.newInterval(true, int_i, false,
					int_j, false);
			list[i * 3] = numberFactory.newInterval(true, int_i, false, int_j,
					false);
		}

		expected = new IntervalUnionSet(expectedList);
		actual = new IntervalUnionSet(list);

		assertTrue(!actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Int_SomeEmpty() {
		// An empty interval cannot occur in the array.
		Interval[] expectedList = new Interval[ARR_SIZE];
		Interval[] list = new Interval[ARR_SIZE];

		for (int i = 0; i < ARR_SIZE; i++) {
			if (i % 5 == 0) {
				IntegerNumber int_i = numberFactory.integer(i);
				IntegerNumber int_j = numberFactory.integer(i + 2);

				expectedList[i / 5] = numberFactory.newInterval(true, int_i,
						false, int_j, false);
				list[i] = numberFactory.newInterval(true, int_i, false, int_j,
						false);
			} else {
				list[i] = INT_EMPTY;
			}
		}

		expected = new IntervalUnionSet(expectedList);
		actual = new IntervalUnionSet(list);

		assertTrue(!actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Int_SomeOverlapped() {
		// All of the intervals in the array are disjoint.
		Interval[] list = new Interval[ARR_SIZE];

		list[0] = numberFactory.newInterval(true, INT_NEG_INF, true, INT_ZERO,
				false);
		list[Math.min(ARR_SIZE, 4)] = numberFactory.newInterval(true, INT_NINE,
				false, INT_POS_INF, true);
		for (int i = 1; i < ARR_SIZE && i < 4; i++) {
			IntegerNumber int_i = numberFactory.integer(i);
			IntegerNumber int_j = numberFactory.integer(i + 5);
			list[i] = numberFactory.newInterval(true, int_i, false, int_j,
					false);
		}

		expected = new IntervalUnionSet(INT_UNIV);
		actual = new IntervalUnionSet(list);

		assertTrue(!actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Rat_descOrdered() {
		// The intervals in the array are ordered from least to greatest.
		Interval[] expectedList = new Interval[ARR_SIZE];
		Interval[] list = new Interval[ARR_SIZE];

		for (int i = 0; i < ARR_SIZE; i++) {
			RationalNumber rat_i = numberFactory
					.rational(numberFactory.integer(i));
			RationalNumber rat_j = numberFactory
					.rational(numberFactory.integer(i + 1));

			expectedList[i] = numberFactory.newInterval(false, rat_i, true,
					rat_j, true);
			list[ARR_SIZE - 1 - i] = numberFactory.newInterval(false, rat_i,
					true, rat_j, true);
		}

		expected = new IntervalUnionSet(expectedList);
		actual = new IntervalUnionSet(list);

		assertTrue(!actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Rat_descOrdered2() {
		// The intervals in the array are ordered from least to greatest.
		Interval[] expectedList = new Interval[ARR_SIZE];
		Interval[] list = new Interval[ARR_SIZE];

		for (int i = 0; i < ARR_SIZE; i++) {
			RationalNumber rat_i = numberFactory
					.rational(numberFactory.integer(i));
			RationalNumber rat_j = numberFactory
					.rational(numberFactory.integer(i + 1));

			expectedList[i] = numberFactory.newInterval(false, rat_i, false,
					rat_j, false);
			list[ARR_SIZE - 1 - i] = numberFactory.newInterval(false, rat_i,
					false, rat_j, false);
		}

		expected = new IntervalUnionSet(expectedList);
		actual = new IntervalUnionSet(list);

		assertTrue(!actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Rat_descOrdered3() {
		// The intervals in the array are ordered from least to greatest.
		Interval[] expectedList = new Interval[ARR_SIZE];
		Interval[] list = new Interval[ARR_SIZE];

		for (int i = 0; i < ARR_SIZE; i++) {
			RationalNumber rat_i = numberFactory
					.rational(numberFactory.integer(i));
			RationalNumber rat_j = numberFactory
					.rational(numberFactory.integer(i + 1));

			expectedList[i] = numberFactory.newInterval(false, rat_i, true,
					rat_j, false);
			list[ARR_SIZE - 1 - i] = numberFactory.newInterval(false, rat_i,
					true, rat_j, false);
		}

		expected = new IntervalUnionSet(expectedList);
		actual = new IntervalUnionSet(list);

		assertTrue(!actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Rat_descOrdered4() {
		// The intervals in the array are ordered from least to greatest.
		Interval[] expectedList = new Interval[ARR_SIZE];
		Interval[] list = new Interval[ARR_SIZE];

		for (int i = 0; i < ARR_SIZE; i++) {
			IntegerNumber int_i = numberFactory.integer(i);
			IntegerNumber int_j = numberFactory.integer(i);

			expectedList[i] = numberFactory.newInterval(true, int_i, false,
					int_j, false);
			list[ARR_SIZE - 1 - i] = numberFactory.newInterval(true, int_i,
					false, int_j, false);
		}

		expected = new IntervalUnionSet(expectedList);
		actual = new IntervalUnionSet(list);

		assertTrue(!actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Rat_Adjacent() {
		/*
		 * If {a,b} and {b,c} are two consecutive intervals in the list, the the
		 * first one must be open on the right and the second one must be open
		 * on the left.
		 */
		Interval[] expectedList = new Interval[ARR_SIZE];
		Interval[] list = new Interval[ARR_SIZE];

		expectedList[0] = numberFactory.newInterval(false, RAT_ZERO, false,
				RAT_TEN, true);
		for (int i = 0; i < ARR_SIZE && i < 10; i++) {
			RationalNumber rat_i = numberFactory
					.rational(numberFactory.integer(i));
			RationalNumber rat_j = numberFactory
					.rational(numberFactory.integer(i + 1));

			list[i] = numberFactory.newInterval(false, rat_i, false, rat_j,
					true);
		}

		expected = new IntervalUnionSet(expectedList);
		actual = new IntervalUnionSet(list);

		assertTrue(!actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test(expected = AssertionError.class)
	public void constructIntervalUnionSet_IntervalList_AssortedType() {
		if (ASSERTION_ENABLED) {
			/*
			 * If the range set has integer type, all of the intervals are
			 * integer intervals. If it has real type, all of the intervals are
			 * real intervals.
			 */
			Interval[] expectedList = new Interval[ARR_SIZE];
			Interval[] list = new Interval[ARR_SIZE];

			for (int i = 0; i < ARR_SIZE; i++) {
				if (i % 2 == 0) {
					IntegerNumber int_i = numberFactory.integer(i);
					IntegerNumber int_j = numberFactory.integer(i + 1);

					expectedList[i / 2] = numberFactory.newInterval(true, int_i,
							false, int_j, false);
					list[i] = numberFactory.newInterval(true, int_i, false,
							int_j, false);
				} else {
					RationalNumber rat_ni = numberFactory
							.rational(numberFactory.integer(-i));
					RationalNumber rat_nj = numberFactory
							.rational(numberFactory.integer(-i + 1));

					list[i] = numberFactory.newInterval(false, rat_ni, true,
							rat_nj, true);
				}
			}

			expected = new IntervalUnionSet(expectedList);
			actual = new IntervalUnionSet(list);
		} else {
			throw new AssertionError();
		}
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_HoldInvariants() {
		Interval[] expectedList = new Interval[ARR_SIZE];
		Interval[] list = new Interval[ARR_SIZE];
		IntegerNumber int_max = numberFactory.integer(ARR_SIZE - 1);

		expectedList[0] = INT_UNIV;
		list[0] = numberFactory.newInterval(true, INT_NEG_INF, true, INT_ZERO,
				false);
		list[ARR_SIZE - 1] = numberFactory.newInterval(true, int_max, false,
				INT_POS_INF, true);
		for (int i = 1; i < ARR_SIZE - 1; i++) {
			IntegerNumber int_i = numberFactory.integer(i);

			list[i] = numberFactory.newInterval(true, int_i, false, int_i,
					false);
		}

		expected = new IntervalUnionSet(expectedList);
		actual = new IntervalUnionSet(list);

		assertTrue(!actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Complicated1() {
		Interval[] expectedList = new Interval[ARR_SIZE];
		Interval[] list = new Interval[ARR_SIZE];
		IntegerNumber int_a = numberFactory.integer(ARR_SIZE);
		IntegerNumber int_b = numberFactory.integer(ARR_SIZE + 2);
		IntegerNumber int_c = numberFactory.integer(ARR_SIZE + 6);

		expectedList[0] = numberFactory.newInterval(true, INT_ZERO, false,
				int_a, false);
		expectedList[1] = numberFactory.newInterval(true, int_b, false, int_c,
				false);
		list[0] = numberFactory.newInterval(true, INT_ZERO, false, int_a,
				false);
		list[ARR_SIZE - 1] = numberFactory.newInterval(true, int_b, false,
				int_c, false);
		for (int i = 1; i < ARR_SIZE - 1; i++) {
			IntegerNumber int_i = numberFactory.integer(i);

			list[i] = numberFactory.newInterval(true, int_i, false, int_i,
					false);
		}

		expected = new IntervalUnionSet(expectedList);
		actual = new IntervalUnionSet(list);

		assertTrue(!actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Complicated2() {
		Interval[] expectedList = new Interval[ARR_SIZE];
		Interval[] list = new Interval[ARR_SIZE];
		IntegerNumber int_x = numberFactory.integer(ARR_SIZE + 2);
		IntegerNumber int_y = numberFactory.integer(ARR_SIZE + 4);
		IntegerNumber int_z = numberFactory.integer(ARR_SIZE + 6);

		expectedList[0] = numberFactory.newInterval(true, INT_ZERO, false,
				int_y, false);
		expectedList[1] = numberFactory.newInterval(true, int_x, false, int_z,
				false);
		list[0] = numberFactory.newInterval(true, INT_ZERO, false, int_y,
				false);
		list[ARR_SIZE - 1] = numberFactory.newInterval(true, int_x, false,
				int_z, false);
		for (int i = 1; i < ARR_SIZE - 1; i++) {
			IntegerNumber int_i = numberFactory.integer(i);

			list[i] = numberFactory.newInterval(true, int_i, false, int_i,
					false);
		}

		expected = new IntervalUnionSet(expectedList);
		actual = new IntervalUnionSet(list);

		assertTrue(!actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Complicated3() {
		Interval[] expectedList = new Interval[ARR_SIZE];
		Interval[] list = new Interval[ARR_SIZE];
		IntegerNumber int_x = numberFactory.integer(ARR_SIZE + 5);
		IntegerNumber int_y = numberFactory.integer(ARR_SIZE + 11);
		IntegerNumber int_z = numberFactory.integer(ARR_SIZE + 20);
		IntegerNumber int_a = numberFactory.integer(ARR_SIZE + 22);
		IntegerNumber int_b = numberFactory.integer(ARR_SIZE + 24);
		IntegerNumber int_c = numberFactory.integer(ARR_SIZE + 25);

		expectedList[0] = numberFactory.newInterval(true, INT_THREE, false,
				INT_FOUR, false);
		expectedList[1] = numberFactory.newInterval(true, INT_SIX, false, int_a,
				false);
		expectedList[2] = numberFactory.newInterval(true, int_b, false, int_c,
				false);

		list[0] = numberFactory.newInterval(true, INT_EIGHT, false, int_y,
				false);
		list[ARR_SIZE - 1] = numberFactory.newInterval(true, int_x, false,
				int_z, false);
		for (int i = 3; i / 3 < ARR_SIZE - 1; i += 3) {
			IntegerNumber int_i = numberFactory.integer(i);
			IntegerNumber int_j = numberFactory.integer(i + 1);

			list[i / 3] = numberFactory.newInterval(true, int_i, false, int_j,
					false);
		}

		expected = new IntervalUnionSet(expectedList);
		actual = new IntervalUnionSet(list);

		assertTrue(!actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Complicated4() {
		Interval[] expectedList = new Interval[ARR_SIZE];
		Interval[] list = new Interval[ARR_SIZE];
		RationalNumber rat_x = numberFactory
				.rational(numberFactory.integer(ARR_SIZE + 24));
		RationalNumber rat_a = numberFactory
				.rational(numberFactory.integer(ARR_SIZE + 25));

		expectedList[0] = numberFactory.newInterval(false, RAT_ZERO, false,
				rat_a, false);

		list[ARR_SIZE - 1] = numberFactory.newInterval(false, RAT_ONE, true,
				rat_x, true);
		for (int i = 0; i / 3 < ARR_SIZE - 1; i += 3) {
			RationalNumber rat_i = numberFactory
					.rational(numberFactory.integer(i));
			RationalNumber rat_j = numberFactory
					.rational(numberFactory.integer(i + 1));

			list[i / 3] = numberFactory.newInterval(false, rat_i, false, rat_j,
					false);
		}

		expected = new IntervalUnionSet(expectedList);
		actual = new IntervalUnionSet(list);

		assertTrue(!actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Complicated5() {
		Interval[] list = new Interval[ARR_SIZE];
		RationalNumber rat_x = numberFactory
				.rational(numberFactory.integer(ARR_SIZE - 1));

		list[0] = numberFactory.newInterval(false, RAT_NEG_INF, true, RAT_ONE,
				false);

		list[ARR_SIZE - 1] = numberFactory.newInterval(false, rat_x, false,
				RAT_POS_INF, true);
		for (int i = 1; i < ARR_SIZE - 1; i++) {
			RationalNumber rat_i = numberFactory
					.rational(numberFactory.integer(i));
			RationalNumber rat_j = numberFactory
					.rational(numberFactory.integer(i + 1));

			list[i] = numberFactory.newInterval(false, rat_i, true, rat_j,
					false);
		}

		expected = new IntervalUnionSet(RAT_UNIV);
		actual = new IntervalUnionSet(list);

		assertTrue(!actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Complicated6() {
		Interval[] list = new Interval[ARR_SIZE];
		RationalNumber rat_x = numberFactory
				.rational(numberFactory.integer(ARR_SIZE - 1));

		list[ARR_SIZE - 1] = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_ONE, false);
		list[0] = numberFactory.newInterval(false, rat_x, false, RAT_POS_INF,
				true);
		for (int i = 1; i < ARR_SIZE - 1; i++) {
			RationalNumber rat_i = numberFactory
					.rational(numberFactory.integer(i));
			RationalNumber rat_j = numberFactory
					.rational(numberFactory.integer(i + 1));

			list[i] = numberFactory.newInterval(false, rat_i, true, rat_j,
					false);
		}

		expected = new IntervalUnionSet(RAT_UNIV);
		actual = new IntervalUnionSet(list);

		assertTrue(!actual.isEmpty());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_SameBoundary1() {
		Interval first = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, true);
		Interval second = numberFactory.newInterval(false, RAT_N_ONE, false,
				RAT_ONE, true);
		Interval third = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, false);
		Interval fourth = numberFactory.newInterval(false, RAT_N_ONE, false,
				RAT_ONE, false);
		expected = new IntervalUnionSet(fourth);
		actual1 = new IntervalUnionSet(first, first, second, second, third);
		actual2 = new IntervalUnionSet(first, third, third, second, fourth);

		assertTrue(!actual1.isEmpty());
		assertTrue(!actual2.isEmpty());
		assertEquals(expected.toString(), actual1.toString());
		assertEquals(expected.toString(), actual2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, " actual1: " + actual1.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_SameBoundary2() {
		Interval before = numberFactory.newInterval(false, RAT_N_NINE, true,
				RAT_N_FOUR, true);
		Interval after = numberFactory.newInterval(false, RAT_FOUR, true,
				RAT_NINE, true);
		Interval first = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, true);
		Interval second = numberFactory.newInterval(false, RAT_N_ONE, false,
				RAT_ONE, true);
		Interval third = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, false);
		Interval fourth = numberFactory.newInterval(false, RAT_N_ONE, false,
				RAT_ONE, false);
		expected = new IntervalUnionSet(before, after, fourth);
		actual1 = new IntervalUnionSet(before, after, first, first, second,
				second, third);
		actual2 = new IntervalUnionSet(before, after, first, third, third,
				second, fourth);

		assertTrue(!actual1.isEmpty());
		assertTrue(!actual2.isEmpty());
		assertEquals(expected.toString(), actual1.toString());
		assertEquals(expected.toString(), actual2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, " actual1: " + actual1.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Coverage1() {
		Interval first = numberFactory.newInterval(false, RAT_N_EIGHT, true,
				RAT_N_SEVEN, true);
		Interval second = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_THREE, true);
		Interval third = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, true);
		Interval fourth = numberFactory.newInterval(false, RAT_THREE, true,
				RAT_FOUR, true);
		Interval fourth2 = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FIVE, true);
		Interval fifth = numberFactory.newInterval(false, RAT_SEVEN, true,
				RAT_EIGHT, true);
		Interval target1 = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_THREE, false);
		Interval target2 = numberFactory.newInterval(false, RAT_FOUR, false,
				RAT_FIVE, true);
		Interval target3 = numberFactory.newInterval(false, RAT_ONE, true,
				RAT_TWO, true);
		Interval[] list = { first, second, third, fourth, fifth, target1,
				target2, target3 };
		expected = new IntervalUnionSet(first, second, third, fourth2, target3,
				fifth);
		actual1 = new IntervalUnionSet(list);

		assertTrue(!actual1.isEmpty());
		assertEquals(expected.toString(), actual1.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, " actual1: " + actual1.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalList_Coverage2() {
		Interval first = numberFactory.newInterval(false, RAT_N_EIGHT, true,
				RAT_N_SEVEN, true);
		Interval second = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_THREE, true);
		Interval third = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, true);
		Interval third2 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_TWO, true);
		Interval fourth = numberFactory.newInterval(false, RAT_THREE, true,
				RAT_FOUR, true);
		Interval fifth = numberFactory.newInterval(false, RAT_SEVEN, true,
				RAT_EIGHT, true);
		Interval target1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_N_ONE, false);
		Interval target2 = numberFactory.newInterval(false, RAT_ONE, false,
				RAT_TWO, true);
		Interval target3 = numberFactory.newInterval(false, RAT_N_THREE, true,
				RAT_N_TWO, true);
		Interval[] list = { first, second, third, fourth, fifth, target1,
				target2, target3 };
		expected = new IntervalUnionSet(first, second, target3, third2, fourth,
				fifth);
		actual1 = new IntervalUnionSet(list);

		assertTrue(!actual1.isEmpty());
		assertEquals(expected.toString(), actual1.toString());
		p(DEBUG, "The list is :");
		p(DEBUG, list);
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, " actual1: " + actual1.toString());
	}

	@Test(expected = AssertionError.class)
	public void constructIntervalUnionSet_IntervalUnionSet_Null() {
		if (ASSERTION_ENABLED) {
			IntervalUnionSet nullIntervalUnionSet = null;
			actual = new IntervalUnionSet(nullIntervalUnionSet);
		} else {
			throw new AssertionError();
		}
	}

	@Test
	public void constructIntervalUnionSet_IntervalUnionSet_Empty() {
		expected = new IntervalUnionSet(false);
		actual = new IntervalUnionSet((IntervalUnionSet) expected);

		assertTrue(actual.isEmpty());
		assertTrue(!actual.isIntegral());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_IntervalUnionSet_Int_Simple() {
		Interval intInterval = numberFactory.newInterval(true, INT_N_TEN, false,
				INT_TEN, false);
		expected = new IntervalUnionSet(intInterval);
		actual = new IntervalUnionSet((IntervalUnionSet) expected);

		assertTrue(!actual.isEmpty());
		assertTrue(actual.isIntegral());
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void constructIntervalUnionSet_Rat_ComplicatedIntervalUnionSet() {
		Interval[] expectedList = new Interval[ARR_SIZE];

		for (int i = 1; i < ARR_SIZE - 1; i += 3) {
			IntegerNumber int_i = numberFactory.integer(i);
			IntegerNumber int_j = numberFactory.integer(i + 1);
			expectedList[i] = numberFactory.newInterval(true, int_i, false,
					int_j, false);
		}
		expected = new IntervalUnionSet(expectedList);
		actual = new IntervalUnionSet((IntervalUnionSet) expected);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test(expected = AssertionError.class)
	public void union_IntervalUnionSet_Null() {
		if (ASSERTION_ENABLED) {
			IntervalUnionSet nullIntervalUnionSet = null;
			IntervalUnionSet original = new IntervalUnionSet(true);
			actual = rangeFactory.union(original, nullIntervalUnionSet);
		} else {
			throw new AssertionError();
		}
	}

	@Test(expected = AssertionError.class)
	public void union_IntervalUnionSet_Mismatched() {
		if (ASSERTION_ENABLED) {
			IntervalUnionSet rational = new IntervalUnionSet(false);
			IntervalUnionSet integral = new IntervalUnionSet(true);
			actual = rangeFactory.union(integral, rational);
		} else {
			throw new AssertionError();
		}
	}

	@Test
	public void union_IntervalUnionSet_Empty() {
		IntervalUnionSet emptyRatSet = new IntervalUnionSet(false);
		IntervalUnionSet nonemptyRatSet = new IntervalUnionSet(numberFactory
				.newInterval(false, RAT_N_ONE, true, RAT_ONE, true));
		expected = nonemptyRatSet;
		actual1 = rangeFactory.union(nonemptyRatSet, emptyRatSet);
		actual2 = rangeFactory.union(emptyRatSet, nonemptyRatSet);

		assertEquals(expected.toString(), actual1.toString());
		assertEquals(expected.toString(), actual2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, " actual1: " + actual1.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void union_IntervalUnionSet_Univ() {
		IntervalUnionSet univIntSet = new IntervalUnionSet(INT_UNIV);
		IntervalUnionSet nonunivIntSet = new IntervalUnionSet(numberFactory
				.newInterval(true, INT_N_ONE, false, INT_ONE, false));
		expected = univIntSet;
		actual1 = rangeFactory.union(nonunivIntSet, univIntSet);
		actual2 = rangeFactory.union(univIntSet, nonunivIntSet);

		assertEquals(expected.toString(), actual1.toString());
		assertEquals(expected.toString(), actual2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, " actual1: " + actual1.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void union_IntervalUnionSet_Self() {
		IntervalUnionSet original = new IntervalUnionSet(numberFactory
				.newInterval(false, RAT_N_ONE, true, RAT_ONE, true));
		expected = original;
		actual = rangeFactory.union(original, original);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void union_IntervalUnionSet_Simple_Disjoint_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_N_TEN, true,
				RAT_N_EIGHT, true);
		Interval first2 = numberFactory.newInterval(false, RAT_N_EIGHT, true,
				RAT_N_SIX, true);
		Interval second1 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_FOUR, true);
		Interval second2 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_TWO, true);
		Interval third1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_ZERO, true);
		Interval third2 = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_TWO, true);
		Interval fourth1 = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FOUR, true);
		Interval fourth2 = numberFactory.newInterval(false, RAT_FOUR, true,
				RAT_SIX, true);
		Interval fifth1 = numberFactory.newInterval(false, RAT_SIX, true,
				RAT_EIGHT, true);
		Interval fifth2 = numberFactory.newInterval(false, RAT_EIGHT, true,
				RAT_TEN, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		Interval[] expectedList = { first1, second1, third1, fourth1, fifth1,
				first2, second2, third2, fourth2, fifth2 };

		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = new IntervalUnionSet(expectedList);
		actual = rangeFactory.union(set1, set2);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void union_IntervalUnionSet_Simple_Adjacent_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_EIGHT, false);
		Interval first2 = numberFactory.newInterval(false, RAT_N_EIGHT, true,
				RAT_N_SIX, false);
		Interval second1 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_FOUR, false);
		Interval second2 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_TWO, false);
		Interval third1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_ZERO, false);
		Interval third2 = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_TWO, false);
		Interval fourth1 = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FOUR, false);
		Interval fourth2 = numberFactory.newInterval(false, RAT_FOUR, true,
				RAT_SIX, false);
		Interval fifth1 = numberFactory.newInterval(false, RAT_SIX, true,
				RAT_EIGHT, false);
		Interval fifth2 = numberFactory.newInterval(false, RAT_EIGHT, true,
				RAT_POS_INF, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };

		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = new IntervalUnionSet(RAT_UNIV);
		actual = rangeFactory.union(set1, set2);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void union_IntervalUnionSet_Simple_Adjacent_Int() {
		Interval first1 = numberFactory.newInterval(true, INT_NEG_INF, true,
				INT_N_TEN, false);
		Interval first2 = numberFactory.newInterval(true, INT_N_NINE, false,
				INT_N_EIGHT, false);
		Interval second1 = numberFactory.newInterval(true, INT_N_SEVEN, false,
				INT_N_FIVE, false);
		Interval second2 = numberFactory.newInterval(true, INT_N_FOUR, false,
				INT_N_TWO, false);
		Interval third1 = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_ZERO, false);
		Interval third2 = numberFactory.newInterval(true, INT_ONE, false,
				INT_ONE, false);
		Interval fourth1 = numberFactory.newInterval(true, INT_TWO, false,
				INT_FOUR, false);
		Interval fourth2 = numberFactory.newInterval(true, INT_FIVE, false,
				INT_SEVEN, false);
		Interval fifth1 = numberFactory.newInterval(true, INT_EIGHT, false,
				INT_NINE, false);
		Interval fifth2 = numberFactory.newInterval(true, INT_TEN, false,
				INT_POS_INF, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };

		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = new IntervalUnionSet(INT_UNIV);
		actual = rangeFactory.union(set1, set2);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void union_IntervalUnionSet_Simple_Overlapped_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_N_NINE, false,
				RAT_N_SEVEN, true);
		Interval first2 = numberFactory.newInterval(false, RAT_N_EIGHT, true,
				RAT_N_FIVE, true);
		Interval second1 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_THREE, true);
		Interval second2 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_ONE, true);
		Interval third1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_ONE, true);
		Interval third2 = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_THREE, true);
		Interval fourth1 = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FIVE, true);
		Interval fourth2 = numberFactory.newInterval(false, RAT_FOUR, true,
				RAT_SEVEN, true);
		Interval fifth1 = numberFactory.newInterval(false, RAT_SIX, true,
				RAT_NINE, true);
		Interval fifth2 = numberFactory.newInterval(false, RAT_EIGHT, true,
				RAT_NINE, false);
		Interval result = numberFactory.newInterval(false, RAT_N_NINE, false,
				RAT_NINE, false);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };

		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = new IntervalUnionSet(result);
		actual = rangeFactory.union(set1, set2);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void union_IntervalUnionSet_Simple_Complicated1_Int() {
		Interval first1 = numberFactory.newInterval(true, INT_N_NINE, false,
				INT_N_ONE, false);
		Interval first2 = numberFactory.newInterval(true, INT_N_TEN, false,
				INT_N_TEN, false);
		Interval second1 = numberFactory.newInterval(true, INT_THREE, false,
				INT_THREE, false);
		Interval second2 = numberFactory.newInterval(true, INT_N_EIGHT, false,
				INT_N_EIGHT, false);
		Interval third1 = numberFactory.newInterval(true, INT_FIVE, false,
				INT_FIVE, false);
		Interval third2 = numberFactory.newInterval(true, INT_N_SIX, false,
				INT_N_SIX, false);
		Interval fourth1 = numberFactory.newInterval(true, INT_SEVEN, false,
				INT_SEVEN, false);
		Interval fourth2 = numberFactory.newInterval(true, INT_N_FOUR, false,
				INT_N_TWO, false);
		Interval fifth1 = numberFactory.newInterval(true, INT_TEN, false,
				INT_TEN, false);
		Interval fifth2 = numberFactory.newInterval(true, INT_ZERO, false,
				INT_NINE, false);
		Interval result = numberFactory.newInterval(true, INT_N_TEN, false,
				INT_TEN, false);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };

		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = new IntervalUnionSet(result);
		actual = rangeFactory.union(set1, set2);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void union_IntervalUnionSet_Simple_Complicated2_Int() {
		Interval first1 = numberFactory.newInterval(true, INT_ZERO, false,
				INT_TWO, false);
		Interval first2 = numberFactory.newInterval(true, INT_N_TWO, false,
				INT_N_ONE, false);
		Interval second1 = numberFactory.newInterval(true, INT_FOUR, false,
				INT_FOUR, false);
		Interval second2 = numberFactory.newInterval(true, INT_ONE, false,
				INT_ONE, false);
		Interval third1 = numberFactory.newInterval(true, INT_SIX, false,
				INT_SIX, false);
		Interval third2 = numberFactory.newInterval(true, INT_THREE, false,
				INT_THREE, false);
		Interval fourth1 = numberFactory.newInterval(true, INT_EIGHT, false,
				INT_EIGHT, false);
		Interval fourth2 = numberFactory.newInterval(true, INT_FIVE, false,
				INT_FIVE, false);
		Interval fifth1 = numberFactory.newInterval(true, INT_TEN, false,
				INT_TEN, false);
		Interval result = numberFactory.newInterval(true, INT_N_TWO, false,
				INT_SIX, false);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2 };

		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = new IntervalUnionSet(result, fourth1, fifth1);
		actual = rangeFactory.union(set1, set2);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void union_IntervalUnionSet_Simple_Complicated3_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_SEVEN, true);
		Interval first2 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_FIVE, true);
		Interval second1 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_THREE, true);
		Interval second2 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_ONE, true);
		Interval third1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_POS_INF, true);
		Interval third2 = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_POS_INF, true);
		Interval[] list1 = { first1, second1, third1 };
		Interval[] list2 = { first2, second2, third2 };

		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = new IntervalUnionSet(RAT_UNIV);
		actual = rangeFactory.union(set1, set2);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void union_IntervalUnionSet_Simple_Complicated4_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_N_TEN, true,
				RAT_N_SEVEN, true);
		Interval first2 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_FIVE, true);
		Interval second1 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_THREE, true);
		Interval second2 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_ONE, true);
		Interval third1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_POS_INF, true);
		Interval third2 = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_TEN, true);
		Interval[] list1 = { first1, second1, third1 };
		Interval[] list2 = { first2, second2, third2 };

		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = new IntervalUnionSet(RAT_UNIV);
		actual = rangeFactory.union(set1, set2);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void union_IntervalUnionSet_Infinity_Int1() {
		Interval first1 = numberFactory.newInterval(true, INT_NEG_INF, true,
				INT_ZERO, false);
		Interval first2 = numberFactory.newInterval(true, INT_NEG_INF, true,
				INT_ONE, false);
		Interval[] list1 = { first1 };
		Interval[] list2 = { first2 };

		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = set2;
		actual = rangeFactory.union(set1, set2);

		assertEquals(expected.toString(), actual.toString());

	}

	@Test
	public void union_IntervalUnionSet_Infinity_Int2() {
		Interval first1 = numberFactory.newInterval(true, INT_NEG_INF, true,
				INT_N_TEN, false);
		Interval first2 = numberFactory.newInterval(true, INT_NEG_INF, true,
				INT_N_SIX, false);
		Interval second1 = numberFactory.newInterval(true, INT_N_EIGHT, false,
				INT_SEVEN, false);
		Interval second2 = numberFactory.newInterval(true, INT_N_FOUR, false,
				INT_N_THREE, false);
		Interval third1 = numberFactory.newInterval(true, INT_N_FIVE, false,
				INT_ONE, false);
		Interval third2 = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_FIVE, false);
		Interval fourth1 = numberFactory.newInterval(true, INT_THREE, false,
				INT_FOUR, false);
		Interval fourth2 = numberFactory.newInterval(true, INT_SEVEN, false,
				INT_EIGHT, false);
		Interval fifth1 = numberFactory.newInterval(true, INT_SIX, false,
				INT_POS_INF, true);
		Interval fifth2 = numberFactory.newInterval(true, INT_TEN, false,
				INT_POS_INF, true);
		Interval result = numberFactory.newInterval(true, INT_NEG_INF, true,
				INT_POS_INF, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };

		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = new IntervalUnionSet(result);
		actual = rangeFactory.union(set1, set2);

		assertEquals(expected.toString(), actual.toString());

	}

	@Test
	public void union_IntervalUnionSet_Infinity_Rat1() {
		Interval first1 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_ONE, true);
		Interval first2 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_ONE, true);
		Interval[] list1 = { first1 };
		Interval[] list2 = { first2 };

		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = new IntervalUnionSet(numberFactory.newInterval(false,
				RAT_NEG_INF, true, RAT_ONE, true));
		actual = rangeFactory.union(set1, set2);

		assertEquals(expected.toString(), actual.toString());
	}

	@Test
	public void union_IntervalUnionSet_Infinity_Rat2() {
		Interval first1 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_ONE, true);
		Interval first2 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_ONE, false);
		Interval[] list1 = { first1 };
		Interval[] list2 = { first2 };

		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = set2;
		actual = rangeFactory.union(set1, set2);

		assertEquals(expected.toString(), actual.toString());
	}

	@Test(expected = AssertionError.class)
	public void containsNumber_Int_Null() {
		if (ASSERTION_ENABLED) {
			IntegerNumber nullIntNum = null;
			IntervalUnionSet univIntSet = new IntervalUnionSet(INT_UNIV);

			univIntSet.containsNumber(nullIntNum);
		} else {
			throw new AssertionError();
		}
	}

	@Test(expected = AssertionError.class)
	public void containsNumber_Rat_mismatchedType() {
		if (ASSERTION_ENABLED) {
			IntegerNumber intNum = INT_ZERO;
			IntervalUnionSet univRatSet = new IntervalUnionSet(RAT_UNIV);

			univRatSet.containsNumber(intNum);
		} else {
			throw new AssertionError();
		}
	}

	@Test(expected = AssertionError.class)
	public void containsNumber_Int_mismatchedType() {
		if (ASSERTION_ENABLED) {
			RationalNumber ratNum = RAT_ZERO;
			IntervalUnionSet univIntSet = new IntervalUnionSet(INT_UNIV);

			univIntSet.containsNumber(ratNum);
		} else {
			throw new AssertionError();
		}
	}

	@Test
	public void containsNumber_Int_withEmptySet() {
		IntervalUnionSet emptyIntSet = new IntervalUnionSet(INT_EMPTY);
		boolean actual = emptyIntSet.containsNumber(INT_ONE);

		assert emptyIntSet.isIntegral();
		assert emptyIntSet.isEmpty();
		assertFalse(actual);
		p(DEBUG, "   Set: " + emptyIntSet.toString());
		p(DEBUG, "Number: " + INT_ONE.toString());
		p(DEBUG, "expected: " + "false");
		p(DEBUG, "  actual: " + actual);
	}

	@Test
	public void containsNumber_Rat_withEmptySet() {
		IntervalUnionSet emptyRatSet = new IntervalUnionSet(RAT_EMPTY);
		boolean actual = emptyRatSet.containsNumber(RAT_ONE);

		assert !emptyRatSet.isIntegral();
		assert emptyRatSet.isEmpty();
		assertFalse(actual);
		p(DEBUG, "   Set: " + emptyRatSet.toString());
		p(DEBUG, "Number: " + RAT_ONE.toString());
		p(DEBUG, "expected: " + "false");
		p(DEBUG, "  actual: " + actual);
	}

	@Test
	public void containsNumber_Int_withUnivSet() {
		IntervalUnionSet univIntSet = new IntervalUnionSet(INT_UNIV);
		boolean actual = univIntSet.containsNumber(INT_ONE);

		assert univIntSet.isIntegral();
		assert !univIntSet.isEmpty();
		assertTrue(actual);
		p(DEBUG, "   Set: " + univIntSet.toString());
		p(DEBUG, "Number: " + INT_ONE.toString());
		p(DEBUG, "expected: " + "true");
		p(DEBUG, "  actual: " + actual);
	}

	@Test
	public void containsNumber_Rat_withUnivSet() {
		IntervalUnionSet univRatSet = new IntervalUnionSet(RAT_UNIV);
		boolean actual = univRatSet.containsNumber(RAT_ONE);

		assert !univRatSet.isIntegral();
		assert !univRatSet.isEmpty();
		assertTrue(actual);
		p(DEBUG, "   Set: " + univRatSet.toString());
		p(DEBUG, "Number: " + RAT_ONE.toString());
		p(DEBUG, "expected: " + "true");
		p(DEBUG, "  actual: " + actual);
	}

	@Test
	public void containsNumber_Int_Num_LeftDisjoint() {
		Interval first = numberFactory.newInterval(true, INT_N_FIVE, false,
				INT_N_TWO, false);
		Interval second = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		Interval third = numberFactory.newInterval(true, INT_TWO, false,
				INT_FIVE, false);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		boolean actual = intervalSet.containsNumber(INT_N_TEN);

		assertFalse(actual);
		p(DEBUG, "   Set: " + intervalSet.toString());
		p(DEBUG, "Number: " + INT_N_TEN.toString());
		p(DEBUG, "expected: " + "false");
		p(DEBUG, "  actual: " + actual);
	}

	@Test
	public void containsNumber_Rat_Num_RightDisjoint() {
		Interval first = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_TWO, true);
		Interval second = numberFactory.newInterval(false, RAT_ZERO, false,
				RAT_ZERO, false);
		Interval third = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FIVE, true);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		boolean actual = intervalSet.containsNumber(RAT_TEN);

		assertFalse(actual);
		p(DEBUG, "   Set: " + intervalSet.toString());
		p(DEBUG, "Number: " + RAT_TEN.toString());
		p(DEBUG, "expected: " + "false");
		p(DEBUG, "  actual: " + actual);
	}

	@Test
	public void containsNumber_Int_Num_NotContained1() {
		Interval first = numberFactory.newInterval(true, INT_N_FIVE, false,
				INT_N_TWO, false);
		Interval second = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		Interval third = numberFactory.newInterval(true, INT_TWO, false,
				INT_FIVE, false);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		boolean actual = intervalSet.containsNumber(INT_ONE);

		assertFalse(actual);
		p(DEBUG, "   Set: " + intervalSet.toString());
		p(DEBUG, "Number: " + INT_ONE.toString());
		p(DEBUG, "expected: " + "false");
		p(DEBUG, "  actual: " + actual);
	}

	@Test
	public void containsNumber_Rat_Num_NotContained1() {
		Interval first = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_TWO, true);
		Interval second = numberFactory.newInterval(false, RAT_ZERO, false,
				RAT_ZERO, false);
		Interval third = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FIVE, true);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		boolean actual = intervalSet.containsNumber(RAT_N_FIVE);

		assertFalse(actual);
		p(DEBUG, "   Set: " + intervalSet.toString());
		p(DEBUG, "Number: " + RAT_N_FIVE.toString());
		p(DEBUG, "expected: " + "false");
		p(DEBUG, "  actual: " + actual);
	}

	@Test
	public void containsNumber_Rat_Num_NotContained2() {
		Interval first = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_TWO, true);
		Interval second = numberFactory.newInterval(false, RAT_ZERO, false,
				RAT_ZERO, false);
		Interval third = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FIVE, true);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		boolean actual = intervalSet.containsNumber(RAT_FIVE);

		assertFalse(actual);
		p(DEBUG, "   Set: " + intervalSet.toString());
		p(DEBUG, "Number: " + RAT_FIVE.toString());
		p(DEBUG, "expected: " + "false");
		p(DEBUG, "  actual: " + actual);
	}

	@Test
	public void containsNumber_Rat_Num_NotContained3() {
		RationalNumber ratNum = numberFactory.divide(RAT_THREE, RAT_TWO);
		Interval first = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_TWO, true);
		Interval second = numberFactory.newInterval(false, RAT_ZERO, false,
				RAT_ZERO, false);
		Interval third = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FIVE, true);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		boolean actual = intervalSet.containsNumber(ratNum);

		assertFalse(actual);
		p(DEBUG, "   Set: " + intervalSet.toString());
		p(DEBUG, "Number: " + ratNum.toString());
		p(DEBUG, "expected: " + "false");
		p(DEBUG, "  actual: " + actual);
	}

	@Test
	public void containsNumber_Int_Num_Contained1() {
		Interval first = numberFactory.newInterval(true, INT_NEG_INF, true,
				INT_N_SEVEN, false);
		Interval second = numberFactory.newInterval(true, INT_N_FIVE, false,
				INT_N_TWO, false);
		Interval third = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		Interval fourth = numberFactory.newInterval(true, INT_TWO, false,
				INT_FIVE, false);
		Interval fifth = numberFactory.newInterval(true, INT_SEVEN, false,
				INT_POS_INF, true);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third, fourth, fifth);
		boolean actual = intervalSet.containsNumber(INT_N_TEN);

		assertTrue(actual);
		p(DEBUG, "   Set: " + intervalSet.toString());
		p(DEBUG, "Number: " + INT_N_TEN.toString());
		p(DEBUG, "expected: " + "true");
		p(DEBUG, "  actual: " + actual);
	}

	@Test
	public void containsNumber_Int_Num_Contained2() {
		Interval first = numberFactory.newInterval(true, INT_NEG_INF, true,
				INT_N_SEVEN, false);
		Interval second = numberFactory.newInterval(true, INT_N_FIVE, false,
				INT_N_TWO, false);
		Interval third = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		Interval fourth = numberFactory.newInterval(true, INT_TWO, false,
				INT_FIVE, false);
		Interval fifth = numberFactory.newInterval(true, INT_SEVEN, false,
				INT_POS_INF, true);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third, fourth, fifth);
		boolean actual = intervalSet.containsNumber(INT_ZERO);

		assertTrue(actual);
		p(DEBUG, "   Set: " + intervalSet.toString());
		p(DEBUG, "Number: " + INT_ZERO.toString());
		p(DEBUG, "expected: " + "true");
		p(DEBUG, "  actual: " + actual);
	}

	@Test
	public void containsNumber_Rat_Num_Contained1() {
		Interval first = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_SEVEN, false);
		Interval second = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_TWO, true);
		Interval third = numberFactory.newInterval(false, RAT_ZERO, false,
				RAT_ZERO, false);
		Interval fourth = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FIVE, true);
		Interval fifth = numberFactory.newInterval(false, RAT_SEVEN, true,
				RAT_POS_INF, true);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third, fourth, fifth);
		boolean actual = intervalSet.containsNumber(RAT_N_SEVEN);

		assertTrue(actual);
		p(DEBUG, "   Set: " + intervalSet.toString());
		p(DEBUG, "Number: " + RAT_N_SEVEN.toString());
		p(DEBUG, "expected: " + "true");
		p(DEBUG, "  actual: " + actual);
	}

	@Test
	public void containsNumber_Rat_Num_Contained2() {
		RationalNumber ratNum = numberFactory.divide(RAT_SEVEN, RAT_TWO);
		Interval first = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_SEVEN, false);
		Interval second = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_TWO, true);
		Interval third = numberFactory.newInterval(false, RAT_ZERO, false,
				RAT_ZERO, false);
		Interval fourth = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FIVE, true);
		Interval fifth = numberFactory.newInterval(false, RAT_SEVEN, true,
				RAT_POS_INF, true);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third, fourth, fifth);
		boolean actual = intervalSet.containsNumber(ratNum);

		assertTrue(actual);
		p(DEBUG, "   Set: " + intervalSet.toString());
		p(DEBUG, "Number: " + ratNum.toString());
		p(DEBUG, "expected: " + "true");
		p(DEBUG, "  actual: " + actual);
	}

	@Test(expected = AssertionError.class)
	public void addNumber_Rat_Null() {
		if (ASSERTION_ENABLED) {
			RationalNumber nullRatNum = null;
			IntervalUnionSet univRatSet = new IntervalUnionSet(RAT_UNIV);

			univRatSet.addNumber(nullRatNum);
		} else {
			throw new AssertionError();
		}
	}

	@Test(expected = AssertionError.class)
	public void addNumber_Rat_mismatchedType() {
		if (ASSERTION_ENABLED) {
			IntegerNumber intNum = INT_ZERO;
			IntervalUnionSet univRatSet = new IntervalUnionSet(RAT_UNIV);

			univRatSet.addNumber(intNum);
		} else {
			throw new AssertionError();
		}
	}

	@Test(expected = AssertionError.class)
	public void addNumber_Int_mismatchedType() {
		if (ASSERTION_ENABLED) {
			RationalNumber ratNum = RAT_ZERO;
			IntervalUnionSet univIntSet = new IntervalUnionSet(INT_UNIV);

			univIntSet.addNumber(ratNum);
		} else {
			throw new AssertionError();
		}
	}

	@Test
	public void addNumber_Int_withEmptySet() {
		IntervalUnionSet emptyIntSet = new IntervalUnionSet(INT_EMPTY);
		actual = emptyIntSet.addNumber(INT_ONE);
		expected = new IntervalUnionSet(INT_ONE);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "      Set: " + emptyIntSet.toString());
		p(DEBUG, "addNumber: " + INT_ONE.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void addNumber_Rat_withEmptySet() {
		IntervalUnionSet emptyRatSet = new IntervalUnionSet(RAT_EMPTY);
		actual = emptyRatSet.addNumber(RAT_ONE);
		expected = new IntervalUnionSet(RAT_ONE);

		assert !actual.isIntegral();
		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "      Set: " + emptyRatSet.toString());
		p(DEBUG, "addNumber: " + RAT_ONE.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void addNumber_Int_withUnivSet() {
		IntervalUnionSet univIntSet = new IntervalUnionSet(INT_UNIV);
		actual = univIntSet.addNumber(INT_ONE);
		expected = univIntSet;

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "      Set: " + univIntSet.toString());
		p(DEBUG, "addNumber: " + INT_ONE.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void addNumber_Rat_withUnivSet() {
		IntervalUnionSet univRatSet = new IntervalUnionSet(RAT_UNIV);
		actual = univRatSet.addNumber(RAT_ONE);
		expected = univRatSet;

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "      Set: " + univRatSet.toString());
		p(DEBUG, "addNumber: " + RAT_ONE.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void addNumber_Int_Num_LeftDisjoint() {
		Interval first = numberFactory.newInterval(true, INT_N_FIVE, false,
				INT_N_TWO, false);
		Interval second = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		Interval third = numberFactory.newInterval(true, INT_TWO, false,
				INT_FIVE, false);
		Interval target = numberFactory.newInterval(true, INT_N_TEN, false,
				INT_N_TEN, false);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		expected = new IntervalUnionSet(first, second, third, target);
		actual = intervalSet.addNumber(INT_N_TEN);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "      Set: " + intervalSet.toString());
		p(DEBUG, "addNumber: " + INT_N_TEN.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void addNumber_Int_Num_LeftJoint() {
		Interval first = numberFactory.newInterval(true, INT_N_FIVE, false,
				INT_N_TWO, false);
		Interval second = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		Interval third = numberFactory.newInterval(true, INT_TWO, false,
				INT_FIVE, false);
		Interval target = numberFactory.newInterval(true, INT_N_SIX, false,
				INT_N_SIX, false);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		expected = new IntervalUnionSet(first, second, third, target);
		actual = intervalSet.addNumber(INT_N_SIX);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "      Set: " + intervalSet.toString());
		p(DEBUG, "addNumber: " + INT_N_SIX.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void addNumber_Int_Num_LeftRightJoint() {
		Interval first = numberFactory.newInterval(true, INT_N_FIVE, false,
				INT_N_TWO, false);
		Interval second = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		Interval third = numberFactory.newInterval(true, INT_TWO, false,
				INT_FIVE, false);
		Interval target = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_N_ONE, false);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		expected = new IntervalUnionSet(first, second, third, target);
		actual = intervalSet.addNumber(INT_N_ONE);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "      Set: " + intervalSet.toString());
		p(DEBUG, "addNumber: " + INT_N_ONE.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void addNumber_Int_Num_RightJoint() {
		Interval first = numberFactory.newInterval(true, INT_N_FIVE, false,
				INT_N_TWO, false);
		Interval second = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		Interval third = numberFactory.newInterval(true, INT_TWO, false,
				INT_FIVE, false);
		Interval target = numberFactory.newInterval(true, INT_SIX, false,
				INT_SIX, false);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		expected = new IntervalUnionSet(first, second, third, target);
		actual = intervalSet.addNumber(INT_SIX);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "      Set: " + intervalSet.toString());
		p(DEBUG, "addNumber: " + INT_SIX.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void addNumber_Int_Num_DisJoint() {
		Interval first = numberFactory.newInterval(true, INT_N_FIVE, false,
				INT_N_FOUR, false);
		Interval second = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		Interval third = numberFactory.newInterval(true, INT_FOUR, false,
				INT_FIVE, false);
		Interval target = numberFactory.newInterval(true, INT_TWO, false,
				INT_TWO, false);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		expected = new IntervalUnionSet(first, second, third, target);
		actual = intervalSet.addNumber(INT_TWO);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "      Set: " + intervalSet.toString());
		p(DEBUG, "addNumber: " + INT_TWO.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void addNumber_Rat_Num_RightDisjoint() {
		Interval first = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_TWO, true);
		Interval second = numberFactory.newInterval(false, RAT_ZERO, false,
				RAT_ZERO, false);
		Interval third = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FIVE, true);
		Interval target = numberFactory.newInterval(false, RAT_TEN, false,
				RAT_TEN, false);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		expected = new IntervalUnionSet(first, second, third, target);
		actual = intervalSet.addNumber(RAT_TEN);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "      Set: " + intervalSet.toString());
		p(DEBUG, "addNumber: " + RAT_TEN.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void addNumber_Rat_Num_LeftJoint() {
		Interval first = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_TWO, true);
		Interval second = numberFactory.newInterval(false, RAT_ZERO, false,
				RAT_ZERO, false);
		Interval third = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FIVE, true);
		Interval target = numberFactory.newInterval(false, RAT_N_FIVE, false,
				RAT_N_FIVE, false);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		expected = new IntervalUnionSet(first, second, third, target);
		actual = intervalSet.addNumber(RAT_N_FIVE);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "      Set: " + intervalSet.toString());
		p(DEBUG, "addNumber: " + RAT_N_FIVE.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void addNumber_Rat_Num_LeftRightJoint() {
		Interval first = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_TWO, true);
		Interval second = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_TWO, true);
		Interval third = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FIVE, true);
		Interval target1 = numberFactory.newInterval(false, RAT_N_TWO, false,
				RAT_N_TWO, false);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		expected1 = new IntervalUnionSet(first, second, third, target1);
		expected2 = new IntervalUnionSet(numberFactory.newInterval(false,
				RAT_N_FIVE, true, RAT_FIVE, true));
		actual1 = intervalSet.addNumber(RAT_N_TWO);
		actual2 = ((IntervalUnionSet) actual1).addNumber(RAT_TWO);

		assertEquals(expected1.toString(), actual1.toString());
		p(DEBUG, "      Set: " + intervalSet.toString());
		p(DEBUG, "addNumber: " + RAT_N_TWO.toString());
		p(DEBUG, "expected: " + expected1.toString());
		p(DEBUG, "  actual: " + actual1.toString());
		assertEquals(expected2.toString(), actual2.toString());
		p(DEBUG, "      Set: " + actual1.toString());
		p(DEBUG, "addNumber: " + RAT_TWO.toString());
		p(DEBUG, "expected: " + expected2.toString());
		p(DEBUG, "  actual: " + actual2.toString());
	}

	@Test
	public void addNumber_Rat_Num_RightJoint() {
		Interval first = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_TWO, true);
		Interval second = numberFactory.newInterval(false, RAT_ZERO, false,
				RAT_ZERO, false);
		Interval third = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FIVE, true);
		Interval target = numberFactory.newInterval(false, RAT_FIVE, false,
				RAT_FIVE, false);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		expected = new IntervalUnionSet(first, second, third, target);
		actual = intervalSet.addNumber(RAT_FIVE);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "      Set: " + intervalSet.toString());
		p(DEBUG, "addNumber: " + RAT_FIVE.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void addNumber_Rat_Num_DisJoint() {
		Interval first = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_TWO, true);
		Interval second = numberFactory.newInterval(false, RAT_ZERO, false,
				RAT_ZERO, false);
		Interval third = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FIVE, true);
		Interval target = numberFactory.newInterval(false, RAT_ONE, false,
				RAT_ONE, false);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		expected = new IntervalUnionSet(first, second, third, target);
		actual = intervalSet.addNumber(RAT_ONE);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "      Set: " + intervalSet.toString());
		p(DEBUG, "addNumber: " + RAT_ONE.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test(expected = AssertionError.class)
	public void contains_IntervalUnionSet_Null() {
		if (ASSERTION_ENABLED) {
			IntervalUnionSet target = null;
			IntervalUnionSet intervalSet = new IntervalUnionSet(INT_UNIV);

			intervalSet.contains(target);
		} else {
			throw new AssertionError();
		}
	}

	@Test(expected = AssertionError.class)
	public void contains_IntervalUnionSet_Mismatch() {
		if (ASSERTION_ENABLED) {
			IntervalUnionSet target = new IntervalUnionSet(INT_EMPTY);
			IntervalUnionSet intervalSet = new IntervalUnionSet(RAT_UNIV);

			intervalSet.contains(target);
		} else {
			throw new AssertionError();
		}
	}

	@Test
	public void contains_IntervalUnionSet_EmptySet() {
		IntervalUnionSet emptySet = new IntervalUnionSet(INT_EMPTY);
		IntervalUnionSet nonemptySet = new IntervalUnionSet(INT_ONE);
		boolean actual1 = emptySet.contains(nonemptySet);
		boolean actual2 = nonemptySet.contains(emptySet);

		assertFalse(actual1);
		assertTrue(actual2);
	}

	@Test
	public void contains_IntervalUnionSet_UnivSet() {
		IntervalUnionSet univSet = new IntervalUnionSet(INT_UNIV);
		IntervalUnionSet nonunivSet = new IntervalUnionSet(INT_ONE);
		boolean actual1 = univSet.contains(nonunivSet);
		boolean actual2 = nonunivSet.contains(univSet);

		assertTrue(actual1);
		assertFalse(actual2);
	}

	@Test
	public void contains_IntervalUnionSet_Interval_Int_LeftDisjoint() {
		Interval current = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_ONE, false);
		Interval target = numberFactory.newInterval(true, INT_N_THREE, false,
				INT_N_TWO, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.contains(intervalSet);
		boolean actual1 = intervalSet.contains(targetSet);

		assertTrue(actual0);
		assertFalse(actual1);
	}

	@Test
	public void contains_IntervalUnionSet_Interval_Rat_LeftDisjoint() {
		Interval current = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, true);
		Interval target = numberFactory.newInterval(false, RAT_N_ONE, false,
				RAT_N_ONE, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.contains(intervalSet);
		boolean actual1 = intervalSet.contains(targetSet);

		assertTrue(actual0);
		assertFalse(actual1);
	}

	@Test
	public void contains_IntervalUnionSet_Interval_Int_LeftIntersect() {
		Interval current = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_ONE, false);
		Interval target = numberFactory.newInterval(true, INT_N_THREE, false,
				INT_N_ONE, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.contains(intervalSet);
		boolean actual1 = intervalSet.contains(targetSet);

		assertTrue(actual0);
		assertFalse(actual1);
	}

	@Test
	public void contains_IntervalUnionSet_Interval_Rat_LeftIntersect() {
		Interval current = numberFactory.newInterval(false, RAT_N_ONE, false,
				RAT_ONE, true);
		Interval target = numberFactory.newInterval(false, RAT_N_THREE, true,
				RAT_N_ONE, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.contains(intervalSet);
		boolean actual1 = intervalSet.contains(targetSet);

		assertTrue(actual0);
		assertFalse(actual1);
	}

	@Test
	public void contains_IntervalUnionSet_Interval_Int_Target_contains_Current() {
		Interval current = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_ONE, false);
		Interval target = numberFactory.newInterval(true, INT_N_THREE, false,
				INT_THREE, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.contains(intervalSet);
		boolean actual1 = intervalSet.contains(targetSet);

		assertTrue(actual0);
		assertFalse(actual1);
	}

	@Test
	public void contains_IntervalUnionSet_Interval_Rat_Target_contains_Current() {
		Interval current = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, true);
		Interval target = numberFactory.newInterval(false, RAT_N_ONE, false,
				RAT_ONE, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.contains(intervalSet);
		boolean actual1 = intervalSet.contains(targetSet);

		assertTrue(actual0);
		assertFalse(actual1);
	}

	@Test
	public void contains_IntervalUnionSet_Interval_Int_RightIntersect() {
		Interval current = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_ONE, false);
		Interval target = numberFactory.newInterval(true, INT_ONE, false,
				INT_THREE, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.contains(intervalSet);
		boolean actual1 = intervalSet.contains(targetSet);

		assertTrue(actual0);
		assertFalse(actual1);
	}

	@Test
	public void contains_IntervalUnionSet_Interval_Rat_RightIntersect() {
		Interval current = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, false);
		Interval target = numberFactory.newInterval(false, RAT_ONE, false,
				RAT_THREE, true);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.contains(intervalSet);
		boolean actual1 = intervalSet.contains(targetSet);

		assertTrue(actual0);
		assertFalse(actual1);
	}

	@Test
	public void contains_IntervalUnionSet_Interval_Int_RightDisjoint() {
		Interval current = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_ONE, false);
		Interval target = numberFactory.newInterval(true, INT_TWO, false,
				INT_THREE, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.contains(intervalSet);
		boolean actual1 = intervalSet.contains(targetSet);

		assertTrue(actual0);
		assertFalse(actual1);
	}

	@Test
	public void contains_IntervalUnionSet_Interval_Rat_RightDisjoint() {
		Interval current = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, true);
		Interval target = numberFactory.newInterval(false, RAT_ONE, false,
				RAT_ONE, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.contains(intervalSet);
		boolean actual1 = intervalSet.contains(targetSet);

		assertTrue(actual0);
		assertFalse(actual1);
	}

	@Test
	public void contains_IntervalUnionSet_Interval_Int_Contains() {
		Interval current = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_ONE, false);
		Interval target = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.contains(intervalSet);
		boolean actual1 = intervalSet.contains(targetSet);

		assertTrue(actual0);
		assertTrue(actual1);
	}

	@Test
	public void contains_IntervalUnionSet_Interval_Rat_Contains() {
		Interval current = numberFactory.newInterval(false, RAT_N_ONE, false,
				RAT_ONE, false);
		Interval target = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, true);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.contains(intervalSet);
		boolean actual1 = intervalSet.contains(targetSet);

		assertTrue(actual0);
		assertTrue(actual1);
	}

	@Test
	public void contains_IntervalUnionSet_Interval_Int_Multiple() {
		Interval first = numberFactory.newInterval(true, INT_N_TEN, false,
				INT_N_SIX, false);
		Interval second = numberFactory.newInterval(true, INT_N_TWO, false,
				INT_TWO, false);
		Interval third = numberFactory.newInterval(true, INT_SIX, false,
				INT_TEN, false);
		Interval target = numberFactory.newInterval(true, INT_N_TEN, false,
				INT_N_FOUR, false);
		IntervalUnionSet firstSet = new IntervalUnionSet(first);
		IntervalUnionSet secondSet = new IntervalUnionSet(second);
		IntervalUnionSet thirdSet = new IntervalUnionSet(third);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		boolean actual0a = intervalSet.contains(firstSet);
		boolean actual0b = intervalSet.contains(secondSet);
		boolean actual0c = intervalSet.contains(thirdSet);
		boolean actual1 = intervalSet.contains(targetSet);

		assertTrue(actual0a);
		assertTrue(actual0b);
		assertTrue(actual0c);
		assertFalse(actual1);
	}

	@Test
	public void contains_IntervalUnionSet_Interval_Rat_Multiple() {
		Interval first = numberFactory.newInterval(false, RAT_N_TEN, true,
				RAT_N_SIX, true);
		Interval second = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_TWO, true);
		Interval third = numberFactory.newInterval(false, RAT_SIX, true,
				RAT_TEN, true);
		Interval target = numberFactory.newInterval(false, RAT_SIX, true,
				RAT_SEVEN, false);
		IntervalUnionSet firstSet = new IntervalUnionSet(first);
		IntervalUnionSet secondSet = new IntervalUnionSet(second);
		IntervalUnionSet thirdSet = new IntervalUnionSet(third);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		boolean actual0a = intervalSet.contains(firstSet);
		boolean actual0b = intervalSet.contains(secondSet);
		boolean actual0c = intervalSet.contains(thirdSet);
		boolean actual1 = intervalSet.contains(targetSet);

		assertTrue(actual0a);
		assertTrue(actual0b);
		assertTrue(actual0c);
		assertTrue(actual1);
	}

	@Test
	public void contains_IntervalUnionSet_Disjoint_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_EIGHT, true);
		Interval first2 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_FIVE, true);
		Interval second1 = numberFactory.newInterval(false, RAT_N_EIGHT, true,
				RAT_N_SEVEN, true);
		Interval second2 = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_FOUR, true);
		Interval third1 = numberFactory.newInterval(false, RAT_N_FIVE, false,
				RAT_N_FIVE, false);
		Interval third2 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_THREE, true);
		Interval fourth1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_N_ONE, true);
		Interval fourth2 = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_ONE, true);
		Interval fifth1 = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ZERO, true);
		Interval fifth2 = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_POS_INF, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		boolean actual = set1.contains(set2);

		assertFalse(actual);
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
	}

	@Test
	public void contains_IntervalUnionSet_Intersection1_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_N_NINE, false,
				RAT_N_EIGHT, true);
		Interval first2 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_NINE, false);
		Interval second1 = numberFactory.newInterval(false, RAT_N_EIGHT, true,
				RAT_N_SEVEN, true);
		Interval second2 = numberFactory.newInterval(false, RAT_N_EIGHT, false,
				RAT_N_SEVEN, true);
		Interval third1 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_FIVE, true);
		Interval third2 = numberFactory.newInterval(false, RAT_N_SIX, false,
				RAT_N_FIVE, false);
		Interval fourth1 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_THREE, true);
		Interval fourth2 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_THREE, false);
		Interval fifth1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_N_ONE, false);
		Interval fifth2 = numberFactory.newInterval(false, RAT_N_ONE, false,
				RAT_POS_INF, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		boolean actual = set1.contains(set2);

		assertFalse(actual);
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
	}

	@Test
	public void contains_IntervalUnionSet_Intersection2_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_N_NINE, false,
				RAT_N_EIGHT, true);
		Interval first2 = first1;
		Interval second1 = numberFactory.newInterval(false, RAT_N_EIGHT, true,
				RAT_N_SEVEN, true);
		Interval second2 = second1;
		Interval third1 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_FOUR, true);
		Interval third2 = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_FOUR, true);
		Interval fourth1 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_THREE, false);
		Interval fourth2 = numberFactory.newInterval(false, RAT_N_THREE, false,
				RAT_N_TWO, false);
		Interval fifth1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_N_ONE, false);
		Interval fifth2 = numberFactory.newInterval(false, RAT_N_ONE, false,
				RAT_POS_INF, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		boolean actual = set1.contains(set2);

		assertFalse(actual);
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
	}

	@Test
	public void contains_IntervalUnionSet_Intersection3_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_N_NINE, false,
				RAT_N_EIGHT, true);
		Interval first2 = first1;
		Interval second1 = numberFactory.newInterval(false, RAT_N_EIGHT, true,
				RAT_N_SEVEN, true);
		Interval second2 = second1;
		Interval third1 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_FOUR, true);
		Interval third2 = third1;
		Interval fourth1 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_THREE, true);
		Interval fourth2 = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_ONE, false);
		Interval fifth1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_N_ONE, false);
		Interval fifth2 = numberFactory.newInterval(false, RAT_TWO, false,
				RAT_POS_INF, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		boolean actual = set1.contains(set2);

		assertFalse(actual);
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
	}

	@Test
	public void contains_IntervalUnionSet_Intersection4_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_N_NINE, false,
				RAT_N_EIGHT, true);
		Interval first2 = first1;
		Interval second1 = numberFactory.newInterval(false, RAT_N_EIGHT, true,
				RAT_N_SEVEN, true);
		Interval second2 = second1;
		Interval third1 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_FOUR, true);
		Interval third2 = third1;
		Interval fourth1 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_THREE, true);
		Interval fourth2 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_ZERO, true);
		Interval fifth1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_N_ONE, false);
		Interval fifth2 = numberFactory.newInterval(false, RAT_N_TWO, false,
				RAT_POS_INF, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		boolean actual = set1.contains(set2);

		assertFalse(actual);
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
	}

	@Test
	public void contains_IntervalUnionSet_Contains1_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_SEVEN, false);
		Interval first2 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_SEVEN, true);
		Interval second1 = numberFactory.newInterval(false, RAT_N_SIX, false,
				RAT_N_FIVE, false);
		Interval second2 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_FIVE, true);
		Interval third1 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_THREE, true);
		Interval third2 = third1;
		Interval fourth1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_TWO, true);
		Interval fourth2 = numberFactory.newInterval(false, RAT_N_ONE, false,
				RAT_ONE, false);
		Interval fifth1 = numberFactory.newInterval(false, RAT_FIVE, true,
				RAT_POS_INF, true);
		Interval fifth2 = numberFactory.newInterval(false, RAT_FIVE, true,
				RAT_POS_INF, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		boolean actual = set1.contains(set2);

		assertTrue(actual);
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
	}

	@Test
	public void contains_IntervalUnionSet_Contains2_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_N_TEN, true,
				RAT_ZERO, true);
		Interval first2 = numberFactory.newInterval(false, RAT_N_NINE, true,
				RAT_N_EIGHT, true);
		Interval second1 = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FOUR, true);
		Interval second2 = numberFactory.newInterval(false, RAT_N_SEVEN, true,
				RAT_N_SIX, true);
		Interval third2 = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_FOUR, true);
		Interval fourth2 = numberFactory.newInterval(false, RAT_N_THREE, true,
				RAT_N_TWO, true);
		Interval[] list1 = { first1, second1 };
		Interval[] list2 = { first2, second2, third2, fourth2 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		boolean actual = set1.contains(set2);

		assertTrue(actual);
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
	}

	@Test
	public void contains_IntervalUnionSet_Contains3_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_SEVEN, false);
		Interval first2 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_SEVEN, true);
		Interval second1 = numberFactory.newInterval(false, RAT_N_SIX, false,
				RAT_N_FIVE, false);
		Interval second2 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_FIVE, true);
		Interval third1 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_THREE, true);
		Interval third2 = third1;
		Interval fourth1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_TWO, true);
		Interval fourth2 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_TWO, true);
		Interval[] list1 = { first1, second1, third1, fourth1 };
		Interval[] list2 = { first2, second2, third2, fourth2 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		boolean actual = set1.contains(set2);

		assertTrue(actual);
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
	}

	@Test
	public void contains_IntervalUnionSet_NotContains1_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_SEVEN, false);
		Interval first2 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_SEVEN, true);
		Interval second1 = numberFactory.newInterval(false, RAT_N_SIX, false,
				RAT_N_FIVE, false);
		Interval second2 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_FIVE, true);
		Interval third1 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_THREE, true);
		Interval third2 = third1;
		Interval fourth1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_TWO, true);
		Interval fourth2 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_TWO, true);
		Interval fifth2 = numberFactory.newInterval(false, RAT_FIVE, true,
				RAT_TEN, true);
		Interval[] list1 = { first1, second1, third1, fourth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		boolean actual = set1.contains(set2);

		assertFalse(actual);
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
	}

	@Test(expected = AssertionError.class)
	public void intersects_Null() {
		if (ASSERTION_ENABLED) {
			IntervalUnionSet target = null;
			IntervalUnionSet intervalSet = new IntervalUnionSet(INT_UNIV);

			intervalSet.intersects(target);
		} else {
			throw new AssertionError();
		}
	}

	@Test(expected = AssertionError.class)
	public void intersects_Mismatch() {
		if (ASSERTION_ENABLED) {
			IntervalUnionSet target = new IntervalUnionSet(INT_UNIV);
			IntervalUnionSet intervalSet = new IntervalUnionSet(RAT_UNIV);

			intervalSet.intersects(target);
		} else {
			throw new AssertionError();
		}
	}

	@Test
	public void intersects_Int_emptySet_In_Univ() {
		IntervalUnionSet target = new IntervalUnionSet(INT_EMPTY);
		IntervalUnionSet intervalSet = new IntervalUnionSet(INT_UNIV);
		boolean actual = intervalSet.intersects(target);

		assertFalse(actual);
	}

	@Test
	public void intersects_Rat_emptySet_In_Univ() {
		IntervalUnionSet target = new IntervalUnionSet(RAT_EMPTY);
		IntervalUnionSet intervalSet = new IntervalUnionSet(RAT_UNIV);
		boolean actual = intervalSet.intersects(target);

		assertFalse(actual);
	}

	@Test
	public void intersects_Int_univSet_In_empty() {
		IntervalUnionSet target = new IntervalUnionSet(INT_UNIV);
		IntervalUnionSet intervalSet = new IntervalUnionSet(INT_EMPTY);
		boolean actual = intervalSet.intersects(target);

		assertFalse(actual);
	}

	@Test
	public void intersects_Rat_univSet_In_empty() {
		IntervalUnionSet target = new IntervalUnionSet(RAT_UNIV);
		IntervalUnionSet intervalSet = new IntervalUnionSet(RAT_EMPTY);
		boolean actual = intervalSet.intersects(target);

		assertFalse(actual);
	}

	@Test
	public void intersects_Int_LeftDisjoint() {
		Interval current = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_ONE, false);
		Interval target = numberFactory.newInterval(true, INT_N_THREE, false,
				INT_N_TWO, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.intersects(intervalSet);
		boolean actual1 = intervalSet.intersects(targetSet);

		assertTrue(actual0);
		assertFalse(actual1);
	}

	//
	@Test
	public void intersects_Rat_LeftDisjoint() {
		Interval current = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, true);
		Interval target = numberFactory.newInterval(false, RAT_N_ONE, false,
				RAT_N_ONE, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.intersects(intervalSet);
		boolean actual1 = intervalSet.intersects(targetSet);

		assertTrue(actual0);
		assertFalse(actual1);
	}

	@Test
	public void intersects_Int_LeftIntersect() {
		Interval current = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_ONE, false);
		Interval target = numberFactory.newInterval(true, INT_N_THREE, false,
				INT_N_ONE, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.intersects(intervalSet);
		boolean actual1 = intervalSet.intersects(targetSet);

		assertTrue(actual0);
		assertTrue(actual1);
	}

	@Test
	public void intersects_Rat_LeftIntersect() {
		Interval current = numberFactory.newInterval(false, RAT_N_ONE, false,
				RAT_ONE, true);
		Interval target = numberFactory.newInterval(false, RAT_N_THREE, true,
				RAT_N_ONE, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.intersects(intervalSet);
		boolean actual1 = intervalSet.intersects(targetSet);

		assertTrue(actual0);
		assertTrue(actual1);
	}

	@Test
	public void intersects_Int_Target_contains_Current() {
		Interval current = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_ONE, false);
		Interval target = numberFactory.newInterval(true, INT_N_THREE, false,
				INT_THREE, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.intersects(intervalSet);
		boolean actual1 = intervalSet.intersects(targetSet);

		assertTrue(actual0);
		assertTrue(actual1);
	}

	@Test
	public void intersects_Rat_Target_contains_Current() {
		Interval current = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, true);
		Interval target = numberFactory.newInterval(false, RAT_N_ONE, false,
				RAT_ONE, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.intersects(intervalSet);
		boolean actual1 = intervalSet.intersects(targetSet);

		assertTrue(actual0);
		assertTrue(actual1);
	}

	@Test
	public void intersects_Int_RightIntersect() {
		Interval current = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_ONE, false);
		Interval target = numberFactory.newInterval(true, INT_ONE, false,
				INT_THREE, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.intersects(intervalSet);
		boolean actual1 = intervalSet.intersects(targetSet);

		assertTrue(actual0);
		assertTrue(actual1);
	}

	@Test
	public void intersects_Rat_RightIntersect() {
		Interval current = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, false);
		Interval target = numberFactory.newInterval(false, RAT_ONE, false,
				RAT_THREE, true);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.intersects(intervalSet);
		boolean actual1 = intervalSet.intersects(targetSet);

		assertTrue(actual0);
		assertTrue(actual1);
	}

	@Test
	public void intersects_Int_RightDisjoint() {
		Interval current = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_ONE, false);
		Interval target = numberFactory.newInterval(true, INT_TWO, false,
				INT_THREE, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.intersects(intervalSet);
		boolean actual1 = intervalSet.intersects(targetSet);

		assertTrue(actual0);
		assertFalse(actual1);
	}

	@Test
	public void intersects_Rat_RightDisjoint() {
		Interval current = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, true);
		Interval target = numberFactory.newInterval(false, RAT_ONE, false,
				RAT_ONE, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.intersects(intervalSet);
		boolean actual1 = intervalSet.intersects(targetSet);

		assertTrue(actual0);
		assertFalse(actual1);
	}

	@Test
	public void intersects_Int_Contains() {
		Interval current = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_ONE, false);
		Interval target = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.intersects(intervalSet);
		boolean actual1 = intervalSet.intersects(targetSet);

		assertTrue(actual0);
		assertTrue(actual1);
	}

	@Test
	public void intersects_Rat_Contains() {
		Interval current = numberFactory.newInterval(false, RAT_N_ONE, false,
				RAT_ONE, false);
		Interval target = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, true);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(current);
		boolean actual0 = intervalSet.intersects(intervalSet);
		boolean actual1 = intervalSet.intersects(targetSet);

		assertTrue(actual0);
		assertTrue(actual1);
	}

	@Test
	public void intersects_Int_Multiple() {
		Interval first = numberFactory.newInterval(true, INT_N_TEN, false,
				INT_N_SIX, false);
		Interval second = numberFactory.newInterval(true, INT_N_TWO, false,
				INT_TWO, false);
		Interval third = numberFactory.newInterval(true, INT_SIX, false,
				INT_TEN, false);
		Interval target = numberFactory.newInterval(true, INT_N_TEN, false,
				INT_N_FOUR, false);
		IntervalUnionSet targetSet = new IntervalUnionSet(target);
		IntervalUnionSet intervalSet = new IntervalUnionSet(first, second,
				third);
		boolean actual0 = intervalSet.intersects(intervalSet);
		boolean actual1 = intervalSet.intersects(targetSet);

		assertTrue(actual0);
		assertTrue(actual1);
	}

	@Test(expected = AssertionError.class)
	public void intersect_IntervalUnionSet_Null() {
		if (ASSERTION_ENABLED) {
			IntervalUnionSet nullSet = null;
			IntervalUnionSet currentSet = new IntervalUnionSet(RAT_ZERO);
			actual = rangeFactory.intersect(currentSet, nullSet);
		} else {
			throw new AssertionError();
		}
	}

	@Test(expected = AssertionError.class)
	public void intersect_IntervalUnionSet_MismatchedType() {
		if (ASSERTION_ENABLED) {
			IntervalUnionSet intSet = new IntervalUnionSet(INT_ZERO);
			IntervalUnionSet ratSet = new IntervalUnionSet(RAT_ZERO);

			actual = rangeFactory.intersect(ratSet, intSet);
		} else {
			throw new AssertionError();
		}
	}

	@Test
	public void intersect_IntervalUnionSet_Empty() {
		IntervalUnionSet emptyRatSet = new IntervalUnionSet(false);
		IntervalUnionSet nonemptyRatSet = new IntervalUnionSet(numberFactory
				.newInterval(false, RAT_N_ONE, true, RAT_ONE, true));
		expected = emptyRatSet;
		actual1 = rangeFactory.intersect(nonemptyRatSet, emptyRatSet);
		actual2 = rangeFactory.intersect(emptyRatSet, nonemptyRatSet);

		assertEquals(expected.toString(), actual1.toString());
		assertEquals(expected.toString(), actual2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, " actual1: " + actual1.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void intersect_IntervalUnionSet_Univ() {
		IntervalUnionSet univIntSet = new IntervalUnionSet(INT_UNIV);
		IntervalUnionSet nonunivIntSet = new IntervalUnionSet(numberFactory
				.newInterval(true, INT_N_ONE, false, INT_ONE, false));
		expected = nonunivIntSet;
		actual1 = rangeFactory.intersect(nonunivIntSet, univIntSet);
		actual2 = rangeFactory.intersect(univIntSet, nonunivIntSet);

		assertEquals(expected.toString(), actual1.toString());
		assertEquals(expected.toString(), actual2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, " actual1: " + actual1.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void intersect_IntervalUnionSet_Self() {
		IntervalUnionSet original = new IntervalUnionSet(numberFactory
				.newInterval(false, RAT_N_ONE, true, RAT_ONE, true));
		expected = original;
		actual = rangeFactory.intersect(original, original);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void intersect_IntervalUnionSet_Simple_Disjoint_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_N_TEN, true,
				RAT_N_EIGHT, true);
		Interval first2 = numberFactory.newInterval(false, RAT_N_EIGHT, true,
				RAT_N_SIX, true);
		Interval second1 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_FOUR, true);
		Interval second2 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_TWO, true);
		Interval third1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_ZERO, true);
		Interval third2 = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_TWO, true);
		Interval fourth1 = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FOUR, true);
		Interval fourth2 = numberFactory.newInterval(false, RAT_FOUR, true,
				RAT_SIX, true);
		Interval fifth1 = numberFactory.newInterval(false, RAT_SIX, true,
				RAT_EIGHT, true);
		Interval fifth2 = numberFactory.newInterval(false, RAT_EIGHT, true,
				RAT_TEN, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = new IntervalUnionSet(false);
		actual1 = rangeFactory.intersect(set1, set2);
		actual2 = rangeFactory.intersect(set2, set1);

		assertEquals(expected.toString(), actual1.toString());
		assertEquals(expected.toString(), actual2.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, " actua1l: " + actual1.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void intersect_IntervalUnionSet_Simple_Adjacent_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_EIGHT, false);
		Interval first2 = numberFactory.newInterval(false, RAT_N_EIGHT, true,
				RAT_N_SIX, false);
		Interval second1 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_FOUR, false);
		Interval second2 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_TWO, false);
		Interval third1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_ZERO, false);
		Interval third2 = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_TWO, false);
		Interval fourth1 = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FOUR, false);
		Interval fourth2 = numberFactory.newInterval(false, RAT_FOUR, true,
				RAT_SIX, false);
		Interval fifth1 = numberFactory.newInterval(false, RAT_SIX, true,
				RAT_EIGHT, false);
		Interval fifth2 = numberFactory.newInterval(false, RAT_EIGHT, true,
				RAT_POS_INF, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = new IntervalUnionSet(false);
		actual1 = rangeFactory.intersect(set1, set2);
		actual2 = rangeFactory.intersect(set2, set1);

		assertEquals(expected.toString(), actual1.toString());
		assertEquals(expected.toString(), actual2.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, " actua1l: " + actual1.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void intersect_IntervalUnionSet_Simple_Adjacent_Int() {
		Interval first1 = numberFactory.newInterval(true, INT_NEG_INF, true,
				INT_N_TEN, false);
		Interval first2 = numberFactory.newInterval(true, INT_N_NINE, false,
				INT_N_EIGHT, false);
		Interval second1 = numberFactory.newInterval(true, INT_N_SEVEN, false,
				INT_N_FIVE, false);
		Interval second2 = numberFactory.newInterval(true, INT_N_FOUR, false,
				INT_N_TWO, false);
		Interval third1 = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_ZERO, false);
		Interval third2 = numberFactory.newInterval(true, INT_ONE, false,
				INT_ONE, false);
		Interval fourth1 = numberFactory.newInterval(true, INT_TWO, false,
				INT_FOUR, false);
		Interval fourth2 = numberFactory.newInterval(true, INT_FIVE, false,
				INT_SEVEN, false);
		Interval fifth1 = numberFactory.newInterval(true, INT_EIGHT, false,
				INT_NINE, false);
		Interval fifth2 = numberFactory.newInterval(true, INT_TEN, false,
				INT_POS_INF, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };

		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = new IntervalUnionSet(true);
		actual1 = rangeFactory.intersect(set1, set2);
		actual2 = rangeFactory.intersect(set2, set1);

		assertEquals(expected.toString(), actual1.toString());
		assertEquals(expected.toString(), actual2.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, " actua1l: " + actual1.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void intersect_IntervalUnionSet_Simple_Overlapped_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_N_NINE, true,
				RAT_N_SEVEN, true);
		Interval first2 = numberFactory.newInterval(false, RAT_N_EIGHT, true,
				RAT_N_SEVEN, true);
		Interval second1 = numberFactory.newInterval(false, RAT_N_SIX, false,
				RAT_N_FIVE, true);
		Interval second2 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_FIVE, true);
		Interval third1 = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_FOUR, true);
		Interval third2 = third1;
		Interval fourth1 = numberFactory.newInterval(false, RAT_N_THREE, false,
				RAT_N_TWO, false);
		Interval fourth2 = numberFactory.newInterval(false, RAT_N_THREE, false,
				RAT_N_TWO, true);
		Interval fifth1 = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, true);
		Interval fifth2 = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ZERO, false);
		Interval sixth1 = numberFactory.newInterval(false, RAT_THREE, false,
				RAT_FIVE, false);
		Interval sixth2 = numberFactory.newInterval(false, RAT_TWO, false,
				RAT_FOUR, false);
		Interval sixth3 = numberFactory.newInterval(false, RAT_THREE, false,
				RAT_FOUR, false);
		Interval seventh1 = numberFactory.newInterval(false, RAT_SIX, false,
				RAT_EIGHT, true);
		Interval seventh2 = numberFactory.newInterval(false, RAT_SIX, true,
				RAT_EIGHT, false);
		Interval seventh3 = numberFactory.newInterval(false, RAT_SIX, true,
				RAT_EIGHT, true);

		Interval[] list1 = { first1, second1, third1, fourth1, fifth1, sixth1,
				seventh1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2, sixth2,
				seventh2 };
		Interval[] list3 = { first2, second2, third2, fourth2, fifth2, sixth3,
				seventh3 };

		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = new IntervalUnionSet(list3);
		actual1 = rangeFactory.intersect(set1, set2);
		actual2 = rangeFactory.intersect(set2, set1);

		assertEquals(expected.toString(), actual1.toString());
		assertEquals(expected.toString(), actual2.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, " actua1l: " + actual1.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void intersect_IntervalUnionSet_Complicated1_Int() {
		Interval first1 = numberFactory.newInterval(true, INT_N_TEN, false,
				INT_N_TWO, false);
		Interval first2 = numberFactory.newInterval(true, INT_N_NINE, false,
				INT_N_SEVEN, false);
		Interval second1 = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		Interval second2 = numberFactory.newInterval(true, INT_N_FIVE, false,
				INT_N_FIVE, false);
		Interval third1 = numberFactory.newInterval(true, INT_THREE, false,
				INT_THREE, false);
		Interval third2 = numberFactory.newInterval(true, INT_N_THREE, false,
				INT_N_TWO, false);
		Interval fourth1 = numberFactory.newInterval(true, INT_SIX, false,
				INT_SEVEN, false);
		Interval fourth2 = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		Interval fifth1 = numberFactory.newInterval(true, INT_NINE, false,
				INT_NINE, false);
		Interval fifth2 = numberFactory.newInterval(true, INT_TWO, false,
				INT_TEN, false);

		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		Interval[] list3 = { first2, second2, third2, fourth2, third1, fourth1,
				fifth1 };

		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = new IntervalUnionSet(list3);
		actual1 = rangeFactory.intersect(set1, set2);
		actual2 = rangeFactory.intersect(set2, set1);

		assertEquals(expected.toString(), actual1.toString());
		assertEquals(expected.toString(), actual2.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, " actua1l: " + actual1.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void intersect_IntervalUnionSet_Complicated2_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_TWO, true);
		Interval first2 = numberFactory.newInterval(false, RAT_N_NINE, true,
				RAT_N_SEVEN, true);
		Interval second1 = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_ONE, true);
		Interval second2 = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_FOUR, true);
		Interval third1 = numberFactory.newInterval(false, RAT_THREE, true,
				RAT_FOUR, true);
		Interval third2 = numberFactory.newInterval(false, RAT_N_THREE, true,
				RAT_N_TWO, true);
		Interval fourth1 = numberFactory.newInterval(false, RAT_SIX, true,
				RAT_SEVEN, true);
		Interval fourth2 = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_ONE, true);
		Interval fifth1 = numberFactory.newInterval(false, RAT_NINE, true,
				RAT_TEN, true);
		Interval fifth2 = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_POS_INF, true);

		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		Interval[] list3 = { first2, second2, third2, fourth2, third1, fourth1,
				fifth1 };

		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected = new IntervalUnionSet(list3);
		actual1 = rangeFactory.intersect(set1, set2);
		actual2 = rangeFactory.intersect(set2, set1);

		assertEquals(expected.toString(), actual1.toString());
		assertEquals(expected.toString(), actual2.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, " actua1l: " + actual1.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test(expected = AssertionError.class)
	public void minus_IntervalUnionSet_Null() {
		if (ASSERTION_ENABLED) {
			IntervalUnionSet nullSet = null;
			IntervalUnionSet currentSet = new IntervalUnionSet(RAT_ZERO);
			actual = rangeFactory.setMinus(currentSet, nullSet);
		} else {
			throw new AssertionError();
		}
	}

	@Test(expected = AssertionError.class)
	public void minus_IntervalUnionSet_MismatchedType() {
		if (ASSERTION_ENABLED) {
			IntervalUnionSet intSet = new IntervalUnionSet(INT_ZERO);
			IntervalUnionSet ratSet = new IntervalUnionSet(RAT_ZERO);
			actual = rangeFactory.setMinus(ratSet, intSet);
		} else {
			throw new AssertionError();
		}
	}

	@Test
	public void minus_IntervalUnionSet_Empty() {
		IntervalUnionSet emptyRatSet = new IntervalUnionSet(false);
		IntervalUnionSet nonemptyRatSet = new IntervalUnionSet(numberFactory
				.newInterval(false, RAT_N_ONE, true, RAT_ONE, true));
		expected1 = nonemptyRatSet;
		expected2 = emptyRatSet;
		actual1 = rangeFactory.setMinus(nonemptyRatSet, emptyRatSet);
		actual2 = rangeFactory.setMinus(emptyRatSet, nonemptyRatSet);

		assertEquals(expected1.toString(), actual1.toString());
		assertEquals(expected2.toString(), actual2.toString());
		p(DEBUG, "expected: " + expected1.toString());
		p(DEBUG, " actual1: " + actual1.toString());
		p(DEBUG, "expected: " + expected2.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void minus_IntervalUnionSet_Univ() {
		IntervalUnionSet univIntSet = new IntervalUnionSet(INT_UNIV);
		IntervalUnionSet nonunivIntSet = new IntervalUnionSet(numberFactory
				.newInterval(true, INT_N_ONE, false, INT_ONE, false));
		expected1 = new IntervalUnionSet(true);
		expected2 = new IntervalUnionSet(
				numberFactory.newInterval(true, INT_NEG_INF, true, INT_N_TWO,
						false),
				numberFactory.newInterval(true, INT_TWO, false, INT_POS_INF,
						true));
		actual1 = rangeFactory.setMinus(nonunivIntSet, univIntSet);
		actual2 = rangeFactory.setMinus(univIntSet, nonunivIntSet);

		assertEquals(expected1.toString(), actual1.toString());
		assertEquals(expected2.toString(), actual2.toString());
		p(DEBUG, "expected: " + expected1.toString());
		p(DEBUG, " actual1: " + actual1.toString());
		p(DEBUG, "expected: " + expected2.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void minus_IntervalUnionSet_Self() {
		IntervalUnionSet original = new IntervalUnionSet(numberFactory
				.newInterval(false, RAT_N_ONE, true, RAT_ONE, true));
		expected = new IntervalUnionSet(false);
		actual = rangeFactory.setMinus(original, original);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void minus_IntervalUnionSet_Simple_Disjoint_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_N_TEN, true,
				RAT_N_EIGHT, true);
		Interval first2 = numberFactory.newInterval(false, RAT_N_EIGHT, true,
				RAT_N_SIX, true);
		Interval second1 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_FOUR, true);
		Interval second2 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_TWO, true);
		Interval third1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_ZERO, true);
		Interval third2 = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_TWO, true);
		Interval fourth1 = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FOUR, true);
		Interval fourth2 = numberFactory.newInterval(false, RAT_FOUR, true,
				RAT_SIX, true);
		Interval fifth1 = numberFactory.newInterval(false, RAT_SIX, true,
				RAT_EIGHT, true);
		Interval fifth2 = numberFactory.newInterval(false, RAT_EIGHT, true,
				RAT_TEN, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected1 = set1;
		expected2 = set2;
		actual1 = rangeFactory.setMinus(set1, set2);
		actual2 = rangeFactory.setMinus(set2, set1);

		assertEquals(expected1.toString(), actual1.toString());
		assertEquals(expected2.toString(), actual2.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected1.toString());
		p(DEBUG, " actua1l: " + actual1.toString());
		p(DEBUG, "expected: " + expected2.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void minus_IntervalUnionSet_Simple_Adjacent_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_EIGHT, false);
		Interval first2 = numberFactory.newInterval(false, RAT_N_EIGHT, true,
				RAT_N_SIX, false);
		Interval second1 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_FOUR, false);
		Interval second2 = numberFactory.newInterval(false, RAT_N_FOUR, true,
				RAT_N_TWO, false);
		Interval third1 = numberFactory.newInterval(false, RAT_N_TWO, true,
				RAT_ZERO, false);
		Interval third2 = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_TWO, false);
		Interval fourth1 = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_FOUR, false);
		Interval fourth2 = numberFactory.newInterval(false, RAT_FOUR, true,
				RAT_SIX, false);
		Interval fifth1 = numberFactory.newInterval(false, RAT_SIX, true,
				RAT_EIGHT, false);
		Interval fifth2 = numberFactory.newInterval(false, RAT_EIGHT, true,
				RAT_POS_INF, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected1 = set1;
		expected2 = set2;
		actual1 = rangeFactory.setMinus(set1, set2);
		actual2 = rangeFactory.setMinus(set2, set1);

		assertEquals(expected1.toString(), actual1.toString());
		assertEquals(expected2.toString(), actual2.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected1.toString());
		p(DEBUG, " actua1l: " + actual1.toString());
		p(DEBUG, "expected: " + expected2.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void minus_IntervalUnionSet_Simple_Adjacent_Int() {
		Interval first1 = numberFactory.newInterval(true, INT_NEG_INF, true,
				INT_N_TEN, false);
		Interval first2 = numberFactory.newInterval(true, INT_N_NINE, false,
				INT_N_EIGHT, false);
		Interval second1 = numberFactory.newInterval(true, INT_N_SEVEN, false,
				INT_N_FIVE, false);
		Interval second2 = numberFactory.newInterval(true, INT_N_FOUR, false,
				INT_N_TWO, false);
		Interval third1 = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_ZERO, false);
		Interval third2 = numberFactory.newInterval(true, INT_ONE, false,
				INT_ONE, false);
		Interval fourth1 = numberFactory.newInterval(true, INT_TWO, false,
				INT_FOUR, false);
		Interval fourth2 = numberFactory.newInterval(true, INT_FIVE, false,
				INT_SEVEN, false);
		Interval fifth1 = numberFactory.newInterval(true, INT_EIGHT, false,
				INT_NINE, false);
		Interval fifth2 = numberFactory.newInterval(true, INT_TEN, false,
				INT_POS_INF, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected1 = set1;
		expected2 = set2;
		actual1 = rangeFactory.setMinus(set1, set2);
		actual2 = rangeFactory.setMinus(set2, set1);

		assertEquals(expected1.toString(), actual1.toString());
		assertEquals(expected2.toString(), actual2.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected1.toString());
		p(DEBUG, " actua1l: " + actual1.toString());
		p(DEBUG, "expected: " + expected2.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void minus_IntervalUnionSet_Simple_Overlapped_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_N_NINE, true,
				RAT_N_SEVEN, true);
		Interval first2 = numberFactory.newInterval(false, RAT_N_EIGHT, true,
				RAT_N_SEVEN, true);
		Interval first3 = numberFactory.newInterval(false, RAT_N_NINE, true,
				RAT_N_EIGHT, false);
		Interval first4 = numberFactory.newInterval(false, RAT_TWO, false,
				RAT_THREE, true);
		Interval second1 = numberFactory.newInterval(false, RAT_N_SIX, false,
				RAT_N_FIVE, true);
		Interval second2 = numberFactory.newInterval(false, RAT_N_SIX, true,
				RAT_N_FIVE, true);
		Interval second3 = numberFactory.newInterval(false, RAT_N_SIX, false,
				RAT_N_SIX, false);
		Interval second4 = numberFactory.newInterval(false, RAT_EIGHT, false,
				RAT_EIGHT, false);
		Interval third1 = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_FOUR, true);
		Interval third2 = third1;
		Interval third3 = numberFactory.newInterval(false, RAT_N_TWO, false,
				RAT_N_TWO, false);
		Interval fourth1 = numberFactory.newInterval(false, RAT_N_THREE, false,
				RAT_N_TWO, false);
		Interval fourth2 = numberFactory.newInterval(false, RAT_N_THREE, false,
				RAT_N_TWO, true);
		Interval fourth3 = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_ONE, true);
		Interval fifth1 = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, true);
		Interval fifth2 = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ZERO, false);
		Interval fifth3 = numberFactory.newInterval(false, RAT_FOUR, true,
				RAT_FIVE, false);
		Interval sixth1 = numberFactory.newInterval(false, RAT_THREE, false,
				RAT_FIVE, false);
		Interval sixth2 = numberFactory.newInterval(false, RAT_TWO, false,
				RAT_FOUR, false);
		Interval sixth3 = numberFactory.newInterval(false, RAT_SIX, false,
				RAT_SIX, false);
		Interval seventh1 = numberFactory.newInterval(false, RAT_SIX, false,
				RAT_EIGHT, true);
		Interval seventh2 = numberFactory.newInterval(false, RAT_SIX, true,
				RAT_EIGHT, false);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1, sixth1,
				seventh1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2, sixth2,
				seventh2 };
		Interval[] list3 = { first3, second3, third3, fourth3, fifth3, sixth3 };
		Interval[] list4 = { first4, second4 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected1 = new IntervalUnionSet(list3);
		expected2 = new IntervalUnionSet(list4);
		actual1 = rangeFactory.setMinus(set1, set2);
		actual2 = rangeFactory.setMinus(set2, set1);

		assertEquals(expected1.toString(), actual1.toString());
		assertEquals(expected2.toString(), actual2.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected1.toString());
		p(DEBUG, " actua1l: " + actual1.toString());
		p(DEBUG, "expected: " + expected2.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void minus_IntervalUnionSet_Complicated1_Int() {
		Interval first1 = numberFactory.newInterval(true, INT_N_TEN, false,
				INT_N_TWO, false);
		Interval first2 = numberFactory.newInterval(true, INT_N_NINE, false,
				INT_N_SEVEN, false);
		Interval first3 = numberFactory.newInterval(true, INT_N_TEN, false,
				INT_N_TEN, false);
		Interval first4 = numberFactory.newInterval(true, INT_TWO, false,
				INT_TWO, false);
		Interval second1 = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		Interval second2 = numberFactory.newInterval(true, INT_N_FIVE, false,
				INT_N_FIVE, false);
		Interval second3 = numberFactory.newInterval(true, INT_N_SIX, false,
				INT_N_SIX, false);
		Interval second4 = numberFactory.newInterval(true, INT_FOUR, false,
				INT_FIVE, false);
		Interval third1 = numberFactory.newInterval(true, INT_THREE, false,
				INT_THREE, false);
		Interval third2 = numberFactory.newInterval(true, INT_N_THREE, false,
				INT_N_TWO, false);
		Interval third3 = numberFactory.newInterval(true, INT_N_FOUR, false,
				INT_N_FOUR, false);
		Interval third4 = numberFactory.newInterval(true, INT_EIGHT, false,
				INT_EIGHT, false);
		Interval fourth1 = numberFactory.newInterval(true, INT_SIX, false,
				INT_SEVEN, false);
		Interval fourth2 = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		Interval fourth4 = numberFactory.newInterval(true, INT_TEN, false,
				INT_TEN, false);
		Interval fifth1 = numberFactory.newInterval(true, INT_NINE, false,
				INT_NINE, false);
		Interval fifth2 = numberFactory.newInterval(true, INT_TWO, false,
				INT_TEN, false);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		Interval[] list3 = { first3, second3, third3 };
		Interval[] list4 = { first4, second4, third4, fourth4 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected1 = new IntervalUnionSet(list3);
		expected2 = new IntervalUnionSet(list4);
		actual1 = rangeFactory.setMinus(set1, set2);
		actual2 = rangeFactory.setMinus(set2, set1);

		assertEquals(expected1.toString(), actual1.toString());
		assertEquals(expected2.toString(), actual2.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected1.toString());
		p(DEBUG, " actua1l: " + actual1.toString());
		p(DEBUG, "expected: " + expected2.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void minus_IntervalUnionSet_Complicated2_Rat() {
		Interval first1 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_TWO, true);
		Interval first2 = numberFactory.newInterval(false, RAT_N_NINE, true,
				RAT_N_SEVEN, true);
		Interval first3 = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_NINE, false);
		Interval first4 = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_THREE, false);
		Interval second1 = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_ONE, true);
		Interval second2 = numberFactory.newInterval(false, RAT_N_FIVE, true,
				RAT_N_FOUR, true);
		Interval second3 = numberFactory.newInterval(false, RAT_N_SEVEN, false,
				RAT_N_FIVE, false);
		Interval second4 = numberFactory.newInterval(false, RAT_FOUR, false,
				RAT_SIX, false);
		Interval third1 = numberFactory.newInterval(false, RAT_THREE, true,
				RAT_FOUR, true);
		Interval third2 = numberFactory.newInterval(false, RAT_N_THREE, true,
				RAT_N_TWO, true);
		Interval third3 = numberFactory.newInterval(false, RAT_N_FOUR, false,
				RAT_N_THREE, false);
		Interval third4 = numberFactory.newInterval(false, RAT_SEVEN, false,
				RAT_NINE, false);
		Interval fourth1 = numberFactory.newInterval(false, RAT_SIX, true,
				RAT_SEVEN, true);
		Interval fourth2 = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_ONE, true);
		Interval fourth4 = numberFactory.newInterval(false, RAT_TEN, false,
				RAT_POS_INF, true);
		Interval fifth1 = numberFactory.newInterval(false, RAT_NINE, true,
				RAT_TEN, true);
		Interval fifth2 = numberFactory.newInterval(false, RAT_TWO, true,
				RAT_POS_INF, true);
		Interval[] list1 = { first1, second1, third1, fourth1, fifth1 };
		Interval[] list2 = { first2, second2, third2, fourth2, fifth2 };
		Interval[] list3 = { first3, second3, third3 };
		Interval[] list4 = { first4, second4, third4, fourth4 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected1 = new IntervalUnionSet(list3);
		expected2 = new IntervalUnionSet(list4);
		actual1 = rangeFactory.setMinus(set1, set2);
		actual2 = rangeFactory.setMinus(set2, set1);

		assertEquals(expected1.toString(), actual1.toString());
		assertEquals(expected2.toString(), actual2.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected1.toString());
		p(DEBUG, " actua1l: " + actual1.toString());
		p(DEBUG, "expected: " + expected2.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void minus_IntervalUnionSet_Complicated3_Int() {
		Interval first1 = numberFactory.newInterval(true, INT_ZERO, false,
				INT_TWO, false);
		Interval first2 = numberFactory.newInterval(true, INT_ONE, false,
				INT_ONE, false);
		Interval first3a = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		Interval first3b = numberFactory.newInterval(true, INT_TWO, false,
				INT_TWO, false);
		Interval second1 = numberFactory.newInterval(true, INT_FOUR, false,
				INT_SIX, false);
		Interval second2 = numberFactory.newInterval(true, INT_FIVE, false,
				INT_SIX, false);
		Interval second3 = numberFactory.newInterval(true, INT_FOUR, false,
				INT_FOUR, false);
		Interval third1 = numberFactory.newInterval(true, INT_EIGHT, false,
				INT_EIGHT, false);
		Interval fourth1 = numberFactory.newInterval(true, INT_TEN, false,
				INT_TEN, false);
		Interval[] list1 = { first1, second1, third1, fourth1 };
		Interval[] list2 = { first2, second2 };
		Interval[] list3 = { first3a, first3b, second3, third1, fourth1 };
		IntervalUnionSet set1 = new IntervalUnionSet(list1);
		IntervalUnionSet set2 = new IntervalUnionSet(list2);
		expected1 = new IntervalUnionSet(list3);
		expected2 = new IntervalUnionSet(true);
		actual1 = rangeFactory.setMinus(set1, set2);
		actual2 = rangeFactory.setMinus(set2, set1);

		assertEquals(expected1.toString(), actual1.toString());
		assertEquals(expected2.toString(), actual2.toString());
		p(DEBUG, "    set1: " + set1.toString());
		p(DEBUG, "    set2: " + set2.toString());
		p(DEBUG, "expected: " + expected1.toString());
		p(DEBUG, " actua1l: " + actual1.toString());
		p(DEBUG, "expected: " + expected2.toString());
		p(DEBUG, " actual2: " + actual2.toString());
	}

	@Test
	public void complement_test() {
		IntervalUnionSet univIntSet = new IntervalUnionSet(INT_UNIV);
		IntervalUnionSet nonunivIntSet = new IntervalUnionSet(numberFactory
				.newInterval(true, INT_N_ONE, false, INT_ONE, false));
		actual = rangeFactory.complement(nonunivIntSet);
		expected1 = new IntervalUnionSet(
				numberFactory.newInterval(true, INT_NEG_INF, true, INT_N_TWO,
						false),
				numberFactory.newInterval(true, INT_TWO, false, INT_POS_INF,
						true));
		expected2 = rangeFactory.setMinus(univIntSet, nonunivIntSet);

		assertEquals(expected1.toString(), actual.toString());
		assertEquals(expected2.toString(), actual.toString());
		p(DEBUG, "expected: " + expected1.toString());
		p(DEBUG, "  actual: " + actual.toString());
		p(DEBUG, "expected: " + expected2.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test(expected = AssertionError.class)
	public void affineTransform_IntA_Null() {
		if (ASSERTION_ENABLED) {
			IntegerNumber a = null;
			IntegerNumber b = INT_ZERO;
			IntervalUnionSet original = new IntervalUnionSet(INT_ONE);
			actual = rangeFactory.affineTransform(original, a, b);
		} else {
			throw new AssertionError();
		}
	}

	@Test(expected = AssertionError.class)
	public void affineTransform_IntB_Null() {
		if (ASSERTION_ENABLED) {
			IntegerNumber a = INT_ONE;
			IntegerNumber b = null;
			IntervalUnionSet original = new IntervalUnionSet(INT_ONE);
			actual = rangeFactory.affineTransform(original, a, b);
		} else {
			throw new AssertionError();
		}
	}

	@Test(expected = AssertionError.class)
	public void affineTransform_RatA_Mismatched() {
		if (ASSERTION_ENABLED) {
			RationalNumber a = RAT_ONE;
			IntegerNumber b = INT_ONE;
			IntervalUnionSet original = new IntervalUnionSet(INT_ONE);
			actual = rangeFactory.affineTransform(original, a, b);
		} else {
			throw new AssertionError();
		}
	}

	@Test(expected = AssertionError.class)
	public void affineTransform_IntB_Mismatched() {
		if (ASSERTION_ENABLED) {
			RationalNumber a = RAT_ONE;
			IntegerNumber b = INT_ONE;
			IntervalUnionSet original = new IntervalUnionSet(RAT_ONE);
			actual = rangeFactory.affineTransform(original, a, b);
		} else {
			throw new AssertionError();
		}
	}

	@Test
	public void affineTransform_IntervalUnionSet_RatEmpty() {
		RationalNumber a = RAT_TEN;
		RationalNumber b = RAT_TEN;
		IntervalUnionSet original = new IntervalUnionSet(false);
		expected = original;
		actual = rangeFactory.affineTransform(original, a, b);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "original: " + original.toString());
		p(DEBUG, "argments: " + "a: " + a.toString() + ", b: " + b.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void affineTransform_IntervalUnionSet_IntUniv() {
		IntegerNumber a = INT_N_TEN;
		IntegerNumber b = INT_N_TEN;
		IntervalUnionSet original = new IntervalUnionSet(INT_UNIV);
		expected = original;
		actual = rangeFactory.affineTransform(original, a, b);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "original: " + original.toString());
		p(DEBUG, "argments: " + "a: " + a.toString() + ", b: " + b.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void affineTransform_IntervalUnionSet_Self() {
		IntegerNumber a = INT_ONE;
		IntegerNumber b = INT_ZERO;
		IntervalUnionSet original = new IntervalUnionSet(numberFactory
				.newInterval(true, INT_N_TEN, false, INT_TEN, false));
		expected = original;
		actual = rangeFactory.affineTransform(original, a, b);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "original: " + original.toString());
		p(DEBUG, "argments: " + "a: " + a.toString() + ", b: " + b.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void affineTransform_IntervalUnionSet_ArgA_GTZERO() {
		IntegerNumber a = INT_THREE;
		IntegerNumber b = INT_ONE;
		IntervalUnionSet original = new IntervalUnionSet(numberFactory
				.newInterval(true, INT_N_THREE, false, INT_THREE, false));
		expected = new IntervalUnionSet(numberFactory.newInterval(true,
				INT_N_EIGHT, false, INT_TEN, false));
		actual = rangeFactory.affineTransform(original, a, b);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "original: " + original.toString());
		p(DEBUG, "argments: " + "a: " + a.toString() + ", b: " + b.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void affineTransform_IntervalUnionSet_ArgA_EQZERO() {
		RationalNumber a = RAT_ZERO;
		RationalNumber b = RAT_ZERO;
		IntervalUnionSet original = new IntervalUnionSet(numberFactory
				.newInterval(false, RAT_N_TEN, true, RAT_TEN, true));
		expected = new IntervalUnionSet(numberFactory.newInterval(false,
				RAT_ZERO, false, RAT_ZERO, false));
		actual = rangeFactory.affineTransform(original, a, b);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "original: " + original.toString());
		p(DEBUG, "argments: " + "a: " + a.toString() + ", b: " + b.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test
	public void affineTransform_IntervalUnionSet_ArgA_LTZERO() {
		IntegerNumber a = INT_N_THREE;
		IntegerNumber b = INT_N_TWO;
		IntervalUnionSet original = new IntervalUnionSet(numberFactory
				.newInterval(true, INT_N_FOUR, false, INT_TWO, false));
		expected = new IntervalUnionSet(numberFactory.newInterval(true,
				INT_N_EIGHT, false, INT_TEN, false));
		actual = rangeFactory.affineTransform(original, a, b);

		assertEquals(expected.toString(), actual.toString());
		p(DEBUG, "original: " + original.toString());
		p(DEBUG, "argments: " + "a: " + a.toString() + ", b: " + b.toString());
		p(DEBUG, "expected: " + expected.toString());
		p(DEBUG, "  actual: " + actual.toString());
	}

	@Test(expected = AssertionError.class)
	public void symbolicRepresentation_NullUniverse() {
		if (ASSERTION_ENABLED) {
			IntervalUnionSet set = new IntervalUnionSet(false);
			SymbolicExpression expected = universe.falseExpression();
			SymbolicExpression actual = set.symbolicRepresentation(RAT_X, null);

			p(DEBUG, expected.toString());
			p(DEBUG, actual.toString());
			assertEquals(expected, actual);
		} else {
			throw new AssertionError();
		}
	}

	@Test(expected = AssertionError.class)
	public void symbolicRepresentation_NullX() {
		if (ASSERTION_ENABLED) {
			IntervalUnionSet set = new IntervalUnionSet(false);
			SymbolicExpression expected = universe.falseExpression();
			SymbolicExpression actual = set.symbolicRepresentation(null,
					universe);

			p(DEBUG, expected.toString());
			p(DEBUG, actual.toString());
			assertEquals(expected, actual);
		} else {
			throw new AssertionError();
		}
	}

	@Test
	public void symbolicRepresentation_Empty() {
		IntervalUnionSet set = new IntervalUnionSet(false);
		SymbolicExpression expected = universe.falseExpression();
		SymbolicExpression actual = set.symbolicRepresentation(RAT_X, universe);

		p(DEBUG, expected.toString());
		p(DEBUG, actual.toString());
		assertEquals(expected, actual);
	}

	@Test
	public void symbolicRepresentation_Univ() {
		IntervalUnionSet set = new IntervalUnionSet(INT_UNIV);
		SymbolicExpression expected = universe.trueExpression();
		SymbolicExpression actual = set.symbolicRepresentation(INT_X, universe);

		p(DEBUG, expected.toString());
		p(DEBUG, actual.toString());
		assertEquals(expected, actual);
	}

	@Test
	public void symbolicRepresentation_SingleInterval() {
		IntervalUnionSet set = new IntervalUnionSet(numberFactory
				.newInterval(false, RAT_ZERO, true, RAT_TEN, true));
		SymbolicExpression expected = universe.and(
				universe.lessThan(universe.zeroReal(), RAT_X),
				universe.lessThan(RAT_X, universe.rational(10.00)));
		SymbolicExpression actual = set.symbolicRepresentation(RAT_X, universe);

		p(DEBUG, expected.toString());
		p(DEBUG, actual.toString());
		assertEquals(expected, actual);
	}

	@Test
	public void symbolicRepresentation_MultiInterval1() {
		Interval first = numberFactory.newInterval(false, RAT_NEG_INF, true,
				RAT_N_TEN, true);
		Interval second = numberFactory.newInterval(false, RAT_N_ONE, true,
				RAT_ONE, true);
		Interval third = numberFactory.newInterval(false, RAT_TEN, true,
				RAT_POS_INF, true);
		IntervalUnionSet set = new IntervalUnionSet(first, second, third);
		SymbolicExpression expected = universe.or(
				universe.or(universe.lessThan(RAT_X, universe.rational(-10)),
						universe.and(
								universe.lessThan(RAT_X, universe.rational(1)),
								universe.lessThan(universe.rational(-1),
										RAT_X))),
				universe.lessThan(universe.rational(10), RAT_X));
		SymbolicExpression actual = set.symbolicRepresentation(RAT_X, universe);

		p(DEBUG, expected.toString());
		p(DEBUG, actual.toString());
		assertEquals(expected, actual);
	}

	@Test
	public void symbolicRepresentation_MultiInterval2() {
		Interval first = numberFactory.newInterval(true, INT_NEG_INF, true,
				INT_N_TEN, false);
		Interval second = numberFactory.newInterval(true, INT_ZERO, false,
				INT_ZERO, false);
		Interval third = numberFactory.newInterval(true, INT_TEN, false,
				INT_POS_INF, true);
		IntervalUnionSet set = new IntervalUnionSet(first, second, third);
		SymbolicExpression expected = universe.or(
				universe.or(universe.equals(INT_X, universe.integer(0)),
						universe.lessThanEquals(universe.integer(10), INT_X)),
				universe.lessThanEquals(INT_X, universe.integer(-10)));
		SymbolicExpression actual = set.symbolicRepresentation(INT_X, universe);

		p(DEBUG, expected.toString());
		p(DEBUG, actual.toString());
		assertEquals(expected, actual);
	}

	@Test
	public void symbolicRepresentation_Infi() {
		Interval infi_to_one = numberFactory.newInterval(true, INT_NEG_INF,
				true, INT_ONE, false);
		Interval three_to_five = numberFactory.newInterval(true, INT_THREE,
				false, INT_FIVE, false);
		Interval seven_to_infi = numberFactory.newInterval(true, INT_SEVEN,
				false, INT_POS_INF, true);
		IntervalUnionSet set = new IntervalUnionSet(infi_to_one, three_to_five,
				seven_to_infi);
		SymbolicExpression expected = universe.and(
				universe.neq(universe.integer(2), INT_X),
				universe.neq(universe.integer(6), INT_X));
		SymbolicExpression actual = set.symbolicRepresentation(INT_X, universe);

		p(DEBUG, expected.toString());
		p(DEBUG, actual.toString());
		assertEquals(expected, actual);
	}

	@Test
	public void divide_IntervalUnionSet_01() {
		Interval interval = numberFactory.newInterval(true, INT_ZERO, false,
				INT_TEN, false);
		Interval expectedInterval = numberFactory.newInterval(true, INT_ZERO,
				false, INT_THREE, false);
		IntervalUnionSet set = new IntervalUnionSet(interval);
		IntervalUnionSet expected = new IntervalUnionSet(expectedInterval);
		IntervalUnionSet actual = (IntervalUnionSet) rangeFactory.divide(set,
				INT_THREE);

		p(DEBUG, expected.toString());
		p(DEBUG, actual.toString());
		assertEquals(expected.toString(), actual.toString());
	}

	@Test
	public void divide_IntervalUnionSet_02() {
		RationalNumber rat_tenThird = numberFactory.divide(RAT_TEN, RAT_THREE);
		Interval interval = numberFactory.newInterval(false, RAT_ZERO, true,
				RAT_TEN, false);
		Interval expectedInterval = numberFactory.newInterval(false, RAT_ZERO,
				true, rat_tenThird, false);
		IntervalUnionSet set = new IntervalUnionSet(interval);
		IntervalUnionSet expected = new IntervalUnionSet(expectedInterval);
		IntervalUnionSet actual = (IntervalUnionSet) rangeFactory.divide(set,
				RAT_THREE);

		p(DEBUG, expected.toString());
		p(DEBUG, actual.toString());
		assertEquals(expected.toString(), actual.toString());
	}

	/**
	 * Get the approximation range from the given range <code>set</code>
	 */
	@Test
	public void rangeApproximation_01() {
		Interval interval1 = numberFactory.newInterval(true, INT_N_ONE, false,
				INT_ZERO, true);
		Interval interval2 = numberFactory.newInterval(true, INT_THREE, false,
				INT_SIX, true);
		Interval interval3 = numberFactory.newInterval(true, INT_SIX, false,
				INT_TEN, true);
		Interval expectedInterval = numberFactory.newInterval(true, INT_N_ONE,
				false, INT_NINE, false);
		IntervalUnionSet set = new IntervalUnionSet(interval1, interval2,
				interval3);
		IntervalUnionSet expected = new IntervalUnionSet(expectedInterval);
		IntervalUnionSet actual = new IntervalUnionSet(
				set.intervalOverApproximation());

		p(DEBUG, expected.toString());
		p(DEBUG, actual.toString());
		assertEquals(expected.toString(), actual.toString());
	}

	@Test
	public void multiply_one_with_univ() {
		IntervalUnionSet int_univ_set = (IntervalUnionSet) rangeFactory
				.universalSet(true);
		IntervalUnionSet rat_univ_set = (IntervalUnionSet) rangeFactory
				.universalSet(false);
		IntervalUnionSet int_one_set = (IntervalUnionSet) rangeFactory
				.singletonSet(INT_ONE);
		IntervalUnionSet rat_one_set = (IntervalUnionSet) rangeFactory
				.singletonSet(RAT_ONE);
		IntervalUnionSet int_actual = ((IntervalUnionSet) rangeFactory
				.multiply(int_one_set, int_univ_set));
		IntervalUnionSet int_expected = ((IntervalUnionSet) rangeFactory
				.universalSet(true));
		IntervalUnionSet rat_actual = ((IntervalUnionSet) rangeFactory
				.multiply(rat_one_set, rat_univ_set));
		IntervalUnionSet rat_expected = ((IntervalUnionSet) rangeFactory
				.universalSet(false));
		assertEquals(int_actual, int_expected);
		assertEquals(rat_actual, rat_expected);
	}

	@Test
	public void symbolicRepresentationIntegerTest() {
		DEBUG = true;

		Interval interval0 = numberFactory.newInterval(true,
				numberFactory.negativeInfinityInteger(), true, INT_N_ONE,
				false);
		Interval interval1 = numberFactory.newInterval(true, INT_ONE, false,
				INT_TWO, false);
		Interval interval2 = numberFactory.newInterval(true, INT_FOUR, false,
				INT_FIVE, false);
		Interval interval3 = numberFactory.newInterval(true, INT_SEVEN, false,
				numberFactory.positiveInfinityInteger(), true);
		Interval interval4 = numberFactory.newInterval(true, INT_EIGHT, false,
				INT_SEVEN, true);
		IntervalUnionSet intervalUnionSet = new IntervalUnionSet(interval1,
				interval2, interval3, interval0, interval4);

		p(DEBUG, "set = " + intervalUnionSet);

		BooleanExpression result = intervalUnionSet
				.symbolicRepresentation(INT_X, universe);

		p(DEBUG, "symbolic expression = " + result);

		// below is the expected answer.
		BooleanExpression xNotEqualSix = universe
				.not(universe.equals(INT_X, universe.number(INT_SIX)));
		BooleanExpression xNotEqualThree = universe
				.not(universe.equals(INT_X, universe.number(INT_THREE)));
		BooleanExpression xNotEqualZero = universe
				.not(universe.equals(INT_X, universe.number(INT_ZERO)));

		assertEquals(universe.and(
				Arrays.asList(xNotEqualZero, xNotEqualThree, xNotEqualSix)),
				result);
	}

	@Test
	public void symbolicRepresentationRealTest() {
		DEBUG = true;

		Interval interval0 = numberFactory.newInterval(false,
				numberFactory.negativeInfinityRational(), true, RAT_ZERO,
				false);
		Interval interval1 = numberFactory.newInterval(false, RAT_ONE, true,
				RAT_FOUR, true); // (1, 4)
		Interval interval2 = numberFactory.newInterval(false, RAT_FOUR, true,
				RAT_FIVE, true); // (4, 5)
		// Interval interval3 = numberFactory.newInterval(false,
		// numberFactory.negativeInfinityRational(), true, RAT_ZERO, false);

		IntervalUnionSet intervalUnionSet = new IntervalUnionSet(interval1,
				interval2, interval0);

		p(DEBUG, "set = " + intervalUnionSet);

		BooleanExpression result = intervalUnionSet
				.symbolicRepresentation(RAT_X, universe);

		p(DEBUG, "symbolic expression = " + result);

		BooleanExpression gtOne = universe.lessThan(universe.number(RAT_ONE),
				RAT_X);
		BooleanExpression leFive = universe.lessThan(RAT_X,
				universe.number(RAT_FIVE));
		BooleanExpression xNotEqualFour = universe
				.not(universe.equals(RAT_X, universe.number(RAT_FOUR)));
		BooleanExpression leZero = universe.lessThanEquals(RAT_X,
				universe.number(RAT_ZERO));

		assertEquals(
				universe.or(leZero,
						universe.and(
								Arrays.asList(gtOne, leFive, xNotEqualFour))),
				result);
	}

}
