/*******************************************************************************
 * Copyright (c) 2013 Stephen F. Siegel, University of Delaware.
 * 
 * This file is part of SARL.
 * 
 * SARL is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free
 * Software Foundation, either version 3 of the License, or (at your option) any
 * later version.
 * 
 * SARL is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE. See the GNU Lesser General Public License for more
 * details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with SARL. If not, see <http://www.gnu.org/licenses/>.
 ******************************************************************************/
package edu.udel.cis.vsl.sarl.number.real;

import java.io.PrintWriter;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.util.BinaryOperator;

/**
 * An implementation of number factory based on infinite precision real
 * arithmetic.
 */
public class RealNumberFactory implements NumberFactory {

	/**
	 * Static variable for the positive integer number
	 */
	private static IntegerNumber INT_POS_INFINITY = new RealIntegerInfinity(
			true);

	/**
	 * Static variable for the negative integer number
	 */
	private static IntegerNumber INT_NEG_INFINITY = new RealIntegerInfinity(
			false);

	/**
	 * Static variable for the positive rational number
	 */
	private static RationalNumber RAT_POS_INFINITY = new RealRationalInfinity(
			true);

	/**
	 * Static variable for the negative rational number
	 */
	private static RationalNumber RAT_NEG_INFINITY = new RealRationalInfinity(
			false);

	/**
	 * Static variable represents the status of two {@link Interval}s <br>
	 * <code>LEFT_DISJOINTED</code> means the first {@link Interval} is on the
	 * left side of the second one, and they have no intersection.
	 */
	private static int LEFT_DISJOINTED = -3;

	/**
	 * Static variable represents the status of two {@link Interval}s <br>
	 * <code>RIGHT_DISJOINTED</code> means the first {@link Interval} is on the
	 * right side of the second one, and they have no intersection.
	 */
	private static int RIGHT_DISJOINTED = 3;

	/**
	 * Static variable represents the status of two {@link Interval}s <br>
	 * <code>LEFT_INTERSECTED</code> means the first {@link Interval} is on the
	 * left side of the second one, and they have a intersection.
	 */
	private static int LEFT_INTERSECTED = -2;

	/**
	 * Static variable represents the status of two {@link Interval}s <br>
	 * <code>RIGHT_INTERSECTED</code> means the first {@link Interval} is on the
	 * right side of the second one, and they have a intersection.
	 */
	private static int RIGHT_INTERSECTED = 2;

	/**
	 * Static variable represents the status of two {@link Interval}s <br>
	 * <code>CONTAINED_IN_INTERVAL1</code> means the first {@link Interval}
	 * contains the second one.
	 */
	private static int CONTAINED_IN_INTERVAL1 = -1;

	/**
	 * Static variable represents the status of two {@link Interval}s <br>
	 * <code>CONTAINED_IN_INTERVAL2</code> means the second {@link Interval}
	 * contains the first one.
	 */
	private static int CONTAINED_IN_INTERVAL2 = 1;

	/**
	 * Static variable represents the status of two {@link Interval}s <br>
	 * <code>EXACTLY_SAME</code> means the first {@link Interval} is exactly
	 * same with the second one.
	 */
	private static int EXACTLY_SAME = 0;

	private Map<BigInteger, RealInteger> integerMap = new HashMap<BigInteger, RealInteger>();

	private Map<RationalKey, RealRational> rationalMap = new HashMap<RationalKey, RealRational>();

	/**
	 * Private fields stores {@link IntegerNumber} frequently used. <br>
	 * 
	 */
	private IntegerNumber zeroInteger, oneInteger, tenInteger;

	/**
	 * Private fields stores {@link RationalNumber} frequently used. <br>
	 */
	private RationalNumber zeroRational, oneRational;

	private BinaryOperator<IntegerNumber> multiplier;

	private Exponentiator<IntegerNumber> exponentiator;

	/**
	 * The empty integer interval: (0, 0).
	 */
	private Interval emptyIntegerInterval;

	/**
	 * The empty real interval: (0.0, 0.0).
	 */
	private Interval emptyRationalInterval;

	/**
	 * The universal integer interval: (-infi, +infi).
	 */
	private Interval universalIntegerInterval;

	/**
	 * The universal real interval: (-infi, +infi).
	 */
	private Interval universalRationalInterval;

	/**
	 * The integer interval represents exactly zero: [0, 0].
	 */
	private Interval zeroIntegerInterval;

	/**
	 * The real interval interval represents exactly zero: [0.0, 0.0].
	 */
	private Interval zeroRationalInterval;

	/**
	 * Uses a new factory to multiply two integer arguments.
	 */
	class IntMultiplier implements BinaryOperator<IntegerNumber> {
		private RealNumberFactory factory;

		IntMultiplier(RealNumberFactory factory) {
			this.factory = factory;
		}

		@Override
		public IntegerNumber apply(IntegerNumber arg0, IntegerNumber arg1) {
			return factory.multiply(arg0, arg1);
		}

	}

	public RealNumberFactory() {
		zeroInteger = integer(BigInteger.ZERO);
		oneInteger = integer(BigInteger.ONE);
		tenInteger = integer(BigInteger.TEN);
		zeroRational = fraction(zeroInteger, oneInteger);
		oneRational = fraction(oneInteger, oneInteger);
		multiplier = new IntMultiplier(this);
		emptyIntegerInterval = new CommonInterval(true, zeroInteger, true,
				zeroInteger, true);
		emptyRationalInterval = new CommonInterval(false, zeroRational, true,
				zeroRational, true);
		zeroIntegerInterval = new CommonInterval(true, zeroInteger, false,
				zeroInteger, false);
		zeroRationalInterval = new CommonInterval(false, zeroRational, false,
				zeroRational, false);
		universalIntegerInterval = new CommonInterval(true, INT_NEG_INFINITY,
				true, INT_POS_INFINITY, true);
		universalRationalInterval = new CommonInterval(false, RAT_NEG_INFINITY,
				true, RAT_POS_INFINITY, true);
	}

	@Override
	/**
	 * See interface javadoc. Returns absolute value of a Number.
	 * 
	 */
	public Number abs(Number number) {
		if (number.signum() < 0) {
			return negate(number);
		} else {
			return number;
		}
	}

	@Override
	/**
	 * See interface. This takes in a BigInteger, and returns an IntegerNumber.
	 * 
	 */
	public RealInteger integer(BigInteger big) {
		RealInteger oldValue = integerMap.get(big);

		if (oldValue != null) {
			return oldValue;
		} else {
			RealInteger newValue = new RealInteger(big);

			integerMap.put(big, newValue);
			return newValue;
		}
	}

	@Override
	/**
	 * Returns the BigInteger interpretation of a long.
	 */
	public RealInteger integer(long value) {
		return integer(BigInteger.valueOf(value));
	}

	@Override
	/**
	 * Returns a RealRational formed from given BigInteger numerator and
	 * denominator. Detects and protects against zero valued denominators. Moves
	 * any negation to the numerator. Simplifies the RealRational If numerator
	 * equals zero, simplifies to 0/1 regardless of denominator.
	 */
	public RealRational rational(BigInteger numerator, BigInteger denominator) {
		int signum = denominator.signum();
		RationalKey key;
		RealRational oldValue;

		if (signum == 0) {
			throw new ArithmeticException("Division by 0");
		}
		// ensures any negation is in numerator
		// protects signum method in RealRational
		if (signum < 0) {
			numerator = numerator.negate();
			denominator = denominator.negate();
		}
		// canonical form for 0 is 0/1 :
		if (numerator.signum() == 0) {
			denominator = BigInteger.ONE;
		} else if (!denominator.equals(BigInteger.ONE)) {
			BigInteger gcd = numerator.gcd(denominator);

			if (!gcd.equals(BigInteger.ONE)) {
				numerator = numerator.divide(gcd);
				denominator = denominator.divide(gcd);
			}
		}
		key = new RationalKey(numerator, denominator);
		oldValue = rationalMap.get(key);
		if (oldValue != null) {
			return oldValue;
		} else {
			RealRational newValue = new RealRational(numerator, denominator);

			rationalMap.put(key, newValue);
			return newValue;
		}
	}

	@Override
	/**
	 * An efficient way of adding two RationalNumbers.
	 */
	public RationalNumber add(RationalNumber arg0, RationalNumber arg1) {
		if (arg0.isInfinite()) {
			if (arg1.isInfinite()) {
				if (arg0.signum() == arg1.signum())
					return arg0;
				else
					throw new ArithmeticException(
							"The sum of the positive infinity and the negative infinity is indeterminate.");
			} else {
				return arg0;
			}
		} else if (arg1.isInfinite()) {
			return arg1;
		}

		RealRational x = (RealRational) arg0;
		RealRational y = (RealRational) arg1;

		return rational(
				x.numerator().multiply(y.denominator())
						.add(x.denominator().multiply(y.numerator())),
				x.denominator().multiply(y.denominator()));
	}

	@Override
	/**
	 * An override of the add function to add two integers with precision
	 */
	public IntegerNumber add(IntegerNumber arg0, IntegerNumber arg1) {
		if (arg0.isInfinite()) {
			if (arg1.isInfinite()) {
				if (arg0.signum() == arg1.signum())
					return arg0;
				else
					// TODO: use the SARLException to replace others.
					throw new SARLException(
							"The sum of the positive infinity and the negative infinity is indeterminate.");
			} else {
				return arg0;
			}
		} else if (arg1.isInfinite()) {
			return arg1;
		}

		RealInteger x = (RealInteger) arg0;
		RealInteger y = (RealInteger) arg1;

		return integer(x.value().add(y.value()));
	}

	@Override
	/**
	 * returns an Integer of the quotient of numerator and denominator
	 */
	public IntegerNumber ceil(RationalNumber arg0) {
		if (arg0.isInfinite())
			if (arg0.signum() > 0)
				return INT_POS_INFINITY;
			else
				return INT_NEG_INFINITY;

		RealRational x = (RealRational) arg0;
		BigInteger numerator = x.numerator();
		BigInteger denominator = x.denominator();
		BigInteger quotient = numerator.divide(denominator);

		if (numerator.signum() <= 0) {
			return integer(quotient);
		} else {
			BigInteger modulus = numerator.mod(denominator);

			if (modulus.equals(BigInteger.ZERO)) {
				return integer(quotient);
			} else {
				return integer(quotient.add(BigInteger.ONE));
			}
		}
	}

	@Override
	/**
	 * Determines the larger of two rationals returns 1 when the first argument
	 * is greater returns 0 when the rationals are equal returns -1 when the
	 * second argument is greater
	 */
	public int compare(RationalNumber arg0, RationalNumber arg1) {
		return arg0.numericalCompareTo(arg1);
	}

	@Override
	/**
	 * Determines the larger of two integers returns 1 when first argument is
	 * greater returns 0 when arguments are equal returns -1 when second
	 * argument is greater
	 */
	public int compare(IntegerNumber arg0, IntegerNumber arg1) {
		return arg0.numericalCompareTo(arg1);
	}

	@Override
	/**
	 * Takes two numbers as arguments and determines how to compare them based
	 * on their more specific identities.
	 */
	public int compare(Number arg0, Number arg1) {
		if (arg0 instanceof IntegerNumber && arg1 instanceof IntegerNumber) {
			return compare((IntegerNumber) arg0, (IntegerNumber) arg1);
		} else if (arg0 instanceof RationalNumber
				&& arg1 instanceof RationalNumber) {
			return compare((RationalNumber) arg0, (RationalNumber) arg1);
		} else {
			return compare(rational(arg0), rational(arg1));
		}
	}

	@Override
	/**
	 * Returns the integer form of the denominator of a rational
	 */
	public IntegerNumber denominator(RationalNumber arg0) {
		return integer(((RealRational) arg0).denominator());
	}

	@Override
	/**
	 * An override of the divide method to accommodate rationals
	 */
	public RationalNumber divide(RationalNumber arg0, RationalNumber arg1) {
		if (arg0.isInfinite() && arg1.isInfinite())
			throw new ArithmeticException(
					"The division of two infinite numbers is indeterminate.");
		if (arg0.isInfinite())
			if (arg1.isZero())
				throw new ArithmeticException("Divided by Zero");
			else
				return infiniteRational(arg0.signum() == arg1.signum());
		if (arg1.isInfinite())
			return zeroRational;

		RealRational x = (RealRational) arg0;
		RealRational y = (RealRational) arg1;

		return rational(x.numerator().multiply(y.denominator()),
				x.denominator().multiply(y.numerator()));
	}

	@Override
	/**
	 * An override of the divide method to maintain precision
	 */
	public IntegerNumber divide(IntegerNumber arg0, IntegerNumber arg1) {
		if (arg0.isInfinite() && arg1.isInfinite())
			throw new ArithmeticException(
					"The division of two infinite numbers is indeterminate.");
		if (arg0.isInfinite())
			if (arg1.isZero())
				throw new ArithmeticException("Divided by Zero");
			else
				return infiniteInteger(arg0.signum() == arg1.signum());
		if (arg1.isInfinite())
			return zeroInteger;

		RealInteger x = (RealInteger) arg0;
		RealInteger y = (RealInteger) arg1;

		return integer(x.value().divide(y.value()));
	}

	@Override
	/**
	 * Modulates argument one by argument two and returns the modulated integer
	 */
	public IntegerNumber mod(IntegerNumber arg0, IntegerNumber arg1) {
		RealInteger x = (RealInteger) arg0;
		RealInteger y = (RealInteger) arg1;

		if (arg0.isInfinite() || arg1.isInfinite())
			throw new IllegalArgumentException(
					"Arguments of the Modulus operation is infinite.");
		if (y.signum() == 0)
			throw new IllegalArgumentException("Modulus divisor is zero");
		if (y.signum() < 0)
			if (x.signum() < 0)
				return negate(integer(x.value().abs().mod(y.value().abs())));
			else
				return integer(x.value().mod(y.value().abs()));
		else if (x.signum() < 0)
			return negate(integer(x.value().abs().mod(y.value())));
		return integer(x.value().mod(y.value()));
	}

	@Override
	/**
	 * Calculates the mathematical floor of a rational number
	 */
	public IntegerNumber floor(RationalNumber arg0) {
		if (arg0.isInfinite())
			if (arg0.signum() > 0)
				return INT_POS_INFINITY;
			else
				return INT_NEG_INFINITY;

		RealRational x = (RealRational) arg0;
		BigInteger numerator = x.numerator();
		BigInteger denominator = x.denominator();
		BigInteger quotient = numerator.divide(denominator);

		if (numerator.signum() >= 0) {
			return integer(quotient);
		} else {
			BigInteger modulus = numerator.mod(denominator);

			if (modulus.equals(BigInteger.ZERO)) {
				return integer(quotient);
			} else {
				return integer(quotient.subtract(BigInteger.ONE));
			}
		}
	}

	@Override
	/**
	 * Creates and returns rationals from two integers
	 */
	public RationalNumber fraction(IntegerNumber numerator,
			IntegerNumber denominator) {
		if (numerator.isInfinite() && denominator.isInfinite())
			throw new ArithmeticException(
					"The division of two infinite numbers is indeterminate.");
		if (numerator.isInfinite())
			if (denominator.isZero())
				throw new ArithmeticException("Divided by Zero");
			else
				return numerator.signum() == denominator.signum()
						? RAT_POS_INFINITY : RAT_NEG_INFINITY;
		if (denominator.isInfinite())
			return zeroRational;

		RealInteger x = (RealInteger) numerator;
		RealInteger y = (RealInteger) denominator;

		return rational(x.value(), y.value());
	}

	@Override
	/**
	 * creates and returns integers from strings
	 */
	public IntegerNumber integer(String string) {
		return integer(new BigInteger(string));
	}

	@Override
	/**
	 * creates and returns rationals from integers by giving them one as a
	 * denominator
	 */
	public RationalNumber integerToRational(IntegerNumber integer) {
		if (integer.isInfinite())
			return integer.signum() > 0 ? RAT_POS_INFINITY : RAT_NEG_INFINITY;

		RealInteger x = (RealInteger) integer;

		return rational(x.value(), BigInteger.ONE);
	}

	@Override
	/**
	 * Returns an integer from rationals that are integral
	 */
	public IntegerNumber integerValue(RationalNumber arg0) {
		RealRational x = (RealRational) arg0;

		if (!isIntegral(arg0)) {
			throw new ArithmeticException("Non-integral number: " + arg0);
		}
		return integer(x.numerator());
	}

	@Override
	/**
	 * Overrides the multiply class to deal with rationals
	 */
	public RationalNumber multiply(RationalNumber arg0, RationalNumber arg1) {
		if (arg0.isInfinite() || arg1.isInfinite())
			if (arg0.isZero() || arg1.isZero())
				throw new ArithmeticException(
						"The multiplication of a infinity and a zero is indeterminate.");
			else
				return infiniteRational(arg0.signum() == arg1.signum());

		RealRational x = (RealRational) arg0;
		RealRational y = (RealRational) arg1;

		return rational(x.numerator().multiply(y.numerator()),
				x.denominator().multiply(y.denominator()));
	}

	@Override
	/**
	 * Overrides the multiply class to maintain precision
	 */
	public IntegerNumber multiply(IntegerNumber arg0, IntegerNumber arg1) {
		if (arg0.isInfinite() || arg1.isInfinite())
			if (arg0.isZero() || arg1.isZero())
				throw new ArithmeticException(
						"The multiplication of a infinity and a zero is indeterminate.");
			else
				return infiniteInteger(arg0.signum() == arg1.signum());

		RealInteger x = (RealInteger) arg0;
		RealInteger y = (RealInteger) arg1;

		return integer(x.value().multiply(y.value()));
	}

	@Override
	/**
	 * negates the numerator of a rational number
	 */
	public RationalNumber negate(RationalNumber arg0) {
		if (arg0.isInfinite())
			return infiniteRational(arg0.signum() < 0);

		RealRational x = (RealRational) arg0;

		return rational(x.numerator().negate(), x.denominator());
	}

	@Override
	/**
	 * negates an integer
	 */
	public IntegerNumber negate(IntegerNumber arg0) {
		if (arg0.isInfinite())
			return infiniteInteger(arg0.signum() < 0);

		RealInteger x = (RealInteger) arg0;

		return integer(x.value().negate());
	}

	@Override
	/**
	 * Determines how to represent a given string based on decimal point
	 * position returns an integer if a decimal point is not found returns a
	 * rational if a decimal point is found
	 */
	public Number number(String string) {
		int decimalPosition = string.indexOf('.');

		if (decimalPosition < 0) {
			return integer(string);
		} else {
			return rational(string);
		}
	}

	@Override
	/**
	 * Returns an integer from a rational number
	 */
	public IntegerNumber numerator(RationalNumber arg0) {
		if (arg0.isInfinite())
			if (arg0.signum() > 0)
				return INT_POS_INFINITY;
			else
				return INT_NEG_INFINITY;
		return integer(((RealRational) arg0).numerator());
	}

	@Override
	/**
	 * returns an integer representation of one
	 */
	public IntegerNumber oneInteger() {
		return oneInteger;
	}

	@Override
	/**
	 * returns a rational representation of one
	 */
	public RationalNumber oneRational() {
		return oneRational;
	}

	@Override
	/**
	 * Returns a rationalNumber crafted from two string arguments
	 */
	public RationalNumber rational(String string) {
		int ePosition = string.indexOf('e');

		if (ePosition < 0) {
			return rationalWithoutE(string);
		} else {
			String left = string.substring(0, ePosition);
			RationalNumber result = rationalWithoutE(left);
			int length = string.length();
			boolean positive;
			String right;
			IntegerNumber exponent, power;
			RationalNumber powerReal;

			if (exponentiator == null)
				exponentiator = new Exponentiator<IntegerNumber>(multiplier,
						oneInteger);
			if (ePosition + 1 < length && string.charAt(ePosition + 1) == '+') {
				right = string.substring(ePosition + 2);
				positive = true;
			} else if (ePosition + 1 < length
					&& string.charAt(ePosition + 1) == '-') {
				right = string.substring(ePosition + 2);
				positive = false;
			} else {
				right = string.substring(ePosition + 1);
				positive = true;
			}
			exponent = integer(right);
			power = exponentiator.exp(tenInteger, exponent);
			powerReal = rational(power);
			if (!positive)
				result = divide(result, powerReal);
			else
				result = multiply(result, powerReal);
			return result;
		}

	}

	/**
	 * Returns a RationalNumber generated from two strings while simultaneously
	 * eliminating the value E from the strings
	 */
	public RationalNumber rationalWithoutE(String string) {
		String left, right; // substrings to left/right of decimal point
		int decimalPosition = string.indexOf('.');
		int rightLength;
		String powerOfTen = "1";

		if (decimalPosition < 0) { // no decimal
			left = string;
			right = "";
		} else if (decimalPosition == 0) {
			left = "";
			right = string.substring(1, string.length());
		} else {
			left = string.substring(0, decimalPosition);
			right = string.substring(decimalPosition + 1, string.length());
		}
		rightLength = right.length();
		for (int j = 0; j < rightLength; j++)
			powerOfTen += "0";
		return rational(new BigInteger(left + right),
				new BigInteger(powerOfTen));
	}

	@Override
	/**
	 * Determines how to represent two numbers as a RationalNumber based on
	 * their more specific classes
	 */
	public RationalNumber rational(Number number) {
		if (number instanceof RationalNumber) {
			return (RationalNumber) number;
		} else if (number instanceof IntegerNumber) {
			return integerToRational((IntegerNumber) number);
		}
		throw new IllegalArgumentException("Unknown type of number: " + number);
	}

	@Override
	/**
	 * An override of the subtract method to deal with RationalNumbers
	 */
	public RationalNumber subtract(RationalNumber arg0, RationalNumber arg1) {
		if (arg0.isInfinite()) {
			if (arg1.isInfinite()) {
				if (arg0.signum() != arg1.signum())
					return arg0;
				else
					throw new ArithmeticException(
							"The sum of the positive infinity and the negative infinity is indeterminate.");
			} else {
				return arg0;
			}
		} else if (arg1.isInfinite()) {
			return infiniteRational(arg1.signum() < 0);
		}

		return add(arg0, negate(arg1));
	}

	@Override
	/**
	 * An override of the subtract method to maintain precision
	 */
	public IntegerNumber subtract(IntegerNumber arg0, IntegerNumber arg1) {
		if (arg0.isInfinite()) {
			if (arg1.isInfinite()) {
				if (arg0.signum() != arg1.signum())
					return arg0;
				else
					throw new ArithmeticException(
							"The sum of the positive infinity and the negative infinity is indeterminate.");
			} else {
				return arg0;
			}
		} else if (arg1.isInfinite()) {
			return infiniteInteger(arg1.signum() < 0);
		}

		RealInteger x = (RealInteger) arg0;
		RealInteger y = (RealInteger) arg1;

		return integer(x.value().subtract(y.value()));
	}

	@Override
	/**
	 * Returns an integer representation of zero
	 */
	public IntegerNumber zeroInteger() {
		return zeroInteger;
	}

	@Override
	/**
	 * Returns a rational representation of zero
	 */
	public RationalNumber zeroRational() {
		return zeroRational;
	}

	@Override
	/**
	 * Determines if a rational is integral by seeing if its denominator equates
	 * to one
	 */
	public boolean isIntegral(RationalNumber arg0) {
		return !arg0.isInfinite() && arg0.denominator().equals(BigInteger.ONE);
	}

	@Override
	/**
	 * Returns an integer representation of a value
	 */
	public IntegerNumber integer(int value) {
		return integer("" + value);
	}

	@Override
	/**
	 * Determines how to properly negate a number based on its more specific
	 * class
	 */
	public Number negate(Number arg0) {
		if (arg0 instanceof IntegerNumber)
			return negate((IntegerNumber) arg0);
		else
			return negate((RationalNumber) arg0);
	}

	@Override
	/**
	 * Determines how to properly add two numbers based on their more specific
	 * classes
	 */
	public Number add(Number arg0, Number arg1) {
		if (arg0 instanceof IntegerNumber) {
			if (!(arg1 instanceof IntegerNumber))
				throw new IllegalArgumentException(
						"Mixed numeric types not allowed:\n" + arg0 + "\n"
								+ arg1);
			return add((IntegerNumber) arg0, (IntegerNumber) arg1);
		} else if (arg0 instanceof RationalNumber) {
			if (!(arg1 instanceof RationalNumber))
				throw new IllegalArgumentException(
						"Mixed numeric types not allowed:\n" + arg0 + "\n"
								+ arg1);
			return add((RationalNumber) arg0, (RationalNumber) arg1);
		} else {
			throw new IllegalArgumentException(
					"Unknown type of number: " + arg0);
		}
	}

	@Override
	/**
	 * Determines how to properly divide two numbers based on their more
	 * specific classes
	 */
	public Number divide(Number arg0, Number arg1) {
		if (arg0 instanceof IntegerNumber) {
			if (!(arg1 instanceof IntegerNumber))
				throw new IllegalArgumentException(
						"Mixed numeric types not allowed:\n" + arg0 + "\n"
								+ arg1);
			return divide((IntegerNumber) arg0, (IntegerNumber) arg1);
		} else if (arg0 instanceof RationalNumber) {
			if (!(arg1 instanceof RationalNumber))
				throw new IllegalArgumentException(
						"Mixed numeric types not allowed:\n" + arg0 + "\n"
								+ arg1);
			return divide((RationalNumber) arg0, (RationalNumber) arg1);
		} else {
			throw new IllegalArgumentException(
					"Unknown type of number: " + arg0);
		}
	}

	@Override
	/**
	 * Determines how to properly multiply two numbers based on their more
	 * specific classes
	 */
	public Number multiply(Number arg0, Number arg1) {
		if (arg0 instanceof IntegerNumber) {
			if (!(arg1 instanceof IntegerNumber))
				throw new IllegalArgumentException(
						"Mixed numeric types not allowed:\n" + arg0 + "\n"
								+ arg1);
			return multiply((IntegerNumber) arg0, (IntegerNumber) arg1);
		} else if (arg0 instanceof RationalNumber) {
			if (!(arg1 instanceof RationalNumber))
				throw new IllegalArgumentException(
						"Mixed numeric types not allowed:\n" + arg0 + "\n"
								+ arg1);
			return multiply((RationalNumber) arg0, (RationalNumber) arg1);
		} else {
			throw new IllegalArgumentException(
					"Unknown type of number: " + arg0);
		}
	}

	@Override
	/**
	 * Determines how to properly subtract two numbers based on their more
	 * specific classes
	 */
	public Number subtract(Number arg0, Number arg1) {
		if (arg0 instanceof IntegerNumber) {
			if (!(arg1 instanceof IntegerNumber))
				throw new IllegalArgumentException(
						"Mixed numeric types not allowed:\n" + arg0 + "\n"
								+ arg1);
			return subtract((IntegerNumber) arg0, (IntegerNumber) arg1);
		} else if (arg0 instanceof RationalNumber) {
			if (!(arg1 instanceof RationalNumber))
				throw new IllegalArgumentException(
						"Mixed numeric types not allowed:\n" + arg0 + "\n"
								+ arg1);
			return subtract((RationalNumber) arg0, (RationalNumber) arg1);
		} else {
			throw new IllegalArgumentException(
					"Unknown type of number: " + arg0);
		}
	}

	@Override
	/**
	 * Returns a RationalNumber incremented by one
	 */
	public RationalNumber increment(RationalNumber arg) {
		return add(arg, oneRational);
	}

	@Override
	/**
	 * Returns an IntegerNumber incremented by one
	 */
	public IntegerNumber increment(IntegerNumber arg) {
		return add(arg, oneInteger);
	}

	@Override
	/**
	 * Determines how to properly increment a number based on its more specific
	 * class
	 */
	public Number increment(Number arg) {
		if (arg instanceof IntegerNumber)
			return add((IntegerNumber) arg, oneInteger);
		return add((RationalNumber) arg, oneRational);
	}

	@Override
	/**
	 * Returns a RationalNumber decremented by one
	 */
	public RationalNumber decrement(RationalNumber arg) {
		return subtract(arg, oneRational);
	}

	@Override
	/**
	 * Returns an IntegerNumber decremented by one
	 */
	public IntegerNumber decrement(IntegerNumber arg) {
		return subtract(arg, oneInteger);
	}

	@Override
	/**
	 * Determines how to properly decrement a number based on its more specific
	 * class
	 */
	public Number decrement(Number arg) {
		if (arg instanceof IntegerNumber)
			return subtract((IntegerNumber) arg, oneInteger);
		return subtract((RationalNumber) arg, oneRational);
	}

	@Override
	/**
	 * Sends BigInteger representations of given IntegerNumbers to the gcd
	 * function
	 */
	public IntegerNumber gcd(IntegerNumber arg0, IntegerNumber arg1) {
		if (arg0.isInfinite() || arg1.isInfinite())
			throw new IllegalArgumentException(
					"Arguments of the gcd method cannot be a infinite number!");

		BigInteger value0 = ((RealInteger) arg0).value();
		BigInteger value1 = ((RealInteger) arg1).value();

		return integer(value0.gcd(value1));
	}

	@Override
	/**
	 * Determines and returns the lcm of two IntegerNumbers by dividing their
	 * product by their gcd
	 */
	public IntegerNumber lcm(IntegerNumber arg0, IntegerNumber arg1) {
		if (arg0.isInfinite() || arg1.isInfinite())
			throw new IllegalArgumentException(
					"Arguments of the lcm method cannot be a infinite number!");
		return divide(multiply(arg0, arg1), gcd(arg0, arg1));
	}

	/**
	 * A simple method to print a matrix of RationalNumbers to screen
	 * 
	 * @param out
	 * @param msg
	 * @param matrix
	 */
	public void printMatrix(PrintWriter out, String msg,
			RationalNumber[][] matrix) {
		out.println(msg);
		for (int i = 0; i < matrix.length; i++) {
			RationalNumber[] row = matrix[i];

			for (int j = 0; j < row.length; j++) {
				RationalNumber element = row[j];

				if (element.isInfinite())
					if (element.signum() > 0)
						out.print("+inf");
					else
						out.print("-inf");
				else
					out.print(element);
				out.print("  ");
			}
			out.println();
		}
		out.println();
		out.flush();
	}

	@Override
	/**
	 * Performs a gaussian elimination on the given RationalNumber matrix
	 * Maintains a boolean 'debug' for easy troubleshooting due to its complex
	 * nature
	 */
	public void gaussianElimination(RationalNumber[][] matrix) {
		int numRows = matrix.length;
		int numCols;
		int top = 0; // index of current top row
		int col = 0; // index of current left column
		int pivotRow = 0; // index of row containing the pivot
		RationalNumber pivot = zeroRational; // the value of the pivot
		int i = 0; // loop variable over rows of matrix
		int j = 0; // loop variable over columns of matrix
		boolean debug = false;
		PrintWriter out = new PrintWriter(System.out);

		if (numRows == 0)
			return;
		numCols = matrix[0].length;

		for (top = col = 0; top < numRows && col < numCols; top++, col++) {
			/*
			 * At this point we know that the submatarix consisting of the first
			 * top rows of A is in reduced row-echelon form. We will now
			 * consider the submatrix B consisting of the remaining rows. We
			 * know, additionally, that the first col columns of B are all zero.
			 */

			if (debug)
				out.println("Top: " + top + "\n");

			/*
			 * Step 1: Locate the leftmost column of B that does not consist
			 * entirely of zeros, if one exists. The top nonzero entry of this
			 * column is the pivot.
			 */

			pivot = zeroRational;
			pivotSearch: for (; col < numCols; col++) {
				for (pivotRow = top; pivotRow < numRows; pivotRow++) {
					pivot = matrix[pivotRow][col];
					if (!pivot.isZero())
						break pivotSearch;
				}
			}

			if (col >= numCols) {
				break;
			}

			/*
			 * At this point we are guaranteed that pivot = A[pivotRow,col] is
			 * nonzero. We also know that all the columns of B to the left of
			 * col consist entirely of zeros.
			 */

			if (debug) {
				out.println("Step 1 result: col=" + col + ", pivotRow="
						+ pivotRow + ", pivot=" + pivot + "\n");
			}

			/*
			 * Step 2: Interchange the top row with the pivot row, if necessary,
			 * so that the entry at the top of the column found in Step 1 is
			 * nonzero.
			 */

			if (pivotRow != top) {
				RationalNumber[] tmpRow = matrix[top];

				matrix[top] = matrix[pivotRow];
				matrix[pivotRow] = tmpRow;
			}

			if (debug) {
				printMatrix(out, "Step 2 result:\n", matrix);
			}

			/*
			 * At this point we are guaranteed that A[top,col] = pivot is
			 * nonzero. Also, we know that (i>=top and j<col) implies A[i,j] =
			 * 0.
			 */

			/*
			 * Step 3: Divide the top row by pivot in order to introduce a
			 * leading 1.
			 */

			if (!pivot.isOne())
				for (j = col; j < numCols; j++) {
					matrix[top][j] = divide(matrix[top][j], pivot);
				}

			if (debug) {
				printMatrix(out, "Step 3 result:\n", matrix);
			}

			/*
			 * At this point we are guaranteed that A[top,col] is 1.0, assuming
			 * that floating point arithmetic guarantees that a/a equals 1.0 for
			 * any nonzero double a.
			 */

			/*
			 * Step 4: Add suitable multiples of the top row to all other rows
			 * so that all entries above and below the leading 1 become zero.
			 */

			for (i = 0; i < numRows; i++) {
				if (i != top) {
					RationalNumber tmp = matrix[i][col];
					for (j = col; j < numCols; j++) {
						matrix[i][j] = subtract(matrix[i][j],
								multiply(tmp, matrix[top][j]));
					}
				}
			}

			if (debug) {
				printMatrix(out, "Step 4 result:\n", matrix);
			}
		}
	}

	@Override
	public Interval emptyIntegerInterval() {
		return emptyIntegerInterval;
	}

	@Override
	public Interval emptyRealInterval() {
		return emptyRationalInterval;
	}

	@Override
	public Interval universalIntegerInterval() {
		return universalIntegerInterval;
	}

	@Override
	public Interval universalRealInterval() {
		return universalRationalInterval;
	}

	@Override
	public Interval newInterval(boolean isIntegral, Number lower,
			boolean strictLower, Number upper, boolean strictUpper) {
		assert (isIntegral == lower instanceof IntegerNumber);
		assert (isIntegral == upper instanceof IntegerNumber);
		if (isIntegral) {
			// Adjust the strict and bound for integral intervals
			if (strictLower && !lower.isInfinite()) {
				lower = add(lower, oneInteger);
				strictLower = false;
			}
			if (strictUpper && !upper.isInfinite()) {
				upper = subtract(upper, oneInteger);
				strictUpper = false;
			}
		}

		boolean isValid = true;

		if (lower.isInfinite()) {
			if (upper.isInfinite())
				isValid = isValid && upper.signum() > 0;
			isValid = isValid && lower.signum() < 0;
		} else {
			if (upper.isInfinite())
				isValid = isValid && upper.signum() > 0;
			else {
				int compareUpperLower = upper.numericalCompareTo(lower);

				isValid = isValid && (compareUpperLower >= 0)
						&& (compareUpperLower != 0
								|| (!strictLower && !strictUpper));
			}
		}

		if (isValid)
			if (lower.isInfinite() && upper.isInfinite())
				return isIntegral ? universalIntegerInterval
						: universalRationalInterval;
			else
				return new CommonInterval(isIntegral, lower, strictLower, upper,
						strictUpper);
		else
			return isIntegral ? emptyIntegerInterval : emptyRationalInterval;
	}

	@Override
	public Interval intersection(Interval i1, Interval i2) {
		assert i1 != null && i2 != null;

		boolean isIntegral = i1.isIntegral();

		assert isIntegral == i2.isIntegral();

		Number lo1 = i1.lower();
		Number lo2 = i2.lower();
		Number up1 = i1.upper();
		Number up2 = i2.upper();
		Number lo, up;
		boolean sl1 = i1.strictLower();
		boolean sl2 = i2.strictLower();
		boolean su1 = i1.strictUpper();
		boolean su2 = i2.strictUpper();
		boolean sl, su;
		int compareLo = lo1.numericalCompareTo(lo2);
		int compareUp = up1.numericalCompareTo(up2);

		// Get the greater lower bound
		if (compareLo < 0) {
			lo = lo2;
			sl = sl2;
		} else if (compareLo == 0) {
			lo = lo1;
			sl = sl1 || sl2;
		} else {
			lo = lo1;
			sl = sl1;
		}
		// Get the lesser upper bound
		if (compareUp > 0) {
			up = up2;
			su = su2;
		} else if (compareUp == 0) {
			up = up1;
			su = su1 || su2;
		} else {
			up = up1;
			su = su1;
		}
		return newInterval(isIntegral, lo, sl, up, su);
	}

	@Override
	public void union(Interval i1, Interval i2, IntervalUnion result) {
		assert i1 != null && i2 != null && result != null;

		boolean isIntegral = i1.isIntegral();

		assert i1.isIntegral() == i2.isIntegral();

		if (i1.isEmpty() || i2.isUniversal()) {
			// Exactly a single interval
			result.status = 0;
			result.union = i2;
			return;
		} else if (i2.isEmpty() || i1.isUniversal()) {
			// Exactly a single interval
			result.status = 0;
			result.union = i1;
			return;
		} else {
			Number lo2 = i2.lower();
			Number up1 = i1.upper();
			boolean sl2 = i2.strictLower();
			boolean su1 = i1.strictUpper();
			boolean su2 = i2.strictUpper();
			int compareUp1Lo2 = up1.numericalCompareTo(lo2);

			if (compareUp1Lo2 > 0) {
				Number lo1 = i1.lower();
				Number up2 = i2.upper();
				boolean sl1 = i1.strictLower();
				int compareLo1Up2 = lo1.numericalCompareTo(up2);

				if (compareLo1Up2 < 0) {
					// Intersected
					Number lo = isIntegral ? INT_NEG_INFINITY
							: RAT_NEG_INFINITY;
					Number up = isIntegral ? INT_POS_INFINITY
							: RAT_POS_INFINITY;
					boolean sl = false, su = false;
					int compareLo1Lo2 = lo1.numericalCompareTo(lo2);
					int compareUp1Up2 = up1.numericalCompareTo(up2);

					if (compareLo1Lo2 < 0) { // lo1<lo2
						lo = lo1;
						sl = sl1;
					} else if (compareLo1Lo2 == 0) {
						lo = lo1;
						sl = sl1 && sl2;
					} else {
						lo = lo2;
						sl = sl2;
					}
					if (compareUp1Up2 < 0) {
						up = up2;
						su = su2;
					} else if (compareUp1Up2 == 0) {
						up = up1;
						su = su1 && su2;
					} else {
						up = up1;
						su = su1;
					}
					result.status = 0;
					result.union = newInterval(isIntegral, lo, sl, up, su);
					return;
				} else if (compareLo1Up2 == 0 && (!sl1 || !su2)) {
					// Connected
					result.status = 0;
					result.union = newInterval(isIntegral, lo2, sl2, up1, su1);
					return;
				} else {
					// Disjoint
					result.status = 1;
					result.union = null;
					return;
				}
			} else if (compareUp1Lo2 == 0 && (!su1 || !su2)) {
				// Connected
				result.status = 0;
				result.union = newInterval(isIntegral, i1.lower(),
						i1.strictLower(), i2.upper(), su2);
				return;
			} else {
				// Disjoint
				result.status = -1;
				result.union = null;
				return;
			}
		}
	}

	@Override
	public Interval affineTransform(Interval itv, Number a, Number b) {
		assert itv != null && a != null && b != null;
		assert !a.isInfinite() && !b.isInfinite();

		boolean isIntegral = itv.isIntegral();

		assert isIntegral == a instanceof IntegerNumber;
		assert isIntegral == b instanceof IntegerNumber;

		if (itv.isEmpty())
			return isIntegral ? emptyIntegerInterval : emptyRationalInterval;

		Number lo = itv.lower();
		Number up = itv.upper();
		boolean sl = itv.strictLower();
		boolean su = itv.strictUpper();

		// New upper and lower of result.union.
		if (a.signum() == 0)
			return singletonInterval(b);
		lo = add(multiply(lo, a), b);
		up = add(multiply(up, a), b);
		if (a.signum() < 0)
			return newInterval(isIntegral, up, su, lo, sl);
		else
			return newInterval(isIntegral, lo, sl, up, su);
	}

	@Override
	public int compare(Interval i1, Interval i2) {
		assert i1 != null && i2 != null;

		boolean isIntegral = i1.isIntegral();

		assert isIntegral == i2.isIntegral();

		Number lo1 = i1.lower(), lo2 = i2.lower();
		Number up1 = i1.upper(), up2 = i2.upper();
		boolean sl1 = i1.strictLower(), sl2 = i2.strictLower();
		boolean su1 = i1.strictUpper(), su2 = i2.strictUpper();
		int compareL1L2 = lo1.numericalCompareTo(lo2);
		int compareU1U2 = up1.numericalCompareTo(up2);

		if (i1.isEmpty() && i2.isEmpty()) {
			return EXACTLY_SAME;
		} else if (i1.isEmpty()) {
			return CONTAINED_IN_INTERVAL2;
		} else if (i2.isEmpty()) {
			return CONTAINED_IN_INTERVAL1;
		}
		if (compareL1L2 < 0) {
			if (compareU1U2 < 0) {
				int compareU1L2 = up1.numericalCompareTo(lo2);

				if (compareU1L2 < 0) {
					return LEFT_DISJOINTED;
				} else if (compareU1L2 > 0) {
					return LEFT_INTERSECTED;
				} else {
					if (!su1 && !sl2) {
						return LEFT_INTERSECTED;
					} else {
						return LEFT_DISJOINTED;
					}
				}
			} else if (compareU1U2 > 0) {
				return CONTAINED_IN_INTERVAL1;
			} else {
				int compareU1L2 = up1.numericalCompareTo(lo2);

				if (su1 && compareU1L2 == 0) {
					return LEFT_DISJOINTED;
				} else if (su1 && !su2 && compareU1L2 > 0) {
					return LEFT_INTERSECTED;
				} else {
					return CONTAINED_IN_INTERVAL1;
				}
			}
		} else if (compareL1L2 > 0) {
			if (compareU1U2 < 0) {
				return CONTAINED_IN_INTERVAL2;
			} else if (compareU1U2 > 0) {
				int compareL1U2 = lo1.numericalCompareTo(up2);

				if (compareL1U2 < 0) {
					return RIGHT_INTERSECTED;
				} else if (compareL1U2 > 0) {
					return RIGHT_DISJOINTED;
				} else {
					if (!sl1 && !su2) {
						return RIGHT_INTERSECTED;
					} else {
						return RIGHT_DISJOINTED;
					}
				}
			} else {
				int compareL1U2 = lo1.numericalCompareTo(up2);

				if (su2 && compareL1U2 == 0) {
					return RIGHT_DISJOINTED;
				} else if (!su1 && su2 && compareL1U2 < 0) {
					return RIGHT_INTERSECTED;
				} else {
					return CONTAINED_IN_INTERVAL2;
				}
			}
		} else {
			if (compareU1U2 < 0) {
				int compareU1L2 = up1.numericalCompareTo(lo2);

				if (compareU1L2 == 0) {
					if (sl2) {
						return LEFT_DISJOINTED;
					} else {
						return CONTAINED_IN_INTERVAL2;
					}
				} else if (compareU1L2 > 0) {
					if (!sl1 && sl2) {
						return LEFT_INTERSECTED;
					} else {
						return CONTAINED_IN_INTERVAL2;
					}
				}
			} else if (compareU1U2 > 0) {
				int compareL1U2 = lo1.numericalCompareTo(up2);

				if (compareL1U2 == 0) {
					if (sl1) {
						return RIGHT_DISJOINTED;
					} else {
						return CONTAINED_IN_INTERVAL1;
					}
				} else if (compareL1U2 < 0) {
					if (sl1 && !sl2) {
						return RIGHT_INTERSECTED;
					} else {
						return CONTAINED_IN_INTERVAL1;
					}
				}
			} else {
				if (sl1 && !sl2) {
					if (!su1 && su2) {
						return RIGHT_INTERSECTED;
					} else {
						return CONTAINED_IN_INTERVAL2;
					}
				} else if (!sl1 && sl2) {
					if (su1 && !su2) {
						return LEFT_INTERSECTED;
					} else {
						return CONTAINED_IN_INTERVAL1;
					}
				} else {
					if (su1 && !su2) {
						return CONTAINED_IN_INTERVAL2;
					} else if (!su1 && su2) {
						return CONTAINED_IN_INTERVAL1;
					} // else Exactly Same
				}
			}
		}
		return EXACTLY_SAME;
	}

	@Override
	public Interval add(Interval i1, Interval i2) {
		assert i1 != null && i2 != null;
		assert !i1.isEmpty() && !i2.isEmpty();

		boolean isIntegral = i1.isIntegral();

		assert isIntegral == i2.isIntegral();
		return newInterval(isIntegral, add(i1.lower(), i2.lower()),
				i1.strictLower() || i2.strictLower(),
				add(i1.upper(), i2.upper()),
				i1.strictUpper() || i2.strictUpper());
	}

	@Override
	public Interval multiply(Interval i1, Interval i2) {
		assert i1 != null && i2 != null;
		assert !i1.isEmpty() && !i2.isEmpty();

		boolean isIntegral = i1.isIntegral();

		assert isIntegral == i2.isIntegral();

		Number lo1 = i1.lower();
		Number up1 = i1.upper();
		Number lo2 = i2.lower();
		Number up2 = i2.upper();
		Number lo = infiniteNumber(isIntegral, false);
		Number up = infiniteNumber(isIntegral, true);
		boolean sl1 = i1.strictLower();
		boolean su1 = i1.strictUpper();
		boolean sl2 = i2.strictLower();
		boolean su2 = i2.strictUpper();
		boolean sl = true;
		boolean su = true;

		// Algorithm used is retrieved from:
		// https://en.wikipedia.org/wiki/Interval_arithmetic
		// Formula:
		// [lo1,up1]*[lo2,up2] = [lo,up]
		// lo = Min(lo1*lo2, lo1*up2, up1*lo2, up1*up2)
		// up = Max(lo1*lo2, lo1*up2, up1*lo2, up1*up2)
		if (i1.isZero() || i2.isZero())
			// If either i1 or i2 is exactly zero, then return zero.
			return isIntegral ? zeroIntegerInterval : zeroRationalInterval;
		else if (i1.isUniversal() || i2.isUniversal())
			// If either i1 or i2 is universal and not exactly zero
			// then return universal.
			return isIntegral ? universalIntegerInterval
					: universalRationalInterval;
		else if (lo1.isInfinite() && lo2.isInfinite()) {
			// i.e. If up1 == 0 && su1, then signumUp1 = 0 * 2 - 1;
			int signumUp1 = su1 ? up1.signum() * 2 - 1 : up1.signum();
			int signumUp2 = su2 ? up2.signum() * 2 - 1 : up2.signum();

			if (signumUp1 > 0 || signumUp2 > 0) {
				return isIntegral ? universalIntegerInterval
						: universalRationalInterval;
			} else {
				sl = (su1 || su2) && (su1 || !up1.isZero())
						&& (su2 || !up2.isZero());
				lo = multiply(up1, up2);
				return newInterval(isIntegral, lo, sl, up, su);
			}
		} else if (lo1.isInfinite() && up2.isInfinite()) {
			int signumUp1 = su1 ? up1.signum() * 2 - 1 : up1.signum();
			int signumLo2 = sl2 ? lo2.signum() * 2 + 1 : lo2.signum();

			// (-inf, x1) * (x2, +inf)

			if (signumUp1 > 0 || signumLo2 < 0) {
				return isIntegral ? universalIntegerInterval
						: universalRationalInterval;
			} else {
				su = (su1 || sl2) && (su1 || !up1.isZero())
						&& (sl2 || !lo2.isZero());
				up = multiply(up1, lo2);
				return newInterval(isIntegral, lo, sl, up, su);
			}
		} else if (up1.isInfinite() && lo2.isInfinite()) {
			int signumLo1 = sl1 ? lo1.signum() * 2 + 1 : lo1.signum();
			int signumUp2 = su2 ? up2.signum() * 2 - 1 : up2.signum();

			if (signumLo1 < 0 || signumUp2 > 0) {
				return isIntegral ? universalIntegerInterval
						: universalRationalInterval;
			} else {
				su = (sl1 || su2) && (sl1 || !lo1.isZero())
						&& (su2 || !up2.isZero());
				up = multiply(lo1, up2);
				return newInterval(isIntegral, lo, sl, up, su);
			}
		} else if (up1.isInfinite() && up2.isInfinite()) {
			int signumLo1 = sl1 ? lo1.signum() * 2 + 1 : lo1.signum();
			int signumLo2 = sl2 ? lo2.signum() * 2 + 1 : lo2.signum();

			if (signumLo1 < 0 || signumLo2 < 0) {
				return isIntegral ? universalIntegerInterval
						: universalRationalInterval;
			} else {
				sl = (sl1 || sl2) && (sl1 || !lo1.isZero())
						&& (sl2 || !lo2.isZero());
				lo = multiply(lo1, lo2);
				return newInterval(isIntegral, lo, sl, up, su);
			}
		} else if (lo1.isInfinite()) {
			int signumLo2 = sl2 ? lo2.signum() * 2 + 1 : lo2.signum();
			int signumUp1 = su1 ? up1.signum() * 2 - 1 : up1.signum();
			int signumUp2 = su2 ? up2.signum() * 2 - 1 : up2.signum();

			if (signumLo2 >= 0) {
				if (signumUp1 <= 0) {
					su = (su1 || sl2) && (su1 || !up1.isZero())
							&& (sl2 || !lo2.isZero());
					up = multiply(up1, lo2);
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					su = (su1 || su2) && (su2 || !up2.isZero());
					up = multiply(up1, up2);
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else if (signumUp2 <= 0) {
				if (signumUp1 <= 0) {
					sl = (su1 || su2) && (su1 || !up1.isZero())
							&& (su2 || !up2.isZero());
					lo = multiply(up1, up2);
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					sl = su1 || sl2;
					lo = multiply(up1, lo2);
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else {
				return isIntegral ? universalIntegerInterval
						: universalRationalInterval;
			}
		} else if (up1.isInfinite()) {
			int signumLo1 = sl1 ? lo1.signum() * 2 + 1 : lo1.signum();
			int signumLo2 = sl2 ? lo2.signum() * 2 + 1 : lo2.signum();
			int signumUp2 = su2 ? up2.signum() * 2 - 1 : up2.signum();

			if (signumLo2 >= 0) {
				if (signumLo1 >= 0) {
					sl = (sl1 || sl2) && (sl1 || !lo1.isZero())
							&& (sl2 || !lo2.isZero());
					lo = multiply(lo1, lo2);
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					sl = (sl1 || su2) && (su2 || !up2.isZero());
					lo = multiply(lo1, up2);
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else if (signumUp2 <= 0) {
				if (signumLo1 >= 0) {
					su = (sl1 || su2) && (sl1 || !lo1.isZero())
							&& (su2 || !up2.isZero());
					up = multiply(lo1, up2);
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					su = sl1 || sl2;
					up = multiply(lo1, lo2);
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else {
				return isIntegral ? universalIntegerInterval
						: universalRationalInterval;
			}
		} else if (lo2.isInfinite()) {
			int signumLo1 = sl1 ? lo1.signum() * 2 + 1 : lo1.signum();
			int signumUp1 = su1 ? up1.signum() * 2 - 1 : up1.signum();
			int signumUp2 = su2 ? up2.signum() * 2 - 1 : up2.signum();

			if (signumLo1 >= 0) {
				if (signumUp2 <= 0) {
					su = (sl1 || su2) && (sl1 || !lo1.isZero())
							&& (su2 || !up2.isZero());
					up = multiply(lo1, up2);
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					su = (su1 || su2) && (su1 || !up1.isZero());
					up = multiply(up1, up2);
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else if (signumUp1 <= 0) {
				if (signumUp2 <= 0) {
					sl = (su1 || su2) && (su1 || !up1.isZero())
							&& (su2 || !up2.isZero());
					lo = multiply(up1, up2);
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					sl = sl1 || su2;
					lo = multiply(lo1, up2);
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else {
				return isIntegral ? universalIntegerInterval
						: universalRationalInterval;
			}
		} else if (up2.isInfinite()) {
			int signumLo1 = sl1 ? lo1.signum() * 2 + 1 : lo1.signum();
			int signumLo2 = sl2 ? lo2.signum() * 2 + 1 : lo2.signum();
			int signumUp1 = su1 ? up1.signum() * 2 - 1 : up1.signum();

			if (signumLo1 >= 0) {
				if (signumLo2 >= 0) {
					sl = (sl1 || sl2) && (sl1 || !lo1.isZero())
							&& (sl2 || !lo2.isZero());
					lo = multiply(lo1, lo2);
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					sl = (su1 || sl2) && (su1 || !up1.isZero());
					lo = multiply(up1, lo2);
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else if (signumUp1 <= 0) {
				if (signumLo2 >= 0) {
					su = (su1 || sl2) && (su1 || !up1.isZero())
							&& (sl2 || !lo2.isZero());
					up = multiply(up1, lo2);
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					su = sl1 || sl2;
					up = multiply(lo1, lo2);
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else {
				return isIntegral ? universalIntegerInterval
						: universalRationalInterval;
			}
		} else {
			int signumLo1 = sl1 ? lo1.signum() * 2 + 1 : lo1.signum();
			int signumLo2 = sl2 ? lo2.signum() * 2 + 1 : lo2.signum();
			int signumUp1 = su1 ? up1.signum() * 2 - 1 : up1.signum();
			int signumUp2 = su2 ? up2.signum() * 2 - 1 : up2.signum();

			if (signumLo1 >= 0) {
				if (signumLo2 >= 0) {
					lo = multiply(lo1, lo2);
					sl = (sl1 || sl2) && (sl1 || !lo1.isZero())
							&& (sl2 || !lo2.isZero());
					up = multiply(up1, up2);
					su = (su1 || su2) && (su1 || !up1.isZero())
							&& (su2 || !up2.isZero());
					return newInterval(isIntegral, lo, sl, up, su);
				} else if (signumUp2 <= 0) {
					lo = multiply(up1, lo2);
					sl = (su1 || sl2) && (su1 || !up1.isZero());
					up = multiply(lo1, up2);
					su = (sl1 || su2) && (sl1 || !lo1.isZero())
							&& (su2 || !up2.isZero());
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					lo = multiply(up1, lo2);
					sl = (su1 || sl2) && (su1 || !up1.isZero());
					up = multiply(up1, up2);
					su = (su1 || su2) && (su1 || !up1.isZero());
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else if (signumUp1 <= 0) {
				if (signumLo2 >= 0) {
					lo = multiply(lo1, up2);
					sl = (sl1 || su2) && (su2 || !up2.isZero());
					up = multiply(up1, lo2);
					su = (su1 || sl2) && (su1 || !up1.isZero())
							&& (sl2 || !lo2.isZero());
					return newInterval(isIntegral, lo, sl, up, su);
				} else if (signumUp2 <= 0) {
					lo = multiply(up1, up2);
					sl = (su1 || su2) && (su1 || !up1.isZero())
							&& (su2 || !up2.isZero());
					up = multiply(lo1, lo2);
					su = sl1 || sl2;
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					lo = multiply(lo1, up2);
					sl = sl1 || su2;
					up = multiply(lo1, lo2);
					su = sl1 || sl2;
					return newInterval(isIntegral, lo, sl, up, su);
				}
			} else {
				if (signumLo2 >= 0) {
					lo = multiply(lo1, up2);
					sl = (sl1 || su2) && (su2 || !up2.isZero());
					up = multiply(up1, up2);
					su = (su1 || su2) && (su2 || !up2.isZero());
					return newInterval(isIntegral, lo, sl, up, su);
				} else if (signumUp2 <= 0) {
					lo = multiply(up1, lo2);
					sl = su1 || sl2;
					up = multiply(lo1, lo2);
					su = sl1 || sl2;
					return newInterval(isIntegral, lo, sl, up, su);
				} else {
					Number lo1lo2 = multiply(lo1, lo2);
					Number up1up2 = multiply(up1, up2);
					Number lo1up2 = multiply(lo1, up2);
					Number up1lo2 = multiply(up1, lo2);

					if (lo1lo2.compareTo(up1up2) < 0) {
						up = up1up2;
						su = su1 || su2;
					} else if (lo1lo2.compareTo(up1up2) > 0) {
						up = lo1lo2;
						su = sl1 || sl2;
					} else {
						up = lo1lo2;
						su = (sl1 || sl2) && (su1 || su2);
					}
					if (lo1up2.compareTo(up1lo2) < 0) {
						lo = lo1up2;
						sl = sl1 || su2;
					} else if (lo1up2.compareTo(up1lo2) > 0) {
						lo = up1lo2;
						sl = su1 || sl2;
					} else {
						lo = up1lo2;
						sl = (sl1 || su2) && (su1 || sl2);
					}
					return newInterval(isIntegral, lo, sl, up, su);
				}
			}
		}
	}

	@Override
	public Interval power(Interval interval, int exp) {
		assert interval != null;

		boolean isIntegral = interval.isIntegral();

		assert exp >= 0 || !isIntegral;
		assert !(interval.isZero() && exp == 0);

		boolean strictLower = interval.strictLower();
		boolean strictUpper = interval.strictUpper();
		boolean newSl = true;
		boolean newSu = true;
		IntegerNumber expNum = integer(exp);
		Number lower = interval.lower();
		Number upper = interval.upper();
		Number newLo = infiniteNumber(isIntegral, false);
		Number newUp = infiniteNumber(isIntegral, true);
		Number oneNumber = isIntegral ? oneInteger : oneRational;
		Number zeroNumber = isIntegral ? zeroInteger : zeroRational;

		if (exp == 0)
			return singletonInterval(oneNumber);
		// if (exp < 0)
		// return power(divide(singletonInterval(oneNumber), interval), -exp);
		// exp > 0
		if (interval.isUniversal()) {
			return interval;
		} else if (lower.isInfinite()) {
			int signumUp = strictUpper ? upper.signum() * 2 - 1
					: upper.signum();

			if (exp % 2 == 0) {
				if (signumUp < 0) {
					newLo = power(upper, expNum);
					newSl = strictUpper;
				} else {
					newLo = zeroNumber;
					newSl = false;
				}
			} else {
				newUp = power(upper, expNum);
				newSu = strictUpper;
			}
			return newInterval(isIntegral, newLo, newSl, newUp, newSu);
		} else if (upper.isInfinite()) {
			int signumLo = strictLower ? lower.signum() * 2 + 1
					: lower.signum();

			if (signumLo > 0) {
				newLo = power(lower, expNum);
				newSl = strictLower;
			} else {
				if (exp % 2 == 0) {
					newLo = zeroNumber;
					newSl = false;
				} else {
					newLo = power(lower, expNum);
					newSl = strictLower;
				}
			}
			return newInterval(isIntegral, newLo, newSl, newUp, newSu);
		} else {
			int signumLo = strictLower ? lower.signum() * 2 + 1
					: lower.signum();
			int signumUp = strictUpper ? upper.signum() * 2 - 1
					: upper.signum();

			newUp = power(upper, expNum);
			newSu = strictUpper;
			newLo = power(lower, expNum);
			newSl = strictLower;

			if (exp % 2 == 0)
				if (signumUp <= 0) {
					assert signumLo <= 0;

					Number tempNum = newUp;
					boolean tempStrict = newSu;

					newUp = newLo;
					newSu = newSl;
					newLo = tempNum;
					newSl = tempStrict;
				} else if (signumLo < 0) {
					Number tempUpFromLo = power(negate(lower), expNum);
					Number tempUpFromUp = power(upper, expNum);

					if (tempUpFromLo.compareTo(tempUpFromUp) < 0) {
						newUp = tempUpFromUp;
						newSu = strictUpper;
					} else {
						newUp = tempUpFromLo;
						newSu = strictLower;
					}
					newLo = zeroNumber;
					newSl = false;
				} else {
					assert signumLo >= 0 && signumUp >= 0;
				}
		}
		return newInterval(isIntegral, newLo, newSl, newUp, newSu);
	}

	@Override
	public Number power(Number number, IntegerNumber exp) {
		assert exp != null && exp.numericalCompareTo(zeroInteger) == 1;
		if (number instanceof IntegerNumber) {
			return power((IntegerNumber) number, exp);
		} else if (number instanceof RationalNumber) {
			return power((RationalNumber) number, exp);
		} else {
			throw new IllegalArgumentException(
					"Unknown type of number: " + number);
		}
	}

	@Override
	public Number power(Number number, int exp) {
		assert exp >= 0;
		if (number instanceof IntegerNumber) {
			return power((IntegerNumber) number, exp);
		} else if (number instanceof RationalNumber) {
			return power((RationalNumber) number, exp);
		} else {
			throw new IllegalArgumentException(
					"Unknown type of number: " + number);
		}
	}

	@Override
	public IntegerNumber power(IntegerNumber number, int exp) {
		assert number != null;
		assert exp >= 0;
		if (exp == 0) {
			if (number.isZero())
				throw new IllegalArgumentException("0 could not power with 0.");
			else if (number.isInfinite())
				throw new IllegalArgumentException(
						"The infinity could not power with 0.");
			else
				return oneInteger;
		}

		if (number.isInfinite())
			if (number.signum() < 0 && exp % 2 != 0)
				return infiniteInteger(false);
			else
				return infiniteInteger(true);

		IntegerNumber result = oneInteger;
		IntegerNumber base = number;
		IntegerNumber e = integer(exp);
		IntegerNumber twoInt = integer(2);

		while (true) {
			if (!mod(e, twoInt).isZero()) {
				result = multiply(result, base);
				e = subtract(e, oneInteger);
				if (e.isZero())
					break;
			}
			base = multiply(base, base);
			e = divide(e, twoInt);
		}
		return result;
	}

	@Override
	public RationalNumber power(RationalNumber number, int exp) {
		IntegerNumber baseNum = integer(number.numerator());
		IntegerNumber baseDen = integer(number.denominator());
		IntegerNumber resultNum = null;
		IntegerNumber resultDen = null;

		if (exp == 0) {
			if (number.isZero())
				throw new IllegalArgumentException(
						"0.0 could not power with 0.");
			else if (number.isInfinite())
				throw new IllegalArgumentException(
						"The infinity could not power with 0.");
			else
				return oneRational;
		}
		if (exp > 0) {
			resultNum = power(baseNum, integer(exp));
			resultDen = power(baseDen, integer(exp));
		} else {
			resultNum = power(baseDen, integer(-exp));
			resultDen = power(baseNum, integer(-exp));
		}
		return fraction(resultNum, resultDen);
	}

	@Override
	public Interval singletonInterval(Number x) {
		assert !x.isInfinite();
		return newInterval(x instanceof IntegerNumber, x, false, x, false);
	}

	// @Override
	public Interval restrictUpperBAD(Interval interval, Number bound,
			boolean strict) {
		assert interval != null;
		assert interval.isIntegral() == bound instanceof IntegerNumber;

		boolean isInt = interval.isIntegral();
		boolean strictUpper = interval.strictUpper();
		boolean strictLower = interval.strictLower();
		Number upper = interval.upper();
		Number lower = interval.lower();

		if (bound == null) {
			assert strict;
			return interval;
		}
		if (interval.isUniversal()) {
			return newInterval(isInt, null, true, bound, strict);
		} else if (lower == null) {
			int compareUpperBound = upper.compareTo(bound);

			if (compareUpperBound > 0) {
				return newInterval(isInt, null, true, bound, strict);
			} else if (compareUpperBound < 0) {
				return interval;
			} else {
				return newInterval(isInt, null, true, bound,
						strict || strictUpper);
			}
		} else if (upper == null) {
			int compareLowerBound = lower.compareTo(bound);

			if (compareLowerBound < 0
					|| (compareLowerBound == 0 && !strict && !strictLower)) {
				return newInterval(isInt, lower, strictLower, bound, strict);
			} else {
				return isInt ? emptyIntegerInterval : emptyRationalInterval;
			}
		} else {
			int compareUpperBound = upper.compareTo(bound);

			if (compareUpperBound < 0) {
				return interval;
			} else if (compareUpperBound == 0) {
				return newInterval(isInt, lower, strictLower, bound,
						strict || strictUpper);
			} else {
				int compareLowerBound = lower.compareTo(bound);

				if ((compareLowerBound < 0) || (compareLowerBound == 0
						&& !strict && !strictLower)) {
					return newInterval(isInt, lower, strictLower, bound,
							strict);
				} else {
					return isInt ? emptyIntegerInterval : emptyRationalInterval;
				}
			}
		}
	}

	// @Override
	public Interval restrictLowerBAD(Interval interval, Number bound,
			boolean strict) {
		assert interval != null;
		assert interval.isIntegral() == bound instanceof IntegerNumber;

		boolean isInt = interval.isIntegral();
		boolean strictUpper = interval.strictUpper();
		boolean strictLower = interval.strictLower();
		Number upper = interval.upper();
		Number lower = interval.lower();

		if (bound == null) {
			assert strict;
			return interval;
		}
		if (interval.isUniversal()) {
			return newInterval(isInt, bound, strict, null, true);
		} else if (lower == null) {
			int compareUpperBound = upper.compareTo(bound);

			if (compareUpperBound > 0
					|| (compareUpperBound == 0 && !strict && !strictUpper)) {
				return newInterval(isInt, lower, strictLower, bound, strict);
			} else {
				return isInt ? emptyIntegerInterval : emptyRationalInterval;
			}
		} else if (upper == null) {
			int compareLowerBound = lower.compareTo(bound);

			if (compareLowerBound > 0) {
				return interval;
			} else if (compareLowerBound < 0) {
				return newInterval(isInt, bound, strict, null, true);
			} else {
				return newInterval(isInt, bound, strict || strictLower, upper,
						strictUpper);
			}
		} else {
			int compareLowerBound = lower.compareTo(bound);

			if (compareLowerBound > 0) {
				return interval;
			} else if (compareLowerBound == 0) {
				return newInterval(isInt, bound, strict || strictLower, upper,
						strictUpper);
			} else {
				int compareUpperBound = upper.compareTo(bound);

				if (compareUpperBound > 0 || (compareUpperBound == 0 && !strict
						&& !strictUpper)) {
					return newInterval(isInt, bound, strict, upper,
							strictUpper);
				} else {
					return isInt ? emptyIntegerInterval : emptyRationalInterval;
				}
			}
		}
	}

	@Override
	public Interval join(Interval i1, Interval i2) {
		assert i1 != null && i2 != null;

		boolean isIntegral = i1.isIntegral();

		assert i1.isIntegral() == i2.isIntegral();

		boolean sl1 = i1.strictLower();
		boolean sl2 = i2.strictLower();
		boolean su1 = i1.strictUpper();
		boolean su2 = i2.strictUpper();
		boolean su = false;
		boolean sl = false;
		Number lo1 = i1.lower();
		Number lo2 = i2.lower();
		Number up1 = i1.upper();
		Number up2 = i2.upper();
		Number lo = null;
		Number up = null;

		if (i2.isEmpty() || i1.isUniversal())
			return i1;
		if (i1.isEmpty() || i2.isUniversal())
			return i2;

		int compareLo = lo1.numericalCompareTo(lo2);
		int compareUp = up1.numericalCompareTo(up2);

		if (compareLo < 0) {
			// lo1 < lo2
			sl = sl1;
			lo = lo1;
		} else if (compareLo > 0) {
			// lo1 > lo2
			sl = sl2;
			lo = lo2;
		} else {
			// lo1 == lo2
			sl = sl1 && sl2;
			lo = lo2;
		}
		if (compareUp > 0) {
			// up1 < up2
			su = su1;
			up = up1;
		} else if (compareUp < 0) {
			// up1 > up2
			su = su2;
			up = up2;
		} else {
			// up1 == up2
			su = su1 && su2;
			up = up2;
		}
		return newInterval(isIntegral, lo, sl, up, su);
	}

	@Override
	public Interval restrictUpper(Interval interval, Number bound,
			boolean strict) {
		boolean isIntegral = interval.isIntegral();
		Interval i2 = newInterval(isIntegral, infiniteNumber(isIntegral, false),
				true, bound, strict);
		Interval result = intersection(interval, i2);

		return result;
	}

	@Override
	public Interval restrictLower(Interval interval, Number bound,
			boolean strict) {
		boolean isIntegral = interval.isIntegral();
		Interval i2 = newInterval(isIntegral, bound, strict,
				infiniteNumber(isIntegral, true), true);
		Interval result = intersection(interval, i2);

		return result;
	}

	@Override
	public IntegerNumber nthRootInt(IntegerNumber number, IntegerNumber n) {
		// Pre-condition Checking
		assert number != null && n != null;
		assert !number.isInfinite() && !n.isInfinite();
		assert n.signum() > 0;

		// If number is negative, n could not be even.
		if (number.signum() < 0) {
			if (mod(n, integer(2)).isZero()) {
				throw new IllegalArgumentException(
						"When the argument 'number' to the method nthRootInt is negative, "
								+ "\nThe argument 'n' should be greater than 0."
								+ "\nThe n is: " + n);
			}
		}
		// Special Cases
		if (n.isOne() || number.isZero() || abs(number).isOne())
			return number;

		boolean flag = true;
		IntegerNumber nMinusOne = subtract(n, integer(1));
		RationalNumber nth = divide(oneRational, rational(n));
		RationalNumber pow = rational(number);
		RationalNumber oldBase = oneRational;
		RationalNumber limit = fraction(oneInteger, integer(100));
		RationalNumber newBase = multiply(nth,
				add(multiply(rational(nMinusOne), oldBase),
						divide(pow, power(oldBase, nMinusOne))));
		RationalNumber cond1 = subtract(newBase, oldBase);
		RationalNumber cond2 = subtract(power(cond1, 2), limit);
		IntegerNumber result = null;

		// Algorithm used is retrived from:
		// https://en.wikipedia.org/wiki/Nth_root#nth_root_algorithm
		// Recursive Formula:
		// newBase=nth*(nMinusOne*OldBase + number/(oldBase^nMinusOne));
		// Loop condition:
		// 1. After the first loop, newBase < oldBase
		// 2. (newBase - oldBase)^2 > 0.01
		while ((flag || cond1.signum() < 0) && cond2.signum() > 0) {
			oldBase = rational(floor(add(newBase, limit)));
			newBase = multiply(nth, add(multiply(rational(nMinusOne), oldBase),
					divide(pow, power(oldBase, nMinusOne))));
			newBase = rational(floor(add(newBase, limit)));
			cond1 = subtract(newBase, oldBase);
			cond2 = subtract(power(cond1, 2), limit);
			flag = false;
		}
		// Ground the result
		newBase = add(newBase, fraction(oneInteger, integer(2)));
		result = floor(newBase);
		if (!subtract(power(result, n), number).isZero())
			/*
			 * If power-result with approximated base is NOT exactly same with
			 * the given number, then the approximated base is not correct.
			 */
			return null;
		// Else, return the result.
		return result;
	}

	@Override
	public RationalNumber power(RationalNumber number, IntegerNumber exp) {
		assert number != null && exp != null;
		assert exp.signum() >= 0;

		IntegerNumber baseNum = integer(number.numerator());
		IntegerNumber baseDen = integer(number.denominator());
		IntegerNumber resultNum = null;
		IntegerNumber resultDen = null;

		if (number.signum() < 0 && exp.isInfinite())
			throw new IllegalArgumentException(
					"The negative number could not power with the positive infinity.");
		if (exp.isZero()) {
			if (number.isZero())
				throw new IllegalArgumentException(
						"0.0 could not power with 0.");
			else if (number.isInfinite())
				throw new IllegalArgumentException(
						"The infinity could not power with 0.");
			else
				return oneRational;
		} else if (exp.signum() > 0) {
			resultNum = power(baseNum, exp);
			resultDen = power(baseDen, exp);
		} else {
			resultNum = power(baseDen, negate(exp));
			resultDen = power(baseNum, negate(exp));
		}
		return fraction(resultNum, resultDen);
	}

	@Override
	public IntegerNumber power(IntegerNumber number, IntegerNumber exp) {
		assert number != null && exp != null;
		assert exp.signum() >= 0;
		if (number.signum() < 0 && exp.isInfinite())
			throw new IllegalArgumentException(
					"The negative number could not power with the positive infinity.");
		if (exp.isZero()) {
			if (number.isZero())
				throw new IllegalArgumentException("0 could not power with 0.");
			else if (number.isInfinite())
				throw new IllegalArgumentException(
						"The infinity could not power with 0.");
			else
				return zeroInteger;
		} else {
			IntegerNumber result = oneInteger;
			IntegerNumber base = number;
			IntegerNumber e = exp;
			IntegerNumber twoInt = integer(2);

			while (true) {
				if (!mod(e, twoInt).isZero()) {
					result = multiply(result, base);
					e = subtract(e, oneInteger);
					if (e.isZero())
						break;
				}
				base = multiply(base, base);
				e = divide(e, twoInt);
			}
			return result;
		}
	}

	@Override
	public Interval divide(Interval interval, Number num) {
		assert interval != null && num != null;

		int sign = num.signum();

		if (num.isZero())
			throw new ArithmeticException("Interval divide by zero");

		Boolean isIntegral = interval.isIntegral();

		assert isIntegral == num instanceof IntegerNumber;
		if (interval.isEmpty() || interval.isUniversal())
			return interval;
		if (num.isInfinite())
			return isIntegral ? zeroIntegerInterval : zeroRationalInterval;

		Number lo = interval.lower();
		Number up = interval.upper();
		boolean sl = interval.strictLower();
		boolean su = interval.strictUpper();

		lo = lo.isInfinite() ? infiniteNumber(isIntegral, false)
				: divide(lo, num);
		up = up.isInfinite() ? infiniteNumber(isIntegral, true)
				: divide(up, num);
		if (sign > 0)
			return newInterval(isIntegral, up, sl, lo, su);
		else
			return newInterval(isIntegral, lo, sl, up, su);
	}

	@Override
	public Interval multiply(Number num, Interval interval) {
		assert interval != null && num != null;
		assert !num.isInfinite();

		Boolean isIntegral = interval.isIntegral();

		assert isIntegral == num instanceof IntegerNumber;
		if (interval.isEmpty())
			return interval;
		if (num.isZero())
			return isIntegral ? zeroIntegerInterval : zeroRationalInterval;

		Number lo = interval.lower();
		Number up = interval.upper();
		boolean sl = interval.strictLower();
		boolean su = interval.strictUpper();
		int sign = num.signum();

		lo = multiply(lo, num);
		up = multiply(up, num);
		if (sign > 0)
			return newInterval(isIntegral, lo, sl, up, su);
		else
			return newInterval(isIntegral, up, su, lo, sl);
	}

	@Override
	public Interval divide(Interval i1, Interval i2) {
		assert i1 != null && i2 != null;

		Boolean isIntegral = i1.isIntegral();

		assert isIntegral == i2.isIntegral();

		if (i2.isZero())
			throw new ArithmeticException(
					"DividedByZero: The Interval used as denominator is exactly 0");
		else if (i2.isEmpty())
			throw new ArithmeticException(
					"DividedByEmptyInterval: The Interval used as denominator is an empty set.");
		else if (i1.isEmpty())
			return i1;

		Number lo2 = i2.lower();
		Number up2 = i2.upper();
		boolean sl2 = i2.strictLower();
		boolean su2 = i2.strictUpper();
		Number tempLo = infiniteNumber(isIntegral, false);
		Number tempUp = infiniteNumber(isIntegral, true);
		boolean tempSl = true;
		boolean tempSu = true;
		Number zeroNum = isIntegral ? zeroInteger : zeroRational;
		Number oneNum = isIntegral ? oneInteger : oneRational;

		// Algorithm used is retrived from:
		// https://en.wikipedia.org/wiki/Interval_arithmetic
		// Fomula:
		// [lo1,up1]/[lo2,up2] = [lo1, up1] * (1 / [lo2, up2]);
		// If 0 is NOT in i2:
		// | (1 / [lo2, up2]) = [1/up2, 1/lo2]
		// Else if 0 is in i2:
		// | If up2 == 0:
		// | | (1 / [lo2, 0]) = (-infi, 1/lo2]
		// | Else if lo2 == 0:
		// | | (1 / [0, up2]) = [1/up2, +infi)
		// | Else
		// | | (1 / [lo2, up2]) = (-infi, 1/lo2] U [1/up2, +infi)
		// | | However in single interval: (-infi, +inif)
		if (i2.contains(zeroNum)) {
			// 0 in i2
			if (lo2.isZero()) {
				tempLo = divide(oneNum, up2);
				tempSl = su2;
			} else if (up2.isZero()) {
				tempUp = divide(oneNum, lo2);
				tempSu = sl2;
			} else
				return isIntegral ? universalIntegerInterval
						: universalRationalInterval;
		} else {
			// 0 not in i2
			if (!lo2.isZero()) {
				tempUp = divide(oneNum, lo2);
				tempSu = sl2;
			}
			if (!up2.isZero()) {
				tempLo = divide(oneNum, up2);
				tempSl = su2;
			}
		}
		return multiply(i1,
				newInterval(isIntegral, tempLo, tempSl, tempUp, tempSu));
	}

	@Override
	public IntegerNumber infiniteInteger(boolean isPositiveInfinity) {
		return isPositiveInfinity ? INT_POS_INFINITY : INT_NEG_INFINITY;
	}

	@Override
	public RationalNumber infiniteRational(boolean isPositiveInfinity) {
		return isPositiveInfinity ? RAT_POS_INFINITY : RAT_NEG_INFINITY;
	}

	@Override
	public Number infiniteNumber(boolean isIntegeral,
			boolean isPositiveInfinity) {
		return isIntegeral ? infiniteInteger(isPositiveInfinity)
				: infiniteRational(isPositiveInfinity);
	}

	@Override
	public RationalNumber positiveInfinityRational() {
		return RAT_POS_INFINITY;
	}

	@Override
	public IntegerNumber positiveInfinityInteger() {
		return INT_POS_INFINITY;
	}

	@Override
	public RationalNumber negativeInfinityRational() {
		return RAT_NEG_INFINITY;
	}

	@Override
	public IntegerNumber negativeInfinityInteger() {
		return INT_NEG_INFINITY;
	}

	@Override
	public Interval negate(Interval interval) {
		assert interval != null;
		if (interval.isEmpty() || interval.isUniversal())
			return interval;

		return newInterval(interval.isIntegral(), negate(interval.upper()),
				interval.strictUpper(), negate(interval.lower()),
				interval.strictLower());
	}
}
