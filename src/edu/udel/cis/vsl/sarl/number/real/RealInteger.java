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

import java.math.BigInteger;

import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;

/**
 * An infinite precision representation of integer numbers, based on Java's
 * BigInteger class. There is no bound on such an integer.
 * 
 * Because we are using the flyweight pattern, two RealIntegers will represent
 * the same integer iff they are the same (==) object. Hence we keep the equals
 * and hashCode methods inherited from Object.
 * 
 * Also note, that because the flyweight pattern is being used, we don't want to
 * use the 'new' keyword (as the hash codes won't match).
 */
public class RealInteger extends RealNumber implements IntegerNumber {

	private BigInteger value;

	/**
	 * Creates RealIntegers from BigIntegers and protects against null values.
	 * 
	 * @param value
	 */
	RealInteger(BigInteger value) {
		assert value != null;
		this.value = value;
	}

	@Override
	public int signum() {
		return value.signum();
	}

	@Override
	public String toString() {
		return value.toString();
	}

	/**
	 * Get the value of this integer;<br>
	 * 
	 * @return
	 */
	public BigInteger value() {
		return value;
	}

	@Override
	public String atomString() {
		return "(" + toString() + ")";
	}

	@Override
	public boolean isZero() {
		return value == BigInteger.ZERO;
	}

	@Override
	public boolean isOne() {
		return value == BigInteger.ONE;
	}

	@Override
	public int intValue() {
		if (value.abs().shiftRight(32).compareTo(BigInteger.ZERO) != 0)
			throw new ArithmeticException(
					"The value of this BigInteger is out of the range of Integer.");
		return value.intValue();
	}

	@Override
	public BigInteger bigIntegerValue() {
		return value;
	}

	@Override
	public int numericalCompareTo(Number other) {
		assert other instanceof IntegerNumber;
		if (other.isInfinite())
			return -other.signum();
		return (this.value().subtract(((RealInteger) other).value())).signum();
	}

	@Override
	public boolean isInfinite() {
		return false;
	}

}
