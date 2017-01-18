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

import java.util.Objects;

import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;

/**
 * Immutable implementation of {@link Interval}.
 */
public class CommonInterval implements Interval {
	// TODO: add Java-doc for fields, constructors and functions.
	// Private Fields ...

	private boolean isIntegral;

	private Number lower;

	private boolean strictLower;

	private Number upper;

	private boolean strictUpper;

	// Constructors ...
	// TODO: Java-doc should include pre-cond.
	public CommonInterval(boolean isIntegral, Number lower, boolean strictLower,
			Number upper, boolean strictUpper) {
		assert lower != null && upper != null;
		assert isIntegral || ((lower instanceof RationalNumber)
				&& (upper instanceof RationalNumber));
		assert !isIntegral || ((lower instanceof IntegerNumber)
				&& (upper instanceof IntegerNumber));
		assert !isIntegral || lower.isZero()
				|| (lower.isInfinite() && strictLower)
				|| (!lower.isInfinite() && !strictLower);
		assert !isIntegral || upper.isZero()
				|| (upper.isInfinite() && strictUpper)
				|| (!upper.isInfinite() && !strictUpper);
		assert !isIntegral || !strictLower || lower.isInfinite()
				|| (lower.isZero() && upper.isZero());
		assert !isIntegral || !strictUpper || upper.isInfinite()
				|| (lower.isZero() && upper.isZero());
		assert (!lower.isInfinite() || strictLower)
				&& (!upper.isInfinite() || strictUpper);

		int compare;

		// <a,b> with a>b is unacceptable
		// (0,0) is fine: the unique representation of the empty set
		// [a,a] is fine, but not (a,a), [a,a), or (a,a]
		assert (compare = lower.numericalCompareTo(upper)) < 0
				|| (compare == 0 && ((!strictLower && !strictUpper)
						|| (lower.isZero() && strictLower && strictUpper)));
		this.isIntegral = isIntegral;
		this.lower = lower;
		this.strictLower = strictLower;
		this.upper = upper;
		this.strictUpper = strictUpper;
	}

	// Methods specified by interface "Object"

	@Override
	public CommonInterval clone() {
		return new CommonInterval(isIntegral, lower, strictLower, upper,
				strictUpper);
	}

	@Override
	public boolean equals(Object object) {
		if (object instanceof CommonInterval) {
			CommonInterval that = (CommonInterval) object;

			return isIntegral == that.isIntegral
					&& strictLower == that.strictLower
					&& strictUpper == that.strictUpper
					&& upper.equals(that.upper) && lower.equals(that.lower);
		} else
			return false;
	}

	@Override
	public int hashCode() {
		return Objects.hash(isIntegral, strictLower, strictUpper, lower, upper);
	}

	@Override
	public String toString() {
		String result;

		result = strictLower ? "(" : "[";
		result += lower.isInfinite() ? "-infty" : lower.toString();
		result += ",";
		result += upper.isInfinite() ? "+infty" : upper.toString();
		result += strictUpper ? ")" : "]";
		return result;
	}

	// Methods specified by interface "Interval"

	@Override
	public Number lower() {
		return lower;
	}

	@Override
	public Number upper() {
		return upper;
	}

	@Override
	public boolean strictLower() {
		return strictLower;
	}

	@Override
	public boolean strictUpper() {
		return strictUpper;
	}

	@Override
	public boolean isIntegral() {
		return isIntegral;
	}

	@Override
	public boolean isReal() {
		return !isIntegral;
	}

	@Override
	public boolean isEmpty() {
		return strictLower && strictUpper && lower.isZero() && upper.isZero();
	}

	@Override
	public boolean isUniversal() {
		return lower.isInfinite() && upper.isInfinite();
	}

	@Override
	public boolean contains(Number number) {
		if (!lower.isInfinite()) {
			int compare = lower.numericalCompareTo(number);

			if (compare > 0 || (compare == 0 && strictLower))
				return false;
		}
		if (!upper.isInfinite()) {
			int compare = upper.numericalCompareTo(number);

			if (compare < 0 || (compare == 0 && strictUpper))
				return false;
		}
		return true;
	}

	@Override
	public int compare(Number number) {
		if (!lower.isInfinite()) {
			int compare = lower.numericalCompareTo(number);

			if (compare > 0 || (compare == 0 && strictLower))
				return 1;
		}
		if (!upper.isInfinite()) {
			int compare = upper.numericalCompareTo(number);

			if (compare < 0 || (compare == 0 && strictUpper))
				return -1;
		}
		return 0;
	}

	@Override
	public boolean isZero() {
		return lower != null && upper != null && lower.isZero()
				&& upper.isZero() && !strictLower;
	}
}
