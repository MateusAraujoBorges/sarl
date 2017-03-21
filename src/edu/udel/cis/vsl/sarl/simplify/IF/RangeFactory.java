package edu.udel.cis.vsl.sarl.simplify.IF;

import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;

/**
 * Factory for producing instances of {@link Range}.
 * 
 * @author Stephen F. Siegel
 *
 */
public interface RangeFactory {

	/**
	 * Returns an empty number set of the specified type.
	 * 
	 * @param isIntegral
	 *            is this integer type (not real type)?
	 * @return empty set of integer type if <code>isIntegral</code> is
	 *         <code>true</code>, else empty set of real type
	 */
	Range emptySet(boolean isIntegral);

	/**
	 * Returns the number set consisting of the single specified element. The
	 * type of <code>number</code> determines the type of the set.
	 * 
	 * @param number
	 *            a non-<code>null</code> {@link Number}
	 * @return singleton set containing <code>number</code>
	 */
	Range singletonSet(Number number);

	/**
	 * <p>
	 * Returns the set consisting of all x between <code>left</code> and
	 * <code>right</code>.
	 * </p>
	 *
	 * If the instance is an implementation of {@link Interval}, the arguments
	 * and the result should satisfy the pre-conditions and the post-conditions
	 * of {@link Interval}<br>
	 * 
	 * @param left
	 *            the lower bound of the set with the type defined by isIntegral
	 * @param strictLeft
	 *            is the lower bound strict? (i.e., "(" if exclusive, as opposed
	 *            to "[" if inclusive)
	 * @param right
	 *            the upper bound of the set with the type defined by isIntegral
	 * @param strictRight
	 *            is the upper bound strict? (i.e., ")" if exclusive, as opposed
	 *            to "]" if inclusive)
	 * @param isIntegral
	 *            does the interval have integer type (as opposed to real type)?
	 * @return a new {@link Range} instance as specified
	 */
	Range interval(Number left, boolean strictLeft, Number right,
			boolean strictRight, boolean isIntegral);

	/**
	 * For two range rSet and rSet, this function will calculate the summary for
	 * those two range and return the result.
	 * 
	 * @param lRange
	 *            a number set of the same type (integer/real) as the other one
	 * @param rRange
	 *            a number set of the same type (integer/real) as the other one
	 * @return the range of the lSet adding the rSet
	 */
	public Range add(Range lRange, Range rRange);

	/**
	 * 
	 * @param lRange
	 *            a number set of the same type (integer/real) as the other one
	 * @param rRange
	 *            a number set of the same type (integer/real) as the other one
	 * @return
	 */
	public Range multiply(Range lRange, Range rRange);

	/**
	 * 
	 * @param lRange
	 *            a number set of the same type (integer/real) as the other one
	 * @param exp
	 *            a natural number as exponent
	 * @return
	 */
	public Range power(Range lRange, int exp);
}
