package edu.udel.cis.vsl.sarl.simplify.IF;

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;

/**
 * An abstract representation of a set of {@link Number}s. Each instance is
 * typed: it is either a set of integers, or a set of reals. The two types are
 * incompatible.
 * 
 * @author Stephen F. Siegel
 */
public interface Range {

	/**
	 * Is this an integer set?
	 * 
	 * @return <code>true</code> if this is a set of integers;
	 *         <code>false</code> if this is a set of reals
	 */
	boolean isIntegral();

	/**
	 * Is this set empty?
	 * 
	 * @return <code>true</code> iff this is the empty set
	 */
	boolean isEmpty();

	/**
	 * Does this set contain the given number as a member?
	 * 
	 * @param number
	 *            any non-<code>null</code> {@link Number} of the same type
	 *            (integer/real) as this set
	 * @return <code>true</code> iff this set contains the given number
	 */
	boolean containsNumber(Number number);

	/**
	 * Is this set a superset of the given one?
	 * 
	 * @param set
	 *            a number set of the same type (integer/real) as this one
	 * @return <code>true</code> iff this one contains the given one
	 */
	boolean contains(Range set);

	/**
	 * Is the intersection of this set with the given one nonempty?
	 * 
	 * @param set
	 *            a number set of the same type (integer/real) as this one
	 * @return <code>true</code> iff the intersection of the two sets is
	 *         nonempty
	 */
	boolean intersects(Range set);

	/**
	 * Computes the complement of this set. If this has integer type, that is
	 * the set of all integers not in this set. If this has real type, it is the
	 * set of all reals not in this set.
	 * 
	 * @return the complement of this set
	 */
	Range complement();

	/**
	 * Computes the union of this set with the given one.
	 * 
	 * @param set
	 *            a non-null number set of the same type (integer/real) as this
	 *            one
	 * @return the union of the two sets
	 */
	Range union(Range set);

	/**
	 * Computes the intersection of this set with the given one.
	 * 
	 * @param set
	 *            a number set of the same type (integer/real) as this one
	 * @return the intersection of the two sets
	 */
	Range intersect(Range set);

	/**
	 * Returns the set difference of this set with that one. That is the set
	 * consisting of all numbers in this set that are not in that one.
	 * 
	 * @param set
	 *            a number set of the same type (integer/real) as this one
	 * @return this - that (the set difference)
	 */
	Range minus(Range set);

	/**
	 * Computes the set aX+b, where X is this set. That is, the set of all
	 * numbers of the form ax+b, where x is in this set. (For integral
	 * {@link Interval} set, it will return the set including all transformed
	 * integers, which are contained in the original set.)
	 * 
	 * @param a
	 *            a number of the same type as this set
	 * @param b
	 *            a number of the same type as this set
	 * @return the set aX+b, where X is the set of numbers in this set
	 */
	Range affineTransform(Number a, Number b);

	/**
	 * Given a {@link NumericExpression} <code>x</code>, returns a
	 * {@link BooleanExpression} which holds iff <code>x</code> is in
	 * <code>this</code> {@link Range}.
	 * 
	 * <p>
	 * Example: suppose <code>this</code> {@link Range} is the {@link Interval}
	 * (0,1]. Given <code>x</code>, this method will return a
	 * {@link BooleanExpression} <code>x>0 && x<=1</code>.
	 * </p>
	 * 
	 * <p>
	 * Example: (0,1] U [4,5]. Given <code>x</code>, returns
	 * <code>(x>0 && x<=1) || (x>=4 && x<=5)</code>.
	 * </p>
	 * 
	 * @param x
	 *            variable to use in the new expression
	 * @param universe
	 *            symbolic universe used to construct the symbolic expression
	 * @return a {@link BooleanExpression} involving <code>x</code> which holds
	 *         iff <code>x</code> is in this set
	 */
	BooleanExpression symbolicRepresentation(NumericExpression x,
			PreUniverse universe);

	/**
	 * If this range represents a singleton set (a set consisting of exactly one
	 * Number), this method returns the value of its sole element; otherwise,
	 * returns <code>null</code>.
	 * 
	 * @return The exact {@link Number} represented by <code>this
	 *         </code> {@link Range}, if <code>this</code> range represents a
	 *         singleton number;<br>
	 *         otherwise, it will return <code>null</code>.
	 */
	Number getSingletonValue();

	/**
	 * If this range is an interval, return the Interval representation,
	 * otherwise, returns <code>null</code>.
	 * 
	 * @return The exact {@link Interval} represented by <code>this
	 *         </code> {@link Range}, if <code>this</code> range represents a
	 *         singleton interval;<br>
	 *         otherwise, it will return <code>null</code>.
	 */
	Interval asInterval();
}
