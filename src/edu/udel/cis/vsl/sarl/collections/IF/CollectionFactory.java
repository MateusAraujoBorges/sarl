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
package edu.udel.cis.vsl.sarl.collections.IF;

import java.util.Comparator;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * A factory for producing persistent collections. A set is either "hash" or
 * "sorted". The operations on sets produce new sets of the same kind. Ditto for
 * maps; the sorted variety are sorted by key. Sequences are already ordered by
 * definition.
 * 
 * @author siegel
 * 
 */
public interface CollectionFactory {

	/**
	 * Returns the comparator that is used to place a total order on the set of
	 * all symbolic collections.
	 * 
	 * @return The comparator that is used to compare any two symbolic
	 *         collections
	 */
	Comparator<SymbolicCollection<? extends SymbolicExpression>> comparator();

	/**
	 * Sets the "element comparator" that is used to compare any two symbolic
	 * expressions. The element comparator will be used by the collection
	 * comparator to place a total order on the symbolic collections.
	 * 
	 * @param s1
	 *            the comparator on symbolic expressions
	 */
	void setElementComparator(Comparator<SymbolicExpression> c);

	/**
	 * Initializes this collection factory. This should be called once, after
	 * the element comparator has been set by
	 * {@link #setElementComparator(Comparator)}.
	 */
	void init();

	/**
	 * Returns a SymbolicSequence comprising the given sequence of elements.
	 * 
	 * @param elements
	 *            any object providing an iterator over SymbolicExpressionIF
	 * @return a single SymbolicExpressionSequenceIF which wraps the given list
	 *         of elements
	 */
	<T extends SymbolicExpression> SymbolicSequence<T> sequence(
			Iterable<? extends T> elements);

	/**
	 * Returns a SymbolicSequence comprising the sequence of elements specified
	 * as an array.
	 * 
	 * @param elements
	 *            any array of SymbolicExpressionIF
	 * @return a single SymbolicExpressionSequenceIF which wraps the given list
	 *         of elements
	 */
	<T extends SymbolicExpression> SymbolicSequence<T> sequence(T[] elements);

	/**
	 * Returns the sequence of length 1 consisting of the given element.
	 * 
	 * @param element
	 * @return the sequence consisting of just the one element
	 */
	<T extends SymbolicExpression> SymbolicSequence<T> singletonSequence(
			T element);

	/**
	 * Returns the empty sequence.
	 * 
	 * @return the empty sequence
	 */
	<T extends SymbolicExpression> SymbolicSequence<T> emptySequence();

}
