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

// TODO: maybe you need a different Collection Factory for each
// comparator? One for PrimitiveComparator, one for MonicComparator,...
// They could be compared and exchanged even if they came from different
// collection factories because they don't store a comparator, so they
// would be interchangeable. BUT how would you compare them?
// You would need a general comparator that would work on any symbolic
// expressions. It wouldn't have to have anything to do with the
// specific comparators used in the different factories.
// But they all have to agree on equality (compareTo==0).
// the same is true if you put the comparator inside each collection: you
// STILL need a general comparator which can compare them all!

// so: multiple CollectionFactories, multiple comparators

// ALSO: collectionFactory is used throughout SARL to generate sequences,
// which don't have any comparator.

// let's just put the comparator inside the collection for now and
// get rid of empty ones without specifying the comparator.
// or insist there can only be one comparator?

import java.util.Collection;
import java.util.Comparator;
import java.util.Map;
import java.util.Map.Entry;

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
	 * Takes in a Java collection and creates a new Basic Collection containing
	 * the elements contained in the in the Java Collection passed in. This
	 * method may or may not copy the elements out of the given collection.
	 * Therefore the given collection should never be accessed directly after
	 * this method is called.
	 * 
	 * @param javaCollection
	 *            any kind of collection of symbolic expressions
	 * @return a symbolic collection based on the given Java collection
	 */
	<T extends SymbolicExpression> SymbolicCollection<T> basicCollection(
			Collection<T> javaCollection);

	// /**
	// * Returns the empty hash set.
	// *
	// * @return the empty hash set set
	// */
	// <T extends SymbolicExpression> SymbolicSet<T> emptyHashSet();

	/**
	 * Returns the empty sorted set using default comparator.
	 * 
	 * @return the empty sorted set
	 */
	<T extends SymbolicExpression> SortedSymbolicSet<T> emptySortedSet();

	/**
	 * Returns the empty sorted set.
	 * 
	 * @param comparator
	 *            Comparator used for sorting
	 * 
	 * @return the empty sorted set
	 */
	<T extends SymbolicExpression> SortedSymbolicSet<T> emptySortedSet(
			Comparator<? super T> comparator);

	// /**
	// * Returns the singleton hash set containing the one element.
	// *
	// * @param element
	// * a symbolic expression
	// * @return the hash set consisting of that one element
	// */
	// <T extends SymbolicExpression> SymbolicSet<T> singletonHashSet(T
	// element);

	/**
	 * Returns the singleton sorted set containing the one element.
	 *
	 * @param element
	 *            a symbolic expression
	 * @return the sorted set consisting of the one element
	 */
	<T extends SymbolicExpression> SortedSymbolicSet<T> singletonSortedSet(
			T element);

	/**
	 * Returns the singleton sorted set containing the one element.
	 * 
	 * @param element
	 *            a symbolic expression
	 * @param comparator
	 *            used for sorting
	 * @return the set consisting of that one element
	 */
	<T extends SymbolicExpression> SortedSymbolicSet<T> singletonSortedSet(
			T element, Comparator<? super T> comparator);

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

	// /**
	// * Returns an empty sorted symbolic map using default comparator on keys.
	// *
	// * @return an empty sorted symbolic map
	// */
	// <K extends SymbolicExpression, V extends SymbolicExpression>
	// SortedSymbolicMap<K, V> emptySortedMap();

	/**
	 * Returns an empty sorted symbolic map using given comparator on keys.
	 * 
	 * @return an empty sorted symbolic map
	 */
	<K extends SymbolicExpression, V extends SymbolicExpression> SortedSymbolicMap<K, V> emptySortedMap(
			Comparator<? super K> comparator);

	// /**
	// * Returns an empty hash symbolic map.
	// *
	// * @return an empty hash symbolic map
	// */
	// <K extends SymbolicExpression, V extends SymbolicExpression>
	// SymbolicMap<K, V> emptyHashMap();

	// /**
	// * Returns the sorted map with one entry (key,value).
	// *
	// * @param key
	// * the key for the entry
	// * @param value
	// * the value for the entry
	// * @return the map with the one entry
	// */
	// <K extends SymbolicExpression, V extends SymbolicExpression>
	// SortedSymbolicMap<K, V> singletonSortedMap(
	// K key, V value);

	/**
	 * Returns the sorted map with one entry (key,value) and using the given
	 * comparator on keys.
	 * 
	 * @param key
	 *            the key for the entry
	 * @param value
	 *            the value for the entry
	 * @return the map with the one entry
	 */
	<K extends SymbolicExpression, V extends SymbolicExpression> SortedSymbolicMap<K, V> singletonSortedMap(
			Comparator<? super K> comparator, K key, V value);

	// /**
	// * Returns the hash map with one entry (key,value).
	// *
	// * @param key
	// * the key for the entry
	// * @param value
	// * the value for the entry
	// * @return the map with the one entry
	// */
	// <K extends SymbolicExpression, V extends SymbolicExpression>
	// SymbolicMap<K, V> singletonHashMap(
	// K key, V value);

	/**
	 * Returns a sorted symbolic map based on the given Java Map. The Java map
	 * should not be modified after this method is invoked.
	 * 
	 * @param javaMap
	 * @return a symbolic map based on the given Java map
	 */
	<K extends SymbolicExpression, V extends SymbolicExpression> SortedSymbolicMap<K, V> sortedMap(
			Map<K, V> javaMap);

	/**
	 * Returns a sorted symbolic map based on the given Java Map. The Java map
	 * should not be modified after this method is invoked.
	 * 
	 * @param javaMap
	 * @return a sorted symbolic map based on the given Java map
	 */
	<K extends SymbolicExpression, V extends SymbolicExpression> SortedSymbolicMap<K, V> sortedMap(
			Comparator<? super K> comparator, Map<K, V> javaMap);

	// /**
	// * Returns an (unsorted) hash symbolic map based on the given Java Map.
	// *
	// * @param javaMap
	// * a Java {@link java.util.Map}
	// * @return an (unsorted) hash symbolic map based on the javaMap
	// */
	// <K extends SymbolicExpression, V extends SymbolicExpression>
	// SymbolicMap<K, V> hashMap(
	// Map<K, V> javaMap);

	/**
	 * Returns an {@link Entry} with the specified key and value. This can be
	 * used to create a {@link SymbolicMap}, e.g., in method
	 * {@link #sortedMap(Comparator, Entry[])}.
	 * 
	 * @param key
	 *            the key for the entry
	 * @param value
	 *            the value for the entry
	 * @return an entry with that key and value
	 */
	<K extends SymbolicExpression, V extends SymbolicExpression> Entry<K, V> entry(
			K key, V value);

	/**
	 * Returns a new sorted map backed by the given array of entries. The given
	 * entries must be sorted according to the given comparator on the keys.
	 * Failure to satisfy this precondition will result in unspecified behavior.
	 * Use at your own risk!
	 * 
	 * @param comparator
	 *            comparator on the key set <code>K</code>
	 * @param entries
	 *            list of entries for the new map, sorted with keys occurring in
	 *            increasing order according to comparator
	 * @return the new map
	 */
	<K extends SymbolicExpression, V extends SymbolicExpression> SortedSymbolicMap<K, V> sortedMap(
			Comparator<? super K> comparator, Entry<K, V>[] entries);

	/**
	 * Given a {@link SymbolicMap} returns the {@link SymbolicMap} obtained by
	 * removing the entries specified by the given <code>mask</code> . The
	 * <code>mask</code> is an array whose length is the
	 * {@link SymbolicMap#size()} (number of entries) of <code>map</code>. A
	 * <code>true</code> mask value indicates the corresponding entry should be
	 * kept; a <code>false</code> value indicates the corresponding entry should
	 * be removed.
	 * 
	 * @param map
	 *            a non-<code>null</code> {@link SortedSymbolicMap}
	 * @param mask
	 *            array of boolean of length size of <code>map</code> specifying
	 *            which entries to keep
	 * @return the map obtained from given map by keeping the specified subset
	 *         of entries
	 */
	<K extends SymbolicExpression, V extends SymbolicExpression> SymbolicMap<K, V> mask(
			SymbolicMap<K, V> map, boolean[] mask);

}
