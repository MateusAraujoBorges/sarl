package edu.udel.cis.vsl.sarl.collections.common;

import java.util.Arrays;
import java.util.Comparator;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.SortedMap;

import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.collections.IF.SimpleEntry;
import edu.udel.cis.vsl.sarl.collections.IF.SortedSymbolicMap;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicCollection;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicMap;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.util.BinaryOperator;

/**
 * An implementation of {@link SortedMap} that uses an ordered array to store
 * the sequence of {@link Entry}s making up the map.
 */
public class SimpleSortedMap<K extends SymbolicExpression, V extends SymbolicExpression>
		extends CommonSortedMap<K, V> implements SortedSymbolicMap<K, V> {

	// Types...

	protected class EntryComparator implements Comparator<Entry<K, V>> {
		@Override
		public int compare(Entry<K, V> o1, Entry<K, V> o2) {
			return comparator.compare(o1.getKey(), o2.getKey());
		}
	}

	// Static fields...

	/**
	 * An empty array (array of length 0) that can be used for any types K and V
	 * because of immutability.
	 */
	private static SimpleEntry[] emptyArray = new SimpleEntry[0];

	// Instance fields...

	/**
	 * The comparator on keys used to order this map. It is sort of inefficient
	 * to store this in every map---might be better to make it another argument
	 * to all of the methods that operate on the map.
	 */
	private Comparator<? super K> comparator;

	/**
	 * The entries of this map, ordered from "least" to "greatest" by key.
	 */
	private Entry<K, V>[] entries;

	// Constructors...

	/**
	 * Constructs new sorted map with given comparator and entries. The entries
	 * are assumed to be ordered. This is not checked.
	 * 
	 * @param comparator
	 *            a comparator on keys
	 * @param entries
	 *            the entries that will become a field of this map; must be
	 *            ordered by increasing key
	 */
	protected SimpleSortedMap(Comparator<? super K> comparator,
			Entry<K, V>[] entries) {
		super();
		this.comparator = comparator;

		// TODO: remove when done debugging:
		for (int i = 0; i < entries.length; i++)
			assert entries[i] != null;

		this.entries = entries;
	}

	/**
	 * Constructs new empty map with given comparator.
	 * 
	 * @param comparator
	 *            the comparator on keys that will be associated to the new map.
	 *            It may seem this is not necessary for an empty map, but
	 *            operations on this map will produce new maps that may not be
	 *            empty, and those new maps will inherit this comparator.
	 */
	@SuppressWarnings("unchecked")
	protected SimpleSortedMap(Comparator<? super K> comparator) {
		this(comparator, (Entry<K, V>[]) emptyArray);
	}

	/**
	 * Constructs new instance from the given Java map. The new instance is
	 * backed by the Java map, i.e., if you modify the Java map you could mess
	 * up this new instance.
	 * 
	 * @param javaMap
	 *            a Java map from K to V, not necessarily ordered
	 * @param comparator
	 *            the comparator on keys
	 */
	protected SimpleSortedMap(Map<K, V> javaMap,
			Comparator<? super K> comparator) {
		super();

		int size = javaMap.size();

		this.comparator = comparator;
		// safety: Java won't let you instantiate a generic array,
		// but I know that all the keys will belong to K and values
		// will belong to V because they come from javaMap:
		@SuppressWarnings("unchecked")
		Entry<K, V>[] entries2 = (Entry<K, V>[]) new Entry<?, ?>[size];

		entries = entries2;
		javaMap.entrySet().toArray(entries);
		Arrays.sort(entries, new EntryComparator());
	}

	// Helper methods...

	/**
	 * Finds the index of the entry in the array {@link #entries} whose key
	 * equals the given key, if there is one. Else returns -1.
	 * 
	 * @param key
	 *            the key to look for; any member of K
	 * @return index of the entry with that key, or -1 if there is none
	 */
	private int find(K key) {
		int lo = 0, hi = entries.length - 1;

		while (lo <= hi) {
			int mid = (lo + hi) / 2;
			int compare = comparator.compare(entries[mid].getKey(), key);

			if (compare == 0) {
				return mid;
			} else if (compare < 0) { // x<element
				lo = mid + 1;
			} else {
				hi = mid - 1;
			}
		}
		return -1;
	}

	/**
	 * Combines the given map with this one using a basic merge of sorted lists.
	 * 
	 * <p>
	 * Preconditions: both maps are non-empty. Both maps use the same
	 * comparator.
	 * </p>
	 * 
	 * @param operator
	 *            binary operator on values
	 * @param map
	 *            the other map
	 * @return result of combining the two maps
	 */
	private SortedSymbolicMap<K, V> combine2(BinaryOperator<V> operator,
			SimpleSortedMap<K, V> map) {
		Entry<K, V>[] entries1 = entries, entries2 = map.entries;
		int n1 = entries1.length, n2 = entries2.length;
		@SuppressWarnings("unchecked")
		Entry<K, V>[] newEntries = (Entry<K, V>[]) new SimpleEntry[n1 + n2];
		int i1 = 0, i2 = 0, count = 0;
		Entry<K, V> entry1 = entries1[0], entry2 = entries2[0];
		K key1 = entry1.getKey(), key2 = entry2.getKey();

		while (true) {
			int c = comparator.compare(key1, key2);

			if (c < 0) { // key1 comes first
				newEntries[count] = entry1;
				count++;
				i1++;
				if (i1 >= n1)
					break;
				entry1 = entries1[i1];
				key1 = entry1.getKey();
			} else if (c > 0) { // key2 comes first
				newEntries[count] = entry2;
				count++;
				i2++;
				if (i2 >= n2)
					break;
				entry2 = entries2[i2];
				key2 = entry2.getKey();
			} else {
				V newValue = operator.apply(entry1.getValue(),
						entry2.getValue());

				if (newValue != null) {
					@SuppressWarnings("unchecked")
					Entry<K, V> newEntry = (Entry<K, V>) new SimpleEntry(key1,
							newValue);

					newEntries[count] = newEntry;
					count++;
				}
				i1++;
				i2++;
				if (i1 >= n1 || i2 >= n2)
					break;
				entry1 = entries1[i1];
				key1 = entry1.getKey();
				entry2 = entries2[i2];
				key2 = entry2.getKey();
			}
		}

		int delta1 = n1 - i1, delta2 = n2 - i2,
				newLength = count + delta1 + delta2;

		if (newLength < n1 + n2) {
			@SuppressWarnings("unchecked")
			Entry<K, V>[] tmp = (Entry<K, V>[]) new SimpleEntry[newLength];

			System.arraycopy(newEntries, 0, tmp, 0, count);
			newEntries = tmp;
		}
		if (i1 < n1)
			System.arraycopy(entries1, i1, newEntries, count, delta1);
		else if (i2 < n2)
			System.arraycopy(entries2, i2, newEntries, count, delta2);
		return new SimpleSortedMap<K, V>(comparator, newEntries);
	}

	/**
	 * Combines the given map with this one. In this implementation, the smaller
	 * map is merged with the bigger one and at each point an attempt is made to
	 * do a minimal number of comparisons by finding the exact index in the
	 * bigger array where the next element should be inserted. However, it
	 * doesn't seem to improve performance over the basic merge.
	 * 
	 * <p>
	 * Preconditions: both maps are non-empty. Both maps use the same
	 * comparator.
	 * </p>
	 * 
	 * @param operator
	 *            binary operator on values
	 * @param map
	 *            the map to combine with this one
	 * @return the combined map
	 */
	@SuppressWarnings("unused")
	private SortedSymbolicMap<K, V> combine3(BinaryOperator<V> operator,
			SimpleSortedMap<K, V> map) {
		Entry<K, V>[] entries1 = entries, entries2 = map.entries;
		int n1 = entries1.length, n2 = entries2.length;
		@SuppressWarnings("unchecked")
		Entry<K, V>[] newEntries = (Entry<K, V>[]) new SimpleEntry[n1 + n2];

		if (n1 < n2) {
			Entry<K, V>[] tmp = entries1;

			entries1 = entries2;
			entries2 = tmp;

			int tmp2 = n1;

			n1 = n2;
			n2 = tmp2;
		}
		assert (n1 >= n2);

		// merge entries2 into entries1...

		int i1 = 0, count = 0;

		// invariant: entries[i]<entry2 forall i<i1.
		for (Entry<K, V> entry2 : entries2) {
			K key2 = entry2.getKey();
			boolean eq = false;
			int lo = i1, hi = n1 - 1;

			// Goals:
			// 1. lo is greatest in [i1,n1] s.t. entries1[i]<entry2 forall i<lo
			// 2. eq iff (lo<n1 && entries1[lo]=entry2)

			while (lo <= hi) {
				int mid = (lo + hi) / 2;
				int compare = comparator.compare(entries1[mid].getKey(), key2);

				if (compare == 0) {
					eq = true;
					lo = mid;
					break;
				} else if (compare < 0) { // entries1[mid]<entry2
					lo = mid + 1;
				} else {
					hi = mid - 1;
				}
			}
			if (lo > i1) { // [i1,lo) gets shifted from entries1 to newEntries
				System.arraycopy(entries1, i1, newEntries, count, lo - i1);
				count += lo - i1;
				i1 = lo;
			}
			if (eq) { // combine entries1[lo] and entry2
				V newValue = operator.apply(entries1[lo].getValue(),
						entry2.getValue());

				if (newValue != null) {
					@SuppressWarnings("unchecked")
					Entry<K, V> newEntry = (Entry<K, V>) new SimpleEntry(
							entry2.getKey(), newValue);

					newEntries[count] = newEntry;
					count++;
				}
				i1++;
			} else { // shift entry2 only
				newEntries[count] = entry2;
				count++;
			}
		}
		if (i1 < n1) {
			System.arraycopy(entries1, i1, newEntries, count, n1 - i1);
			count += n1 - i1;
		}
		if (count < n1 + n2) {
			@SuppressWarnings("unchecked")
			Entry<K, V>[] tmp = (Entry<K, V>[]) new SimpleEntry[count];

			System.arraycopy(newEntries, 0, tmp, 0, count);
			newEntries = tmp;
		}
		return new SimpleSortedMap<K, V>(comparator, newEntries);
	}

	@Override
	public Comparator<? super K> comparator() {
		return comparator;
	}

	@Override
	public SortedSymbolicMap<K, V> put(K key, V value) {
		int lo = 0, hi = entries.length - 1;

		// loop invariant: hi-lo >= -1.
		// hi>=lo -> hi-((lo+hi)/2 + 1) >= -1.
		// hi>=lo -> ((lo+hi)/2 -1) - lo >= -1.
		while (lo <= hi) {
			int mid = (lo + hi) / 2;
			Entry<K, V> entry = entries[mid];
			int keyComparison = comparator.compare(entry.getKey(), key);

			if (keyComparison == 0) {
				if (value.equals(entry.getValue()))
					return this;

				@SuppressWarnings("unchecked")
				Entry<K, V> newEntry = (Entry<K, V>) new SimpleEntry(key,
						value);
				// new version replacing old entry with new one at mid
				@SuppressWarnings("unchecked")
				Entry<K, V>[] newEntries = (Entry<K, V>[]) new SimpleEntry[entries.length];

				System.arraycopy(entries, 0, newEntries, 0, entries.length);
				newEntries[mid] = newEntry;
				return new SimpleSortedMap<K, V>(comparator, newEntries);
			} else if (keyComparison < 0) { // x<element
				lo = mid + 1;
			} else { // x>element
				hi = mid - 1;
			}
		}
		assert hi - lo == -1;
		// Example: hi=-1, lo=0
		// Example: hi=length-1, lo=length
		// lo is where element should be inserted
		// new version inserting new entry at position lo
		@SuppressWarnings("unchecked")
		Entry<K, V> newEntry = (Entry<K, V>) new SimpleEntry(key, value);
		@SuppressWarnings("unchecked")
		Entry<K, V>[] newEntries = (Entry<K, V>[]) new SimpleEntry[entries.length
				+ 1];

		System.arraycopy(entries, 0, newEntries, 0, lo);
		newEntries[lo] = newEntry;
		System.arraycopy(entries, lo, newEntries, lo + 1, entries.length - lo);
		return new SimpleSortedMap<K, V>(comparator, newEntries);
	}

	@Override
	public SortedSymbolicMap<K, V> remove(K key) {
		int index = find(key);

		if (index < 0) {
			return this;
		} else {
			@SuppressWarnings("unchecked")
			Entry<K, V>[] newEntries = (Entry<K, V>[]) new SimpleEntry[entries.length
					- 1];

			System.arraycopy(entries, 0, newEntries, 0, index);
			System.arraycopy(entries, index + 1, newEntries, index,
					entries.length - index - 1);
			return new SimpleSortedMap<K, V>(comparator, newEntries);
		}
	}

	@Override
	public V get(K key) {
		int index = find(key);

		if (index < 0) {
			return null;
		} else {
			return entries[index].getValue();
		}
	}

	class KeyIterable implements Iterable<K> {
		class KeyIterator implements Iterator<K> {
			int nextIndex = 0;

			@Override
			public boolean hasNext() {
				return nextIndex < entries.length;
			}

			@Override
			public K next() {
				K result = entries[nextIndex].getKey();

				nextIndex++;
				return result;
			}

			@Override
			public void remove() {
				throw new SARLException("unimplemented");
			}
		}

		@Override
		public Iterator<K> iterator() {
			return new KeyIterator();
		}
	}

	@Override
	public Iterable<K> keys() {
		return new KeyIterable();
	}

	class ValueIterable implements Iterable<V> {
		class ValueIterator implements Iterator<V> {
			int nextIndex = 0;

			@Override
			public boolean hasNext() {
				return nextIndex < entries.length;
			}

			@Override
			public V next() {
				V result = entries[nextIndex].getValue();

				nextIndex++;
				return result;
			}

			@Override
			public void remove() {
				throw new SARLException("unimplemented");
			}
		}

		@Override
		public Iterator<V> iterator() {
			return new ValueIterator();
		}
	}

	@Override
	public Iterable<V> values() {
		return new ValueIterable();
	}

	class EntriesIterable implements Iterable<Entry<K, V>> {
		class EntriesIterator implements Iterator<Entry<K, V>> {
			int nextIndex = 0;

			@Override
			public boolean hasNext() {
				return nextIndex < entries.length;
			}

			@Override
			public Entry<K, V> next() {
				Entry<K, V> result = entries[nextIndex];

				nextIndex++;
				return result;
			}

			@Override
			public void remove() {
				throw new SARLException("unimplemented");
			}
		}

		@Override
		public Iterator<Entry<K, V>> iterator() {
			return new EntriesIterator();
		}
	}

	@Override
	public Iterable<Entry<K, V>> entries() {
		return new EntriesIterable();
	}

	@Override
	public boolean isEmpty() {
		return entries.length == 0;
	}

	@Override
	public int size() {
		return entries.length;
	}

	@Override
	public Iterator<V> iterator() {
		return (new ValueIterable()).iterator();
	}

	@Override
	public void canonizeChildren(ObjectFactory factory) {
		for (Entry<K, V> entry : entries) {
			V oldValue = entry.getValue();
			V newValue = factory.canonic(oldValue);

			if (oldValue != newValue)
				entry.setValue(newValue);
		}
	}

	@Override
	protected boolean collectionEquals(SymbolicCollection<V> o) {
		if (o instanceof SimpleSortedMap<?, ?>) {
			@SuppressWarnings("unchecked")
			SimpleSortedMap<K, V> that = (SimpleSortedMap<K, V>) o;

			if (comparator != that.comparator)
				return false;

			Entry<K, V>[] thoseEntries = that.entries;
			int n = entries.length;
			// recall: they must have the same size

			for (int i = 0; i < n; i++) {
				if (!entries[i].getValue().equals(thoseEntries[i].getValue()))
					return false;
			}
			return true;
		} else {
			throw new SARLInternalException("Unknown sorted map kind: " + o);
		}
	}

	@Override
	protected int computeHashCode() {
		int result = comparator.hashCode() ^ collectionKind().hashCode();

		for (Entry<K, V> entry : entries) {
			result ^= entry.getValue().hashCode();
		}
		return result;
	}

	@Override
	public Entry<K, V> getEntry(int index) {
		return entries[index];
	}

	@Override
	public Entry<K, V>[] entryArray() {
		return entries;
	}

	@Override
	public SortedSymbolicMap<K, V> combine(BinaryOperator<V> operator,
			SymbolicMap<K, V> map) {
		int n2 = map.size();

		if (n2 == 0)
			return this;
		if (map instanceof SimpleSortedMap<?, ?>) {
			int n1 = this.size();
			SimpleSortedMap<K, V> map2 = (SimpleSortedMap<K, V>) map;

			if (n1 == 0)
				return map2;
			// currently, combine2 is best in all cases...
			return combine2(operator, map2);
		} else {
			return super.combine(operator, map);
		}
	}
}
