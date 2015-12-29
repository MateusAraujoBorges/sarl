package edu.udel.cis.vsl.sarl.collections.common;

import java.util.Arrays;
import java.util.Comparator;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.collections.IF.SimpleEntry;
import edu.udel.cis.vsl.sarl.collections.IF.SortedSymbolicMap;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicCollection;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicMap;
import edu.udel.cis.vsl.sarl.object.common.CommonObjectFactory;
import edu.udel.cis.vsl.sarl.util.BinaryOperator;

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

	private static SimpleEntry[] emptyArray = new SimpleEntry[0];

	// Instance fields...

	private Comparator<? super K> comparator;

	private Entry<K, V>[] entries;

	// Constructors...

	protected SimpleSortedMap(Comparator<? super K> comparator,
			Entry<K, V>[] entries) {
		super();
		this.comparator = comparator;
		this.entries = entries;
	}

	@SuppressWarnings("unchecked")
	protected SimpleSortedMap(Comparator<? super K> comparator) {
		this(comparator, (Entry<K, V>[]) emptyArray);
	}

	/**
	 * Constructs new instance from the given Java map. The new instances is
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
	public void canonizeChildren(CommonObjectFactory factory) {
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
			Entry<K, V>[] thoseEntries = ((SimpleSortedMap<K, V>) o).entries;
			int n = entries.length;
			// recall: they must have the same size

			for (int i = 0; i < n; i++) {
				if (!entries[i].getValue().equals(thoseEntries[i].getValue()))
					return false;
			}
			return true;
		}
		return super.collectionEquals(o);
	}

	/**
	 * @{inheritDoc} This is an optimized implementation. The order is
	 *               completely determined by the keys, so can use a merge.
	 * 
	 * @param operator
	 *            binary operator on values
	 * @param map
	 *            the other map
	 * @return result of combining the two maps
	 */
	@Override
	public SortedSymbolicMap<K, V> combine(BinaryOperator<V> operator,
			SymbolicMap<K, V> map) {
		SortedSymbolicMap<K, V> result;

		if (map instanceof SimpleSortedMap<?, ?>) {
			SimpleSortedMap<K, V> map2 = (SimpleSortedMap<K, V>) map;
			Entry<K, V>[] entries1 = entries, entries2 = map2.entries;
			int n1 = entries1.length, n2 = entries2.length;

			if (n1 == 0) {
				result = map2;
			} else if (n2 == 0) {
				result = this;
			} else {
				@SuppressWarnings("unchecked")
				Entry<K, V>[] newEntries = (Entry<K, V>[]) new SimpleEntry[n1
						+ n2];
				int i1 = 0, i2 = 0, count = 0;
				Entry<K, V> entry1 = entries1[0], entry2 = entries2[0];
				K key1 = entry1.getKey(), key2 = entry2.getKey();
				V val1 = entry1.getValue(), val2 = entry2.getValue();

				while (i1 < n1 && i2 < n2) {
					int c = comparator.compare(key1, key2);

					if (c < 0) { // key1 comes first
						@SuppressWarnings("unchecked")
						Entry<K, V> newEntry = (Entry<K, V>) new SimpleEntry(
								key1, val1);

						newEntries[count] = newEntry;
						count++;
						i1++;
						if (i1 < n1) {
							entry1 = entries1[i1];
							key1 = entry1.getKey();
							val1 = entry1.getValue();
						} else {
							break;
						}
					} else if (c > 0) { // key2 comes first
						@SuppressWarnings("unchecked")
						Entry<K, V> newEntry = (Entry<K, V>) new SimpleEntry(
								key2, val2);

						newEntries[count] = newEntry;
						count++;
						i2++;
						if (i2 < n2) {
							entry2 = entries2[i2];
							key2 = entry2.getKey();
							val2 = entry2.getValue();
						} else {
							break;
						}
					} else {
						V newValue = operator.apply(val1, val2);

						if (newValue != null) {
							@SuppressWarnings("unchecked")
							Entry<K, V> newEntry = (Entry<K, V>) new SimpleEntry(
									key1, newValue);

							newEntries[count] = newEntry;
							count++;
						}
						i1++;
						i2++;
						if (i1 < n1) {
							entry1 = entries1[i1];
							key1 = entry1.getKey();
							val1 = entry1.getValue();
						} else {
							break;
						}
						if (i2 < n2) {
							entry2 = entries2[i2];
							key2 = entry2.getKey();
							val2 = entry2.getValue();
						} else {
							break;
						}
					}
				}
				while (i1 < n1) {
					entry1 = entries1[i1];

					@SuppressWarnings("unchecked")
					Entry<K, V> newEntry = (Entry<K, V>) new SimpleEntry(
							entry1.getKey(), entry1.getValue());

					newEntries[count] = newEntry;
					count++;
					i1++;
				}
				while (i2 < n2) {
					entry2 = entries2[i2];

					@SuppressWarnings("unchecked")
					Entry<K, V> newEntry = (Entry<K, V>) new SimpleEntry(
							entry2.getKey(), entry2.getValue());

					newEntries[count] = newEntry;
					count++;
					i2++;
				}
				if (count < n1 + n2) {
					@SuppressWarnings("unchecked")
					Entry<K, V>[] tmp = (Entry<K, V>[]) new SimpleEntry[count];

					System.arraycopy(newEntries, 0, tmp, 0, count);
					newEntries = tmp;
				}
				result = new SimpleSortedMap<K, V>(comparator, newEntries);
			}
		} else {
			result = super.combine(operator, map);
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
}
