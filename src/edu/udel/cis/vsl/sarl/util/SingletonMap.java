package edu.udel.cis.vsl.sarl.util;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.sarl.IF.SARLInternalException;

public class SingletonMap<K, V> implements Map<K, V> {

	private K theKey;

	private V theValue;

	public SingletonMap(K key, V value) {
		assert key != null;
		theKey = key;
		theValue = value;
	}

	@Override
	public int size() {
		return 1;
	}

	@Override
	public boolean isEmpty() {
		return false;
	}

	@Override
	public boolean containsKey(Object key) {
		return theKey.equals(key);
	}

	@Override
	public boolean containsValue(Object value) {
		return theValue == null ? (value == null) : theValue.equals(value);
	}

	@Override
	public V get(Object key) {
		return theKey.equals(key) ? theValue : null;
	}

	@Override
	public V put(K key, V value) {
		throw new SARLInternalException("Map is immutable");
	}

	@Override
	public V remove(Object key) {
		throw new SARLInternalException("Map is immutable");
	}

	@Override
	public void putAll(Map<? extends K, ? extends V> m) {
		throw new SARLInternalException("Map is immutable");
	}

	@Override
	public void clear() {
		throw new SARLInternalException("Map is immutable");
	}

	@Override
	public Set<K> keySet() {
		return new SingletonSet<K>(theKey);
	}

	@Override
	public Collection<V> values() {
		return new SingletonSet<V>(theValue);
	}

	@Override
	public Set<java.util.Map.Entry<K, V>> entrySet() {
		return new SingletonSet<Entry<K, V>>(new Entry<K, V>() {
			@Override
			public K getKey() {
				return theKey;
			}

			@Override
			public V getValue() {
				return theValue;
			}

			@Override
			public V setValue(V value) {
				throw new SARLInternalException("Map is immutable");
			}
		});
	}

}
