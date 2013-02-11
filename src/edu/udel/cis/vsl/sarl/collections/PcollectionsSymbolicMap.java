package edu.udel.cis.vsl.sarl.collections;

import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import org.pcollections.HashTreePMap;
import org.pcollections.PMap;

import edu.udel.cis.vsl.sarl.IF.collections.SymbolicCollection;
import edu.udel.cis.vsl.sarl.IF.collections.SymbolicMap;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpressionIF;
import edu.udel.cis.vsl.sarl.object.ObjectFactory;

public class PcollectionsSymbolicMap extends CommonSymbolicMap implements
		SymbolicMap {

	private PMap<SymbolicExpressionIF, SymbolicExpressionIF> pmap;

	PcollectionsSymbolicMap(
			PMap<SymbolicExpressionIF, SymbolicExpressionIF> pmap) {
		super();
		this.pmap = pmap;
	}

	PcollectionsSymbolicMap() {
		super();
		this.pmap = HashTreePMap.empty();
	}

	PcollectionsSymbolicMap(
			Map<SymbolicExpressionIF, SymbolicExpressionIF> javaMap) {
		this(HashTreePMap.from(javaMap));
	}

	@Override
	public SymbolicExpressionIF get(SymbolicExpressionIF key) {
		return pmap.get(key);
	}

	@Override
	public Iterable<SymbolicExpressionIF> keys() {
		return pmap.keySet();
	}

	@Override
	public Iterable<SymbolicExpressionIF> values() {
		return pmap.values();
	}

	@Override
	public Iterable<Entry<SymbolicExpressionIF, SymbolicExpressionIF>> entries() {
		return pmap.entrySet();
	}

	@Override
	public Iterator<SymbolicExpressionIF> iterator() {
		return pmap.values().iterator();
	}

	@Override
	protected int computeHashCode() {
		return SymbolicCollectionKind.MAP.hashCode() ^ pmap.hashCode();
	}

	@Override
	public int size() {
		return pmap.size();
	}

	@Override
	protected boolean collectionEquals(SymbolicCollection o) {
		PcollectionsSymbolicMap that = (PcollectionsSymbolicMap) o;

		return pmap.equals(that.pmap);
	}

	@Override
	public String toString() {
		return pmap.toString();
	}

	@Override
	public boolean isEmpty() {
		return pmap.isEmpty();
	}

	@Override
	public boolean isSorted() {
		return false;
	}

	@Override
	public SymbolicMap put(SymbolicExpressionIF key, SymbolicExpressionIF value) {
		return new PcollectionsSymbolicMap(pmap.plus(key, value));
	}

	@Override
	public SymbolicMap remove(SymbolicExpressionIF key) {
		return new PcollectionsSymbolicMap(pmap.minus(key));
	}

	/**
	 * Runs a few simple tests.
	 * 
	 * @param args
	 *            ignored
	 */
	public static void main(String[] args) {
		// TODO
	}

	@Override
	public void canonizeChildren(ObjectFactory factory) {
		// TODO Auto-generated method stub

	}

}
