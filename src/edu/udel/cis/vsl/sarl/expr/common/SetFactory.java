package edu.udel.cis.vsl.sarl.expr.common;

import java.util.Comparator;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.util.BinaryOperator;

public abstract class SetFactory<V extends SymbolicExpression>
		extends KeySetFactory<V, V> {

	private BinaryOperator<V> project1 = new BinaryOperator<V>() {
		@Override
		public V apply(V x, V y) {
			return x;
		}
	};

	public SetFactory(Comparator<V> comparator) {
		super(comparator);
	}

	protected V key(V value) {
		return value;
	}

	public V[] union(V[] set1, V[] set2) {
		return combine(project1, set1, set2);
	}

	public boolean contains(V[] set, V element) {
		return find(set, element) >= 0;
	}
}
