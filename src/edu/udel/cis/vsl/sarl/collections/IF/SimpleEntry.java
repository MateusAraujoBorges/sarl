package edu.udel.cis.vsl.sarl.collections.IF;

import java.util.Map.Entry;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class SimpleEntry
		implements Entry<SymbolicExpression, SymbolicExpression> {
	SymbolicExpression key;
	SymbolicExpression value;

	public SimpleEntry(SymbolicExpression key, SymbolicExpression value) {
		this.key = key;
		this.value = value;
	}

	@Override
	public SymbolicExpression getKey() {
		return key;
	}

	@Override
	public SymbolicExpression getValue() {
		return value;
	}

	/**
	 * Sets the value component of this entry. We need this because of the
	 * canonicalization process, which replaces the value with the canonical
	 * version of the value.
	 */
	@Override
	public SymbolicExpression setValue(SymbolicExpression value) {
		SymbolicExpression oldValue = this.value;

		this.value = value;
		return oldValue;
	}
}