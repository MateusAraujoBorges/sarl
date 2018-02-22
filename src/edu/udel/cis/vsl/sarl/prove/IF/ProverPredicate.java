package edu.udel.cis.vsl.sarl.prove.IF;

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;

/**
 * <p>
 * A data structure that stores all informations of a prover predicate,
 * including the name (identifier), formal parameters and a boolean definition
 * expression.
 * <code>predicate [identifier] ([formal-parameters]) = [definition]</code>
 * </p>
 * 
 * <p>
 * A prover predicate is used to factor complex and common boolean expression in
 * prover queries and contexts
 * </p>
 * 
 * @author ziqing
 */
public class ProverPredicate implements Comparable<ProverPredicate> {

	public final BooleanExpression definition;

	public final SymbolicConstant parameters[];

	public final String identifier;

	private ProverPredicate(String identifier, SymbolicConstant parameters[],
			BooleanExpression definition) {
		this.definition = definition;
		this.identifier = identifier;
		this.parameters = parameters;
	}

	public static ProverPredicate newProverPredicate(String identifier,
			SymbolicConstant parameters[], BooleanExpression definition) {
		return new ProverPredicate(identifier, parameters, definition);
	}

	@Override
	public int hashCode() {
		return identifier.hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == this)
			return true;
		else if (obj instanceof ProverPredicate) {
			ProverPredicate ppd = (ProverPredicate) obj;

			return ppd.identifier.equals(ppd.identifier);
		}
		return false;
	}

	@Override
	public int compareTo(ProverPredicate o) {
		return identifier.compareTo(o.identifier);
	}
}
