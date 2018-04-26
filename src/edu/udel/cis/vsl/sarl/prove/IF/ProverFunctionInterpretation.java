package edu.udel.cis.vsl.sarl.prove.IF;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * <p>
 * A data structure that represents the interpretation of a
 * {@link LogicFunction}. An instance of {@link ProverFunctionInterpretation}
 * consists of a {@link String} type identifier which identifies a logic
 * function, a list of formal parameters which are {@link SymbolicConstant}s and
 * a definition which is a {@link SymbolicExpression}.
 * </p>
 * 
 * <p>
 * Provers can translate {@link ProverFunctionInterpretation} as function
 * definitions in their languages.
 * </p>
 * 
 * @author ziqing
 */
public class ProverFunctionInterpretation
		implements Comparable<ProverFunctionInterpretation> {

	public final SymbolicExpression definition;

	public final SymbolicConstant parameters[];

	public final String identifier;

	private ProverFunctionInterpretation(String identifier,
			SymbolicConstant parameters[], SymbolicExpression definition) {
		this.definition = definition;
		this.identifier = identifier;
		this.parameters = parameters;
	}

	public static ProverFunctionInterpretation newProverPredicate(
			String identifier, SymbolicConstant parameters[],
			SymbolicExpression definition) {
		return new ProverFunctionInterpretation(identifier, parameters,
				definition);
	}

	@Override
	public int hashCode() {
		return identifier.hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == this)
			return true;
		else if (obj instanceof ProverFunctionInterpretation) {
			ProverFunctionInterpretation ppd = (ProverFunctionInterpretation) obj;

			return ppd.identifier.equals(ppd.identifier);
		}
		return false;
	}

	@Override
	public int compareTo(ProverFunctionInterpretation o) {
		return identifier.compareTo(o.identifier);
	}
}
