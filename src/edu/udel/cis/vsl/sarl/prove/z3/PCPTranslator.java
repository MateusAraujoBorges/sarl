package edu.udel.cis.vsl.sarl.prove.z3;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.util.FastList;

public class PCPTranslator extends Z3Translator {

	public PCPTranslator(PreUniverse universe, SymbolicExpression theExpression, boolean simplifyIntDivision) {
		super(universe, theExpression, simplifyIntDivision);
	}


	@Override
	protected FastList<String> translateSymbolicConstant(
					SymbolicConstant symbolicConstant, boolean isBoundVariable) {
		String name = symbolicConstant.name().getString();
		FastList<String> result = new FastList<>(name);
		SymbolicType symbolicType = symbolicConstant.type();

		if (symbolicType.typeKind() == SymbolicType.SymbolicTypeKind.FUNCTION) {
			z3Declarations.append(functionDeclaration(name,
							(SymbolicFunctionType) symbolicType));
		} else {
			if (!isBoundVariable) {
				String type;
				Number lo, hi;
				switch (symbolicConstant.type().typeKind()) {
					case INTEGER:
						type = "Int"; //TODO add longs
						lo = Integer.MIN_VALUE;
						hi = Integer.MAX_VALUE;
						break;
					case BOOLEAN:
						type = "Int";
						lo = 0;
						hi = 1;
						break;
					case CHAR:
						type = "Int";
						lo = -128;
						hi = 127;
						break;
					default:
						throw new UnsupportedOperationException("Unsupported type: " + symbolicConstant);
				}

				z3Declarations.addAll("(declare-var ", name, " (", type, " ",
								lo + "", " ", hi + "", "))\n");
			}
		}
		variableMap.put(symbolicConstant, result); // currently not used
		expressionMap.put(symbolicConstant, result);
		return result.clone();
	}

	// might need to implement this one
//	private FastList<String> translateCond(SymbolicExpression expression) {
//		// syntax: (ite b x y)
//		FastList<String> result = new FastList<>("(ite ");
//
//		result.append(translate((SymbolicExpression) expression.argument(0)));
//		result.add(" ");
//		result.append(translate((SymbolicExpression) expression.argument(1)));
//		result.add(" ");
//		result.append(translate((SymbolicExpression) expression.argument(2)));
//		result.add(")");
//		return result;
//	}
}
