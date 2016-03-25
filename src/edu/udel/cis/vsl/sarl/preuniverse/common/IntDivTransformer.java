package edu.udel.cis.vsl.sarl.preuniverse.common;

import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.TheoremProverException;
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;

public class IntDivTransformer implements UnaryOperator<SymbolicExpression>{
	
	private boolean inForallOrExists = false;
	@Override
	public SymbolicExpression apply(SymbolicExpression x) {
		// TODO Auto-generated method stub
		return null;
	}
	
	private Transformation transform(SymbolicExpression expression){
		SymbolicOperator operator = expression.operator();
		
		/**
		 * If not within a quantifier, the current translation is doing fine.
		 * So no changes.
		 */
		if(!inForallOrExists && !(operator == SymbolicOperator.FORALL
				|| operator == SymbolicOperator.EXISTS))
			return new Transformation(expression);
		
		switch(operator){
		case ADD: 
		case AND:
			return transformKeySet(expression);
		case APPLY:
			return transformApply(expression);
		case ARRAY:
			return new Transformation(expression);
		case ARRAY_LAMBDA:
			throw new TheoremProverException(
					"Array lambdas are not supported by CVC");
		case ARRAY_READ:
			return new Transformation(expression);
		case ARRAY_WRITE:
			return new Transformation(expression);
		case CAST:
			return new Transformation(expression);
		case CONCRETE:
			return new Transformation(expression);
		default:
			throw new SARLInternalException(
					"unreachable: unknown operator: " + operator);
		}
	}
	
	private Transformation transformApply(SymbolicExpression expression) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * MULTIPLY; ADD
	 * AND; OR
	 * 
	 * @param operator
	 * @param defaultValue
	 * @param expression
	 * @return
	 */
	private Transformation transformKeySet(SymbolicExpression expression) {
		return null;
	}
}
