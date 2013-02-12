package edu.udel.cis.vsl.sarl.symbolic.standard;

import java.util.Arrays;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpressionIF;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTypeIF;
import edu.udel.cis.vsl.sarl.expr.common.CommonSymbolicExpression;
import edu.udel.cis.vsl.sarl.symbolic.IF.tree.TreeExpressionIF;

/**
 * A standard symbolic expression is the most simple representation of a
 * symbolic expression: a tree in which the non-leaf nodes are operators and the
 * leaf nodes are symbolic constants or concrete values.
 * 
 * @author siegel
 * 
 */
public class StandardSymbolicExpression extends CommonSymbolicExpression implements
		TreeExpressionIF {

	private SymbolicExpressionIF[] arguments;

	private SymbolicOperator kind;

	public StandardSymbolicExpression(SymbolicOperator kind, SymbolicTypeIF type,
			SymbolicExpressionIF[] arguments) {
		super(type);
		this.kind = kind;
		this.arguments = arguments;
	}

	@Override
	public TreeExpressionIF argument(int index) {
		return (TreeExpressionIF) arguments[index];
	}

	@Override
	public SymbolicOperator operator() {
		return kind;
	}

	@Override
	public int numArguments() {
		return arguments.length;
	}

	@Override
	public String toString() {
		String result = kind.toString() + "(";

		for (int i = 0; i < arguments.length; i++) {
			SymbolicExpressionIF argument = arguments[i];

			if (i > 0)
				result += ",";
			result += argument;
		}
		result += ")";
		return result;
	}

	@Override
	public String atomString() {
		return toString();
	}

	@Override
	protected boolean intrinsicEquals(CommonSymbolicExpression expression) {
		if (expression instanceof StandardSymbolicExpression) {
			StandardSymbolicExpression that = (StandardSymbolicExpression) expression;

			return type().equals(that.type()) && kind.equals(that.kind)
					&& Arrays.equals(arguments, that.arguments);
		}
		return false;
	}

	@Override
	protected int intrinsicHashCode() {
		return type().hashCode() + kind.hashCode() + Arrays.hashCode(arguments);
	}
}
