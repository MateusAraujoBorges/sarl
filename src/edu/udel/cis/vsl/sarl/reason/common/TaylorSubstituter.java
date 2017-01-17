package edu.udel.cis.vsl.sarl.reason.common;

import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicSequence;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTypeSequence;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.preuniverse.common.ExpressionSubstituter;
import edu.udel.cis.vsl.sarl.type.IF.SymbolicTypeFactory;

public class TaylorSubstituter extends ExpressionSubstituter {

	private SymbolicConstant[] limitVars;

	private int[] orders;

	private NumericExpression[] lowerBounds;

	private NumericExpression[] upperBounds;

	/**
	 * Reasoner containing expanded context, which includes assumptions on index
	 * variables.
	 */
	private Reasoner reasoner;

	public TaylorSubstituter(PreUniverse universe, ObjectFactory objectFactory,
			SymbolicTypeFactory typeFactory) {
		super(universe, objectFactory, typeFactory);
		// TODO Auto-generated constructor stub
	}

	@Override
	protected SubstituterState newState() {
		// TODO Auto-generated method stub
		return null;
	}

	private boolean isConstantMultiple(NumericExpression expr,
			NumericSymbolicConstant h) {
		if (expr.equals(h))
			return true;
		if (expr.operator() == SymbolicOperator.MULTIPLY) {
			NumericExpression arg0 = (NumericExpression)expr.argument(0);
		}
	
		return false;
	}

	@Override
	protected SymbolicExpression substituteExpression(
			SymbolicExpression expression, SubstituterState state) {
		if (expression.operator() != SymbolicOperator.APPLY)
			return expression;

		SymbolicExpression function = (SymbolicExpression) expression
				.argument(0);

		if (function.operator() != SymbolicOperator.SYMBOLIC_CONSTANT)
			return expression;

		SymbolicFunctionType functionType = (SymbolicFunctionType) function
				.type();

		if (!functionType.outputType().isReal())
			return expression;

		SymbolicTypeSequence inputTypes = functionType.inputTypes();
		int n = inputTypes.numTypes();

		for (int i = 0; i < n; i++) {
			if (!inputTypes.getType(i).isReal())
				return expression;
		}

		SymbolicSequence<SymbolicExpression> args = (SymbolicSequence<SymbolicExpression>) expression
				.argument(1);

		for (int i = 0; i < n; i++) {
			NumericExpression arg = (NumericExpression) args.get(i);
			BooleanExpression inDomain = universe.and(
					universe.lessThanEquals(lowerBounds[i], arg),
					universe.lessThanEquals(arg, upperBounds[i]));

			if (!reasoner.isValid(inDomain))
				return expression;
		}

		for (int i = 0; i < n; i++) {
			NumericExpression arg = (NumericExpression) args.get(i);
			SymbolicOperator op = arg.operator();

			if (op == SymbolicOperator.ADD) {
				// can have 1 or 2 arguments
			} else if (op == SymbolicOperator.SUBTRACT) {
				// has 2 arguments
			}
		}
		// look for +/- constant*hi

		// TODO: store differentiability information in type?

		return null;
	}

}
