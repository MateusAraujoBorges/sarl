package edu.udel.cis.vsl.sarl.preuniverse.common;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.type.IF.SymbolicTypeFactory;

/**
 * A substituter specified by a single symbolic constant and a value that is to
 * replace that symbolic constant. Bound variables are ignored.
 * 
 * @author Stephen F. Siegel
 */
public class SimpleSubstituter extends ExpressionSubstituter {

	/**
	 * The symbolic constant that is to be replaced.
	 */
	// private SymbolicConstant var;
	private List<SymbolicConstant> vars;

	/**
	 * The symbolic expression that should be substituted for every occurrence
	 * of {@link #var}.
	 */
	// private SymbolicExpression value;
	private List<SymbolicExpression> values;

	/**
	 * The state of the search: a stack of bound symbolic constants. Used so
	 * that bound variables are not replaced. When a quantified expression is
	 * reached, an entry is pushed onto the stack, then the body of the
	 * expression is processed, then the stack is popped.
	 * 
	 * @author siegel
	 */
	class BoundStack implements SubstituterState {
		Deque<SymbolicConstant> stack = new ArrayDeque<>();

		@Override
		public boolean isInitial() {
			return stack.isEmpty();
		}
	}

	public SimpleSubstituter(PreUniverse universe, ObjectFactory objectFactory,
			SymbolicTypeFactory typeFactory, SymbolicConstant var,
			SymbolicExpression value) {
		super(universe, objectFactory, typeFactory);
		this.vars = new ArrayList<>();
		this.values = new ArrayList<>();
		vars.add(var);
		values.add(value);
	}

	public SimpleSubstituter(PreUniverse universe, ObjectFactory objectFactory,
			SymbolicTypeFactory typeFactory, Collection<SymbolicConstant> vars,
			Collection<SymbolicExpression> values) {
		super(universe, objectFactory, typeFactory);
		this.vars = new ArrayList<>();
		this.values = new ArrayList<>();
		this.vars.addAll(vars);
		this.values.addAll(values);
	}

	@Override
	protected SubstituterState newState() {
		return new BoundStack();
	}

	@Override
	protected SymbolicExpression substituteQuantifiedExpression(
			SymbolicExpression expression, SubstituterState state) {
		SymbolicConstant boundVariable = (SymbolicConstant) expression
				.argument(0);
		SymbolicType oldType = expression.type();
		SymbolicType newType = substituteType(oldType, state);

		((BoundStack) state).stack.push(boundVariable);

		SymbolicExpression oldBody = (SymbolicExpression) expression
				.argument(1);
		SymbolicExpression newBody = substituteExpression(oldBody, state);

		((BoundStack) state).stack.pop();

		SymbolicExpression result;

		if (oldBody == newBody && oldType == newType)
			result = expression;
		else
			result = universe.make(expression.operator(), newType,
					new SymbolicObject[] { boundVariable, newBody });
		return result;
	}

	@Override
	protected SymbolicExpression substituteNonquantifiedExpression(
			SymbolicExpression expr, SubstituterState state) {
		if (expr instanceof SymbolicConstant
				&& !((BoundStack) state).stack.contains(expr)) {
			int varsSize = vars.size();
			int valuesSize = values.size();

			for (int i = 0; i < varsSize; i++) {
				SymbolicConstant var = vars.get(i);

				if (var.equals(expr) && valuesSize > i)
					return values.get(i);
			}
		}
		return super.substituteNonquantifiedExpression(expr, state);
	}

}
