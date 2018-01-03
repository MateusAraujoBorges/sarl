package edu.udel.cis.vsl.sarl.prove.why3;

import java.util.Stack;

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject.SymbolicObjectKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.util.Pair;

/**
 * Transform away ARRAY_LAMBDA expression in quantified expressions.
 * 
 * @author ziqing
 */
class ContextualArrayLambdaTransfomer {
	private static enum CONTEXT_KIND {
		FORALL, EXIST
	}

	private PreUniverse universe;

	private Stack<Pair<SymbolicConstant, CONTEXT_KIND>> contexts;

	private Stack<BooleanExpression> arrayLambdaAxioms;

	private int counter = 0;

	ContextualArrayLambdaTransfomer(PreUniverse universe) {
		this.universe = universe;
		this.contexts = new Stack<>();
		this.arrayLambdaAxioms = new Stack<>();
	}

	/**
	 * transform from <code>
	 * forall int i. ... (ARRAY_LAMBDA int k. p(i, k))...
	 * </code> to <code>
	 * constant T c[]
	 * 
	 * forall int i. 
	 *   (forall int j. c[j] == p(i, j)) =>
	 *  ... c ...
	 * </code>
	 * 
	 * @param expr
	 * @return
	 */
	BooleanExpression transform(BooleanExpression expr) {
		return (BooleanExpression) visitExpression(expr);
	}

	private SymbolicExpression visitExpressionChildren(
			SymbolicExpression expr) {
		boolean changed = false;
		int numArgs = expr.numArguments();
		SymbolicObject newArgs[] = new SymbolicObject[numArgs];

		for (int i = 0; i < numArgs; i++) {
			SymbolicObject arg = expr.argument(i);

			if (arg.symbolicObjectKind() == SymbolicObjectKind.EXPRESSION) {
				newArgs[i] = visitExpression((SymbolicExpression) arg);
				if (newArgs[i] != arg)
					changed = true;
			} else
				newArgs[i] = arg;
		}
		if (changed)
			return universe.make(expr.operator(), expr.type(), newArgs);
		else
			return expr;
	}

	private SymbolicExpression visitExpression(SymbolicExpression expr) {
		SymbolicOperator operator = expr.operator();
		SymbolicConstant boundVar;
		SymbolicExpression result;
		CONTEXT_KIND kind;

		if (operator == SymbolicOperator.FORALL) {
			boundVar = (SymbolicConstant) expr.argument(0);
			kind = CONTEXT_KIND.FORALL;
		} else if (operator == SymbolicOperator.EXISTS) {
			boundVar = (SymbolicConstant) expr.argument(0);
			kind = CONTEXT_KIND.EXIST;
		} else if (operator == SymbolicOperator.ARRAY_LAMBDA) {
			return visitArrayLambda(expr);
		} else
			return this.visitExpressionChildren(expr);

		contexts.push(new Pair<>(boundVar, kind));
		arrayLambdaAxioms.push(universe.trueExpression());
		result = visitExpressionChildren(expr);

		BooleanExpression axiom = arrayLambdaAxioms.pop();

		if (!axiom.isTrue()) {
			BooleanExpression pred = (BooleanExpression) result.argument(1);
			SymbolicObject newargs[] = new SymbolicObject[2];

			if (kind == CONTEXT_KIND.FORALL) {
				pred = universe.implies(axiom, pred);
			} else if (kind == CONTEXT_KIND.EXIST)
				pred = universe.and(axiom, pred);
			newargs[0] = result.argument(0);
			newargs[1] = pred;
			result = universe.make(operator, universe.booleanType(), newargs);
		}
		contexts.pop();
		return result;
	}

	/**
	 * If the array lambda is inside an quantified context, replacing array
	 * lambda with a fresh new symbolic constant of the same array type. Add an
	 * axiom for this array lambda to the {@link #arrayLambdaAxioms}
	 * 
	 * @param expr
	 *            an array lambda expression
	 * @return the equivalent array expression
	 */
	private SymbolicExpression visitArrayLambda(SymbolicExpression expr) {
		if (this.contexts.isEmpty())
			return expr;

		String boundVarRootName = contexts.peek().left.name().getString();
		SymbolicArrayType arrayType = (SymbolicArrayType) expr.type();
		SymbolicConstant substitutor = universe.symbolicConstant(
				universe.stringObject(boundVarRootName + "_arr_" + counter++),
				arrayType);
		SymbolicExpression lambdaApplication = visitExpressionChildren(expr);
		SymbolicExpression substitutorElement = substitutor;
		int dims = arrayType.dimensions();
		NumericSymbolicConstant axiomBoundVars[] = new NumericSymbolicConstant[dims];

		for (int i = 0; i < dims; i++) {
			axiomBoundVars[i] = (NumericSymbolicConstant) universe
					.symbolicConstant(
							universe.stringObject(
									boundVarRootName + "_" + counter++),
							universe.integerType());
			lambdaApplication = universe.arrayRead(lambdaApplication,
					axiomBoundVars[i]);
			substitutorElement = universe.arrayRead(substitutorElement,
					axiomBoundVars[i]);
		}

		BooleanExpression axiom = universe.equals(lambdaApplication,
				substitutorElement);
		NumericExpression extents[] = new NumericExpression[dims];

		extents[0] = arrayType.isComplete()
				? ((SymbolicCompleteArrayType) arrayType).extent() : null;
		for (int i = 1; i < dims; i++) {
			arrayType = (SymbolicArrayType) arrayType.elementType();
			extents[i] = arrayType.isComplete()
					? ((SymbolicCompleteArrayType) arrayType).extent() : null;
		}
		for (int i = dims - 1; i >= 0; i--) {
			if (extents[i] != null)
				axiom = universe.forallInt(axiomBoundVars[i],
						universe.zeroInt(), extents[i],
						(BooleanExpression) axiom);
			else
				axiom = universe.forall(axiomBoundVars[i], axiom);
		}
		axiom = universe.and(arrayLambdaAxioms.pop(),
				(BooleanExpression) axiom);
		arrayLambdaAxioms.push((BooleanExpression) axiom);
		return substitutor;
	}
}
