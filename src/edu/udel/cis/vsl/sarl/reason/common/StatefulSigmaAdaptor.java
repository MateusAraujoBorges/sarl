package edu.udel.cis.vsl.sarl.reason.common;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicSequence;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;

/**
 * <p>
 * Transform sigma (sum) expressions to the forms that are accepted by all
 * provers
 * </p>
 * 
 * <p>
 * For every sigma expression <code>sigma(l, h, lambda)</code>, create a unique
 * uninterpreted function <code>f</code> which is associated to the
 * <code>lambda</code> expression. Transform the
 * <code>sigma(l, h, lambda)</code> to <code>f(l, h+1)</code>. The second
 * argument is inclusive in sigma but not in <code>f</code>.
 * </p>
 * 
 * <p>
 * A set of axioms over function <code>f</code> are created as well. Currently,
 * two axioms are created for each function <code>f</code>: <code>
 * 1. FORALL _lo, _hi : int, (other-bound-vars decls). 
 *    if (_lo >= _hi) then 0 == f(_lo, _hi) else 
 *      f(_lo, _hi) == f(_lo + 1, _hi) + lambda(_lo)  &&
 *      f(_lo, _hi) == f(_lo, _hi - 1) + lambda(_hi - 1)
 *  
 * 2. FORALL _lo, _mid, _hi : int, (other-bound-vars decls). 
 *    f(_lo, _mid) + f(_mid, _hi)  == f(_lo, _hi)
 * </code>
 * 
 * Axioms can be obtained from interface {@link #getAxioms()}
 * </p>
 * 
 * 
 * @author ziqing
 *
 */
public class StatefulSigmaAdaptor extends ExpressionVisitor
		implements UnaryOperator<SymbolicExpression> {

	private static String SIGMA_LOW_PREFIX = "_lo";

	private static String SIGMA_MID_PREFIX = "_mid";

	private static String SIGMA_HIGH_PREFIX = "_hi";

	private static String UNINTERPRETED_SIGMA_NAME_PREFIX = "$sigma";

	/**
	 * A map that associates each unique lambda expression with a name:
	 */
	private Map<SymbolicExpression, String> uniqueNamesForLambdas;

	/**
	 * A stack for keeping track of bound variables:
	 */
	private Stack<SymbolicConstant> boundVarStack;

	/**
	 * A list of axioms for transformed uninterpreted functions:
	 */
	private List<BooleanExpression> axioms;

	StatefulSigmaAdaptor(PreUniverse universe) {
		super(universe);
		uniqueNamesForLambdas = new HashMap<>();
		boundVarStack = new Stack<>();
		axioms = new LinkedList<>();
	}

	@Override
	public SymbolicExpression apply(SymbolicExpression x) {
		return visitExpression(x);
	}

	@Override
	SymbolicExpression visitExpression(SymbolicExpression expr) {
		switch (expr.operator()) {
		case FORALL:
		case EXISTS:
		case LAMBDA:
			boundVarStack.push((SymbolicConstant) expr.argument(0));
			expr = visitExpressionChildren(expr);
			boundVarStack.pop();
			return expr;
		default:
		}
		if (universe.isSigmaCall(expr))
			return translateSigma(expr);
		else
			return visitExpressionChildren(expr);
	}

	/**
	 * @return axioms for generated uninterpreted functions.
	 */
	List<BooleanExpression> getAxioms() {
		return axioms;
	}

	private SymbolicExpression translateSigma(SymbolicExpression sigma) {
		@SuppressWarnings("unchecked")
		SymbolicSequence<SymbolicExpression> sigmaArguments = (SymbolicSequence<SymbolicExpression>) sigma
				.argument(1);
		SymbolicExpression lambda = (SymbolicExpression) sigmaArguments.get(2);
		// get all bound variables, including ones representing "low", "middle"
		// and "high" and other bound variables belong to superior expressions:
		BoundVariables allBVs = getAllBoundVariables(
				(SymbolicExpression) lambda.argument(1));

		// build the uninterpreted function :
		String unintFuncName = uniqueNamesForLambdas.get(lambda);
		SymbolicExpression unintFunc;
		SymbolicFunctionType unintFuncType = universe.functionType(
				Arrays.asList(universe.integerType(), universe.integerType()),
				sigma.type());
		BooleanExpression predicate;

		if (unintFuncName == null) {
			unintFuncName = UNINTERPRETED_SIGMA_NAME_PREFIX
					+ uniqueNamesForLambdas.size();
			unintFunc = universe.symbolicConstant(
					universe.stringObject(unintFuncName), unintFuncType);
			predicate = expansion(allBVs.low, allBVs.high, lambda, unintFunc,
					sigma.type());
			// add left and right expansion axiom:
			for (SymbolicConstant bv : allBVs.all)
				if (bv != allBVs.mid)
					predicate = universe.forall(bv, predicate);
			axioms.add(predicate);

			// add transitive axiom:
			predicate = transitive(allBVs.low, allBVs.mid, allBVs.high,
					unintFunc);
			for (SymbolicConstant bv : allBVs.all)
				predicate = universe.forall(bv, predicate);
			axioms.add(predicate);
		} else
			unintFunc = universe.symbolicConstant(
					universe.stringObject(unintFuncName), unintFuncType);
		// the "high" is exclusive in provers but inclusive in SARL sigma:
		return universe
				.apply(unintFunc,
						Arrays.asList(sigmaArguments.get(0), universe.add(
								universe.oneInt(),
								(NumericExpression) sigmaArguments.get(1))));
	}

	/**
	 * Put all bounded variables that are needed into an instance of
	 * {@link BoundVariables}
	 */
	private BoundVariables getAllBoundVariables(SymbolicExpression lambda) {
		Set<SymbolicConstant> allVars = universe
				.getFreeSymbolicConstants(lambda);
		Set<String> names = new HashSet<>();
		LinkedList<SymbolicConstant> others = new LinkedList<>();
		int i = 0;
		String lowName, midName, highName;

		for (SymbolicConstant sc : allVars)
			names.add(sc.name().getString());

		do {
			lowName = SIGMA_LOW_PREFIX + i++;
		} while (names.contains(lowName));
		i = 0;
		do {
			midName = SIGMA_MID_PREFIX + i++;
		} while (names.contains(midName));
		i = 0;
		do {
			highName = SIGMA_HIGH_PREFIX + i++;
		} while (names.contains(highName));
		for (SymbolicConstant var : allVars)
			if (boundVarStack.contains(var))
				others.add(var);

		NumericSymbolicConstant low = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject(lowName),
						universe.integerType());
		NumericSymbolicConstant mid = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject(midName),
						universe.integerType());
		NumericSymbolicConstant high = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject(highName),
						universe.integerType());

		others.addFirst(high);
		others.addFirst(mid);
		others.addFirst(low);
		return new BoundVariables(low, mid, high, others);
	}

	private BooleanExpression expansion(NumericExpression low,
			NumericExpression excluHigh, SymbolicExpression lambda,
			SymbolicExpression unintFunc, SymbolicType sigmaType) {
		NumericExpression zero = sigmaType.isInteger() ? universe.zeroInt()
				: universe.zeroReal();
		SymbolicExpression normCase = universe.apply(unintFunc,
				Arrays.asList(low, excluHigh));
		NumericExpression leftInductiveCase = (NumericExpression) universe
				.apply(unintFunc, Arrays.asList(
						universe.add(low, universe.oneInt()), excluHigh));
		NumericExpression leftInductiveAddend = (NumericExpression) universe
				.apply(lambda, Arrays.asList(low));
		NumericExpression rightInductiveCase = (NumericExpression) universe
				.apply(unintFunc, Arrays.asList(low,
						universe.subtract(excluHigh, universe.oneInt())));
		NumericExpression rightInductiveAddend = (NumericExpression) universe
				.apply(lambda, Arrays.asList(
						universe.subtract(excluHigh, universe.oneInt())));

		// axioms:
		BooleanExpression lemmas[] = new BooleanExpression[2];

		// left expansion:
		lemmas[0] = universe.equals(normCase,
				universe.add(leftInductiveCase, leftInductiveAddend));
		// right expansion:
		lemmas[1] = universe.equals(normCase,
				universe.add(rightInductiveCase, rightInductiveAddend));

		return (BooleanExpression) universe.cond(
				universe.lessThanEquals(excluHigh, low),
				universe.equals(normCase, zero),
				universe.and(Arrays.asList(lemmas)));
	}

	private BooleanExpression transitive(NumericExpression low,
			NumericExpression mid, NumericExpression high,
			SymbolicExpression unintFunc) {
		SymbolicExpression normCase = universe.apply(unintFunc,
				Arrays.asList(low, high));
		NumericExpression firstHalfCase = (NumericExpression) universe
				.apply(unintFunc, Arrays.asList(low, mid));
		NumericExpression secondHalfCase = (NumericExpression) universe
				.apply(unintFunc, Arrays.asList(mid, high));

		return universe.equals(normCase,
				universe.add(firstHalfCase, secondHalfCase));
	}

	private class BoundVariables {
		final NumericSymbolicConstant low;
		final NumericSymbolicConstant mid;
		final NumericSymbolicConstant high;
		final List<SymbolicConstant> all;

		BoundVariables(NumericSymbolicConstant low, NumericSymbolicConstant mid,
				NumericSymbolicConstant high, List<SymbolicConstant> all) {
			this.low = low;
			this.mid = mid;
			this.high = high;
			this.all = all;
		}
	}
}
