package edu.udel.cis.vsl.sarl.simplify;

import static org.junit.Assert.assertTrue;

import java.io.PrintStream;
import java.util.Arrays;

import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class SimplifyExpressionTest {

	private static PrintStream out = System.out;

	private static SymbolicUniverse universe = SARL.newStandardUniverse();

	private static SymbolicType boolType = universe.booleanType();

	private static SymbolicType intType = universe.integerType();

	@BeforeClass
	public static void setUpBeforeClass() {
		universe.setUseBackwardSubstitution(true);
	}

	@Test
	public void conditionalExpr() {
		// given X?Y:Y, it should be simplified to be Y
		SymbolicConstant X = universe
				.symbolicConstant(universe.stringObject("X"), boolType);
		SymbolicConstant Y = universe
				.symbolicConstant(universe.stringObject("Y"), intType);
		SymbolicExpression cond = universe.cond((BooleanExpression) X, Y, Y);
		Reasoner reasoner = universe.reasoner(universe.trueExpression());
		SymbolicExpression symplified = reasoner.simplify(cond);

		out.println("original expression: " + cond);
		out.println("symplified expression: " + symplified);
		assertTrue(universe.equals(Y, symplified).isTrue());
	}

	@Test
	public void simplifyOpenRange() {
		// When simplify following expression:
		// (x + 1 <= 0) || (x + 2 <= 0) || (0 <= x - 2) || (0 <= x - 1)
		// an error will happen.
		NumericSymbolicConstant x = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("X"),
						universe.integerType());
		BooleanExpression predicate, clause0, clause1, clause2, clause3;

		clause0 = universe.lessThanEquals(x, universe.minus(universe.oneInt()));

		clause1 = universe.lessThanEquals(x,
				universe.minus(universe.integer(2)));
		clause2 = universe.lessThanEquals(universe.oneInt(), x);
		clause3 = universe.lessThanEquals(universe.integer(2), x);
		predicate = universe
				.or(Arrays.asList(clause0, clause1, clause2, clause3));
		predicate = universe.reasoner(universe.trueExpression())
				.simplify(predicate);
		out.println(predicate);
	}

	// context : X_N - 1*Y3 <= 0 && 0 <= X_N - 1*Y3 && 0 <= X_N - 1 && 0 <= Y3
	// simplified : 0 <= Y3 - 1
	// query: 0 <= X_N
	// expected result: YES
	@Test
	public void backwradsSubstitutionTest() {
		universe.setUseBackwardSubstitution(true);

		SymbolicUniverse u = universe;
		NumericSymbolicConstant X_N = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("X_N"),
						universe.integerType());
		NumericSymbolicConstant Y3 = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("Y3"), intType);
		BooleanExpression context = u.and(Arrays.asList(
				u.lessThanEquals(X_N, Y3), u.lessThanEquals(Y3, X_N),
				u.lessThanEquals(u.oneInt(), X_N),
				u.lessThanEquals(u.zeroInt(), Y3)));

		Reasoner reasoner = u.reasoner(context);

		out.println(context);
		out.println(reasoner.getReducedContext());
		assertTrue(reasoner.isValid(u.lessThanEquals(u.zeroInt(), X_N)));
	}

	@Test
	// context:
	// forall i0 : int . ((Y7[i0] == Y6[i0]) || (_uf_$mpi_sizeof(Y9)*Y8 - 1*i0
	// <= 0) || (i0 + 1 <= 0))
	// forall i0 : int . ((Y7[i0] == Y11[i0]) || (2*_uf_$mpi_sizeof(Y9)*Y8 -
	// 1*i0 <= 0) || (i0 + 1 <= 0))
	public void backwardsSubstitutionWithForall() {
		NumericSymbolicConstant i = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("i"), intType);
		SymbolicConstant Y6, Y7, Y11;
		NumericSymbolicConstant N, X;

		N = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("N"), intType);
		X = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("X"), intType);
		Y6 = universe.symbolicConstant(universe.stringObject("Y6"),
				universe.arrayType(intType, N));
		Y7 = universe.symbolicConstant(universe.stringObject("Y7"),
				universe.arrayType(intType, N));
		Y11 = universe.symbolicConstant(universe.stringObject("Y11"),
				universe.arrayType(intType, X));

		BooleanExpression pred0 = universe.equals(universe.arrayRead(Y6, i),
				universe.arrayRead(Y7, i));
		BooleanExpression pred1 = universe.equals(universe.arrayRead(Y11, i),
				universe.arrayRead(Y7, i));
		BooleanExpression context = universe.forallInt(i, universe.zeroInt(), N,
				pred0);

		context = universe.and(context,
				universe.forallInt(i, universe.zeroInt(), N, pred1));
		context = universe.and(context, universe.equals(N, X));

		Reasoner reasoner = universe.reasoner(context);

		out.println("full context    : " + reasoner.getFullContext());
		out.println("reduced context : " + reasoner.getReducedContext());
		out.println("SubMap: " + reasoner.constantSubstitutionMap());
		out.println();

		SymbolicExpression arrayLambdaY7 = universe.arrayLambda(
				universe.arrayType(intType, N),
				universe.lambda(i, universe.arrayRead(Y7, i)));
		SymbolicExpression arrayLambdaY6 = universe.arrayLambda(
				universe.arrayType(intType, N),
				universe.lambda(i, universe.arrayRead(Y6, i)));
		SymbolicExpression arrayLambdaY11 = universe.arrayLambda(
				universe.arrayType(intType, N),
				universe.lambda(i, universe.arrayRead(Y11, i)));

		out.println(arrayLambdaY7);
		out.println(reasoner.simplify(arrayLambdaY7));
		out.println(arrayLambdaY6);
		out.println(reasoner.simplify(arrayLambdaY6));
		out.println(arrayLambdaY11);
		out.println(reasoner.simplify(arrayLambdaY11));
		assertTrue(reasoner.simplify(arrayLambdaY7)
				.equals(reasoner.simplify(arrayLambdaY6)));
		assertTrue(reasoner.simplify(arrayLambdaY7)
				.equals(reasoner.simplify(arrayLambdaY11)));
	}
}
