package edu.udel.cis.vsl.sarl.simplify;

import static org.junit.Assert.assertTrue;

import java.util.Arrays;

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
	private static SymbolicUniverse universe = SARL.newStandardUniverse();
	private static SymbolicType boolType = universe.booleanType();
	private static SymbolicType intType = universe.integerType();

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

		System.out.println("original expression: " + cond);
		System.out.println("symplified expression: " + symplified);
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
		System.out.println(predicate);
	}
}
