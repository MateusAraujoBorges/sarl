package performance;


import java.util.Arrays;

import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class PerformanceTest {

	/**
	 * The negation of <code>
	 * 0 <= X_N - 1*Y6 - 1 &&
	 * 0 <= X_N - 1*Y7 - 1 &&
	 * 0 <= X_N - 3 &&
	 * 0 <= Y6 &&
	 * 0 <= Y7 &&
	 * (is_duplet(X_a,0,X_N,Y0,Y1) || (!Y4)) &&
	 * (is_duplet(X_a,0,X_N,Y2,Y3) || (!Y5)) &&
	 * ((0 == X_N - 1*Y6 - 1) || Y4) &&
	 * ((0 == X_N - 1*Y7 - 1) || Y5) &&
	 * ((0 == Y0 - 1*Y6 + 1) || (!Y4)) &&
	 * ((0 == Y2 - 1*Y7 + 1) || (!Y5)) &&
	 * ((0 == Y0) || Y4) &&
	 * ((0 == Y2) || Y5) &&
	 * ((Y0 - 1*Y1 + 1 <= 0) || (!Y4)) &&
	 * ((Y2 - 1*Y3 + 1 <= 0) || (!Y5)) &&
	 * ((0 <= X_N - 1*Y1 - 1) || (!Y4)) &&
	 * ((0 <= X_N - 1*Y3 - 1) || (!Y5)) &&
	 * ((0 <= Y6 - 1) || (!Y4)) &&
	 * ((0 <= Y7 - 1) || (!Y5)) &&
	 * ((0 != X_a[Y0] - 1*X_a[Y2]) || (!Y5)) &&
	 * </code>
	 */
	@Test
	public void slowNegation() {
		SymbolicUniverse u = SARL.newStandardUniverse();
		// types:
		SymbolicType intType = u.integerType();
		SymbolicArrayType arrayType = u.arrayType(intType);
		SymbolicFunctionType funcType = u.functionType(
				Arrays.asList(arrayType, intType, intType, intType, intType),
				u.booleanType());
		// constants:
		NumericSymbolicConstant X_N = (NumericSymbolicConstant) u
				.symbolicConstant(u.stringObject("X_N"), u.integerType());
		NumericSymbolicConstant Y0 = (NumericSymbolicConstant) u
				.symbolicConstant(u.stringObject("Y0"), intType);
		NumericSymbolicConstant Y1 = (NumericSymbolicConstant) u
				.symbolicConstant(u.stringObject("Y1"), intType);
		NumericSymbolicConstant Y2 = (NumericSymbolicConstant) u
				.symbolicConstant(u.stringObject("Y2"), intType);
		NumericSymbolicConstant Y3 = (NumericSymbolicConstant) u
				.symbolicConstant(u.stringObject("Y3"), intType);
		BooleanExpression Y4 = (BooleanExpression) u
				.symbolicConstant(u.stringObject("Y4"), u.booleanType());
		BooleanExpression Y5 = (BooleanExpression) u
				.symbolicConstant(u.stringObject("Y5"), u.booleanType());
		NumericSymbolicConstant Y6 = (NumericSymbolicConstant) u
				.symbolicConstant(u.stringObject("Y6"), intType);
		NumericSymbolicConstant Y7 = (NumericSymbolicConstant) u
				.symbolicConstant(u.stringObject("Y7"), intType);
		SymbolicConstant array = u.symbolicConstant(u.stringObject("X_a"),
				arrayType);
		SymbolicConstant isDuplet = u
				.symbolicConstant(u.stringObject("is_duplet"), funcType);
		// clauses:
		BooleanExpression clauses[] = new BooleanExpression[15];

		clauses[0] = u.or(u.equals(u.oneInt(), u.subtract(X_N, Y6)), Y4);
		clauses[1] = u.or(u.equals(u.oneInt(), u.subtract(X_N, Y7)), Y5);
		clauses[2] = u.or(u.equals(Y6, u.add(Y0, u.oneInt())), u.not(Y4));
		clauses[3] = u.or(u.equals(Y7, u.add(Y2, u.oneInt())), u.not(Y5));
		clauses[4] = u.or(u.equals(Y0, u.zeroInt()), Y4);
		clauses[5] = u.or(u.equals(Y2, u.zeroInt()), Y5);
		clauses[6] = u.or(u.lessThanEquals(u.add(Y0, u.oneInt()), Y1),
				u.not(Y4));
		clauses[7] = u.or(u.lessThanEquals(u.add(Y2, u.oneInt()), Y3),
				u.not(Y5));
		clauses[8] = u.or(u.lessThanEquals(Y1, u.subtract(X_N, u.oneInt())),
				u.not(Y4));
		clauses[9] = u.or(u.lessThanEquals(Y3, u.subtract(X_N, u.oneInt())),
				u.not(Y5));
		clauses[10] = u.or(u.lessThanEquals(u.oneInt(), Y6), u.not(Y4));
		clauses[11] = u.or(u.lessThanEquals(u.oneInt(), Y7), u.not(Y5));
		clauses[12] = u.or(
				u.neq(u.zeroInt(),
						u.subtract((NumericExpression) u.arrayRead(array, Y0),
								(NumericExpression) u.arrayRead(array, Y2))),
				u.not(Y5));
		clauses[13] = u.or(
				(BooleanExpression) u.apply(isDuplet,
						Arrays.asList(array, u.zeroInt(), X_N, Y0, Y1)),
				u.not(Y4));
		clauses[14] = u.or(
				(BooleanExpression) u.apply(isDuplet,
						Arrays.asList(array, u.zeroInt(), X_N, Y2, Y3)),
				u.not(Y5));
		// test:
		u.not(u.and(Arrays.asList(clauses)));
	}
}
