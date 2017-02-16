package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.PrintStream;
import java.util.Arrays;

import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class OrderOfAccuracyTest {

	private static PrintStream out = System.out;

	private static SymbolicUniverse universe = SARL.newStandardUniverse();

	private static NumericExpression zeroInt = universe.zeroInt();

	private static SymbolicType real = universe.realType();

	private static SymbolicType integer = universe.integerType();

	private static SymbolicFunctionType r2 = universe
			.functionType(Arrays.asList(real, real), real);

	private static SymbolicConstant f = universe
			.symbolicConstant(universe.stringObject("f"), r2);

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@Test
	public void deriv1() {
		SymbolicExpression df0 = universe.derivative(f, universe.intObject(0),
				universe.intObject(1));

		out.println(df0);
		assertEquals(f, df0.argument(0));
		assertEquals(universe.intObject(0), df0.argument(1));
		assertEquals(universe.intObject(1), df0.argument(2));
		assertEquals(3, df0.numArguments());
	}

	@Test
	public void diff1() {
		BooleanExpression diff = universe.differentiable(f,
				universe.intObject(4),
				Arrays.asList(universe.rational(1.0), universe.rational(2.0)),
				Arrays.asList(universe.rational(2.0), universe.rational(3.0)));

		out.println(diff);
		assertEquals(f, diff.argument(0));
		assertEquals(universe.intObject(4), diff.argument(1));
	}

	@Test
	public void arraySolution1() {
		// n>=0
		// assume forall i in [0..n-1] a[i] = f(i*h,i*h)

		universe.setShowQueries(true);
		universe.setShowProverQueries(true);

		NumericSymbolicConstant h = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("h"), real);
		NumericSymbolicConstant n = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("n"), integer);
		SymbolicArrayType arrayType = universe.arrayType(real, n);
		SymbolicConstant a = universe
				.symbolicConstant(universe.stringObject("a"), arrayType);
		NumericSymbolicConstant i = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("i"), integer);
		NumericSymbolicConstant j = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("j"), integer);
		NumericExpression ih = universe
				.multiply((NumericExpression) universe.cast(real, i), h);
		BooleanExpression p0 = universe.lessThanEquals(zeroInt, n);
		BooleanExpression p1 = universe.forallInt(i, zeroInt, n,
				universe.equals(universe.arrayRead(a, i),
						universe.apply(f, Arrays.asList(ih, ih))));
		BooleanExpression context = universe.and(p0, p1);
		Reasoner reasoner = universe.reasoner(context);
		SymbolicExpression expr = universe.arrayRead(a, j);
		SymbolicExpression result = reasoner.simplify(expr);
		NumericExpression jh = universe
				.multiply((NumericExpression) universe.cast(real, j), h);
		NumericExpression expected = (NumericExpression) universe.apply(f,
				Arrays.asList(jh, jh));

		out.println("Context    : " + context);
		out.println("Reduced    : " + reasoner.getReducedContext());
		out.println("Expression : " + expr);
		out.println("Result     : " + result);
		out.println("Expected   : " + expected);

		assertEquals(expected, result);
	}

	@Test
	public void arraySolution2() {
		// n>=0, m>=0
		// real a[n][m];
		// assume forall i in [0..n-1] . forall j in [0..m-1] .
		// a[i][j] = f(i*h,j*h)
		NumericSymbolicConstant h = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("h"), real);
		NumericSymbolicConstant n = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("n"), integer);
		NumericSymbolicConstant m = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("m"), integer);
		SymbolicArrayType arrayType = universe
				.arrayType(universe.arrayType(real, m), n);
		SymbolicConstant a = universe
				.symbolicConstant(universe.stringObject("a"), arrayType);
		NumericSymbolicConstant i = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("i"), integer);
		NumericSymbolicConstant j = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("j"), integer);
		NumericExpression ih = universe
				.multiply((NumericExpression) universe.cast(real, i), h);
		NumericExpression jh = universe
				.multiply((NumericExpression) universe.cast(real, j), h);
		BooleanExpression p0 = universe.lessThanEquals(zeroInt, n);
		BooleanExpression p1 = universe.lessThanEquals(zeroInt, m);
		NumericExpression aij = (NumericExpression) universe
				.arrayRead(universe.arrayRead(a, i), j);
		BooleanExpression p2 = universe.forallInt(i, zeroInt, n,
				universe.forallInt(j, zeroInt, m, universe.equals(aij,
						universe.apply(f, Arrays.asList(ih, jh)))));
		BooleanExpression context = universe.and(Arrays.asList(p0, p1, p2));
		Reasoner reasoner = universe.reasoner(context);
		SymbolicExpression expr = universe.arrayRead(
				universe.arrayRead(a, universe.integer(3)),
				universe.integer(4));
		SymbolicExpression result = reasoner.simplify(expr);

		NumericExpression expected = (NumericExpression) universe.apply(f,
				Arrays.asList(universe.multiply(universe.rational(3), h),
						universe.multiply(universe.rational(4), h)));

		out.println("Context    : " + context);
		out.println("Reduced    : " + reasoner.getReducedContext());
		out.println("Expression : " + expr);
		out.println("Result     : " + result);
		out.println("Expected   : " + expected);

		assertEquals(expected, result);
	}

	@Test
	public void taylor1() {
		// f:R^2 -> R
		// f(x+h,y) = f(x,y) + f'(x,y)h + f''(x,y)h^2/2 +O(h^3)
		// assume h as 3 derivs in [0,1]x[0,1]

		universe.setShowQueries(true);
		universe.setShowProverQueries(true);

		NumericExpression a = universe.zeroReal();
		NumericExpression b = universe.oneReal();
		NumericExpression a1 = universe.rational(0.01);
		NumericExpression b1 = universe.rational(0.99);
		BooleanExpression differentiable = universe.differentiable(f,
				universe.intObject(3), Arrays.asList(a, a),
				Arrays.asList(b, b));
		NumericSymbolicConstant x = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("x"), real);
		NumericSymbolicConstant y = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("y"), real);
		NumericSymbolicConstant h = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("h"), real);
		BooleanExpression xInRange = universe.and(
				universe.lessThanEquals(a1, x), universe.lessThanEquals(x, b1));
		BooleanExpression yInRange = universe.and(
				universe.lessThanEquals(a1, y), universe.lessThanEquals(y, b1));
		NumericExpression expr0 = (NumericExpression) universe.apply(f,
				Arrays.asList(universe.add(x, h), y));
		NumericExpression f0 = (NumericExpression) universe.apply(f,
				Arrays.asList(x, y));
		SymbolicExpression df = universe.derivative(f, universe.intObject(0),
				universe.intObject(1));
		SymbolicExpression ddf = universe.derivative(f, universe.intObject(0),
				universe.intObject(2));
		NumericExpression f1 = universe.multiply(
				(NumericExpression) universe.apply(df, Arrays.asList(x, y)), h);
		NumericExpression f2 = universe.divide(
				universe.multiply((NumericExpression) universe.apply(ddf,
						Arrays.asList(x, y)), universe.multiply(h, h)),
				universe.rational(2));
		NumericExpression expr1 = universe.add(Arrays.asList(f0, f1, f2));
		BooleanExpression context = differentiable;
		Reasoner reasoner = universe.reasoner(context);
		BooleanExpression indexConstraint = universe.and(xInRange, yInRange);
		NumericExpression lhs = universe.subtract(expr1, expr0);
		NumericSymbolicConstant[] limitVars = new NumericSymbolicConstant[] {
				h };
		int[] orders = new int[] { 3 };

		out.println(reasoner.getReducedContext());

		boolean result = reasoner.checkBigOClaim(indexConstraint, lhs,
				limitVars, orders);
		assertTrue(result);
	}

	@Test
	public void derivativeProve() {
		
		universe.setShowQueries(true);
		universe.setShowProverQueries(true);
		// $abstract $differentiable(3, [-1.0,1.0]) $real rho($real x);
		SymbolicFunctionType functionType = universe.functionType(
				Arrays.asList(universe.realType()), universe.realType());
		SymbolicConstant rho = universe
				.symbolicConstant(universe.stringObject("rho"), functionType);
		BooleanExpression context = universe.differentiable(rho,
				universe.intObject(3),
				Arrays.asList(universe.minus(universe.oneReal())),
				Arrays.asList(universe.oneReal()));
		// result[] array:
		SymbolicConstant result = universe.symbolicConstant(
				universe.stringObject("Y3"),
				universe.arrayType(universe.realType()));
		// dx constant:
		NumericSymbolicConstant dx = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("X_dx"),
						universe.realType());
		// 0 < dx < 1:
		context = universe.and(context,
				universe.and(universe.lessThan(universe.zeroReal(), dx),
						universe.lessThan(dx, universe.oneReal())));
		// forall j : int . ((0 == Y3[j]*X_dx + (1/2)*rho(((real)j - 1)*X_dx) +
		// (-1/2)*rho(((real)j + 1)*X_dx)) || (Y2 - 1*j <= 0) || (j <= 0))
		NumericSymbolicConstant j = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("j"),
						universe.integerType());
		NumericSymbolicConstant Y2 = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("Y2"),
						universe.integerType());

		NumericExpression Y3_j_dx = universe.multiply(
				(NumericExpression) universe.arrayRead(result, j), dx);
		NumericExpression j_minus_1_dx = universe.multiply(universe.subtract(
				(NumericExpression) universe.cast(universe.realType(), j),
				universe.oneReal()), dx);
		NumericExpression j_add_1_dx = universe.multiply(universe.add(
				(NumericExpression) universe.cast(universe.realType(), j),
				universe.oneReal()), dx);
		NumericExpression one_over_2 = universe.divide(universe.oneReal(),
				universe.number(universe.numberFactory().number("2.0")));
		NumericExpression sum = Y3_j_dx;

		sum = universe.add(sum,
				universe.multiply(one_over_2, (NumericExpression) universe
						.apply(rho, Arrays.asList(j_minus_1_dx))));
		sum = universe.add(sum,
				universe.multiply(universe.minus(one_over_2),
						(NumericExpression) universe.apply(rho,
								Arrays.asList(j_add_1_dx))));

		BooleanExpression clause = universe.equals(universe.zeroReal(), sum);

		clause = universe.or(clause, universe.lessThanEquals(Y2, j));
		clause = universe.or(clause,
				universe.lessThanEquals(j, universe.zeroInt()));
		context = universe.and(context, universe.forall(j, clause));

		// 0==(X_num_elements - 1*Y2 - 1) &&
		// 0<=(X_num_elements-2) &&
		// (((real)X_num_elements*X_dx)-1)<=0
		NumericSymbolicConstant X_num_elements = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("X_num_elements"),
						universe.integerType());

		context = universe.and(context, universe.equals(Y2,
				universe.subtract(X_num_elements, universe.oneInt())));
		context = universe.and(context,
				universe.lessThanEquals(universe.integer(2), X_num_elements));
		context = universe.and(context, universe.lessThanEquals(
				universe.multiply((NumericExpression) universe
						.cast(universe.realType(), X_num_elements), dx),
				universe.oneReal()));

		Reasoner reasoner = universe.reasoner(context);
		NumericSymbolicConstant boundVar = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("i"),
						universe.integerType());
		SymbolicExpression derivative = universe.derivative(rho,
				universe.intObject(0), universe.intObject(1));

		// $D[rho, {x,1}]((($real) i*h))
		SymbolicExpression derivativeApplicaiton = universe
				.apply(derivative,
						Arrays.asList(universe.multiply(
								(NumericExpression) universe
										.cast(universe.realType(), boundVar),
								dx)));
		NumericExpression lhs = universe.subtract(
				(NumericExpression) universe.arrayRead(result, boundVar),
				(NumericExpression) derivativeApplicaiton);
		// int i: 1 .. n-2
		BooleanExpression constraint = universe.and(
				universe.lessThanEquals(universe.oneInt(), boundVar),
				universe.lessThanEquals(boundVar, universe
						.subtract(X_num_elements, universe.integer(2))));
		NumericSymbolicConstant limitVars[] = { dx };
		int[] orders = { 2 };
		
		System.out.println("Context    : " + context);
		System.out.println("Constraint : " + constraint);
		System.out.println("Lhs        : " + lhs);
		System.out.println("limitVars  : " + limitVars[0]);
		System.out.println("orders     : " + orders[0]);
		System.out.flush();
		
		boolean valid = reasoner.checkBigOClaim(constraint, lhs, limitVars,
				orders);

		assertTrue(valid);
	}

}
