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

}
