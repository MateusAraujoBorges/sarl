package edu.udel.cis.vsl.sarl.IF;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicRealType;

public class PrintCompressedTest {

	public final static PrintStream out = System.out;

	public final static SymbolicUniverse universe = SARL.newStandardUniverse();

	// using idealFactory
//	public final static SymbolicRealType real = universe.realType();

	// using herbrandFactory
	public final static SymbolicRealType real = universe.herbrandRealType();

	public final static NumericExpression one = (NumericExpression) universe
			.cast(real, universe.oneReal());

	public final static NumericExpression x = (NumericExpression) universe
			.symbolicConstant(universe.stringObject("x"), real);

	public final static NumericExpression y = (NumericExpression) universe
			.symbolicConstant(universe.stringObject("y"), real);

	public final static NumericExpression z = (NumericExpression) universe
			.symbolicConstant(universe.stringObject("z"), real);

	public final static NumericExpression u = (NumericExpression) universe
			.symbolicConstant(universe.stringObject("u"), real);

	public final static NumericExpression k = (NumericExpression) universe
			.symbolicConstant(universe.stringObject("k"), real);

	/**
	 * (x+y)z + (x+y)(x+y)
	 */
	@Test
	public void expressionTest1() {
		NumericExpression e1 = universe.add(x, y);
		NumericExpression e2 = universe.add(universe.multiply(e1, z),
				universe.multiply(e1, e1));

		out.println("expr is: " + e2);
		// out.println("====== original tree =======");
		// universe.printExprTree(e2, out);
		out.println("====== compressed tree ======");
		universe.printCompressed(e2, out);
		out.println("==================== \n");
	}

	/**
	 * x + y*z
	 */
	@Test
	public void expressionTest11() {
		NumericExpression e1 = universe.multiply(y, z);
		NumericExpression e2 = universe.add(x, e1);

		out.println("expr is: " + e2 + "\n");
		// out.println("====== original tree =======");
		// universe.printExprTree(e2, out);
		out.println("====== compressed tree ======");
		universe.printCompressed(e2, out);
		out.println("====================");
	}

	/**
	 * (x+1)z + (x+1)(x+1)
	 */
	@Test
	public void expressionTest2() {
		NumericExpression e1 = universe.add(x, one);
		NumericExpression e2 = universe.add(universe.multiply(e1, z),
				universe.multiply(e1, e1));

		out.println("expr is " + e2);
//		out.println("====== original tree =======");
//		universe.printExprTree(e2, out);
		out.println("====== compressed tree ======");
		universe.printCompressed(e2, out);
		out.println("====================\n");
	}

	/**
	 * (x+y)(y+z) + (y+z)(z+u) + (x+y)(z+u)
	 */
	@Test
	public void expressionTest3() {
		NumericExpression e1 = universe.add(x, y);
		NumericExpression e2 = universe.add(y, z);
		NumericExpression e3 = universe.add(z, u);
		NumericExpression e4 = universe.multiply(e1, e2);
		NumericExpression e5 = universe.multiply(e2, e3);
		NumericExpression e6 = universe.multiply(e1, e3);
		NumericExpression e7 = universe.add(universe.add(e4, e5), e6);

		out.println("expr is " + e7 );
//		out.println("====== original tree =======");
//		universe.printExprTree(e7, out);
		out.println("====== compressed tree ======");
		universe.printCompressed(e7, out);
		out.println("====================\n");
	}

	/**
	 * (x+y+z)(y+z+u)
	 */
	@Test
	public void printTest4() {
		List<NumericExpression> numList1 = new ArrayList<NumericExpression>();
		List<NumericExpression> numList2 = new ArrayList<NumericExpression>();
		NumericExpression e1, e2, e3;

		numList1.add(x);
		numList1.add(y);
		numList1.add(z);
		numList2.add(y);
		numList2.add(z);
		numList2.add(u);
		e1 = universe.add(numList1);
		e2 = universe.add(numList2);
		e3 = universe.multiply(e1, e2);
		out.println("expr is " + e3 + "\n");
		universe.printCompressed(e3, out);
		out.println("====================");
	}

	/**
	 * (x - y*(z+u)) / y
	 */
	@Test
	public void printTest6() {
		NumericExpression e1 = universe.divide(
				universe.subtract(x, universe.multiply(y, universe.add(z, u))),
				y);

		out.println("expr is " + e1 + "\n");
		universe.printCompressed(e1, out);
		out.println("====================");
	}

	/**
	 * y*(x+z) / (x-y)
	 */
	@Test
	public void printTest7() {
		NumericExpression e1 = universe.divide(
				universe.multiply(y, universe.add(x, z)),
				universe.subtract(x, y));

		out.println("expr is: " + e1 + "\n");
		// out.println("====== original tree =======");
		// universe.printExprTree(e1, out);
		out.println("====== compressed tree ======");
		universe.printCompressed(e1, out);
		out.println("====================");
	}

	/**
	 * (x+y) + (x+y)^2 + (x+y)^3
	 */
	@Test
	public void printTest8() {
		NumericExpression e1 = universe.add(x, y);
		NumericExpression e2 = universe.power(e1, 2);
		NumericExpression e3 = universe.multiply(e1, e2);
		NumericExpression e4 = universe.add(universe.add(e1, e2), e3);

		out.println("expr is " + e4 );
//		out.println("====== original tree =======");
//		universe.printExprTree(e4, out);
		out.println("====== compressed tree ======");
		universe.printCompressed(e4, out);
		out.println("====================\n");
	}

	/**
	 * the large expression from CG 2x2 which calculate the numerator of beta
	 * 
	 * <pre>
	 * beta = rsnew / rsold = <r1, r1> / <r0, r0> 
	 * 
	 * numerator = [b0*m - (b0^2+b1^2)(a0b0+a1b1)]^2 + [b1*m - (b0^2+b1^2)(a1b0+a2b1)]^2
	 * 
	 * (construct our test expression by replace a0, a1, a2 with x, y, z; replace b0, b1 with u,k.)
	 * numerator = [k*m - n(yu+zk)]^2 + [u*m - n(xu+yk)]^2
	 * 
	 * m = u(xu + yk) + k(yu + zk) 
	 * 
	 * n = (u^2 + k^2)
	 * </pre>
	 */
	@Test
	public void printTest9() {
		NumericExpression m = universe.add(
				universe.multiply(u,
						universe.add(universe.multiply(x, u),
								universe.multiply(y, k))),
				universe.multiply(k, universe.add(universe.multiply(y, u),
						universe.multiply(z, k))));
		NumericExpression n = universe.add(universe.power(u, 2),
				universe.power(k, 2));

		NumericExpression e1 = universe
				.power(universe.subtract(universe.multiply(u, m),
						universe.multiply(n,
								universe.add(universe.multiply(x, u),
										universe.multiply(y, k)))),
						2);
		NumericExpression e2 = universe
				.power(universe.subtract(universe.multiply(k, m),
						universe.multiply(n,
								universe.add(universe.multiply(y, u),
										universe.multiply(z, k)))),
						2);
		NumericExpression e = universe.add(e1, e2);

		out.println("m is " + m + "\n");
		out.println("n is " + n + "\n");
		out.println("e1 is " + e1 + "\n");
		out.println("e2 is " + e2 + "\n");
		out.println("e is " + e + "\n");
//		out.println("====== original tree =======");
//		universe.printExprTree(e, out);
		out.println("====== compressed tree ======");
		universe.printCompressed(e, out);
		out.println("====================\n");
	}

	/**
	 * x + y + f(x+y)
	 */
	@Test
	public void printTest10() {
		SymbolicFunctionType fType = universe.functionType(Arrays.asList(real),
				real);
		String fName = "f";
		SymbolicConstant r2rConst = universe
				.symbolicConstant(universe.stringObject(fName), fType);
		NumericExpression e1 = universe.add(x, y);
		NumericExpression e4 = universe.add(e1, (NumericExpression) universe
				.apply(r2rConst, Arrays.asList(e1)));

		out.println("expr is: " + e4);
		// out.println("====== original tree =======");
		// universe.printExprTree(e4, out);
		out.println("====== compressed tree ======");
		universe.printCompressed(e4, out);
		out.println("==================== \n");
	}

	/**
	 * f(x+y+z)
	 */
	@Test
	public void printTest11() {
		SymbolicFunctionType fType = universe.functionType(Arrays.asList(real),
				real);
		String fName = "f";
		SymbolicConstant r2rConst = universe
				.symbolicConstant(universe.stringObject(fName), fType);
		NumericExpression e1 = universe.add(universe.add(x, y), z);
		NumericExpression e4 = (NumericExpression) universe.apply(r2rConst,
				Arrays.asList(e1));

		out.println("expr is: " + e4);
//		out.println("====== original tree =======");
//		universe.printExprTree(e4, out);
		out.println("====== compressed tree ======");
		universe.printCompressed(e4, out);
		out.println("====================\n");
	}
}
