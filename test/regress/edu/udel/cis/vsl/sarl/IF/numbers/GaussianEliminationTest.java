package edu.udel.cis.vsl.sarl.IF.numbers;

import java.io.PrintStream;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.number.IF.Numbers;

public class GaussianEliminationTest {

	private static PrintStream out = System.out;

	private static NumberFactory factory = Numbers.REAL_FACTORY;

	private static RationalNumber r0 = factory.zeroRational();

	private static RationalNumber r1 = factory.oneRational();

	private static RationalNumber r2 = factory.rational("2");

	private static RationalNumber r3 = factory.rational("3");

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	private static String mat2string(RationalNumber[][] mat) {
		StringBuilder builder = new StringBuilder();
		builder.append('[');

		boolean first1 = true;

		for (RationalNumber[] row : mat) {
			if (first1)
				first1 = false;
			else
				builder.append(' ');
			builder.append('[');

			boolean first2 = true;

			for (RationalNumber x : row) {
				if (first2)
					first2 = false;
				else
					builder.append(' ');
				builder.append(x.toString());
			}
			builder.append(']');
		}
		builder.append(']');
		return builder.toString();
	}

	/**
	 * Test Gaussian elimination on a simple 2x3 matrix:
	 * 
	 * <pre>
	 * 1  1  2
	 * 2  1  3
	 * 
	 * 1  1  2
	 * 0 -1 -1
	 * 
	 * 1  1  2
	 * 0  1  1
	 * 
	 * 1  0  1
	 * 0  1  1
	 * </pre>
	 */
	@Test
	public void gauss1() {
		RationalNumber[][] matrix = { { r1, r1, r2 }, { r2, r1, r3 } };

		out.println("matrix = " + mat2string(matrix));
		factory.gaussianElimination(matrix);
		out.println("result = " + mat2string(matrix));

		RationalNumber[][] expect = { { r1, r0, r1 }, { r0, r1, r1 } };

		Assert.assertArrayEquals(expect, matrix);
	}

	@Test
	public void gauss2() {
		RationalNumber[][] matrix = { { r2, r2 }, { r2, r2 }, { r1, r1 } };

		out.println("matrix = " + mat2string(matrix));
		factory.gaussianElimination(matrix);
		out.println("result = " + mat2string(matrix));

		RationalNumber[][] expect = { { r1, r1 }, { r0, r0 }, { r0, r0 } };

		Assert.assertArrayEquals(expect, matrix);
	}

	@Test
	public void gauss3() {
		RationalNumber[][] matrix = { { r0, r1 }, { r1, r0 } };

		out.println("matrix = " + mat2string(matrix));
		factory.gaussianElimination(matrix);
		out.println("result = " + mat2string(matrix));

		RationalNumber[][] expect = { { r1, r0 }, { r0, r1 } };

		Assert.assertArrayEquals(expect, matrix);
	}

	/**
	 * <pre>
	 * Super-context:
	 * 1  1  1  0
	 * 
	 * Matrix:
	 * 0  1  1  0
	 * 1  1  0  2
	 * </pre>
	 */
	@Test
	public void relative1() {
		RationalNumber[][] mat1 = { { r1, r1, r1, r0 } };
		RationalNumber[][] mat2 = { { r0, r1, r1, r0 }, { r1, r1, r0, r2 } };

		out.println("mat1 = " + mat2string(mat1));
		out.println("mat2 = " + mat2string(mat2));
		factory.relativeGaussianElimination(mat1, mat2);
		out.println("res1 = " + mat2string(mat1));
		out.println("res2 = " + mat2string(mat2));

		// RationalNumber[][] expect = { { r1, r0 }, { r0, r1 } };
		//
		// Assert.assertArrayEquals(expect, matrix);
	}

}
