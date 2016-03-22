package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.io.PrintStream;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * Standard equivalence in propositional logic.
 * 
 * @author sili
 *
 */
public class BooleanReasonTest {
	public final static PrintStream out = System.out;
	public final static boolean debug = true;
	private SymbolicUniverse universe;
	private BooleanExpression A, B, C;
	private StringObject a_obj, b_obj, c_obj;
	private SymbolicType boolType;
	private BooleanExpression trueExpr, falseExpr;

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@Before
	public void setUp() throws Exception {
		universe = SARL.newStandardUniverse();
		a_obj = universe.stringObject("A");
		b_obj = universe.stringObject("B");
		c_obj = universe.stringObject("C");
		boolType = universe.booleanType();
		A = (BooleanExpression) universe.symbolicConstant(a_obj, boolType);
		B = (BooleanExpression) universe.symbolicConstant(b_obj, boolType);
		C = (BooleanExpression) universe.symbolicConstant(c_obj, boolType);
		trueExpr = universe.bool(true);
		falseExpr = universe.bool(false);
	}

	@After
	public void tearDown() throws Exception {
	}

	/**
	 * (A ^ B) equiv (B ^ A)
	 */
	@Test
	public void commutativityAndTest() {
		BooleanExpression e1 = universe.and(A, B);
		BooleanExpression e2 = universe.and(B, A);
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * (A v B) equiv (B v A)
	 */
	@Test
	public void commutativityOrTest() {
		BooleanExpression e1 = universe.or(A, B);
		BooleanExpression e2 = universe.or(B, A);
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A ^ (B ^ C) equiv (A ^ B) ^ C
	 */
	@Test
	public void associativityAndTest() {
		BooleanExpression e1 = universe.and(A, universe.and(B, C));
		BooleanExpression e2 = universe.and(universe.and(A, B), C);
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A v (B v C) equiv (A v B) v C
	 */
	@Test
	public void associativityOrTest() {
		BooleanExpression e1 = universe.or(A, universe.or(B, C));
		BooleanExpression e2 = universe.or(universe.or(A, B), C);
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A ^ (A v B) equiv A
	 */
	@Test
	public void absorptionTest1() {
		BooleanExpression e1 = universe.and(A, universe.or(A, B));
		BooleanExpression e2 = A;
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e2), reasoner.simplify(e1));
	}

	/**
	 * A v (A ^ B) equiv A
	 */
	@Test
	public void absorptionTest2() {
		BooleanExpression e1 = universe.or(A, universe.and(A, B));
		BooleanExpression e2 = A;
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e2), reasoner.simplify(e1));
	}

	/**
	 * A ^ (not A) equiv false
	 */
	@Test
	public void complement1() {
		BooleanExpression e = universe.and(A, universe.not(A));
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e is " + e);
		}
		assertEquals(falseExpr, reasoner.simplify(e));
	}

	/**
	 * A v (not A) equiv true
	 */
	@Test
	public void complement2() {
		BooleanExpression e = universe.or(A, universe.not(A));
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e is " + e);
		}
		assertEquals(trueExpr, reasoner.simplify(e));
	}

	/**
	 * A ^ (B v C) equiv (A ^ B) v (A ^ C)
	 */
	@Test
	public void distributivityTest1() {
		BooleanExpression e1 = universe.and(A, universe.or(B, C));
		BooleanExpression e2 = universe.or(universe.and(A, B),
				universe.and(A, C));
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A v (B ^ C) equiv (A v B) ^ (A v C)
	 */
	@Test
	public void distributivityTest2() {
		BooleanExpression e1 = universe.or(A, universe.and(B, C));
		BooleanExpression e2 = universe.and(universe.or(A, B),
				universe.or(A, C));
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}
}
