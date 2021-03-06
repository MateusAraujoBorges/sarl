package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

import java.io.PrintStream;
import java.util.Arrays;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
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

	/**
	 * not (A ^ B) equiv (not A) v (not B)
	 */
	@Test
	public void DeMorganLawTest1() {
		BooleanExpression e1 = universe.not(universe.and(A, B));
		BooleanExpression e2 = universe.or(universe.not(A), universe.not(B));
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * not (A v B) equiv (not A) ^ (not B)
	 */
	@Test
	public void DeMorganLawTest2() {
		BooleanExpression e1 = universe.not(universe.or(A, B));
		BooleanExpression e2 = universe.and(universe.not(A), universe.not(B));
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A -> B equiv (not A) v B
	 */
	@Test
	public void DeMorganLawTest3() {
		BooleanExpression e1 = universe.implies(A, B);
		BooleanExpression e2 = universe.or(universe.not(A), B);
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * not A equiv A -> false
	 */
	@Test
	public void DeMorganLawTest4() {
		BooleanExpression e1 = universe.not(A);
		BooleanExpression e2 = universe.implies(A, falseExpr);
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * not (not A) equiv A
	 */
	@Test
	public void doubleNegationTest() {
		BooleanExpression e1 = universe.not(universe.not(A));
		BooleanExpression e2 = A;
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A ^ true equiv A
	 */
	@Test
	public void neutralElementTest1() {
		BooleanExpression e1 = universe.and(A, trueExpr);
		BooleanExpression e2 = A;
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A v false equiv A
	 */
	@Test
	public void neutralElementTest2() {
		BooleanExpression e1 = universe.or(A, falseExpr);
		BooleanExpression e2 = A;
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A ^ false equiv false
	 */
	@Test
	public void absorptionElementTest1() {
		BooleanExpression e1 = universe.and(A, falseExpr);
		BooleanExpression e2 = falseExpr;
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * A v true equiv true
	 */
	@Test
	public void absorptionElementTest2() {
		BooleanExpression e1 = universe.or(A, trueExpr);
		BooleanExpression e2 = trueExpr;
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e1), reasoner.simplify(e2));
	}

	/**
	 * (A -> B) -> A equiv A
	 * 
	 * <pre>
	 * proof:
	 * (A -> B) -> A equiv !(!A v B) v A
	 * 				 equiv (A ^ !B) v A
	 * 				 equiv A v (A ^ !B)
	 * 				 equiv A
	 * </pre>
	 */
	@Test
	public void extraEquiv() {
		BooleanExpression e1 = universe.implies(universe.implies(A, B), A);
		BooleanExpression e2 = A;
		Reasoner reasoner = universe.reasoner(trueExpr);

		if (debug) {
			out.println("e1 is " + e1);
			out.println("e2 is " + e2);
		}
		assertEquals(reasoner.simplify(e2), reasoner.simplify(e1));
	}

	/**
	 * (forall int i; 1&le;i&le;UP ==> array[i-1] == 0) && i == 0;
	 */
	@Test
	public void quantifiedExpressionInterfere() {
		BooleanExpression context;
		NumericSymbolicConstant idx = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("i"),
						universe.integerType());
		NumericSymbolicConstant upper = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("UP"),
						universe.integerType());
		SymbolicExpression array = universe.array(universe.integerType(),
				Arrays.asList(universe.zeroInt(), universe.zeroInt(),
						universe.zeroInt()));

		context = universe
				.forallInt(idx, universe.integer(1), upper,
						universe.equals(
								universe.arrayRead(array,
										universe.subtract(idx,
												universe.oneInt())),
								universe.zeroInt()));
		context = universe.and(context,
				universe.equals(universe.integer(0), idx));

		Reasoner reasoner = universe.reasoner(context);

		reasoner.getFullContext();
	}

	/**
	 * Context: <code>
	 * forall i0 : int . ((Y5[i0] == Y11[i0]) || (2*_uf_$mpi_sizeof(Y3)*Y2 - 1*i0 <= 0) || (i0 + 1 <= 0)) &&
	 * forall i0 : int . ((Y11[i0] == Y5[i0]) || (2*_uf_$mpi_sizeof(Y9)*Y8 - 1*i0 <= 0) || (i0 + 1 <= 0))
	 * </code>
	 * 
	 * Query: <code>
	 * 0 == _uf_$mpi_sizeof(Y1)*Y0 - 1*_uf_$mpi_sizeof(Y3)*Y2 && 
	 * forall i0 : int. ((Y4[i0] == Y5[i0]) || (_uf_$mpi_sizeof(Y1)*Y0 - 1*i0 <= 0) || (i0 + 1<= 0))
	 * </code>
	 */
	@Test
	public void infiniteSimplificationBug() {
		// Types: Abstract function f(int) : int
		SymbolicType intType = universe.integerType();
		SymbolicType functionType = universe
				.functionType(Arrays.asList(intType), universe.integerType());
		// Function:
		SymbolicConstant function = universe.symbolicConstant(
				universe.stringObject("_uf_$mpi_sizeof"), functionType);
		// Constants:
		NumericSymbolicConstant Y0 = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("Y0"),
						universe.integerType());
		NumericSymbolicConstant Y1 = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("Y1"),
						universe.integerType());
		NumericExpression fY1 = (NumericExpression) universe.apply(function,
				Arrays.asList(Y1));
		NumericSymbolicConstant Y2 = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("Y2"),
						universe.integerType());
		NumericSymbolicConstant Y3 = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("Y3"),
						universe.integerType());
		NumericExpression fY3 = (NumericExpression) universe.apply(function,
				Arrays.asList(Y3));
		NumericSymbolicConstant Y8 = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("Y8"),
						universe.integerType());
		NumericSymbolicConstant Y9 = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("Y9"),
						universe.integerType());
		NumericExpression fY9 = (NumericExpression) universe.apply(function,
				Arrays.asList(Y9));
		NumericSymbolicConstant i0 = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("i0"),
						universe.integerType());

		SymbolicType arrayType0 = universe.arrayType(universe.characterType(),
				universe.multiply(Arrays.asList(fY3, Y2, universe.integer(2))));
		SymbolicType arrayType1 = universe.arrayType(universe.characterType(),
				universe.multiply(Arrays.asList(fY9, Y8, universe.integer(2))));
		SymbolicType arrayType3 = universe.arrayType(universe.characterType(),
				universe.multiply(Arrays.asList(fY3, Y2)));
		// Array
		SymbolicConstant Y5 = universe
				.symbolicConstant(universe.stringObject("Y5"), arrayType0);
		SymbolicConstant Y11 = universe
				.symbolicConstant(universe.stringObject("Y11"), arrayType1);
		SymbolicConstant Y4 = universe
				.symbolicConstant(universe.stringObject("Y4"), arrayType3);
		// forall i0. 0<= i0 < Y2*f(Y3)*2 ==> Y5[i0] == Y11[i0]
		// forall i0. 0<= i0 < Y8*f(Y9)*2 ==> Y5[i0] == Y11[i0]
		BooleanExpression propsition1 = universe.equals(
				universe.arrayRead(Y5, i0), universe.arrayRead(Y11, i0));
		BooleanExpression propsition3 = universe.equals(
				universe.arrayRead(Y11, i0), universe.arrayRead(Y5, i0));
		BooleanExpression forall1 = universe.forallInt(i0, universe.zeroInt(),
				universe.multiply(Arrays.asList(Y2, fY3, universe.integer(2))),
				propsition1);
		BooleanExpression forall3 = universe.forallInt(i0, universe.zeroInt(),
				universe.multiply(Arrays.asList(fY9, Y8, universe.integer(2))),
				propsition3);

		BooleanExpression query = universe.forallInt(i0, universe.zeroInt(),
				universe.multiply(fY1, Y0),
				universe.equals(universe.arrayRead(Y4, i0),
						universe.arrayRead(Y5, i0)));

		query = universe.and(query, universe.equals(universe.multiply(Y0, fY1),
				universe.multiply(fY3, Y2)));

		BooleanExpression context = universe
				.and(Arrays.asList(forall1, forall3));
		Reasoner reasoner = universe.reasoner(context);
		reasoner.valid(query);
	}

	@Test
	public void modmodCrash() {
		NumericSymbolicConstant A = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("X_A"),
						universe.integerType());
		NumericSymbolicConstant B = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("X_B"),
						universe.integerType());
		NumericSymbolicConstant i = (NumericSymbolicConstant) universe
				.symbolicConstant(universe.stringObject("i"),
						universe.integerType());
		BooleanExpression claim = universe.forall(i, universe.or(
				universe.equals(universe.modulo(universe.modulo(A, i), i),
						universe.zeroInt()),
				universe.equals(universe.modulo(universe.modulo(B, i), i),
						universe.zeroInt())));
		Reasoner reasoner = universe.reasoner(universe.trueExpression());

		assertFalse(reasoner.isValid(claim));
	}
}
