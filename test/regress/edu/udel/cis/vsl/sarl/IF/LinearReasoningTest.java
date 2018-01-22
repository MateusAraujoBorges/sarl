package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Map;

import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicIntegerType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicRealType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

public class LinearReasoningTest {

	@SuppressWarnings("unused")
	private static boolean debug = true;

	private static PrintStream out = System.out;

	private static SymbolicUniverse uv = SARL.newStandardUniverse();

	private static SymbolicIntegerType intType = uv.integerType();

	private static SymbolicRealType realType = uv.realType();

	@SuppressWarnings("unused")
	private static SymbolicType booleanType = uv.booleanType();

	@SuppressWarnings("unused")
	private static NumericSymbolicConstant a = (NumericSymbolicConstant) uv
			.symbolicConstant(uv.stringObject("a"), intType);

	@SuppressWarnings("unused")
	private static NumericSymbolicConstant b = (NumericSymbolicConstant) uv
			.symbolicConstant(uv.stringObject("b"), intType);

	@SuppressWarnings("unused")
	private static NumericSymbolicConstant c = (NumericSymbolicConstant) uv
			.symbolicConstant(uv.stringObject("c"), intType);

	private static NumericSymbolicConstant x = (NumericSymbolicConstant) uv
			.symbolicConstant(uv.stringObject("x"), realType);

	private static NumericSymbolicConstant y = (NumericSymbolicConstant) uv
			.symbolicConstant(uv.stringObject("y"), realType);

	@SuppressWarnings("unused")
	private static NumericSymbolicConstant z = (NumericSymbolicConstant) uv
			.symbolicConstant(uv.stringObject("z"), realType);
	@SuppressWarnings("unused")
	private static NumericExpression i0 = uv.zeroInt(), i1 = uv.oneInt(),
			i2 = uv.integer(2);
	@SuppressWarnings("unused")
	private static NumericExpression r0 = uv.zeroReal(), r1 = uv.oneReal(),
			r2 = uv.rational(2);
	@SuppressWarnings("unused")
	private static BooleanExpression trueExpr = uv.trueExpression(),
			falseExpr = uv.falseExpression();

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
		uv.setUseBackwardSubstitution(true);
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
	}

	@Before
	public void setUp() throws Exception {
	}

	/**
	 * X=Y && Y=1 -> X=1, Y=1
	 */
	@Test
	public void linear1() {
		Reasoner r = uv.reasoner(uv.and(uv.equals(x, y), uv.equals(y, r1)));
		Map<SymbolicConstant, SymbolicExpression> m = r
				.constantSubstitutionMap();
		Map<SymbolicConstant, SymbolicExpression> oracle = new HashMap<>();

		oracle.put(x, r1);
		oracle.put(y, r1);
		assertEquals(oracle, m);
		assertEquals(trueExpr, r.getReducedContext());
	}

	/**
	 * Assume X=Y : then if using backwards substitution, one of these variables
	 * should be eliminated from the state.
	 */
	@Test
	public void linear2() {
		Reasoner r = uv.reasoner(uv.equals(x, y));
		Map<SymbolicConstant, SymbolicExpression> m = r
				.constantSubstitutionMap();

		out.println(m);
		assertEquals(1, m.size());
	}
}
