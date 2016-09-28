package edu.udel.cis.vsl.sarl.preuniverse;

import static org.junit.Assert.*;

import java.io.PrintStream;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.IF.ExpressionFactory;
import edu.udel.cis.vsl.sarl.preuniverse.IF.FactorySystem;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverses;

public class PrintExpressionTreeTest {

	public final static boolean DEBUG = true;

	public final static PrintStream OUT = System.out;

	// Universe
	private static PreUniverse universe;
	// Factories
	private static ExpressionFactory expressionFactory;
	// SymbolicTypes
	private static SymbolicType int_Type;
	private static SymbolicType real_Type;
	private static SymbolicType int_ArrayType;
	private static SymbolicType intArray_ArrayType;
	// SymbolicExpressions
	private static NumericExpression int_1, real_1p5, int_2, real_0p5;

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
		FactorySystem system = PreUniverses.newIdealFactorySystem();
		universe = PreUniverses.newPreUniverse(system);

		// Instantiate the nullExpression SymbolicExpression
		expressionFactory = system.expressionFactory();
		// Instantiate Types
		int_Type = universe.integerType();
		real_Type = universe.realType();
		int_ArrayType = universe.arrayType(int_Type);
		intArray_ArrayType = universe.arrayType(int_ArrayType);
		// Instantiate NumberExpressions
		int_1 = universe.integer(1);
		int_2 = universe.integer(2);
		real_1p5 = universe.rational(1.5);
		real_0p5 = universe.rational(0.5);
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
	}

	@Before
	public void setUp() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}

	@Test
	public void test() {
		fail("Not yet implemented");
	}

}
