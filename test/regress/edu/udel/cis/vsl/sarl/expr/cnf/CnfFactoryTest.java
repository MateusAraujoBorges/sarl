/*******************************************************************************
 * Copyright (c) 2013 Stephen F. Siegel, University of Delaware.
 * 
 * This file is part of SARL.
 * 
 * SARL is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free
 * Software Foundation, either version 3 of the License, or (at your option) any
 * later version.
 * 
 * SARL is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE. See the GNU Lesser General Public License for more
 * details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with SARL. If not, see <http://www.gnu.org/licenses/>.
 ******************************************************************************/
package edu.udel.cis.vsl.sarl.expr.cnf;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.IF.BooleanExpressionFactory;
import edu.udel.cis.vsl.sarl.expr.IF.ExpressionFactory;
import edu.udel.cis.vsl.sarl.number.IF.Numbers;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.preuniverse.IF.FactorySystem;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverses;
import edu.udel.cis.vsl.sarl.type.IF.SymbolicTypeFactory;

/**
 * CnfFactoryTest is used to test the code mostly in CnfFactory. This includes
 * all of the various binary comparators and other methods for comparing and
 * determining expressions.
 * 
 */
public class CnfFactoryTest {

	// private static SymbolicUniverse sUniverse = Universes.newIdealUniverse();

	private static SymbolicType booleanType;
	private static SymbolicTypeFactory stf;
	private static ObjectFactory of;
	private static ExpressionFactory ef;

	private static BooleanExpressionFactory factory;

	static StringObject string1;
	static StringObject string2;
	static StringObject string3;

	private static NumericSymbolicConstant x; // real symbolic constant "X"
	private static BooleanSymbolicConstant b;

	private static BooleanSymbolicConstant p, q;

	static NumberFactory numberFactory = Numbers.REAL_FACTORY;

	/**
	 * setUp() initializes many of the variables used in the following tests.
	 * 
	 * @throws Exception
	 */
	@Before
	public void setUpBeforeClass() {
		FactorySystem system = PreUniverses.newIdealFactorySystem();

		factory = system.booleanFactory();
		stf = system.typeFactory();
		of = system.objectFactory();
		ef = system.expressionFactory();
		booleanType = stf.booleanType();
		p = factory.booleanSymbolicConstant(of.stringObject("p"));
		q = factory.booleanSymbolicConstant(of.stringObject("q"));
	}

	/**
	 * Check !(p&&q) equals (!p)||(!q).
	 */
	@Test
	public void notAnd() {
		BooleanExpression e1 = factory.not(factory.and(p, q));
		BooleanExpression e2 = factory.or(factory.not(p), factory.not(q));

		assertEquals(e1, e2);
	}

	/**
	 * Testing for code in CnfFactoryNot() makes sure that the function not
	 * actually returns not(value)
	 */
	@Test
	public void notTest() {
		BooleanExpression testingfalse = factory.falseExpr();
		StringObject pobject = of.stringObject("a");
		StringObject qobject = of.stringObject("b");
		BooleanExpression testingtrue = factory.trueExpr();
		BooleanExpression p = (BooleanExpression) ef.symbolicConstant(pobject,
				booleanType);
		BooleanExpression q = (BooleanExpression) ef.symbolicConstant(qobject,
				booleanType);
		BooleanExpression foralltruechk = factory.exists(b, testingfalse);
		BooleanExpression EXISTS = factory
				.booleanExpression(SymbolicOperator.EXISTS, foralltruechk);
		BooleanPrimitive cnf2 = (BooleanPrimitive) EXISTS;
		BooleanExpression existschk = factory.forall(b, testingtrue);
		BooleanExpression FORALL = factory
				.booleanExpression(SymbolicOperator.FORALL, existschk);
		BooleanPrimitive cnf3 = (BooleanPrimitive) FORALL;
		BooleanExpression andtrue = factory.and(p, q);
		BooleanExpression ortrue = factory.or(p, q);
		BooleanExpression nottrue = factory.not(q);
		BooleanExpression foralltrue = factory.forall(b, testingtrue);
		BooleanExpression existstrue = factory.exists(b, testingfalse);

		// Use DeMorgan's rules logic to create same functions using ands or ors
		// to test
		assertEquals(factory.or(factory.not(p), factory.not(q)),
				factory.not(andtrue));
		assertEquals(factory.and(factory.not(p), factory.not(q)),
				factory.not(ortrue));
		assertEquals(q, factory.not(nottrue));

		// for not(forall) since it is not, check with reverse(i.e. exists)
		assertEquals(cnf2.argument(0), factory.not(foralltrue));

		// for not(exists)
		assertEquals(cnf3.argument(0), factory.not(existstrue));
	}

	/**
	 * Testing for code in CnfFactoryNot(). Uses longer groups of values to
	 * ensure that even in long sets, not will still return not(value)
	 * 
	 */
	@Test
	public void cnFFactoryNotTest() {
		BooleanExpression testingfalse = factory.falseExpr();
		StringObject pobject = of.stringObject("a");
		StringObject qobject = of.stringObject("b");
		BooleanExpression p = (BooleanExpression) ef.symbolicConstant(pobject,
				booleanType);
		BooleanExpression q = (BooleanExpression) ef.symbolicConstant(qobject,
				booleanType);
		BooleanExpression testingtrue = factory.trueExpr();
		BooleanExpression andtrue = factory.and(p, q);
		BooleanExpression ortrue = factory.or(p, q);
		BooleanExpression nottrue = factory.not(q);
		BooleanExpression foralltrue = factory.forall(b, testingtrue);
		BooleanExpression existstrue = factory.exists(b, testingfalse);
		BooleanExpression foralltruechk = factory.exists(b, testingfalse);
		BooleanExpression EXISTS = factory
				.booleanExpression(SymbolicOperator.EXISTS, foralltruechk);
		BooleanPrimitive cnf2 = (BooleanPrimitive) EXISTS;
		BooleanExpression existschk = factory.forall(b, testingtrue);
		BooleanExpression FORALL = factory
				.booleanExpression(SymbolicOperator.FORALL, existschk);
		BooleanPrimitive cnf3 = (BooleanPrimitive) FORALL;

		assertEquals(factory.or(factory.not(p), factory.not(q)),
				factory.not(andtrue));
		assertEquals(factory.and(factory.not(p), factory.not(q)),
				factory.not(ortrue));
		assertEquals(q, factory.not(nottrue));

		assertEquals(cnf2.argument(0), factory.not(foralltrue));

		// for not(exists)
		assertEquals(cnf3.argument(0), factory.not(existstrue));
	}

	/**
	 * Testing for code in CnfFactoryOr() this includes combination and
	 * simplification of boolean variables
	 * 
	 */
	@Test
	public void orTest() {
		StringObject pobject = of.stringObject("p");
		StringObject qobject = of.stringObject("q");
		StringObject robject = of.stringObject("r");
		BooleanExpression p = (BooleanExpression) ef.symbolicConstant(pobject,
				booleanType);
		BooleanExpression q = (BooleanExpression) ef.symbolicConstant(qobject,
				booleanType);
		BooleanExpression r = (BooleanExpression) ef.symbolicConstant(robject,
				booleanType);
		BooleanExpression falseExpr = factory.falseExpr();
		BooleanExpression trueExpr = factory.trueExpr();
		BooleanExpression qandtrue = factory.and(q, trueExpr);
		BooleanExpression pandfalse = factory.and(p, falseExpr);
		BooleanExpression qortrue = factory.or(q, factory.not(p));
		BooleanExpression porfalse = factory.or(p, r);
		BooleanExpression testingtrue = factory.trueExpr();
		BooleanExpression testingfalse = factory.falseExpr();

		// testing for various combinations of true and false and and or results
		if (factory.getBooleanExpressionSimplification()) {
			assertEquals(trueExpr, (factory.or(p,
					factory.or(q, factory.or(factory.not(p), r)))));
			assertEquals(trueExpr, factory.or(qortrue, porfalse));
		}

		assertEquals(falseExpr, factory.and(factory.not(p), p));
		assertEquals(falseExpr, factory.and(p, factory.not(p)));
		assertEquals(factory.or(factory.not(p), r),
				(factory.or(factory.not(p), factory.and(p, r))));

		assertEquals(factory.and(p, r),
				factory.or(factory.and(p, r), factory.and(r, p)));
		assertEquals(factory.or(factory.or(p, r), p), factory.or(r, p));
		assertEquals(factory.or(factory.or(p, r), factory.or(q, r)),
				factory.or(r, factory.or(q, p)));
		assertEquals(testingtrue, factory.or(p, factory.not(p)));
		assertEquals(testingtrue, factory.or(factory.not(p), p));
		assertEquals(testingfalse, factory.not(factory.or(factory.not(p), p)));
		assertEquals(q, factory.or(qandtrue, pandfalse));
	}

	/**
	 * Testing for code in CnfFactoryOr() with simplification on.
	 * 
	 */
	@Test
	public void orSimplifyTest() {
		factory.setBooleanExpressionSimplification(true);
		StringObject pobject = of.stringObject("p");
		StringObject qobject = of.stringObject("q");
		StringObject robject = of.stringObject("r");
		BooleanExpression p = (BooleanExpression) ef.symbolicConstant(pobject,
				booleanType);
		BooleanExpression q = (BooleanExpression) ef.symbolicConstant(qobject,
				booleanType);
		BooleanExpression r = (BooleanExpression) ef.symbolicConstant(robject,
				booleanType);
		BooleanExpression falseExpr = factory.falseExpr();
		BooleanExpression trueExpr = factory.trueExpr();
		BooleanExpression qandtrue = factory.and(q, trueExpr);
		BooleanExpression pandfalse = factory.and(p, falseExpr);
		BooleanExpression qortrue = factory.or(q, factory.not(p));
		BooleanExpression porfalse = factory.or(p, r);
		BooleanExpression testingtrue = factory.trueExpr();
		BooleanExpression testingfalse = factory.falseExpr();

		// testing for various combinations of true and false and and or results
		if (factory.getBooleanExpressionSimplification()) {
			assertEquals(trueExpr, (factory.or(p,
					factory.or(q, factory.or(factory.not(p), r)))));
			assertEquals(trueExpr, factory.or(qortrue, porfalse));
		}

		assertEquals(falseExpr, factory.and(factory.not(p), p));
		assertEquals(falseExpr, factory.and(p, factory.not(p)));
		assertEquals(factory.or(factory.not(p), r),
				(factory.or(factory.not(p), factory.and(p, r))));

		assertEquals(factory.and(p, r),
				factory.or(factory.and(p, r), factory.and(r, p)));
		assertEquals(factory.or(factory.or(p, r), p), factory.or(r, p));
		assertEquals(factory.or(factory.or(p, r), factory.or(q, r)),
				factory.or(r, factory.or(q, p)));
		assertEquals(testingtrue, factory.or(p, factory.not(p)));
		assertEquals(testingtrue, factory.or(factory.not(p), p));
		assertEquals(testingfalse, factory.not(factory.or(factory.not(p), p)));
		assertEquals(q, factory.or(qandtrue, pandfalse));
	}

	/**
	 * Tests CnfFactory and(bool boolExpr1, bool boolExpr2) method. ensures that
	 * and correctly makes (expr1 && expr2) as well anding groups of sets
	 */
	@Test
	public void andTrueExprTest() {
		BooleanExpression testingtrue = factory.trueExpr();
		BooleanExpression testingfalse = factory.falseExpr();
		BooleanExpression falseExpr = factory.falseExpr();
		BooleanExpression trueExpr = factory.trueExpr();

		assertEquals(testingtrue, factory.and(testingtrue, testingtrue));
		assertEquals(testingtrue, factory.and(trueExpr, testingtrue));
		assertEquals(testingfalse, factory.and(trueExpr, testingfalse));
		assertEquals(testingfalse, factory.and(testingfalse, trueExpr));
		assertEquals(testingfalse, factory.and(falseExpr, testingtrue));
		assertEquals(testingfalse, factory.and(testingtrue, falseExpr));
	}

	/**
	 * Tests CnfFactory or(bool boolExpr1, bool boolExpr2) method. Tests for
	 * combinations of statements, and simplifications for or
	 */
	@Test
	public void orTrueExprTest() {
		BooleanExpression testingtrue = factory.trueExpr();
		BooleanExpression testingfalse = factory.falseExpr();
		BooleanExpression falseExpr = factory.falseExpr();
		BooleanExpression trueExpr = factory.trueExpr();

		assertEquals(testingtrue, factory.or(testingtrue, testingtrue));
		assertEquals(testingtrue, factory.or(trueExpr, testingtrue));
		assertEquals(testingtrue, factory.or(trueExpr, testingfalse));
		assertEquals(testingtrue, factory.or(falseExpr, testingtrue));
		assertEquals(testingfalse, factory.or(testingfalse, falseExpr));
	}

	/**
	 * Testing for code in CnfFactoryNot() makes sure not(false) is true
	 */
	@Test
	public void booleannotTest() {
		BooleanExpression falseEx = factory.falseExpr();

		assertEquals(false, factory.not(falseEx).isFalse());
	}

	/**
	 * Testing for code in CnfFactoryforall(). Tests to ensure all combinations
	 * of forall(values) return their correct output.
	 */
	@Test
	public void forAllTest() {
		BooleanExpression falseEx = factory.falseExpr();
		BooleanExpression trueEx = factory.trueExpr();

		assertEquals(true, factory.forall(x, falseEx).isFalse());
		assertEquals(false, factory.forall(x, falseEx).isTrue());
		assertEquals(true, factory.forall(x, trueEx).isTrue());
		assertEquals(false, factory.forall(x, trueEx).isFalse());
	}

	/**
	 * Testing for code in CnfFactoryExists() Tests to make sure if something
	 * exists, then exists(something) = true
	 */
	@Test
	public void existsTest() {
		BooleanExpression falseEx = factory.falseExpr();
		BooleanExpression trueEx = factory.trueExpr();
		BooleanExpression b = factory.or(trueEx, falseEx);

		assertEquals(true, factory.exists(x, b).isTrue());
		assertEquals(true, factory.exists(x, falseEx).isFalse());
		assertEquals(false, factory.exists(x, falseEx).isTrue());
		assertEquals(true, factory.exists(x, trueEx).isTrue());
		assertEquals(false, factory.exists(x, trueEx).isFalse());
	}

	/**
	 * Testing for code in CnfSymbolicConstant() Tests to make sure the super is
	 * working correctly. This is for tostring() and .name
	 */
	@Test
	public void cnfSymbolicConstantTest() {
		StringObject name = of.stringObject("Hello");
		CnfSymbolicConstant hellotest = (CnfSymbolicConstant) factory
				.booleanSymbolicConstant(name);
		StringObject hellomsg = of.stringObject("Hello");
		StringObject hellomsgfalse = of.stringObject("hello");

		assertEquals(hellomsg, hellotest.name());
		assertNotEquals(hellomsgfalse, hellotest.name());
		assertEquals("Hello", hellotest.toString());
		assertNotEquals("hello", hellotest.toString());
	}

	@Test
	public void unsatisfiableTest() {
		SymbolicUniverse universe = SARL.newStandardUniverse();
		NumericExpression two = universe.integer(2);
		SymbolicConstant X = universe.symbolicConstant(
				universe.stringObject("X"), universe.integerType());
		BooleanExpression clause1 = universe.lessThanEquals(
				universe.divide((NumericExpression) X, two), universe.oneInt());
		BooleanExpression clause2 = universe.lessThanEquals(universe.integer(3),
				(NumericExpression) X);

		BooleanExpression result = universe
				.reasoner(universe.and(clause1, clause2)).getReducedContext();
		System.out.println(result);

		// want X=3.
		// need to reason as follows:
		// a div b <= c ==>
		// assume a>=0, b>0
		// a = q*b + r
		// q>=0, 0<=r<b
		// q=(a-r)/b=a/b-r/b
		// (a/b)-1<q<=a/b

		// X/2>=3/2
		// X div 2 > (X/2)-1 >= 3/2-1 >= .5 -> X div 2 >= 1
		// -> X div 2 = 1
		// X/2<X div 2 + 1 = 2 -> X<4 -> X=3

		// Here is how to do it:

		// To get a bound on a%b, where b>0 is constant:
		// first, get a bound on a. if a>=0: a%b is in [0,b-1].
		// if a<=0 a%b in [1-b,0]. In any case: a%b in [1-b,b-1].

		// if a bound I1 is created on a div b:
		// 1. get bound I2 on a%b as above (if not already present)
		// 2. use fact that a=(a div b)*b+a%b to get bound on a:
		// b*I1+I2

	}
}
