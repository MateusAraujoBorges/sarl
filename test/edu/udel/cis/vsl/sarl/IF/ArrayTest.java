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
package edu.udel.cis.vsl.sarl.IF;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertSame;

import java.io.PrintStream;
import java.util.Arrays;
import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.universe.IF.Universes;
import edu.udel.cis.vsl.sarl.util.Pair;

public class ArrayTest {

	private static PrintStream out = System.out;
	private SymbolicUniverse universe;
	private StringObject a_obj; // "a"
	private SymbolicType integerType;
	private NumericExpression zero, one, two, three, five, six, seventeen; // integer constants
	private List<NumericExpression> list1; // {5,6}
	private List<NumericExpression> list2; // {17}
	
	private SymbolicExpression write2d(SymbolicExpression array,
			NumericExpression i, NumericExpression j, SymbolicExpression value) {
		SymbolicExpression row = universe.arrayRead(array, i);
		SymbolicExpression newRow = universe.arrayWrite(row, j, value);

		return universe.arrayWrite(array, i, newRow);
	}

	private SymbolicExpression read2d(SymbolicExpression array,
			NumericExpression i, NumericExpression j) {
		SymbolicExpression row = universe.arrayRead(array, i);

		return universe.arrayRead(row, j);
	}
	
	@Before
	public void setUp() throws Exception {
		universe = Universes.newIdealUniverse();
		integerType = universe.integerType();
		a_obj = universe.stringObject("a");
		zero = universe.integer(0);
		one = universe.integer(1);
		two = universe.integer(2);
		three = universe.integer(3);
		five = universe.integer(5);
		six = universe.integer(6);
		seventeen = universe.integer(17);
		list1 = Arrays.asList(new NumericExpression[] { five, six });
		list2 = Arrays.asList(new NumericExpression[] { seventeen });
	}

	@After
	public void tearDown() throws Exception {
	}
	
	/**
	 * create a integer array with two elements {5,6}
	 */
	@Test
	public void arrayCreateTest(){
		SymbolicExpression a = universe.array(integerType, list1);
		assertEquals(universe.arrayType(integerType, two), a.type());
	}
	
	/**
	 * get the dimension and the base type of an array
	 */
	@Test
	public void arrayDimensionAndBaseTypeTest(){
		SymbolicExpression a = universe.array(integerType, list1);
		Pair<Integer, SymbolicType> pair = universe.arrayDimensionAndBaseType((SymbolicArrayType)(a.type()));
		assertEquals(pair.left, new Integer(1));
		assertEquals(pair.right, integerType);
	}
	
	/**
	 * create an empty array
	 */
	@Test
	public void emptyArrayTest(){
		SymbolicExpression a = universe.emptyArray(integerType);
		assertEquals(a.type(), universe.arrayType(integerType, zero));
		
		
	}
	
	/**
	 * create a constant array {1,1,1,1,1,1}
	 */
	@Test
	public void constantArrayTest(){
		SymbolicExpression a = universe.constantArray(integerType, six, one);
		
		for(int i=0; i<6; i++){
			NumericExpression num = universe.integer(i);
			assertEquals(universe.arrayRead(a, num), one);
		}
	}
	
	/**
	 * append a number after an array
	 * {5,6} ==> {5,6,17}
	 */
	@Test
	public void appendTest(){
		//{five, six}
		SymbolicExpression a = universe.array(integerType, list1);
		SymbolicExpression c = universe.append(a, seventeen);
		
		assertEquals(universe.arrayType(integerType, three), c.type());
		int i=0;
		for(; i<2; i++){
			NumericExpression num = universe.integer(i);
			assertEquals(universe.arrayRead(a, num), universe.arrayRead(c, num));
		}
		NumericExpression num = universe.integer(i);
		assertEquals(universe.arrayRead(c, num), seventeen);
	}
	
	/**
	 * append an element into an empty array
	 * {} ==> {1}
	 */
	@Test
	public void appendEmptyArrayTest(){
		SymbolicExpression a = universe.emptyArray(integerType);
		SymbolicExpression b = universe.append(a, one);
		
		assertEquals(universe.length(b), one);
	}
	
	
	/**
	 * remove an element from an array
	 * {5,6} ==> {6}
	 */
	@Test
	public void removeElementTest(){
		SymbolicExpression a = universe.array(integerType, list1);
		SymbolicExpression b = universe.removeElementAt(a, 0);
		
		assertEquals(universe.arrayType(integerType, one), b.type());
		assertEquals(universe.arrayRead(b, zero), six);
	}
	
	/**
	 * insert an element into an array
	 * {5,6} ==> {5,17,6}
	 */
	@Test
	public void insertElementTest(){
		SymbolicExpression a = universe.array(integerType, list1);
		SymbolicExpression b = universe.insertElementAt(a, 1, seventeen);
		
		assertEquals(universe.arrayType(integerType, three), b.type());
		assertEquals(universe.arrayRead(b, zero), five);
		assertEquals(universe.arrayRead(b, one), seventeen);
		assertEquals(universe.arrayRead(b, two), six);
	}
	
	/**
	 * get the length of an array
	 */
	@Test
	public void lengthTest(){
		SymbolicExpression a = universe.array(integerType, list1);
		
		assertEquals(two, universe.length(a));
	}
	
	/**
	 * array access test
	 */
	@Test
	public void arrayRead() {
		SymbolicExpression a = universe.array(integerType, list1);
		assertEquals(five, universe.arrayRead(a, zero));
		assertEquals(six, universe.arrayRead(a, one));
	}
	
	/**
	 * 
	 * write an constant array
	 */
	@Test
	public void constantArrayWrite(){
		SymbolicExpression a = universe.constantArray(integerType, one, one);
		SymbolicExpression b = universe.arrayWrite(a, zero, two);
		
		assertEquals(universe.arrayRead(b, zero), two);
	}
	
	/**
	 * remove an element from a constant array
	 */
	@Test
	public void constantArrayRemove(){
		SymbolicExpression a = universe.constantArray(integerType, two, one);
		SymbolicExpression b = universe.removeElementAt(a, 0);
		
		assertEquals(one, universe.length(b));
	}
	
	@Test
	public void arrayWrite2Test() {
		SymbolicArrayType t1 = universe.arrayType(integerType);
		SymbolicArrayType t2 = universe.arrayType(t1, universe.integer(2));
		SymbolicExpression a1 = universe.array(integerType, list1);
		SymbolicExpression a2 = universe.array(integerType, list2);
		SymbolicExpression a = universe.symbolicConstant(a_obj, t2);

		assertTrue(t2.isComplete());
		a = universe.arrayWrite(a, zero, a1);
		a = universe.arrayWrite(a, one, a2);
		out.println("jagged1: a = " + a);
		// a={{5,6},{17}}
		assertEquals(five,
				universe.arrayRead(universe.arrayRead(a, zero), zero));
		assertEquals(six, universe.arrayRead(universe.arrayRead(a, zero), one));
		assertEquals(seventeen,
				universe.arrayRead(universe.arrayRead(a, one), zero));
		assertTrue(((SymbolicArrayType) a.type()).isComplete());
		assertEquals(two, universe.length(a));
		assertEquals(two, universe.length(universe.arrayRead(a, zero)));
		assertEquals(one, universe.length(universe.arrayRead(a, one)));
	}

	/**
	 * Write and read a 2d array.
	 */
	@Test
	public void array2dTest() {
		SymbolicArrayType t = universe.arrayType(universe
				.arrayType(integerType));
		SymbolicExpression a = universe.symbolicConstant(a_obj, t);
		NumericExpression zero = universe.integer(0);
		NumericExpression twoInt = universe.integer(2);
		SymbolicExpression read;

		a = write2d(a, zero, zero, twoInt);
		read = read2d(a, zero, zero);
		assertEquals(twoInt, read);
		// for the heck of it...
		out.println("array2d: new row is: " + universe.arrayRead(a, zero));
	}
	
	@Test
	public void denseArrayWriteTest() {
		SymbolicArrayType t = universe.arrayType(integerType);
		SymbolicExpression a = universe.symbolicConstant(
				universe.stringObject("a"), t);
		SymbolicExpression b1 = universe.denseArrayWrite(
				a,
				Arrays.asList(new SymbolicExpression[] { null, null, two, null,
						two, null, null }));
		SymbolicExpression b2 = universe.arrayWrite(a, two, two);

		b2 = universe.arrayWrite(b2, universe.integer(4), two);
		out.println("b1 = " + b1);
		out.println("b2 = " + b2);
		assertEquals(b2, b1);
	}
	
	@Test
	public void canonic1() {
		SymbolicArrayType t1 = universe.arrayType(integerType,
				universe.integer(3));
		SymbolicArrayType t2 = universe.arrayType(integerType,
				universe.integer(3));
		assertEquals(t1, t2);
		t1 = (SymbolicArrayType) universe.canonic(t1);
		t2 = (SymbolicArrayType) universe.canonic(t2);
		assertSame(t1, t2);
	}
	
}
