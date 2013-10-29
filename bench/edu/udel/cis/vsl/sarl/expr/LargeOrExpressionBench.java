package edu.udel.cis.vsl.sarl.expr;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;


import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.universe.Universes;

public class LargeOrExpressionBench {
	private static SymbolicUniverse sUniverse;
	private static SymbolicType booleanType;
	static long start;
	static long end;
	static long mark;
	

	/**
	 * benchmark for large boolean operation on large boolean expressions
	 * does not include time to construct individual expressions
	 * 
	 * @param args
	 *            ignored
	 */
	
	public static void main(String[] args) {

		sUniverse = Universes.newIdealUniverse();
		booleanType = sUniverse.booleanType();
				
		BooleanExpression[] ExpressionList1 = {};
		Collection<BooleanExpression> col1= new ArrayList<BooleanExpression>(Arrays.asList(ExpressionList1));
		BooleanExpression[] ExpressionList2 = {};
		Collection<BooleanExpression> col2= new ArrayList<BooleanExpression>(Arrays.asList(ExpressionList2));
		for(int i = 0; i < 105; i++){
			col1.add((BooleanExpression) sUniverse.symbolicConstant(sUniverse.stringObject(Integer.toString(i)), booleanType));
		}
		for(int i = 0; i < 105; i++){
			col2.add((BooleanExpression) sUniverse.symbolicConstant(sUniverse.stringObject(Integer.toString(-i)), booleanType));
		}
		
		start = System.currentTimeMillis();
			BooleanExpression s1 = sUniverse.and(col1);
			BooleanExpression s2 = sUniverse.and(col2);
			BooleanExpression s3 = sUniverse.or(s1,s2);
	
		end = System.currentTimeMillis();
		mark = end - start;
		System.out.println(mark);
			
			}
}
