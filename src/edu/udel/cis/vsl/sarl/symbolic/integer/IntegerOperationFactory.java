package edu.udel.cis.vsl.sarl.symbolic.integer;

import java.util.HashMap;
import java.util.Map;

import edu.udel.cis.vsl.sarl.symbolic.CommonSymbolicExpression;
import edu.udel.cis.vsl.sarl.symbolic.CommonSymbolicExpression;
import edu.udel.cis.vsl.sarl.symbolic.IF.tree.TreeExpressionIF;

public class IntegerOperationFactory {

	Map<SymbolicExpressionKey<IntegerDivisionExpression>, IntegerDivisionExpression> integerDivisionMap = new HashMap<SymbolicExpressionKey<IntegerDivisionExpression>, IntegerDivisionExpression>();

	Map<SymbolicExpressionKey<IntegerModulusExpression>, IntegerModulusExpression> integerModulusMap = new HashMap<SymbolicExpressionKey<IntegerModulusExpression>, IntegerModulusExpression>();

	public IntegerDivisionExpression integerDivision(
			TreeExpressionIF numerator, TreeExpressionIF denominator) {
		return CommonSymbolicExpression.flyweight(integerDivisionMap,
				new IntegerDivisionExpression(numerator, denominator));
	}

	public IntegerModulusExpression integerModulus(
			TreeExpressionIF numerator, TreeExpressionIF denominator) {
		return CommonSymbolicExpression.flyweight(integerModulusMap,
				new IntegerModulusExpression(numerator, denominator));
	}

}
