package edu.udel.cis.vsl.sarl.expr.IF;

import java.util.Collection;
import java.util.Comparator;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;

public interface ExpressionFactory {

	void setObjectComparator(Comparator<SymbolicObject> c);

	void setTypeComparator(Comparator<SymbolicType> c);

	void init();

	NumericExpressionFactory numericFactory();

	BooleanExpressionFactory booleanFactory();

	ObjectFactory objectFactory();

	SymbolicExpression canonic(SymbolicExpression expression);

	Comparator<SymbolicExpression> comparator();

	SymbolicExpression expression(SymbolicOperator operator, SymbolicType type,
			SymbolicObject[] arguments);

	SymbolicExpression expression(SymbolicOperator operator, SymbolicType type,
			SymbolicObject arg0);

	SymbolicExpression expression(SymbolicOperator operator, SymbolicType type,
			SymbolicObject arg0, SymbolicObject arg1);

	SymbolicExpression expression(SymbolicOperator operator, SymbolicType type,
			SymbolicObject arg0, SymbolicObject arg1, SymbolicObject arg2);

	SymbolicExpression expression(SymbolicOperator operator, SymbolicType type,
			Collection<SymbolicObject> args);

	SymbolicConstant symbolicConstant(StringObject name, SymbolicType type);

	SymbolicExpression nullExpression();

}
