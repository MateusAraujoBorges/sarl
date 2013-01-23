package edu.udel.cis.vsl.sarl.symbolic;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.BinaryOperatorIF;
import edu.udel.cis.vsl.sarl.IF.BooleanObject;
import edu.udel.cis.vsl.sarl.IF.IntObject;
import edu.udel.cis.vsl.sarl.IF.NumberIF;
import edu.udel.cis.vsl.sarl.IF.NumberObject;
import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.SimplifierIF;
import edu.udel.cis.vsl.sarl.IF.StringObject;
import edu.udel.cis.vsl.sarl.IF.SymbolicArrayTypeIF;
import edu.udel.cis.vsl.sarl.IF.SymbolicCollection;
import edu.udel.cis.vsl.sarl.IF.SymbolicCompleteArrayTypeIF;
import edu.udel.cis.vsl.sarl.IF.SymbolicConstantIF;
import edu.udel.cis.vsl.sarl.IF.SymbolicExpressionIF;
import edu.udel.cis.vsl.sarl.IF.SymbolicExpressionIF.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.SymbolicFunctionTypeIF;
import edu.udel.cis.vsl.sarl.IF.SymbolicMap;
import edu.udel.cis.vsl.sarl.IF.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.SymbolicSequence;
import edu.udel.cis.vsl.sarl.IF.SymbolicSet;
import edu.udel.cis.vsl.sarl.IF.SymbolicTupleTypeIF;
import edu.udel.cis.vsl.sarl.IF.SymbolicTypeIF;
import edu.udel.cis.vsl.sarl.IF.SymbolicTypeSequenceIF;
import edu.udel.cis.vsl.sarl.IF.SymbolicUnionTypeIF;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverseIF;
import edu.udel.cis.vsl.sarl.IF.UnaryOperatorIF;
import edu.udel.cis.vsl.sarl.symbolic.type.SymbolicTypeFactory;

/**
 * This class provides partial implementation of the SymbolicUniverseIF
 * interface. Generic implementations of methods "make" and "canonicalize" are
 * given.
 * 
 * @author siegel
 */
public class CommonSymbolicUniverse implements SymbolicUniverseIF {

	private Map<SymbolicObject, SymbolicObject> objectMap = new HashMap<SymbolicObject, SymbolicObject>();

	private ArrayList<SymbolicObject> objectList = new ArrayList<SymbolicObject>();

	private SymbolicTypeFactory typeFactory;

	private SymbolicTypeIF booleanType, integerType, realType;

	private SymbolicExpressionIF trueExpr, falseExpr;

	private SymbolicExpressionIF zeroInt, zeroReal, oneInt, oneReal;

	public CommonSymbolicUniverse(SymbolicTypeFactory typeFactory) {
		this.typeFactory = typeFactory;
		this.booleanType = typeFactory.booleanType();
		this.integerType = typeFactory.integerType();
		this.realType = typeFactory.realType();
		this.trueExpr = expression(SymbolicOperator.CONCRETE, booleanType,
				booleanObject(true));
		this.falseExpr = expression(SymbolicOperator.CONCRETE, booleanType,
				booleanObject(false));
	}

	// Helpers...

	protected SymbolicObject canonic(SymbolicObject object) {
		SymbolicObject result = objectMap.get(object);

		if (result == null) {
			((CommonSymbolicObject) object).setId(objectList.size());
			objectMap.put(object, object);
			objectList.add(object);
			return object;
		}
		return result;
	}

	protected SymbolicExpressionIF canonic(SymbolicExpressionIF expression) {
		return (SymbolicExpressionIF) canonic((SymbolicObject) expression);
	}

	protected SymbolicExpressionIF expression(SymbolicOperator operator,
			SymbolicTypeIF type, SymbolicObject[] arguments) {
		return canonic(new CommonSymbolicExpression(operator, type, arguments));
	}

	protected SymbolicExpressionIF expression(SymbolicOperator operator,
			SymbolicTypeIF type, SymbolicObject arg0) {
		return canonic(new CommonSymbolicExpression(operator, type, arg0));
	}

	protected SymbolicExpressionIF expression(SymbolicOperator operator,
			SymbolicTypeIF type, SymbolicObject arg0, SymbolicObject arg1) {
		return canonic(new CommonSymbolicExpression(operator, type, arg0, arg1));
	}

	protected SymbolicExpressionIF expression(SymbolicOperator operator,
			SymbolicTypeIF type, SymbolicObject arg0, SymbolicObject arg1,
			SymbolicObject arg2) {
		return canonic(new CommonSymbolicExpression(operator, type, arg0, arg1,
				arg2));
	}

	protected SymbolicExpressionIF zero(SymbolicTypeIF type) {
		if (type.isInteger())
			return zeroInt();
		else if (type.isReal())
			return zeroReal();
		else
			throw new SARLInternalException("Expected type int or real, not "
					+ type);
	}

	protected SymbolicSet set(SymbolicExpressionIF x, SymbolicExpressionIF y) {
		return add(singleton(x), y);
	}

	// Exported methods...

	/**
	 * For exists and forall, must provide an instance of
	 * SymbolicConstantExpressionIF as arg0. Cannot be applied to make concrete
	 * expressions or SymbolicConstantExpressionIF. There are separate methods
	 * for those.
	 */
	@Override
	public SymbolicExpressionIF make(SymbolicOperator operator,
			SymbolicTypeIF type, SymbolicObject[] args) {
		int numArgs = args.length;

		switch (operator) {
		case ADD: // 1 or 2 args
			if (numArgs == 1) // collection
				return add((SymbolicCollection) args[0]);
			else
				return add((SymbolicExpressionIF) args[0],
						(SymbolicExpressionIF) args[1]);
		case AND: // 1 or 2 args
			if (numArgs == 1) // collection
				return and((SymbolicCollection) args[0]);
			else
				return and((SymbolicExpressionIF) args[0],
						(SymbolicExpressionIF) args[1]);
		case APPLY: // 2 args: function and sequence
			return apply((SymbolicExpressionIF) args[0],
					(SymbolicSequence) args[1]);
		case ARRAY_LAMBDA:
			return arrayLambda((SymbolicCompleteArrayTypeIF) type,
					(SymbolicExpressionIF) args[0]);
		case ARRAY_READ:
			return arrayRead((SymbolicExpressionIF) args[0],
					(SymbolicExpressionIF) args[1]);
		case ARRAY_WRITE:
			return arrayWrite((SymbolicExpressionIF) args[0],
					(SymbolicExpressionIF) args[1],
					(SymbolicExpressionIF) args[2]);
		case CAST:
			return castToReal((SymbolicExpressionIF) args[0]);
		case CONCRETE:
			return expression(SymbolicOperator.CONCRETE, type, args[0]);
		case COND:
			return cond((SymbolicExpressionIF) args[0],
					(SymbolicExpressionIF) args[1],
					(SymbolicExpressionIF) args[2]);
		case DENSE_ARRAY_WRITE:
			return denseArrayWrite((SymbolicExpressionIF) args[0],
					(SymbolicSequence) args[1]);
		case DIVIDE:
			return divide((SymbolicExpressionIF) args[0],
					(SymbolicExpressionIF) args[1]);
		case EQUALS:
			return equals((SymbolicExpressionIF) args[0],
					(SymbolicExpressionIF) args[1]);
		case EXISTS:
			return exists((SymbolicConstantIF) args[0],
					(SymbolicExpressionIF) args[1]);
		case FORALL:
			return forall((SymbolicConstantIF) args[0],
					(SymbolicExpressionIF) args[1]);
		case INT_DIVIDE:
			return divide((SymbolicExpressionIF) args[0],
					(SymbolicExpressionIF) args[1]);
		case LAMBDA:
			return lambda((SymbolicConstantIF) args[0],
					(SymbolicExpressionIF) args[1]);
		case LENGTH:
			return length((SymbolicConstantIF) args[0]);
		case LESS_THAN:
			return lessThan((SymbolicExpressionIF) args[0],
					(SymbolicExpressionIF) args[1]);
		case LESS_THAN_EQUALS:
			return lessThanEquals((SymbolicExpressionIF) args[0],
					(SymbolicExpressionIF) args[1]);
		case MODULO:
			return modulo((SymbolicExpressionIF) args[0],
					(SymbolicExpressionIF) args[1]);
		case MULTIPLY:
			if (numArgs == 1) // collection
				return multiply((SymbolicCollection) args[0]);
			else
				return multiply((SymbolicExpressionIF) args[0],
						(SymbolicExpressionIF) args[1]);
		case NEGATIVE:
			return minus((SymbolicExpressionIF) args[0]);
		case NEQ:
			return neq((SymbolicExpressionIF) args[0],
					(SymbolicExpressionIF) args[1]);
		case NOT:
			return not((SymbolicExpressionIF) args[0]);
		case OR: {
			if (numArgs == 1) // collection
				return or((SymbolicCollection) args[0]);
			else
				return or((SymbolicExpressionIF) args[0],
						(SymbolicExpressionIF) args[1]);
		}
		case POWER: // exponent could be expression or int constant
			if (args[1] instanceof SymbolicExpressionIF)
				return power((SymbolicExpressionIF) args[0],
						(SymbolicExpressionIF) args[1]);
			else
				return power((SymbolicExpressionIF) args[0],
						(IntObject) args[1]);
		case SUBTRACT:
			return subtract((SymbolicExpressionIF) args[0],
					(SymbolicExpressionIF) args[1]);
		case SYMBOLIC_CONSTANT:
			return symbolicConstant((StringObject) args[0], type);
		case TUPLE_READ:
			return tupleRead((SymbolicExpressionIF) args[0],
					(IntObject) args[1]);
		case TUPLE_WRITE:
			return tupleWrite((SymbolicExpressionIF) args[0],
					(IntObject) args[1], (SymbolicExpressionIF) args[2]);
		case UNION_EXTRACT: {
			SymbolicExpressionIF expression = (SymbolicExpressionIF) args[1];
			SymbolicUnionTypeIF unionType = (SymbolicUnionTypeIF) expression
					.type();

			return unionExtract(unionType, (IntObject) args[0], expression);
		}
		case UNION_INJECT: {
			SymbolicExpressionIF expression = (SymbolicExpressionIF) args[1];
			SymbolicUnionTypeIF unionType = (SymbolicUnionTypeIF) type;

			return unionInject(unionType, (IntObject) args[0], expression);

		}
		case UNION_TEST: {
			SymbolicExpressionIF expression = (SymbolicExpressionIF) args[1];
			SymbolicUnionTypeIF unionType = (SymbolicUnionTypeIF) expression
					.type();

			return unionTest(unionType, (IntObject) args[0], expression);
		}
		default:
			throw new IllegalArgumentException("Unknown expression kind: "
					+ operator);
		}
	}

	@Override
	public SymbolicExpressionIF add(SymbolicCollection args) {
		int size = args.size();
		SymbolicExpressionIF result = null;

		if (size == 0)
			throw new IllegalArgumentException(
					"Collection must contain at least one element");
		for (SymbolicExpressionIF arg : args) {
			if (result == null)
				result = arg;
			else
				result = add(result, arg);
		}
		return result;
	}

	/**
	 * Cannot assume anything about the collection of arguments. Therefore just
	 * apply the binary and operator to them in order.
	 */
	@Override
	public SymbolicExpressionIF and(SymbolicCollection args) {
		SymbolicExpressionIF result = trueExpr;

		for (SymbolicExpressionIF arg : args)
			result = and(result, arg);
		return result;
	}

	/**
	 * Assumes the given arguments are in CNF form and produces the conjunction
	 * of the two.
	 * 
	 * CNF form: true | false | AND set | e
	 * 
	 * where set is a set of boolean expressions which are not true, false, or
	 * AND expressions and set has cardinality at least 2. e is any boolean
	 * expression not a true, false, or AND expression. Strategy: eliminate the
	 * true and false cases in the obvious way. Then
	 * 
	 * <pre>
	 * AND s1, AND s2 -> AND union(s1,s2)
	 * AND s1, e -> AND add(s1, e)
	 * AND e1, e2-> if e1.equals(e2) then e1 else AND {e1,e2}
	 * </pre>
	 */
	@Override
	public SymbolicExpressionIF and(SymbolicExpressionIF arg0,
			SymbolicExpressionIF arg1) {
		if (arg0 == trueExpr)
			return arg1;
		if (arg1 == trueExpr)
			return arg0;
		if (arg0 == falseExpr || arg1 == falseExpr)
			return falseExpr;
		if (arg0.equals(arg1))
			return arg0;
		else {
			boolean isAnd0 = arg0.operator() == SymbolicOperator.AND;
			boolean isAnd1 = arg1.operator() == SymbolicOperator.AND;

			if (isAnd0 && isAnd1)
				return expression(
						SymbolicOperator.AND,
						booleanType,
						union((SymbolicSet) arg0.argument(0),
								(SymbolicSet) arg1.argument(0)));
			if (isAnd0 && !isAnd1)
				return expression(SymbolicOperator.AND, booleanType,
						add((SymbolicSet) arg0.argument(0), arg1));
			if (!isAnd0 && isAnd1)
				return expression(SymbolicOperator.AND, booleanType,
						add((SymbolicSet) arg1.argument(0), arg0));
			return expression(SymbolicOperator.AND, booleanType,
					set(arg0, arg1));
		}
	}

	@Override
	public SymbolicTypeIF booleanType() {
		return booleanType;
	}

	@Override
	public SymbolicTypeIF integerType() {
		return integerType;
	}

	@Override
	public SymbolicTypeIF realType() {
		return realType;
	}

	@Override
	public SymbolicCompleteArrayTypeIF arrayType(SymbolicTypeIF elementType,
			SymbolicExpressionIF extent) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicArrayTypeIF arrayType(SymbolicTypeIF elementType) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicTypeSequenceIF typeSequence(SymbolicTypeIF[] types) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicTypeSequenceIF typeSequence(Iterable<SymbolicTypeIF> types) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicTupleTypeIF tupleType(StringObject name,
			SymbolicTypeSequenceIF fieldTypes) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicFunctionTypeIF functionType(
			SymbolicTypeSequenceIF inputTypes, SymbolicTypeIF outputType) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicUnionTypeIF unionType(StringObject name,
			SymbolicTypeSequenceIF memberTypes) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public int numObjects() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public SymbolicObject objectWithId(int index) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<SymbolicObject> objects() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SimplifierIF simplifier(SymbolicExpressionIF assumption) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanObject booleanObject(boolean value) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IntObject intObject(int value) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public NumberObject numberObject(NumberIF value) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public StringObject stringObject(String string) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicConstantIF symbolicConstant(StringObject name,
			SymbolicTypeIF type) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<SymbolicConstantIF> symbolicConstants() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicConstantIF extractSymbolicConstant(
			SymbolicExpressionIF expression) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF substitute(SymbolicExpressionIF expression,
			Map<SymbolicConstantIF, SymbolicExpressionIF> map) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF symbolic(NumberObject numberObject) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF symbolic(int value) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF zeroInt() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF zeroReal() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF oneInt() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF oneReal() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF add(SymbolicExpressionIF arg0,
			SymbolicExpressionIF arg1) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF subtract(SymbolicExpressionIF arg0,
			SymbolicExpressionIF arg1) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF multiply(SymbolicExpressionIF arg0,
			SymbolicExpressionIF arg1) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF multiply(SymbolicCollection args) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF divide(SymbolicExpressionIF arg0,
			SymbolicExpressionIF arg1) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF modulo(SymbolicExpressionIF arg0,
			SymbolicExpressionIF arg1) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF minus(SymbolicExpressionIF arg) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF power(SymbolicExpressionIF base,
			IntObject exponent) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF power(SymbolicExpressionIF base,
			SymbolicExpressionIF exponent) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF castToReal(
			SymbolicExpressionIF numericExpression) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public NumberIF extractNumber(SymbolicExpressionIF expression) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF symbolic(BooleanObject object) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF symbolic(boolean value) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * Assume both args are in CNF normal form:
	 * 
	 * arg: true | false | AND set1 | OR set2 | e
	 * 
	 * Strategy: get rid of true false cases as usual. Then:
	 * 
	 * <pre>
	 * or(AND set, X) = and(s in set) or(s,X)
	 * or(X, AND set) = and(s in set) or(X,s)
	 * or(OR set0, OR set1) = OR(union(set0, set1))
	 * or(OR set, e) = OR(add(set, e))
	 * or(e, OR set) = OR(add(set, e))
	 * or(e1, e2) = OR(set(e1,e2))
	 * </pre>
	 * 
	 * where X is an AND, OR or e expression; set0 and set1 are sets of e
	 * expressions.
	 */
	@Override
	public SymbolicExpressionIF or(SymbolicExpressionIF arg0,
			SymbolicExpressionIF arg1) {
		if (arg0 == trueExpr || arg1 == trueExpr)
			return trueExpr;
		if (arg0 == falseExpr)
			return arg1;
		if (arg1 == falseExpr)
			return arg0;
		if (arg0.equals(arg1))
			return arg0;
		else {
			SymbolicOperator op0 = arg0.operator();
			SymbolicOperator op1 = arg1.operator();

			if (op0 == SymbolicOperator.AND) {
				SymbolicExpressionIF result = falseExpr;

				for (SymbolicExpressionIF clause : (SymbolicSet) arg0
						.argument(0))
					result = or(result, and(clause, arg1));
				return result;
			}
			if (op1 == SymbolicOperator.AND) {
				SymbolicExpressionIF result = falseExpr;

				for (SymbolicExpressionIF clause : (SymbolicSet) arg1
						.argument(0))
					result = or(result, and(arg0, clause));
				return result;
			}
			if (op0 == SymbolicOperator.OR && op1 == SymbolicOperator.OR)
				return expression(
						op0,
						booleanType,
						union((SymbolicSet) arg0.argument(0),
								(SymbolicSet) arg1.argument(0)));
			if (op0 == SymbolicOperator.OR)
				return expression(op0, booleanType,
						add((SymbolicSet) arg0.argument(0), arg1));
			if (op1 == SymbolicOperator.OR)
				return expression(op1, booleanType,
						add((SymbolicSet) arg1.argument(0), arg0));
			return expression(SymbolicOperator.OR, booleanType, set(arg0, arg1));
		}
	}

	/**
	 * Assume nothing about the list of args.
	 */
	@Override
	public SymbolicExpressionIF or(SymbolicCollection args) {
		SymbolicExpressionIF result = falseExpr;

		for (SymbolicExpressionIF arg : args)
			result = or(result, arg);
		return result;
	}

	@Override
	public SymbolicExpressionIF not(SymbolicExpressionIF arg) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF lessThan(SymbolicExpressionIF arg0,
			SymbolicExpressionIF arg1) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF lessThanEquals(SymbolicExpressionIF arg0,
			SymbolicExpressionIF arg1) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF equals(SymbolicExpressionIF arg0,
			SymbolicExpressionIF arg1) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF neq(SymbolicExpressionIF arg0,
			SymbolicExpressionIF arg1) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF forall(SymbolicConstantIF boundVariable,
			SymbolicExpressionIF predicate) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF exists(SymbolicConstantIF boundVariable,
			SymbolicExpressionIF predicate) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Boolean extractBoolean(SymbolicExpressionIF expression) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF lambda(SymbolicConstantIF boundVariable,
			SymbolicExpressionIF expression) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF apply(SymbolicExpressionIF function,
			SymbolicSequence argumentSequence) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF unionInject(SymbolicUnionTypeIF unionType,
			IntObject memberIndex, SymbolicExpressionIF object) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF unionTest(SymbolicUnionTypeIF unionType,
			IntObject memberIndex, SymbolicExpressionIF object) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF unionExtract(SymbolicUnionTypeIF unionType,
			IntObject memberIndex, SymbolicExpressionIF object) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF array(SymbolicSequence elements) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF length(SymbolicExpressionIF array) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF arrayRead(SymbolicExpressionIF array,
			SymbolicExpressionIF index) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF arrayWrite(SymbolicExpressionIF array,
			SymbolicExpressionIF index, SymbolicExpressionIF value) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF denseArrayWrite(SymbolicExpressionIF array,
			SymbolicSequence values) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF arrayLambda(
			SymbolicCompleteArrayTypeIF arrayType, SymbolicExpressionIF function) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF tuple(SymbolicTupleTypeIF type,
			SymbolicSequence components) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF tupleRead(SymbolicExpressionIF tuple,
			IntObject index) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF tupleWrite(SymbolicExpressionIF tuple,
			IntObject index, SymbolicExpressionIF value) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF cast(SymbolicTypeIF newType,
			SymbolicExpressionIF expression) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicExpressionIF cond(SymbolicExpressionIF predicate,
			SymbolicExpressionIF trueValue, SymbolicExpressionIF falseValue) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicSequence sequence(
			Iterable<? extends SymbolicExpressionIF> elements) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicSequence sequence(SymbolicExpressionIF[] elements) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicSequence add(SymbolicSequence sequence,
			SymbolicExpressionIF element) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicSequence set(SymbolicSequence sequence, int index,
			SymbolicExpressionIF element) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicSequence remove(SymbolicSequence sequence, int index) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicMap emptyMap() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicMap put(SymbolicMap map, SymbolicExpressionIF key,
			SymbolicExpressionIF value) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicMap map(
			Map<SymbolicExpressionIF, SymbolicExpressionIF> javaMap) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicMap apply(SymbolicMap map, UnaryOperatorIF operator) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicMap combine(BinaryOperatorIF operator, SymbolicMap map1,
			SymbolicMap map2) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicSet emptySet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicSet add(SymbolicSet set, SymbolicExpressionIF element) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicSet union(SymbolicSet set0, SymbolicSet set1) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicSet singleton(SymbolicExpressionIF element) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicSet remove(SymbolicSet set, SymbolicExpressionIF element) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicSet intersection(SymbolicSet set1, SymbolicSet set2) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicSet removeAll(SymbolicSet set1, SymbolicSet set2) {
		// TODO Auto-generated method stub
		return null;
	}

}
