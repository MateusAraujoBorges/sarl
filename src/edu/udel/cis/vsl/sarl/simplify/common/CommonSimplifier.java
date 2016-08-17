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
package edu.udel.cis.vsl.sarl.simplify.common;

import java.io.PrintStream;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject.SymbolicObjectKind;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicSequence;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTypeSequence;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.simplify.IF.Simplifier;

/**
 * A partial implementation of {@link Simplifier} which can be extended.
 * 
 * @author Stephen F. Siegel
 */
public abstract class CommonSimplifier implements Simplifier {

	// Static fields...

	/**
	 * Keeps count of the number of simplifications performed, for performance
	 * debugging.
	 */
	public static int simplifyCount = 0;

	/**
	 * Where to send debugging output.
	 */
	public final static PrintStream out = System.out;

	/**
	 * The symbolic universe used to make new expressions.
	 */
	protected PreUniverse universe;

	/**
	 * Factory used for producing {@link SymbolicCollection}s.
	 */
	protected ObjectFactory objectFactory;

	/**
	 * Cached simplifications.
	 * 
	 * Problem here: the keys and/or values may or may not be canonic. Should we
	 * insist that before simplifying any expression, it should be canonic?
	 */
	private Map<SymbolicObject, SymbolicObject> simplifyMap = new HashMap<SymbolicObject, SymbolicObject>();

	public CommonSimplifier(PreUniverse universe) {
		assert universe != null;
		this.universe = universe;
		this.objectFactory = universe.objectFactory();
	}

	@Override
	public PreUniverse universe() {
		return universe;
	}

	/**
	 * Determines if the given expression is a quantified expression.
	 * 
	 * @param expr
	 *            a non-<code>null</code> symbolic expression
	 * @return <code>true</code> iff the expression is quantified
	 */
	protected boolean isQuantified(SymbolicExpression expr) {
		SymbolicOperator operator = expr.operator();

		return operator == SymbolicOperator.EXISTS
				|| operator == SymbolicOperator.FORALL
				|| operator == SymbolicOperator.LAMBDA;
	}

	/**
	 * Simplifies a symbolic expression. A concrete extension of this class must
	 * implement this method. The implementation may use
	 * {@link CommonSimplifier#simplifyGenericExpression}, a generic
	 * simplification method provided here.
	 * 
	 * Typically, an implementation of this method should not look in the cache
	 * for a simplified version of expression, because that is done already in
	 * the "main" simplify method, {@link #apply}, which then calls this method
	 * if it does not find it in the cache.
	 * 
	 * 
	 * @param expression
	 *            any symbolic expression.
	 * @return the simplified version of that expression
	 */
	protected abstract SymbolicExpression simplifyExpression(
			SymbolicExpression expression, SimplifierState state);

	protected SymbolicObject getCachedSimplification(SymbolicObject key,
			SimplifierState state) {
		if (key instanceof SymbolicConstant
				&& state.isBoundVaraible((SymbolicConstant) key))
			return key;
		return simplifyMap.get(key);
	}

	protected SymbolicObject cacheSimplification(SymbolicObject key,
			SymbolicObject value) {
		key = universe.canonic(key);
		value = universe.canonic(value);
		return simplifyMap.put(key, value);
	}

	protected void clearSimplificationCache() {
		simplifyMap.clear();
	}

	private SymbolicType simplifyTypeWork(SymbolicType type,
			SimplifierState state) {
		switch (type.typeKind()) {
		case BOOLEAN:
		case INTEGER:
		case REAL:
		case CHAR:
			return type;
		case ARRAY: {
			SymbolicArrayType arrayType = (SymbolicArrayType) type;
			SymbolicType elementType = arrayType.elementType();
			SymbolicType simplifiedElementType = simplifyType(elementType,
					state);

			if (arrayType.isComplete()) {
				NumericExpression extent = ((SymbolicCompleteArrayType) arrayType)
						.extent();
				NumericExpression simplifiedExtent = (NumericExpression) apply(
						extent);

				if (elementType != simplifiedElementType
						|| extent != simplifiedExtent)
					return universe.arrayType(simplifiedElementType,
							simplifiedExtent);
				return arrayType;
			} else {
				if (elementType != simplifiedElementType)
					return universe.arrayType(simplifiedElementType);
				return arrayType;
			}
		}
		case FUNCTION: {
			SymbolicFunctionType functionType = (SymbolicFunctionType) type;
			SymbolicTypeSequence inputs = functionType.inputTypes();
			SymbolicTypeSequence simplifiedInputs = simplifyTypeSequence(inputs,
					state);
			SymbolicType output = functionType.outputType();
			SymbolicType simplifiedOutput = simplifyType(output, state);

			if (inputs != simplifiedInputs || output != simplifiedOutput)
				return universe.functionType(simplifiedInputs,
						simplifiedOutput);
			return type;
		}
		case TUPLE: {
			SymbolicTypeSequence sequence = ((SymbolicTupleType) type)
					.sequence();
			SymbolicTypeSequence simplifiedSequence = simplifyTypeSequence(
					sequence, state);

			if (simplifiedSequence != sequence)
				return universe.tupleType(((SymbolicTupleType) type).name(),
						simplifiedSequence);
			return type;
		}
		case UNION: {
			SymbolicTypeSequence sequence = ((SymbolicUnionType) type)
					.sequence();
			SymbolicTypeSequence simplifiedSequence = simplifyTypeSequence(
					sequence, state);

			if (simplifiedSequence != sequence)
				return universe.unionType(((SymbolicUnionType) type).name(),
						simplifiedSequence);
			return type;
		}
		default:
			throw new SARLInternalException("unreachable");
		}
	}

	protected SymbolicType simplifyType(SymbolicType type,
			SimplifierState state) {
		SymbolicType result = (SymbolicType) getCachedSimplification(type,
				state);

		if (result == null) {
			result = simplifyTypeWork(type, state);
			result = (SymbolicType) universe.canonic(result);
			cacheSimplification(type, result);
		}
		return result;
	}

	private Iterable<? extends SymbolicType> simplifyTypeSequenceWork(
			SymbolicTypeSequence sequence, SimplifierState state) {
		int size = sequence.numTypes();

		for (int i = 0; i < size; i++) {
			SymbolicType type = sequence.getType(i);
			SymbolicType simplifiedType = simplifyType(type, state);

			if (type != simplifiedType) {
				SymbolicType[] newTypes = new SymbolicType[size];

				for (int j = 0; j < i; j++)
					newTypes[j] = sequence.getType(j);
				newTypes[i] = simplifiedType;
				for (int j = i + 1; j < size; j++)
					newTypes[j] = simplifyType(sequence.getType(j), state);
				return Arrays.asList(newTypes);
			}
		}
		return sequence;
	}

	private SymbolicTypeSequence simplifyTypeSequence(
			SymbolicTypeSequence sequence, SimplifierState state) {
		return universe.typeSequence(simplifyTypeSequenceWork(sequence, state));
	}

	private SymbolicSequence<?> simplifySequenceWork(
			SymbolicSequence<?> sequence, SimplifierState state) {
		int size = sequence.size();
		SymbolicExpression[] newElements = new SymbolicExpression[size];
		SymbolicSequence<?> result = sequence;

		for (int i = 0; i < size; i++) {
			SymbolicExpression oldElement = sequence.get(i);
			SymbolicExpression newElement = simplifyExpression(oldElement,
					state);

			newElements[i] = newElement;
			if (newElement != oldElement) {
				i++;
				for (; i < size; i++)
					newElements[i] = simplifyExpression(sequence.get(i), state);
				result = objectFactory.sequence(newElements);
				break;
			}
		}
		return result;
	}

	protected SymbolicSequence<?> simplifySequence(
			SymbolicSequence<?> collection, SimplifierState state) {
		SymbolicSequence<?> result = (SymbolicSequence<?>) getCachedSimplification(
				collection, state);

		if (result == null) {
			result = simplifySequenceWork(collection, state);
			result = (SymbolicSequence<?>) universe.canonic(result);
			cacheSimplification(collection, result);
		}
		return result;
	}

	protected SymbolicObject simplifyObject(SymbolicObject object,
			SimplifierState state) {
		switch (object.symbolicObjectKind()) {
		case BOOLEAN:
		case INT:
		case NUMBER:
		case STRING:
		case CHAR:
			return object;
		case EXPRESSION:
			return simplifyExpression((SymbolicExpression) object, state);
		case SEQUENCE:
			return simplifySequence((SymbolicSequence<?>) object, state);
		case TYPE:
			return simplifyType((SymbolicType) object, state);
		case TYPE_SEQUENCE:
			return simplifyTypeSequence((SymbolicTypeSequence) object, state);
		default:
			throw new SARLInternalException("unreachable");
		}
	}

	/**
	 * <p>
	 * This method simplifies an expression in a generic way that should work
	 * correctly on any symbolic expression: it simplifies the type and the
	 * arguments of the expression, and then rebuilds the expression using
	 * method
	 * {@link PreUniverse#make(SymbolicOperator, SymbolicType, SymbolicObject[])}
	 * .
	 * </p>
	 * 
	 * <p>
	 * This method does <strong>not</strong> look in the table of cached
	 * simplification results for <code>expression</code>. However, the
	 * recursive calls to the arguments may invoke the method
	 * {@link #apply(SymbolicExpression)}, which will look for cached results on
	 * those arguments.
	 * </p>
	 * 
	 * @param expression
	 *            any symbolic expression
	 * @return a simplified version of that expression
	 */
	protected SymbolicExpression simplifyGenericExpression(
			SymbolicExpression expression, SimplifierState state) {
		if (expression.isNull())
			return expression;
		else {
			SymbolicOperator operator = expression.operator();

			if (operator == SymbolicOperator.CONCRETE) {
				SymbolicObject object = (SymbolicObject) expression.argument(0);
				SymbolicObjectKind kind = object.symbolicObjectKind();

				switch (kind) {
				case BOOLEAN:
				case INT:
				case NUMBER:
				case STRING:
					return expression;
				default:
				}
			}
			{
				SymbolicType type = expression.type();
				SymbolicType simplifiedType = simplifyType(type, state);
				int numArgs = expression.numArguments();
				SymbolicObject[] simplifiedArgs = null;

				if (type == simplifiedType) {
					for (int i = 0; i < numArgs; i++) {
						SymbolicObject arg = expression.argument(i);
						SymbolicObject simplifiedArg = simplifyObject(arg,
								state);

						assert simplifiedArg != null;
						if (simplifiedArg != arg) {
							simplifiedArgs = new SymbolicObject[numArgs];
							for (int j = 0; j < i; j++)
								simplifiedArgs[j] = expression.argument(j);
							simplifiedArgs[i] = simplifiedArg;
							for (int j = i + 1; j < numArgs; j++)
								simplifiedArgs[j] = simplifyObject(
										expression.argument(j), state);
							break;
						}
					}
				} else {
					simplifiedArgs = new SymbolicObject[numArgs];
					for (int i = 0; i < numArgs; i++)
						simplifiedArgs[i] = simplifyObject(
								expression.argument(i), state);
				}
				if (simplifiedArgs == null)
					return expression;
				return (SymbolicExpression) universe.canonic(universe
						.make(operator, simplifiedType, simplifiedArgs));
			}
		}
	}

	protected abstract SimplifierState newState();

	@Override
	public SymbolicExpression apply(SymbolicExpression expression) {
		// ensure that the expression is canonic:
		expression = universe.canonic(expression);
		return simplifyExpression(expression, newState());
	}

}
