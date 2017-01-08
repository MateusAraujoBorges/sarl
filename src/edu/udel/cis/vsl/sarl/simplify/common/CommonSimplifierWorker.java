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

import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
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
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.simplify.IF.Simplifier;

/**
 * A partial implementation of {@link Simplifier} which can be extended.
 * 
 * @author Stephen F. Siegel
 */
public abstract class CommonSimplifierWorker {

	// Static fields...

	public final static boolean debug = false;

	/**
	 * Print debugging information when any non-trivial simplification is
	 * performed?
	 */
	public final static boolean debugSimps = false;

	/**
	 * Where to send debugging output.
	 */
	public final static PrintStream out = System.out;

	// Instance fields...

	protected CommonSimplifier simplifier;

	protected int quantificationDepth = 0;

	// Constructors...

	protected CommonSimplifierWorker(CommonSimplifier simplifier) {
		this.simplifier = simplifier;
	}

	// Abstract methods...

	/**
	 * Simplifies a symbolic expression. This method is called by
	 * {@link #simplifyExpression} when the latter does not find
	 * <code>expression</code> in its simplification cache. (In particular, this
	 * method should not look in the cache, since that was already done.)
	 * 
	 * @param expression
	 *            the symbolic expression to be simplified. Must be canonic.
	 * @return the simplified version of the symbolic expression
	 */
	protected abstract SymbolicExpression simplifyExpressionWork(
			SymbolicExpression expression);

	// Non-abstract methods...

	protected SymbolicObject getCachedSimplification(SymbolicObject object) {
		return simplifier.getCachedSimplification(object);
	}

	protected SymbolicType simplifyTypeWork(SymbolicType type) {
		switch (type.typeKind()) {
		case BOOLEAN:
		case INTEGER:
		case REAL:
		case CHAR:
			return type;
		case ARRAY: {
			SymbolicArrayType arrayType = (SymbolicArrayType) type;
			SymbolicType elementType = arrayType.elementType();
			SymbolicType simplifiedElementType = simplifyType(elementType);

			if (arrayType.isComplete()) {
				NumericExpression extent = ((SymbolicCompleteArrayType) arrayType)
						.extent();
				NumericExpression simplifiedExtent = (NumericExpression) simplifyExpression(
						extent);

				if (elementType != simplifiedElementType
						|| extent != simplifiedExtent)
					return simplifier.universe.arrayType(simplifiedElementType,
							simplifiedExtent);
				return arrayType;
			} else {
				if (elementType != simplifiedElementType)
					return simplifier.universe.arrayType(simplifiedElementType);
				return arrayType;
			}
		}
		case FUNCTION: {
			SymbolicFunctionType functionType = (SymbolicFunctionType) type;
			SymbolicTypeSequence inputs = functionType.inputTypes();
			SymbolicTypeSequence simplifiedInputs = simplifyTypeSequence(
					inputs);
			SymbolicType output = functionType.outputType();
			SymbolicType simplifiedOutput = simplifyType(output);

			if (inputs != simplifiedInputs || output != simplifiedOutput)
				return simplifier.universe.functionType(simplifiedInputs,
						simplifiedOutput);
			return type;
		}
		case TUPLE: {
			SymbolicTypeSequence sequence = ((SymbolicTupleType) type)
					.sequence();
			SymbolicTypeSequence simplifiedSequence = simplifyTypeSequence(
					sequence);

			if (simplifiedSequence != sequence)
				return simplifier.universe.tupleType(
						((SymbolicTupleType) type).name(), simplifiedSequence);
			return type;
		}
		case UNION: {
			SymbolicTypeSequence sequence = ((SymbolicUnionType) type)
					.sequence();
			SymbolicTypeSequence simplifiedSequence = simplifyTypeSequence(
					sequence);

			if (simplifiedSequence != sequence)
				return simplifier.universe.unionType(
						((SymbolicUnionType) type).name(), simplifiedSequence);
			return type;
		}
		default:
			throw new SARLInternalException("unreachable");
		}
	}

	protected SymbolicTypeSequence simplifyTypeSequenceWork(
			SymbolicTypeSequence sequence) {
		int size = sequence.numTypes();

		for (int i = 0; i < size; i++) {
			SymbolicType type = sequence.getType(i);
			SymbolicType simplifiedType = simplifyType(type);

			if (type != simplifiedType) {
				SymbolicType[] newTypes = new SymbolicType[size];

				for (int j = 0; j < i; j++)
					newTypes[j] = sequence.getType(j);
				newTypes[i] = simplifiedType;
				for (int j = i + 1; j < size; j++)
					newTypes[j] = simplifyType(sequence.getType(j));

				return simplifier.universe
						.typeSequence(Arrays.asList(newTypes));
			}
		}
		return sequence;
	}

	protected SymbolicSequence<?> simplifySequenceWork(
			SymbolicSequence<?> sequence) {
		int size = sequence.size();
		// TODO: why create this array if it may not be needed?
		SymbolicExpression[] newElements = new SymbolicExpression[size];
		SymbolicSequence<?> result = sequence;

		for (int i = 0; i < size; i++) {
			SymbolicExpression oldElement = sequence.get(i);
			SymbolicExpression newElement = simplifyExpression(oldElement);

			newElements[i] = newElement;
			if (newElement != oldElement) {
				i++;
				for (; i < size; i++)
					newElements[i] = simplifyExpression(sequence.get(i));
				result = simplifier.objectFactory.sequence(newElements);
				break;
			}
		}
		return result;
	}

	protected SymbolicObject simplifyObjectWork(SymbolicObject object) {
		switch (object.symbolicObjectKind()) {
		case BOOLEAN:
		case INT:
		case NUMBER:
		case STRING:
		case CHAR:
			return object;
		case EXPRESSION:
			return simplifyExpressionWork((SymbolicExpression) object);
		case SEQUENCE:
			return simplifySequenceWork((SymbolicSequence<?>) object);
		case TYPE:
			return simplifyTypeWork((SymbolicType) object);
		case TYPE_SEQUENCE:
			return simplifyTypeSequenceWork((SymbolicTypeSequence) object);
		default:
			throw new SARLInternalException("unreachable");
		}
	}

	protected SymbolicObject simplifyObject(SymbolicObject object) {
		object = simplifier.universe.canonic(object);

		SymbolicObject result = simplifier.getCachedSimplification(object);

		if (result == null) {
			result = simplifyObjectWork(object);
			result = simplifier.universe.canonic(result);
			if (quantificationDepth == 0)
				simplifier.cacheSimplification(object, result);
		}
		return result;
	}

	protected SymbolicType simplifyType(SymbolicType type) {
		type = (SymbolicType) simplifier.universe.canonic(type);

		SymbolicType result = (SymbolicType) simplifier
				.getCachedSimplification(type);

		if (result == null) {
			result = simplifyTypeWork(type);
			result = (SymbolicType) simplifier.universe.canonic(result);
			if (quantificationDepth == 0)
				simplifier.cacheSimplification(type, result);
		}
		return result;
	}

	protected SymbolicTypeSequence simplifyTypeSequence(
			SymbolicTypeSequence seq) {
		seq = (SymbolicTypeSequence) simplifier.universe.canonic(seq);

		SymbolicTypeSequence result = (SymbolicTypeSequence) simplifier
				.getCachedSimplification(seq);

		if (result == null) {
			result = simplifyTypeSequenceWork(seq);
			result = (SymbolicTypeSequence) simplifier.universe.canonic(result);
			if (quantificationDepth == 0)
				simplifier.cacheSimplification(seq, result);
		}
		return result;
	}

	protected SymbolicSequence<?> simplifySequence(
			SymbolicSequence<?> sequence) {
		sequence = (SymbolicSequence<?>) simplifier.universe.canonic(sequence);

		SymbolicSequence<?> result = (SymbolicSequence<?>) simplifier
				.getCachedSimplification(sequence);

		if (result == null) {
			result = simplifySequenceWork(sequence);
			result = (SymbolicSequence<?>) simplifier.universe.canonic(result);
			if (quantificationDepth == 0)
				simplifier.cacheSimplification(sequence, result);
		}
		return result;
	}

	protected SymbolicExpression simplifyExpression(
			SymbolicExpression expression) {
		expression = simplifier.universe.canonic(expression);

		SymbolicExpression result = (SymbolicExpression) simplifier
				.getCachedSimplification(expression);

		if (result == null) {
			result = simplifyExpressionWork(expression);
			result = simplifier.universe.canonic(result);
			if (quantificationDepth == 0)
				simplifier.cacheSimplification(expression, result);
		}
		return result;
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
	 * You almost certainly want to override this method.
	 * </p>
	 * 
	 * <p>
	 * This method does <strong>not</strong> look in the table of cached
	 * simplification results for <code>expression</code>. However, the
	 * recursive calls to the arguments may look in the cache.
	 * </p>
	 * 
	 * @param expression
	 *            any symbolic expression
	 * @return a simplified version of that expression
	 */
	public SymbolicExpression simplifyExpressionGeneric(
			SymbolicExpression expression) {
		if (expression.isNull())
			return expression;
	
		SymbolicOperator operator = expression.operator();
		boolean isQuantified = false;
	
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
		} else if (operator == SymbolicOperator.FORALL
				|| operator == SymbolicOperator.EXISTS
				|| operator == SymbolicOperator.LAMBDA) {
			isQuantified = true;
			quantificationDepth++;
		}
	
		SymbolicType type = expression.type();
		SymbolicType simplifiedType = simplifyType(type);
		int numArgs = expression.numArguments();
		SymbolicObject[] simplifiedArgs = null;
	
		if (type == simplifiedType) {
			for (int i = 0; i < numArgs; i++) {
				SymbolicObject arg = expression.argument(i);
				SymbolicObject simplifiedArg = simplifyObject(arg);
	
				assert simplifiedArg != null;
				if (simplifiedArg != arg) {
					simplifiedArgs = new SymbolicObject[numArgs];
					for (int j = 0; j < i; j++)
						simplifiedArgs[j] = expression.argument(j);
					simplifiedArgs[i] = simplifiedArg;
					for (int j = i + 1; j < numArgs; j++)
						simplifiedArgs[j] = simplifyObject(
								expression.argument(j));
					break;
				}
			}
		} else {
			simplifiedArgs = new SymbolicObject[numArgs];
			for (int i = 0; i < numArgs; i++)
				simplifiedArgs[i] = simplifyObject(expression.argument(i));
		}
		if (isQuantified)
			quantificationDepth--;
		if (simplifiedArgs == null)
			return expression;
		return simplifier.universe.make(operator, simplifiedType,
				simplifiedArgs);
	}

}
