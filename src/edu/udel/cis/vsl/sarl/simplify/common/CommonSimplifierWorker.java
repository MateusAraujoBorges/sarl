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
 * An instance of this class is formed to simplify a symbolic expression. It
 * disappears after it completes the simplification of that expression. Should
 * be extended by implementing the abstract methods.
 * 
 * @author Stephen F. Siegel
 */
public abstract class CommonSimplifierWorker {

	// Static fields...

	/**
	 * Are we going to print general debugging information?
	 */
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

	/**
	 * The universe we're using to create new symbolic objects.
	 */
	protected PreUniverse universe;

	/**
	 * Current depth of quantified expression stack.
	 */
	protected int quantificationDepth = 0;

	// Constructors...

	protected CommonSimplifierWorker(PreUniverse universe) {
		this.universe = universe;
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

	/**
	 * Retrieves a simplification result from the cache. The simplification
	 * methods of the {@link Simplifier} will cache the results of
	 * simplification. This method will get one of those cached results.
	 * 
	 * @param object
	 *            a symbolic object
	 * @return the result of a previous simplification of that object, or
	 *         <code>null</code> is no result has been cached for that object
	 */
	protected abstract SymbolicObject getCachedSimplification(
			SymbolicObject object);

	protected abstract void cacheSimplification(SymbolicObject object,
			SymbolicObject result);

	// Non-abstract methods...

	/**
	 * Performs the work required to simplify a symbolic type. A primitive type
	 * is returned unchanged. For compound types, simplification is recursive on
	 * the structure of the type. Ultimately a non-trivial simplification can
	 * occur because array types may involve an expression for the length of the
	 * array.
	 * 
	 * @param type
	 *            any canonic symbolic type
	 * @return simplified version of that type
	 */
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
			SymbolicTypeSequence simplifiedInputs = simplifyTypeSequence(
					inputs);
			SymbolicType output = functionType.outputType();
			SymbolicType simplifiedOutput = simplifyType(output);

			if (inputs != simplifiedInputs || output != simplifiedOutput)
				return universe.functionType(simplifiedInputs,
						simplifiedOutput);
			return type;
		}
		case TUPLE: {
			SymbolicTypeSequence sequence = ((SymbolicTupleType) type)
					.sequence();
			SymbolicTypeSequence simplifiedSequence = simplifyTypeSequence(
					sequence);

			if (simplifiedSequence != sequence)
				return universe.tupleType(((SymbolicTupleType) type).name(),
						simplifiedSequence);
			return type;
		}
		case UNION: {
			SymbolicTypeSequence sequence = ((SymbolicUnionType) type)
					.sequence();
			SymbolicTypeSequence simplifiedSequence = simplifyTypeSequence(
					sequence);

			if (simplifiedSequence != sequence)
				return universe.unionType(((SymbolicUnionType) type).name(),
						simplifiedSequence);
			return type;
		}
		default:
			throw new SARLInternalException("unreachable");
		}
	}

	/**
	 * Performs the work necessary to simplify a type sequence. The
	 * simplification of a type sequence is the sequence resulting from
	 * simplifying each component type individually.
	 * 
	 * @param sequence
	 *            any canonic type sequence
	 * @return the simplified sequence
	 */
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

				return universe.typeSequence(Arrays.asList(newTypes));
			}
		}
		return sequence;
	}

	/**
	 * Performs the work necessary for simplifying a sequence of symbolic
	 * expressions. The result is obtained by simplifying each component
	 * individually.
	 * 
	 * @param sequence
	 *            any canonic symbolic expression sequence
	 * @return the simplified sequence
	 */
	protected SymbolicSequence<?> simplifySequenceWork(
			SymbolicSequence<?> sequence) {
		int size = sequence.size();
		SymbolicSequence<?> result = sequence;

		for (int i = 0; i < size; i++) {
			SymbolicExpression oldElement = sequence.get(i);
			SymbolicExpression newElement = simplifyExpression(oldElement);

			if (newElement != oldElement) {
				SymbolicExpression[] newElements = new SymbolicExpression[size];

				for (int j = 0; j < i; j++)
					newElements[j] = sequence.get(j);
				newElements[i] = newElement;
				for (int j = i + 1; j < size; j++)
					newElements[j] = simplifyExpression(sequence.get(j));
				result = universe.objectFactory().sequence(newElements);
				break;
			}
		}
		return result;
	}

	/**
	 * Performs the work necessary to simplify a symbolic object. This just
	 * redirects to the appropriate specific method, such as
	 * {@link #simplifySequenceWork(SymbolicSequence)},
	 * {@link #simplifyTypeWork(SymbolicType)}, etc.
	 * 
	 * @param object
	 *            any canonic symbolic object
	 * @return the simplified version of that object
	 */
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

	/**
	 * Simplifies a symbolic object by first looking in the cache for the
	 * previous result of simplifying that object, and, if not found there,
	 * invoking {@link #simplifyObjectWork(SymbolicObject)}
	 * 
	 * @param object
	 *            any non-<code>null</code> symbolic object
	 * @return result of simplification of <code>object</code>
	 */
	protected SymbolicObject simplifyObject(SymbolicObject object) {
		SymbolicObject result = getCachedSimplification(object);

		if (result == null) {
			result = simplifyObjectWork(object);
			if (quantificationDepth == 0)
				cacheSimplification(object, result);
		}
		return result;
	}

	protected SymbolicType simplifyType(SymbolicType type) {
		SymbolicType result = (SymbolicType) getCachedSimplification(type);

		if (result == null) {
			result = simplifyTypeWork(type);
			if (quantificationDepth == 0)
				cacheSimplification(type, result);
		}
		return result;
	}

	protected SymbolicTypeSequence simplifyTypeSequence(
			SymbolicTypeSequence seq) {
		SymbolicTypeSequence result = (SymbolicTypeSequence) getCachedSimplification(
				seq);

		if (result == null) {
			result = simplifyTypeSequenceWork(seq);
			if (quantificationDepth == 0)
				cacheSimplification(seq, result);
		}
		return result;
	}

	protected SymbolicSequence<?> simplifySequence(
			SymbolicSequence<?> sequence) {
		SymbolicSequence<?> result = (SymbolicSequence<?>) getCachedSimplification(
				sequence);

		if (result == null) {
			result = simplifySequenceWork(sequence);
			if (quantificationDepth == 0)
				cacheSimplification(sequence, result);
		}
		return result;
	}

	public SymbolicExpression simplifyExpression(
			SymbolicExpression expression) {
		SymbolicExpression result = (SymbolicExpression) getCachedSimplification(
				expression);

		if (result == null) {
			result = simplifyExpressionWork(expression);
			if (quantificationDepth == 0)
				cacheSimplification(expression, result);
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
	 * This method does <strong>not</strong> look in the table of cached
	 * simplification results for <code>expression</code>. However, the
	 * recursive calls to the arguments may look in the cache.
	 * </p>
	 * 
	 * <p>
	 * You will probably want to use this method in your implementation of
	 * {@link #simplifyExpressionWork(SymbolicExpression)}.
	 * </p>
	 * 
	 * @param expression
	 *            any non-<code>null</code> symbolic expression
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
		return universe.make(operator, simplifiedType, simplifiedArgs);
	}
}
