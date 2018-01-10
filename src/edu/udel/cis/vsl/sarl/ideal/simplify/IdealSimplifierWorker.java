package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import edu.udel.cis.vsl.sarl.IF.CoreUniverse;
import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject.SymbolicObjectKind;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicSequence;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType.SymbolicTypeKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTypeSequence;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;
import edu.udel.cis.vsl.sarl.ideal.IF.Constant;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Polynomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal.IF.PrimitivePower;
import edu.udel.cis.vsl.sarl.ideal.IF.RationalExpression;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.simplify.IF.Range;

/**
 * An ideal simplifier worker is created by an {@link OldIdealSimplifier} to
 * simplify one symbolic expression. It disappears once that task has completed.
 * The {@link OldIdealSimplifier} is persistent and will usually continue to
 * live through the lifetime of the JVM.
 * 
 * @author siegel
 */
public class IdealSimplifierWorker {

	// Instance fields...

	/**
	 * The context which represents the assumptions under which simplification
	 * is taking place. It is a structured representation of a boolean
	 * expression.
	 */
	private Context theContext;

	// Constructors ...

	/**
	 * Creates new simplifier worker from given info object and context
	 * (assumption). Does not do anything.
	 * 
	 * @param info
	 *            the info object to use
	 * @param context
	 *            the assumption under which simplification is taking place
	 */
	public IdealSimplifierWorker(Context context) {
		this.theContext = context;
	}

	// Private methods ...

	private SimplifierInfo info() {
		return theContext.getInfo();
	}

	private IdealFactory idealFactory() {
		return theContext.getInfo().idealFactory;
	}

	private NumberFactory numberFactory() {
		return theContext.getInfo().numberFactory;
	}

	private PreUniverse universe() {
		return theContext.getInfo().universe;
	}

	/**
	 * Build up entries in power map from the monic factors of a {@link Monic}.
	 * This method modifies two given {@link Map}s. The first map encodes a set
	 * of power expressions in which the base is a {@link Primitive} (in
	 * particular, is not concrete) and the second map encodes a set of power
	 * expressions in which the base is a concrete number. The final values of
	 * the maps is essentially the original value multiplied by the factors of
	 * the {@link Monic} (if <code>positive</code> is <code>true</code>)) or
	 * divided by the factors of the {@link Monic} (if <code>positive</code> is
	 * <code>false</code>). Simplifications are performed under the assumptions
	 * of {@link #theContext}).
	 * 
	 * @param powerMap1
	 *            map from the primitives to the exponent assigned to that
	 *            primitive; this is an input/output variable
	 * @param powerMap2
	 *            like <code>powerMap1</code>, but for expressions in which the
	 *            base is {@link Constant}; this is an input/output variable
	 * @param positive
	 *            if true, exponents should be added to the entries in the
	 *            powerMaps, otherwise they should be subtracted from entries;
	 *            an input
	 * @param monic
	 *            the {@link Monic} expression that is being simplified and
	 *            decomposed into a product of powers; this is an input
	 * 
	 * @return true iff change occurred
	 */
	private boolean simplifyPowers(Map<Primitive, RationalExpression> powerMap1,
			Map<Constant, RationalExpression> powerMap2, boolean positive,
			Monic monic) {
		IdealFactory idf = idealFactory();
		PrimitivePower[] factors = monic.monicFactors(idf);
		boolean isInteger = monic.type().isInteger();
		boolean change = false;
		NumberFactory nf = numberFactory();

		for (PrimitivePower pp : factors) {
			Primitive primitive = pp.primitive(idf);
			IntegerNumber outerExp = (IntegerNumber) pp
					.primitivePowerExponent(idf).getNumber();
			IntegerNumber signedOuterExp = positive ? outerExp
					: nf.negate(outerExp);
			RationalExpression realSignedOuterExp = idf.constant(isInteger
					? signedOuterExp : nf.integerToRational(signedOuterExp));
			RationalExpression newExp;
			SymbolicObject baseObj = primitive.argument(0);
			Primitive base;

			if (baseObj instanceof Constant) {
				Constant baseConst;

				if (primitive.operator() == SymbolicOperator.POWER) {
					baseConst = (Constant) primitive.argument(0);
					newExp = idf.multiply(realSignedOuterExp,
							(RationalExpression) primitive.argument(1));
					change = change || outerExp.numericalCompareTo(
							nf.abs(idf.getConcreteExponent(newExp))) != 0;

					NumericExpression oldExponent = powerMap2.get(baseConst);

					if (oldExponent == null) {
						powerMap2.put(baseConst, newExp);
						powerMap1.remove(primitive);
					} else {
						powerMap2.put(baseConst, idf.add(oldExponent, newExp));
						change = true;
					}
				}
			} else {
				if (primitive.operator() == SymbolicOperator.POWER) {
					base = (Primitive) primitive.argument(0);
					newExp = idf.multiply(realSignedOuterExp,
							(RationalExpression) primitive.argument(1));
					change = change || outerExp.numericalCompareTo(
							nf.abs(idf.getConcreteExponent(newExp))) != 0;
				} else {
					base = primitive;
					newExp = realSignedOuterExp;
				}

				NumericExpression oldExponent = powerMap1.get(base);

				if (oldExponent == null) {
					powerMap1.put(base, newExp);
				} else {
					powerMap1.put(base, idf.add(oldExponent, newExp));
					change = true;
				}
			}
		}
		return change;
	}

	/**
	 * Simplifies any {@link SymbolicOperator#POWER} operations occurring in a
	 * rational expression.
	 * 
	 * @param rational
	 *            a rational expression
	 * @return equivalent rational expression in which power operations that can
	 *         be combined are combined or simplified
	 */
	private RationalExpression simplifyPowersRational(
			RationalExpression rational) {
		IdealFactory idf = idealFactory();
		Monomial numerator = rational.numerator(idf),
				denominator = rational.denominator(idf);
		Monic m1 = numerator.monic(idf), m2 = denominator.monic(idf);
		Map<Primitive, RationalExpression> powerMap = new HashMap<>();
		Map<Constant, RationalExpression> powerMap2 = new HashMap<>();
		boolean change1 = simplifyPowers(powerMap, powerMap2, true, m1);
		boolean change2 = simplifyPowers(powerMap, powerMap2, false, m2);

		if (change1 || change2) {
			RationalExpression result = idf.one(rational.type());

			for (Entry<Constant, RationalExpression> entry : powerMap2
					.entrySet()) {
				result = idf.multiply(result,
						idf.power(entry.getKey(), entry.getValue()));
			}
			for (Entry<Primitive, RationalExpression> entry : powerMap
					.entrySet()) {
				result = idf.multiply(result,
						idf.power(entry.getKey(), entry.getValue()));
			}
			result = idf.divide(
					idf.multiply(result, numerator.monomialConstant(idf)),
					denominator.monomialConstant(idf));
			return result;
		}
		return rational;
	}

	/**
	 * <p>
	 * Simplifies a {@link Polynomial}. Note that method
	 * {@link #simplifyGenericExpression(SymbolicExpression)} cannot be used,
	 * since that method will invoke
	 * {@link CoreUniverse#make(SymbolicOperator, SymbolicType, SymbolicObject[])}
	 * , which will apply binary addition repeatedly on the terms of a
	 * {@link Polynomial}, which will not result in the correct form.
	 * </p>
	 * 
	 * <p>
	 * The following strategies are used:
	 * <ul>
	 * <li>look up the polynomial in the {@link #constantMap()}</li>
	 * <li>convert to an {@link AffineExpression} and look for a constant value
	 * of the pseudo</li>
	 * <li>simplify the individual terms and sum the results</li>
	 * <li>full expand the polynomial</li>
	 * </ul>
	 * The process is repeated until it stabilizes or a constant value is
	 * determined.
	 * </p>
	 * 
	 * @param poly
	 *            a {@link Polynomial} with at least 2 terms
	 * @return a simplified version of <code>poly</code> equivalent to
	 *         <code>poly</code> under the existing assumptions
	 */
	private RationalExpression simplifyPolynomial(Polynomial poly) {
		IdealFactory idf = idealFactory();
		Constant constantTerm = poly.constantTerm(idf);

		if (!constantTerm.isZero()) {
			RationalExpression result = idf.subtract(poly, constantTerm);

			result = simplifyRationalExpression(result);
			result = idf.add(result, constantTerm);
			return result;
		}

		Monomial[] termMap = poly.termMap(idf);
		int size = termMap.length;

		// TODO: why allocate this array if you may never use it...

		Monomial[] terms = new Monomial[size];
		boolean simplified = false;

		assert size >= 2;
		for (int i = 0; i < size; i++) {
			Monomial term = termMap[i];
			Monomial simplifiedTerm = (Monomial) simplifyExpression(term);

			simplified = simplified || term != simplifiedTerm;
			terms[i] = simplifiedTerm;
		}

		Monomial result = simplified ? idf.addMonomials(terms) : poly;

		return result;
	}

	/**
	 * Simplifies a {@link Monic}.
	 * 
	 * @param monic
	 *            a non-<code>null</code> {@link Monic} which is not an instance
	 *            of {@link Polynomial}.
	 * 
	 * @return a simplified version of <code>monic</code> which is equivalent to
	 *         <code>monic</code> under the current assumptions
	 */
	private RationalExpression simplifyMonic(Monic monic) {
		if (monic instanceof Polynomial) {
			return simplifyPolynomial((Polynomial) monic);
		}

		RationalExpression result = (RationalExpression) theContext
				.getSub(monic);

		if (result != null)
			return result;

		return (Monomial) simplifyExpressionGeneric(monic);
	}

	private RationalExpression simplifyMonomial(Monomial monomial) {
		if (monomial instanceof Monic)
			return simplifyMonic((Monic) monomial);
		return (RationalExpression) simplifyExpressionGeneric(monomial);
	}

	private RationalExpression simplifyRationalExpression(
			RationalExpression expression) {
		if (expression instanceof Constant)
			return expression;

		RationalExpression result1;

		if (expression instanceof Monomial)
			result1 = simplifyMonomial((Monomial) expression);
		else
			result1 = (RationalExpression) simplifyExpressionGeneric(
					expression);
		if (result1 instanceof Primitive || result1 instanceof Constant)
			return result1;

		RationalExpression result2 = simplifyPowersRational(result1);

		if (result1 == result2)
			return result1;
		return (RationalExpression) simplifyExpression(result2);
	}

	private BooleanExpression simplifyQuantifiedBooleanExpression(
			BooleanExpression expr) {
		SymbolicConstant boundVar = (SymbolicConstant) expr.argument(0);
		BooleanExpression body = (BooleanExpression) expr.argument(1);
		Context subContext = new SubContext(theContext, body);
		BooleanExpression body2 = subContext.getFullAssumption();

		if (body == body2)
			return expr;
		return expr.operator() == SymbolicOperator.FORALL
				? universe().forall(boundVar, body2)
				: universe().exists(boundVar, body2);
	}

	/**
	 * Simplifies a boolean expression.
	 * 
	 * Implementation notes: for relational expression, a {@link SubContext} is
	 * formed and then the full assumption is taken from that sub-context.
	 * Similarly for boolean operators (and, or, not). For other expressions,
	 * generic simplification is used.
	 * 
	 * @param expression
	 *            a non-<code>null</code> boolean expression
	 * @return a simplified version of the expression, under the assumption of
	 *         {@link #theContext}.
	 */
	private BooleanExpression simplifyBoolean(BooleanExpression expression) {
		if (expression.isTrue() || expression.isFalse())
			return expression;
		switch (expression.operator()) {
		case AND:
		case EQUALS:
		case LESS_THAN:
		case LESS_THAN_EQUALS:
		case NEQ:
		case NOT:
		case OR:
			// TODO: no, I just want to skip if theContext is being
			// formed around expression
			return new SubContext((Context) theContext, expression)
					.getFullAssumption();
		// case EXISTS:
		// case FORALL:
		// return simplifyQuantifiedBooleanExpression(expression);
		// case APPLY:
		// case ARRAY_READ:
		// case CAST:
		// case CONCRETE:
		// case COND:
		// case DIFFERENTIABLE:
		// case SYMBOLIC_CONSTANT:
		// case TUPLE_READ:
		// case UNION_EXTRACT:
		// case UNION_TEST:
		default:
		}
		return (BooleanExpression) simplifyExpressionGeneric(expression);
	}

	private SymbolicExpression simplifyLambda(SymbolicExpression expr) {
		// lambda x . e;
		SymbolicConstant boundVar = (SymbolicConstant) expr.argument(0);
		SymbolicExpression body = (SymbolicExpression) expr.argument(1);
		Context subContext = new SubContext(theContext, info().trueExpr);
		SymbolicExpression body2 = subContext.simplify(body);

		if (body2 == body)
			return expr;
		return universe().lambda(boundVar, body2);
	}

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
	private SymbolicType simplifyTypeWork(SymbolicType type) {
		SymbolicTypeKind kind = type.typeKind();

		switch (kind) {
		case BOOLEAN:
		case INTEGER:
		case REAL:
		case CHAR:
			return type;
		default:
		}

		PreUniverse universe = universe();

		switch (kind) {
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
	private SymbolicTypeSequence simplifyTypeSequenceWork(
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

				return universe().typeSequence(Arrays.asList(newTypes));
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
	private SymbolicSequence<?> simplifySequenceWork(
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
				result = universe().objectFactory().sequence(newElements);
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
	private SymbolicObject simplifyObjectWork(SymbolicObject object) {
		switch (object.symbolicObjectKind()) {
		case BOOLEAN:
		case INT:
		case NUMBER:
		case STRING:
		case CHAR:
			return object;
		case EXPRESSION:
			return simplifyExpressionWork((SymbolicExpression) object, false);
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
	private SymbolicObject simplifyObject(SymbolicObject object) {
		SymbolicObject result = getCachedSimplification(object);

		if (result == null) {
			result = simplifyObjectWork(object);
			cacheSimplification(object, result);
		}
		return result;
	}

	private SymbolicType simplifyType(SymbolicType type) {
		SymbolicType result = (SymbolicType) getCachedSimplification(type);

		if (result == null) {
			result = simplifyTypeWork(type);
			cacheSimplification(type, result);
		}
		return result;
	}

	private SymbolicTypeSequence simplifyTypeSequence(
			SymbolicTypeSequence seq) {
		SymbolicTypeSequence result = (SymbolicTypeSequence) getCachedSimplification(
				seq);

		if (result == null) {
			result = simplifyTypeSequenceWork(seq);
			cacheSimplification(seq, result);
		}
		return result;
	}

	// Package-private methods...

	/**
	 * Retrieves a cached simplification result. Simplification results are
	 * cached using method
	 * {@link #cacheSimplification(SymbolicObject, SymbolicObject)}, which in
	 * turns uses {@link #theContext}'s simplification cache to cache results.
	 * Note that every time {@link #theContext} changes, its cache is cleared.
	 * 
	 * @param object
	 *            the object to be simplified
	 * @return the result of a previous simplification applied to {@code object}
	 *         , or <code>null</code> if no such result is cached
	 */
	private SymbolicObject getCachedSimplification(SymbolicObject object) {
		// if (theContext.isInconsistent())
		return theContext.getSimplification(object);
		// else
		// return null;
	}

	/**
	 * Caches the given simplification result within {@link #theContext}.
	 * 
	 * @param object
	 *            any non-<code>null</code> {@link SymbolicObject}
	 * @param result
	 *            the result returned of simplifying that object
	 */
	private void cacheSimplification(SymbolicObject object,
			SymbolicObject result) {
		// if (theContext.isInitialized())
		theContext.cacheSimplification(object, result);
	}

	// Package-private methods...

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
	SymbolicExpression simplifyExpressionGeneric(
			SymbolicExpression expression) {
		if (expression.isNull())
			return expression;

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
		} else if (operator == SymbolicOperator.FORALL
				|| operator == SymbolicOperator.EXISTS) {
			return simplifyQuantifiedBooleanExpression(
					(BooleanExpression) expression);
		} else if (operator == SymbolicOperator.LAMBDA) {
			return simplifyLambda(expression);
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
		if (simplifiedArgs == null)
			return expression;
		return universe().make(operator, simplifiedType, simplifiedArgs);
	}

	/**
	 * Computes an interval over-approximation to the possible values that can
	 * be taken by the given numeric expression under the assumption of the
	 * context.
	 * 
	 * @param expr
	 *            a numeric expression (or integer or real type)
	 * @return an {@link Interval} of the same type as <code>expr</code> with
	 *         the property that the set of concrete values that can result from
	 *         evaluating <code>expr</code> at any point satisfying the
	 *         assumption of {@link #theContext} is contained within that
	 *         interval
	 */
	Interval intervalApproximation(NumericExpression expr) {
		Range range = theContext.computeRange((RationalExpression) expr);
		Interval result = range.intervalOverApproximation();

		return result;
	}

	/**
	 * Simplifies a symbolic expression without caching the result.
	 * 
	 * @param expression
	 *            any non-<code>null</code> {@link SymbolicExpression}
	 * @return an expression guaranteed to be equivalent to the given one under
	 *         the assumption of {@link #theContext}
	 */
	SymbolicExpression simplifyExpressionWork(SymbolicExpression expression,
			boolean noMoreSubcontexts) {
		SymbolicType type = expression.type();

		if (type == null)
			return expression;
		// Note: the following excludes Herbrand expressions, as it should:
		if (expression instanceof RationalExpression)
			return simplifyRationalExpression((RationalExpression) expression);

		SymbolicExpression result = theContext.getSub(expression);

		if (result != null)
			return result;
		if (type.isBoolean() && !noMoreSubcontexts)
			return simplifyBoolean((BooleanExpression) expression);
		return simplifyExpressionGeneric(expression);
	}

	/**
	 * Simplifies a symbolic expression, caching the result in the underlying
	 * {@link Context}.
	 * 
	 * @param expression
	 *            any non-<code>null</code> {@link SymbolicExpression}
	 * @return an expression guaranteed to be equivalent to the given one under
	 *         the assumption of {@link #theContext}
	 */
	SymbolicExpression simplifyExpression(SymbolicExpression expression) {
		// It is OK to cache simplification results even if the context
		// is changing because the context clears its cache every time
		// a change is made...
		SymbolicExpression result = (SymbolicExpression) getCachedSimplification(
				expression);

		if (result == null) {
			result = simplifyExpressionWork(expression, false);
			cacheSimplification(expression, result);
		}
		return result;
	}
}
