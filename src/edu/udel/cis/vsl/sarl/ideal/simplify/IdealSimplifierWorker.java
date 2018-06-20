package edu.udel.cis.vsl.sarl.ideal.simplify;

import static edu.udel.cis.vsl.sarl.IF.SARLConstants.polyProbThreshold;

import java.io.PrintStream;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;

import edu.udel.cis.vsl.sarl.IF.CoreUniverse;
import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.IF.object.NumberObject;
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
import edu.udel.cis.vsl.sarl.expr.IF.BooleanExpressionFactory;
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
import edu.udel.cis.vsl.sarl.type.IF.SymbolicTypeFactory;

/**
 * An ideal simplifier worker is created to simplify one symbolic expression. It
 * disappears once that task has completed. It maintains a reference to a
 * {@link Context} under which the simplification is taking place. It makes no
 * changes to the context, other than to cache the results of simplification in
 * the context's cache.
 * 
 * @author siegel
 */
public class IdealSimplifierWorker {

	public final static boolean debug = false;

	/**
	 * A random number generator with seed very likely to be distinct from all
	 * other seeds.
	 * 
	 * Note from Java API: "Instances of java.util.Random are threadsafe.
	 * However, the concurrent use of the same java.util.Random instance across
	 * threads may encounter contention and consequent poor performance.
	 * Consider instead using ThreadLocalRandom in multithreaded designs."
	 */
	private static Random random = new Random();

	// Instance fields...

	/**
	 * The context which represents the assumptions under which simplification
	 * is taking place. It is a structured representation of a boolean
	 * expression.
	 */
	private Context theContext;

	/**
	 * This is a stack of expressions being simplified, but since an expression
	 * is only allowed to occur at most once on the stack, a set is used. When
	 * simplifying an expression e, first e will be pushed onto the stack. In
	 * the process of simplifying e, other expressions may need to be simplified
	 * and are pushed onto the stack. If at any point an expression is
	 * encountered that is already on the stack, simplification returns
	 * immediately with that expression (no simplification is done). This is to
	 * avoid infinite cycles in the simplification process.
	 * 
	 * @see #simplifyExpressionWork(SymbolicExpression)
	 */
	private Set<SymbolicExpression> simplificationStack;

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
	public IdealSimplifierWorker(Context context,
			Set<SymbolicExpression> seenExpressions) {
		this.theContext = context;
		this.simplificationStack = seenExpressions;
		// this.boundCleaner = boundCleaner;
		// TODO: need a reference to the boundCleaner. Will have to put it in
		// Context too.
	}

	// Private methods ...

	/**
	 * Is this a simple type --- i.e., one that is its own simplification.
	 * 
	 * @param type
	 *            a non-{@code null} type
	 * @return {@code true} iff {@code type} is a simple type
	 */
	private static boolean isSimpleType(SymbolicType type) {
		switch (type.typeKind()) {
		case BOOLEAN:
		case INTEGER:
		case REAL:
		case CHAR:
		case UNINTERPRETED:
			return true;
		default:
		}
		return false;
	}

	/**
	 * Is the object a "simple object", i.e., one which is its own
	 * simplification?
	 * 
	 * @param object
	 * @return if {@code true}, the object is a simple object
	 */
	private static boolean isSimpleObject(SymbolicObject object) {
		switch (object.symbolicObjectKind()) {
		case BOOLEAN:
		case INT:
		case NUMBER:
		case STRING:
		case CHAR:
			return true;
		case EXPRESSION:
			return isSimpleConstant((SymbolicExpression) object);
		case SEQUENCE:
			return false;
		case TYPE:
			return isSimpleType((SymbolicType) object);
		case TYPE_SEQUENCE:
			return false;
		default:
			throw new SARLInternalException("unreachable");
		}
	}

	/**
	 * Gets the {@link SimplifierInfo} object associated to the context.
	 * 
	 * @return the {@link SimplifierInfo} object
	 */
	private SimplifierInfo info() {
		return theContext.getInfo();
	}

	/**
	 * Gets the stream to which debugging output is sent.
	 * 
	 * @return the stream to which debugging output is sent
	 */
	private PrintStream out() {
		return theContext.info.out;
	}

	/**
	 * Gets the factory responsible for creating ideal expressions
	 * 
	 * @return the factory responsible for creating ideal expressions
	 */
	private IdealFactory idealFactory() {
		return theContext.getInfo().idealFactory;
	}

	/**
	 * Gets the number factory used by the context.
	 * 
	 * @return the number factory
	 */
	private NumberFactory numberFactory() {
		return theContext.getInfo().numberFactory;
	}

	/**
	 * Gets the symbolic universe used by the context.
	 * 
	 * @return the symbolic universe
	 */
	private PreUniverse universe() {
		return theContext.getInfo().universe;
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
		theContext.cacheSimplification(object, result);
	}

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
		return theContext.getSimplification(object);
	}

	/**
	 * Simplifies an expression in which the operator is
	 * {@link SymbolicOperator#OR}. In the CNF form, this expression is a clause
	 * of the outer "and" expression.
	 * 
	 * Note: many different techniques have been tried here. They have different
	 * performance-benefit tradeoffs. This method should be considered under
	 * construction
	 * 
	 * @param expr
	 *            a boolean expression with operator {@link SymbolicOperator#OR}
	 * @return a simplified version of the expression
	 */
	private BooleanExpression simplifyOr(BooleanExpression expr) {
		BooleanExpression result = universe().not(
				(BooleanExpression) simplifyExpression(universe().not(expr)));
		// out().println("Or result 1: " + result);

		Context subContext = new SubContext(theContext, simplificationStack);
		ContextExtractor extractor = new ContextExtractor(subContext,
				new HashSet<>());
		boolean success;

		try {
			success = extractor.extractNumericOr(result);
		} catch (InconsistentContextException e) {
			return info().falseExpr;
		}
		if (success)
			result = subContext.getFullAssumption();
		// out().println("Or result 2: " + result);
		return result;

		// if (debug) {
		// out().println(
		// "[" + count + "] Starting OR simplification on: " + expr);
		// out().flush();
		// count++;
		// }
		// order the clauses of the OR expression so that all
		// clauses that occur somewhere else in the subMap keys
		// occur first...

		// BooleanExpression result;
		// int numArgs = expr.numArguments();
		// BooleanExpression[] orderedClauses = new BooleanExpression[numArgs];
		// LinkedList<BooleanExpression> regulars = new LinkedList<>();
		// int n = 0;
		// Set<BooleanExpression> orClauses = theContext.getAllOrClauses();
		//
		// for (int i = 0; i < numArgs; i++) {
		// BooleanExpression clause = (BooleanExpression) expr.argument(i);
		//
		// if (orClauses.contains(clause)) {
		// orderedClauses[n] = clause;
		// n++;
		// } else {
		// regulars.add(clause);
		// }
		// }
		//
		// int numSharedClauses = n;
		//
		// if (numSharedClauses == 0) {
		// result = (BooleanExpression) simplifyExpressionGeneric(expr);
		// } else {
		// Context c = theContext.collapsedClone();
		//
		// result = info().falseExpr;
		// for (BooleanExpression reg : regulars) {
		// orderedClauses[n] = reg;
		// n++;
		// }
		// for (int i = 0; i < numArgs; i++) {
		// BooleanExpression clause = (BooleanExpression) orderedClauses[i];
		//
		// clause = (BooleanExpression) c.simplify(clause);
		// result = universe().or(result, clause);
		// if (i < numArgs - 1) {
		// c.assume(universe().not(clause));
		// c.normalize();
		// if (c.isInconsistent())
		// break;
		// }
		// }
		// }
		//
		// if (debug) {
		// count--;
		// out().println(
		// "[" + count + "] Finished OR simplification on: " + expr);
		// out().println("Result: " + result);
		// out().flush();
		// }
		// return result;
	}

	/**
	 * Performs the work required to simplify a non-simple symbolic type. A
	 * primitive type is returned unchanged. For compound types, simplification
	 * is recursive on the structure of the type. Ultimately a non-trivial
	 * simplification can occur because array types may involve an expression
	 * for the length of the array.
	 * 
	 * @param type
	 *            any non-null non-simple symbolic type
	 * @return simplified version of that type
	 */
	private SymbolicType simplifyTypeWork(SymbolicType type) {
		SymbolicTypeKind kind = type.typeKind();
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
	 * Simplifies a symbolic type, using caching.
	 * 
	 * @param type
	 *            a non-{@code null} symbolic type
	 * @return the simplified version of the type
	 */
	private SymbolicType simplifyType(SymbolicType type) {
		if (isSimpleType(type))
			return type;

		SymbolicType result = (SymbolicType) getCachedSimplification(type);

		if (result == null) {
			result = simplifyTypeWork(type);
			cacheSimplification(type, result);
		}
		return result;
	}

	/**
	 * Performs the work necessary to simplify a type sequence. The
	 * simplification of a type sequence is the sequence resulting from
	 * simplifying each component type individually.
	 * 
	 * @param sequence
	 *            any non-{@code null} type sequence
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
	 * Simplifies a type sequence, using caching.
	 * 
	 * @param seq
	 *            and non-{@code null} type sequence
	 * @return the simplified version of that type sequence
	 */
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
	 * Performs the work necessary to simplify a non-simple symbolic object.
	 * This just redirects to the appropriate specific method, such as
	 * {@link #simplifySequenceWork(SymbolicSequence)},
	 * {@link #simplifyTypeWork(SymbolicType)}, etc.
	 * 
	 * @param object
	 *            a non-null non-simple symbolic object
	 * @return the simplified version of that object
	 */
	private SymbolicObject simplifyObjectWork(SymbolicObject object) {
		switch (object.symbolicObjectKind()) {
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
	private SymbolicObject simplifyObject(SymbolicObject object) {
		if (isSimpleObject(object))
			return object;

		SymbolicObject result = getCachedSimplification(object);

		if (result == null) {
			result = simplifyObjectWork(object);
			cacheSimplification(object, result);
		}
		return result;
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
	private boolean simplifyPowers(Map<Monomial, RationalExpression> powerMap1,
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
				Monomial baseMonomial;

				if (primitive.operator() == SymbolicOperator.POWER) {
					baseMonomial = (Monomial) primitive.argument(0);
					newExp = idf.multiply(realSignedOuterExp,
							(RationalExpression) primitive.argument(1));
					change = change || outerExp.numericalCompareTo(
							nf.abs(idf.getConcreteExponent(newExp))) != 0;
				} else {
					baseMonomial = primitive;
					newExp = realSignedOuterExp;
				}

				NumericExpression oldExponent = powerMap1.get(baseMonomial);

				if (oldExponent == null) {
					powerMap1.put(baseMonomial, newExp);
				} else {
					powerMap1.put(baseMonomial, idf.add(oldExponent, newExp));
					change = true;
				}
			}
		}
		return change;
	}

	/**
	 * <p>
	 * Attempts to decompose a power operation <code>base ^ exp</code> while the
	 * base is a monomial with a non-trivial (not one) constant.
	 * </p>
	 * 
	 * <p>
	 * Precondition and postcondition: {@code powerExpr} is generically
	 * simplified.
	 * </p>
	 * 
	 * <p>
	 * <code>base ^ exp</code> will be decomposed to
	 * <code>monomial_constant ^ exp * monomial_monic ^ expr</code> if both
	 * <code>monomial_constant & monomial_monic</code> are positive.
	 * </p>
	 * 
	 * @param powerExpr
	 *            the {@link SymbolicOperator#POWER} expression that might gets
	 *            decomposed (simplified).
	 * @param idf
	 *            A reference to the {@link IdealFactory}
	 * @return the simplified expression. If no simplification can be further
	 *         applied, the expression in unchanged.
	 */
	private RationalExpression simplifyPowerDecompose(
			RationalExpression powerExpr, IdealFactory idf) {
		NumericExpression base = (NumericExpression) powerExpr.argument(0);
		SymbolicObject exp = powerExpr.argument(1);
		NumericExpression neExp;

		if (exp.symbolicObjectKind() == SymbolicObjectKind.NUMBER) {
			NumberObject nobj = (NumberObject) exp;

			neExp = idf.number(nobj);
		} else
			neExp = (NumericExpression) exp;

		if (!(base instanceof Monomial))
			return powerExpr;

		Monomial monomialBase = (Monomial) base;
		Constant cons = monomialBase.monomialConstant(idf);
		Monic monic = monomialBase.monic(idf);

		if (cons.isOne())
			return powerExpr;

		// if exponent is an integer, both monic and constant are positive
		// this power expression can be decomposed:
		boolean decompose = false;

		if (neExp.type().isInteger())
			decompose = true;
		if (!decompose && intervalApproximation(cons).lower().signum() >= 0
				&& intervalApproximation(monic).lower().signum() >= 0)
			decompose = true;
		if (decompose) {
			RationalExpression result = idf.multiply(
					simplifyPowersRational(idf.power(monic, neExp)),
					idf.power(cons, neExp));

			result = (RationalExpression) simplifyExpressionGeneric(result);
			return result;
		}
		return powerExpr;
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
		Map<Monomial, RationalExpression> powerMap = new HashMap<>();
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
			for (Entry<Monomial, RationalExpression> entry : powerMap
					.entrySet()) {
				result = idf.multiply(result,
						idf.power(entry.getKey(), entry.getValue()));
			}
			result = idf.divide(
					idf.multiply(result, numerator.monomialConstant(idf)),
					denominator.monomialConstant(idf));
			result = (RationalExpression) simplifyExpressionGeneric(result);
			return result;
		}
		return rational;
	}

	/**
	 * Attempts to determine, using probabilistic techniques, if the given
	 * polynomial is constant. If the method determines that the polynomial
	 * probably is constant, it returns the constant, otherwise, it returns
	 * {@code null}.
	 * 
	 * @param poly
	 *            the polynomial
	 * @param totalDegree
	 *            an upper bound on the total degree of the polynomial
	 * @param vars
	 *            the "variables" of the polynomial, these are primitive
	 *            expressions that are not additions, subtractions, or
	 *            multiplications
	 * @param epsilon
	 *            upper bound on the probability of error
	 * @return if this method returns a non-{@code null} {@link Constant}, the
	 *         polynomial is probably equivalent to that constant, with
	 *         probability of error at most {@code epsilon}; if it returns
	 *         {@code null}, the polynomial is definitely not constant
	 */
	private Constant getProbableConstantValue(Polynomial poly,
			IntegerNumber totalDegree, Set<Primitive> vars,
			RationalNumber epsilon) {
		FastEvaluator fe = new FastEvaluator(random, numberFactory(), poly,
				totalDegree);

		if (debug)
			fe.printTreeInformation(out());

		Rat rat = fe.getConstantValue(epsilon);

		return rat == null ? null
				: (Constant) universe().rational(rat.a, rat.b);
	}

	/**
	 * Attempts to simplify a polynomial using probabilistic techniques. For
	 * now, this just attempts to determine if the polynomial is constant.
	 * Experimental and under construction.
	 * 
	 * @param poly
	 *            the polynomial to simplify
	 * @return a possibly simplified version of the given polynomial
	 */
	@SuppressWarnings("unused")
	private RationalExpression simplifyPolyProb(Polynomial poly) {
		RationalNumber prob = universe().getProbabilisticBound();

		if (prob.isZero())
			return poly;

		NumberFactory nf = numberFactory();
		RationalExpression result;
		Set<Primitive> vars = poly.getTruePrimitives();
		IntegerNumber totalDegree = poly.totalDegree(nf);
		int numVars = vars.size();
		IntegerNumber numVarsNumber = nf.integer(numVars);
		IntegerNumber product = nf.multiply(totalDegree, numVarsNumber);

		if (debug) {
			out().println("Poly2: product = " + product + ", threshold = "
					+ polyProbThreshold);
			out().flush();
		}
		if (nf.compare(product, polyProbThreshold) >= 0) {
			if (debug) {
				out().println("Entering probabilistic mode...");
				out().flush();
			}
			result = getProbableConstantValue(poly, totalDegree, vars, prob);
			if (result != null) {
				out().print(
						"Warning: simplified probabilistically with probability of error < ");
				out().println(nf.scientificString(prob, 4));
				out().flush();
				return result;
			}
		}
		return poly;
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
	 * Precondition: {@code poly} is generically simplified
	 * 
	 * Postcondition: result is generically simplified and equivalent under
	 * {@link #theContext} to {@code poly}
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
			result = (RationalExpression) simplifyExpressionGeneric(result);
			return result;
		}

		// try simplifying the terms of this polynomial...

		Monomial[] termMap = poly.termMap(idf);
		int size = termMap.length;
		Monomial[] terms = null;

		assert size >= 2;
		for (int i = 0; i < size; i++) {
			Monomial term = termMap[i];
			Monomial simplifiedTerm = (Monomial) simplifyExpression(term);

			if (term != simplifiedTerm) { // a simplification
				terms = new Monomial[size];
				for (int j = 0; j < i; j++)
					terms[j] = termMap[j];
				terms[i] = simplifiedTerm;
				for (int j = i + 1; j < size; j++)
					terms[j] = (Monomial) simplifyExpression(termMap[j]);
				return (RationalExpression) simplifyExpressionGeneric(
						idf.addMonomials(terms));
			}
		}
		return poly;
	}

	/**
	 * Simplifies a {@link Monic}.
	 * 
	 * Precondition: {@code monic} is generically simplified.
	 * 
	 * Postcondition: result is generically simplified, and is equivalent under
	 * {@link #theContext} to {@code monic}
	 * 
	 * @param monic
	 *            a non-<code>null</code> {@link Monic}
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
		// entries in the sub-map are always generically simplified

		if (result != null)
			return result;
		return monic;
	}

	/**
	 * Simplifies a {@link Monomial}.
	 * 
	 * Pre-condition: {@code monomial} is generically simplified.
	 * 
	 * Post-condition: result is generically simplified, and is equivalent under
	 * {@link #theContext} to {@code monomial}
	 * 
	 * @param monomial
	 *            a {@link Monomial}
	 * @return a simplified version of {@link Monomial}
	 */
	private RationalExpression simplifyMonomial(Monomial monomial) {
		if (monomial instanceof Monic)
			return simplifyMonic((Monic) monomial);
		return monomial;
	}

	/**
	 * <p>
	 * Simplifies a {@link RationalExpression}.
	 * </p>
	 * 
	 * <p>
	 * Pre-condition: expression is generically simplified.
	 * </p>
	 * 
	 * <p>
	 * Post-condition: result is generically simplified.
	 * </p>
	 * 
	 * @param expression
	 *            an instance of {@link RationalExpression} which is already
	 *            generically simplified
	 * 
	 * @return a simplified version
	 */
	private RationalExpression simplifyRationalExpression(
			RationalExpression expression) {
		if (expression instanceof Constant)
			return expression;

		RationalExpression result1;

		if (expression instanceof Monomial)
			result1 = simplifyMonomial((Monomial) expression);
		else
			result1 = expression;
		if (result1.operator() == SymbolicOperator.POWER)
			result1 = simplifyPowerDecompose(result1, idealFactory());
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
		Context subContext = new SubContext(theContext, simplificationStack,
				body);
		BooleanExpression body2 = subContext.getFullAssumption();

		if (body == body2)
			return expr;
		return expr.operator() == SymbolicOperator.FORALL
				? universe().forall(boundVar, body2)
				: universe().exists(boundVar, body2);
	}

	private SymbolicExpression simplifyLambda(SymbolicExpression expr) {
		// lambda x . e;
		SymbolicConstant boundVar = (SymbolicConstant) expr.argument(0);
		SymbolicExpression body = (SymbolicExpression) expr.argument(1);
		Context subContext = new SubContext(theContext, simplificationStack,
				info().trueExpr);
		SymbolicExpression body2 = subContext.simplify(body);

		if (body2 == body)
			return expr;
		return universe().lambda(boundVar, body2);
	}

	/**
	 * Simplifies an array lambda expression.
	 * 
	 * Pre-condition: expr is generically simplified.
	 * 
	 * Post-condition: result is generically simplified.
	 * 
	 * @param expr
	 *            an expression in which the operator is
	 *            {@link SymbolicOperator#ARRAY_LAMBDA}.
	 * @return the simplified expression
	 */
	private SymbolicExpression simplifyArrayLambda(SymbolicExpression expr) {
		assert expr.operator() == SymbolicOperator.ARRAY_LAMBDA;
		SymbolicArrayType arrayType = (SymbolicArrayType) expr.type();
		SymbolicExpression function = (SymbolicExpression) expr.argument(0);
		BooleanExpressionFactory bf = info().booleanFactory;
		IdealFactory idf = idealFactory();
		SymbolicTypeFactory tf = idf.typeFactory();
		PreUniverse uv = universe();

		if (arrayType.isComplete()) {
			SymbolicCompleteArrayType completeType = (SymbolicCompleteArrayType) arrayType;
			SymbolicCompleteArrayType newCompleteType = (SymbolicCompleteArrayType) simplifyType(
					arrayType);
			NumericExpression length = newCompleteType.extent();
			// function : [0,length-1] -> elementType
			// when simplifying function, can assume domain is [0,length-1].
			// create temporary symbolic constant i
			// create sub-context, add assumption 0<=i<length
			// simplify (APPLY function i) in this context, yielding g.
			// result is lambda(i).g.
			// small optimization: if function is a lambda expression, just
			// use the existing bound variable of that lambda expression,
			// no need to create a new one
			if (function.operator() == SymbolicOperator.LAMBDA) {
				NumericSymbolicConstant boundVar = (NumericSymbolicConstant) function
						.argument(0);
				SymbolicExpression body = (SymbolicExpression) function
						.argument(1);
				BooleanExpression boundAssumption = bf.and(
						idf.lessThanEquals(idf.zeroInt(), boundVar),
						idf.lessThan(boundVar, length));
				SubContext subContext = new SubContext(theContext,
						simplificationStack, boundAssumption);
				SymbolicExpression newBody = subContext.simplify(body);

				if (newBody == body && newCompleteType == completeType)
					return expr;

				SymbolicFunctionType functionType = (SymbolicFunctionType) function
						.type();
				SymbolicFunctionType newFunctionType = tf.functionType(
						functionType.inputTypes(), newBody.type());
				SymbolicExpression newFunction = uv.make(
						SymbolicOperator.LAMBDA, newFunctionType,
						new SymbolicObject[] { boundVar, newBody });
				SymbolicExpression result = uv.make(
						SymbolicOperator.ARRAY_LAMBDA, newCompleteType,
						new SymbolicObject[] { newFunction });

				result = simplifyExpressionGeneric(result);
				return result;
			} else {
				// TODO: need a fresh bound variable
			}
		} else {
			// TODO: incomplete array type.
			// Still know i>=0.
		}
		return expr;
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
	private SymbolicExpression simplifyExpressionGeneric(
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
	 * If the expression is of the form that will benefit from creating a
	 * sub-context, this method creates the sub-context and simplifies the
	 * expression there, and returns the result. Otherwise, it returns
	 * {@code null}
	 * 
	 * @param expression
	 *            any non-{@code null} symbolic expression
	 * @return a simplified version of the expressin or {@code null}
	 */
	private SymbolicExpression simplifySpecial(SymbolicExpression expression) {
		if (expression.type().isBoolean()) {
			if (expression.isTrue() || expression.isFalse())
				return expression;
			switch (expression.operator()) {
			case AND:
			case LESS_THAN:
			case LESS_THAN_EQUALS:
			case NEQ:
				return new SubContext(theContext, simplificationStack,
						(BooleanExpression) expression).getFullAssumption();
			case EQUALS:
				if (((SymbolicExpression) expression.argument(0)).isNumeric())
					return new SubContext(theContext, simplificationStack,
							(BooleanExpression) expression).getFullAssumption();
				else
					break;
			case OR:
				return simplifyOr((BooleanExpression) expression);
			default:
				break;
			}
		}
		return null;
	}

	/**
	 * Simplifies a non-simple-constant symbolic expression without caching the
	 * result.
	 * 
	 * Post-condition: the expression returned will be generically simplified.
	 * That means the result returned will be the output from a call to
	 * {@link #simplifyExpressionGeneric(SymbolicExpression)} under the current
	 * context.
	 * 
	 * Post-condition: under the current context, the result returned will be
	 * equivalent to the given expression.
	 * 
	 * Frame condition: assigns nothing. In between entrance and return, the
	 * {@link #simplificationStack} will change, but it should be back to its
	 * original state upon return.
	 * 
	 * @param expression
	 *            any non-<code>null</code> non-simple constant
	 *            {@link SymbolicExpression}
	 * @return an expression guaranteed to be equivalent to the given one under
	 *         the assumption of {@link #theContext}
	 */
	private SymbolicExpression simplifyExpressionWork(
			SymbolicExpression expression) {
		assert expression != null;
		if (simplificationStack.contains(expression))
			return expression;

		SymbolicExpression result;

		result = simplifySpecial(expression);
		if (result != null)
			return result;

		SymbolicExpression originalExpression = expression;
		Set<SymbolicExpression> seen = new HashSet<>();

		simplificationStack.add(originalExpression);
		result = expression = simplifyExpressionGeneric(expression);

		if (debug) {
			out().println(
					"Starting simplification loop on: " + originalExpression);
			out().flush();
		}
		// loop invariant: result == expression is non-null
		// loop invariant: expression is generically simplified
		while (seen.add(expression)) {
			result = theContext.getSub(expression);
			if (result != null)
				// post-condition of getSub: result is generically simplified
				break;
			result = simplifySpecial(expression);
			if (result != null)
				break;
			if (expression.operator() == SymbolicOperator.ARRAY_LAMBDA) {
				// simplifyArrayLambda pre-condition and post-condition:
				// expression is generically simplified
				result = simplifyArrayLambda(expression);
			} else if (expression instanceof RationalExpression) {
				// the following excludes Herbrand expressions, as it should
				result = simplifyRationalExpression(
						(RationalExpression) expression);
			} else {
				result = expression;
			}
			if (result == expression)
				break; // out of loop
			expression = result;
		}
		simplificationStack.remove(originalExpression);
		if (debug) {
			out().println(
					"Finished simplification loop on: " + originalExpression);
			out().println("Result is: " + result);
			out().flush();
		}
		return result;
	}

	// Package-private methods...

	/**
	 * Is the given expression a "simple constant": "NULL", a concrete boolean,
	 * int, number, or string? If so, there is nothing to do --- it is its own
	 * simplification.
	 * 
	 * @param x
	 *            any non-{@code null} symbolic expression
	 * @return {@code true} iff {@code x} is a simple constant
	 */
	static boolean isSimpleConstant(SymbolicExpression x) {
		if (x.isNull())
			return true;

		SymbolicOperator operator = x.operator();

		if (operator == SymbolicOperator.CONCRETE) {
			SymbolicObject object = (SymbolicObject) x.argument(0);
			SymbolicObjectKind kind = object.symbolicObjectKind();

			switch (kind) {
			case BOOLEAN:
			case INT:
			case NUMBER:
			case STRING:
				return true;
			default:
			}
		}
		return false;
	}

	/**
	 * Simplifies an expression that is not a simple constant.
	 * 
	 * @param expression
	 *            a non-{@code null} symbolic expression not a simple constant
	 * @return the simplified version of the given expression
	 */
	SymbolicExpression simplifyNonSimpleConstant(
			SymbolicExpression expression) {
		// It is OK to cache simplification results even if the context
		// is changing because the context clears its cache every time
		// a change is made...
		SymbolicExpression result = (SymbolicExpression) getCachedSimplification(
				expression);

		if (result == null) {
			result = simplifyExpressionWork(expression);
			cacheSimplification(expression, result);
		}
		return result;
	}

	// public methods ...

	/**
	 * Simplifies a symbolic expression, caching the result in the underlying
	 * {@link Context}.
	 * 
	 * @param expression
	 *            any non-<code>null</code> {@link SymbolicExpression}
	 * @return an expression guaranteed to be equivalent to the given one under
	 *         the assumption of {@link #theContext}
	 */
	public SymbolicExpression simplifyExpression(
			SymbolicExpression expression) {
		if (isSimpleConstant(expression))
			return expression;
		return simplifyNonSimpleConstant(expression);
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
	public Interval intervalApproximation(NumericExpression expr) {
		Range range = theContext.computeRange((RationalExpression) expr);
		Interval result = range.intervalOverApproximation();

		return result;
	}
}
