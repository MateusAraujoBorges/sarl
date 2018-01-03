package edu.udel.cis.vsl.sarl.prove.why3;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.SARLInternalException;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.IF.object.BooleanObject;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.NumberObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicSequence;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicMapType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType.SymbolicTypeKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTypeSequence;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.prove.why3.Why3Primitives.Axiom;
import edu.udel.cis.vsl.sarl.prove.why3.Why3Primitives.Why3FunctionType;
import edu.udel.cis.vsl.sarl.prove.why3.Why3Primitives.Why3InfixOperator;
import edu.udel.cis.vsl.sarl.prove.why3.Why3Primitives.Why3Lib;
import edu.udel.cis.vsl.sarl.prove.why3.Why3Primitives.Why3TupleType;
import edu.udel.cis.vsl.sarl.prove.why3.Why3Primitives.Why3Type;

/**
 * <p>
 * Translates SARL {@link SymbolicExpression}s to the
 * <a href="http://why3.lri.fr/doc-0.88.0/syntax.html">why3 (logic) language</a>
 * of the verification platform Why3 (
 * <a href="http://why3.lri.fr">why3-website</a>).
 * </p>
 * 
 * <p>
 * The translated result sent to Why3 is a 'theory': <code>
 * theory QUERY_#
 *   (* libraries *)
 *   use import int.Int 
 *   ...
 *   (* declarations *)
 *   constant x : int
 *   ...
 *   (* context *)
 *   predicate context = ...
 *   (* many goals *)
 *   goal G0 : context -> goal0
 *   goal G1 : context -> goal1
 *   ...
 * end
 * </code>
 * </p>
 * 
 * @author ziqingluo
 *
 */
public class Why3Translator {
	// TODO: namespace conflicts ?
	/* ***************** Uninterpreted functions ********************/
	/**
	 * Uninterpreted function for undefined union extracts.
	 * 
	 * <p>
	 * The SARL Union type is translated into a why3 tuple with a fixed 0-th
	 * integer field which indicates which field is significant. A union field
	 * access on a non-significant field results in a undefined behavior which
	 * is represented by this uninterpreted function: <code>
	 * _union_extract(tuple, field) </code>
	 * </p>
	 */
	static private String union_extract_undefined_function_name = "_union_undefined_extract";

	/* ***************** Constants ********************/
	/**
	 * Translates SARL NULL to this following string. Such a string is NOT
	 * suppose to be in the translated text.
	 */
	static private String NULL = "NULL";

	/**
	 * The flag field index of a union type object. The field should indicates
	 * which field of the union type object is significant.
	 */
	static private int union_flag_field = 0;

	/**
	 * prefix for field name of tuple types
	 */
	static private String tuple_field_prefix = "_t";

	/**
	 * Pre-defined formal parameter names for sigma
	 */
	private NumericSymbolicConstant sigma_low = null;

	static private String sigma_low_name = "_l";

	private NumericSymbolicConstant sigma_high = null;

	static private String sigma_high_name = "_h";

	/* ********************* private fields ************************ */
	/**
	 * translated context in Why3 logic language
	 */
	private Map<String, Axiom> contexts;

	/**
	 * the name of the context axiom
	 */
	private static String context_name = "context";

	/**
	 * the name of the theory that encodes the queries
	 */
	private static String executable_theory_name = "Why3Query_";

	/**
	 * All stateful informations including cache, counter for renaming, stack
	 * for recursively translating quantified expressions
	 */
	private Why3TranslationState state;

	private PreUniverse universe;

	public Why3Translator(PreUniverse universe, SymbolicExpression theContext) {
		initialize(universe);

		String ctx = translate(theContext);

		this.contexts.put(context_name,
				Why3Primitives.newAxiom(context_name, stringPostProcess(ctx)));
	}

	public Why3Translator(PreUniverse universe) {
		initialize(universe);
		this.contexts.put(context_name,
				Why3Primitives.newAxiom(context_name, "true"));
		state.addLibrary(Why3Lib.BOOL); // add Bool lib for literal true.
	}

	/**
	 * Initializing all fields
	 * 
	 * @param universe
	 */
	private void initialize(PreUniverse universe) {
		// this.universe = universe;
		this.state = new Why3TranslationState();
		this.universe = universe;
		this.contexts = new TreeMap<>();
	}

	/* *********************** Public Interfaces ************************** */

	/**
	 * Translates a {@link SymbolicExpression} to a Why3 goal.
	 * 
	 * @param theGoal
	 *            The expression that will be translated to a goal
	 * @return The translated goal. e.g.
	 *         <code>goal G0 : the-translated-goal</code>
	 */
	public String translateGoal(SymbolicExpression theGoal) {
		String goalText = translate(theGoal);
		String result;
		String goalIdent = state.newGoalIdentifier();

		goalText = this.stringPostProcess(goalText);
		result = Why3Primitives.keyword_goal + " " + goalIdent + ": context"
				+ Why3Primitives.implies.text + goalText + "\n";
		return result;
	}

	public String getExecutableOutput(int id, String... goals) {
		String queryName = executable_theory_name + id;
		String output = Why3Primitives.REAL_NAME_SPACE;

		output += Why3Primitives.keyword_theory + " " + queryName + "\n";
		output += importTranslation();
		output += declarations();
		output += context();
		for (int i = 0; i < goals.length; i++)
			output += goals[i] + "\n";
		output += Why3Primitives.keyword_end + "\n";
		return output;
	}

	/**
	 * @return translated why3 constant declarations
	 */
	public String declarations() {
		String result = "";

		for (String decl : state.getDeclaration())
			result += decl + "\n";
		result = stringPostProcess(result);
		return result;
	}

	/**
	 * @return The translated "context"
	 */
	public String context() {
		String result = null;
		String context = Why3Primitives.keyword_predicate + " context = ";
		boolean first = true;

		for (Axiom ax : contexts.values()) {
			if (first) {
				result = ax.text;
				context += ax.name;
				first = false;
				continue;
			}
			result += ax.text;
			context += " && " + ax.name;
		}
		return result + context + "\n";
	}

	/* *********************** Private methods ************************** */

	private String translate(SymbolicExpression theExpression) {
		String result = state.getCachedExpressionTranslation(theExpression);

		if (result == null) {
			result = translateWorker(theExpression);
			state.cacheExpressionTranslation(theExpression, result);
		}
		return result;
	}

	/**
	 * @return translated "import" statements for used libraries
	 */
	private String importTranslation() {
		String result = "";

		for (Why3Lib lib : state.getLibraries())
			result += Why3Primitives.importText(lib);
		return result;
	}
	/* ************** Translation Methods *************** */

	// TODO: this can be parallelized
	private String[] translateArgumentList(
			Iterable<? extends SymbolicObject> argExprs, int numArgs) {
		String results[] = new String[numArgs];
		int counter = 0;

		for (SymbolicObject argExpr : argExprs)
			results[counter++] = translate((SymbolicExpression) argExpr);
		return results;
	}

	/**
	 * Same as {@link #translateArgumentList(Iterable, int)} but less efficient
	 * due to the missing of the number of arguments.
	 */
	private String[] translateArgumentList(
			Iterable<? extends SymbolicObject> argExprs) {
		ArrayList<String> tmpResults = new ArrayList<>();
		String[] results = new String[tmpResults.size()];

		for (SymbolicObject argExpr : argExprs)
			tmpResults.add(translate((SymbolicExpression) argExpr));
		results = tmpResults.toArray(results);
		return results;
	}

	// TODO: this can be parallelized
	/**
	 * Interpolates an infix-operator <code>op</code> to a list of operands
	 * <code>opr0, opr1, opr2,... </code>. The result would be like this:
	 * <code>opr0 op opr1 op opr2 op ... </code>. If the length of the operands
	 * less than or equal to one, no-op.
	 * 
	 * @param operands
	 *            A list of operands
	 * @param operator
	 *            The operator
	 * @return A single term that represents a sequence of operations.
	 */
	private String interpolateOperator(String[] operands,
			Why3InfixOperator infixOp) {
		StringBuffer result = new StringBuffer();
		int numPositions = (operands.length * 2 - 1);

		for (int i = 0; i < numPositions; i++)
			if (i % 2 == 0)
				result.append(operands[i / 2]);
			else
				result.append(" " + infixOp.text + " ");
		return result.toString();
	}

	/**
	 * Wraps a term with a pair of parenthesis.
	 */
	private String wrap(String term) {
		return "(" + term + ")";
	}

	protected String translateWorker(SymbolicExpression theExpression) {
		SymbolicOperator op = theExpression.operator();

		switch (op) {
		case ADD:
			return translateAdd(theExpression);
		case AND:
			return translateAnd(theExpression);
		case ARRAY:
			return translateArray(theExpression);
		case ARRAY_READ:
			return translateArrayRead(theExpression);
		case ARRAY_WRITE:
			return translateArrayWrite(theExpression);
		case ARRAY_LAMBDA:
			return translateArrayLambda(theExpression);
		case APPLY:
			return translateApply(theExpression);
		case CAST:
			return translateCast(theExpression);
		case CONCRETE:
			return translateConcrete(theExpression);
		case COND:
			return translateCond(theExpression);
		case DENSE_ARRAY_WRITE:
			return translateDenseArrayWrite(theExpression);
		case DENSE_TUPLE_WRITE:
			return translateDenseTupleWrite(theExpression);
		case DIVIDE:
			return translateRealDivision(theExpression);
		case EQUALS:
			return translateNumEquals(theExpression);
		case EXISTS:
			return translateExists(theExpression);
		case FORALL:
			return translateForall(theExpression);
		case INT_DIVIDE:
			return translateIntDivision(theExpression);
		case LENGTH:
			return translateArrayLength(theExpression);
		case LESS_THAN:
			return translateLessThan(theExpression);
		case LESS_THAN_EQUALS:
			return translateLessThanEquals(theExpression);
		case MODULO:
			return translateIntModulo(theExpression);
		case MULTIPLY:
			return translateMultiply(theExpression);
		case NEGATIVE:
			return translateNegative(theExpression);
		case NEQ:
			return translateNotEqual(theExpression);
		case NOT:
			return translateNot(theExpression);
		case NULL:
			return NULL;
		case OR:
			return translateOr(theExpression);
		case SUBTRACT:
			return translateSubtract(theExpression);
		case SYMBOLIC_CONSTANT:
			return translateSymbolicConstants((SymbolicConstant) theExpression);
		case TUPLE:
			return translateTuple(theExpression);
		case TUPLE_READ:
			return translateTupleRead(theExpression);
		case TUPLE_WRITE:
			return translateTupleWrite(theExpression);
		// Translation of union:
		// 1. An union type is a tuple. The first field is an int type whose
		// value indicates which member field is significant.
		// 2. An union extract on the significant field is like a tuple-read
		// A union extract on the non-significant field is undefined behavior
		// 3. An union inject sets the significant field
		// 4. An union test returns true if the specified field is the
		// significant field.
		case UNION_EXTRACT:
			return translateUnionExtract(theExpression);
		case UNION_INJECT:
			return translateUnionInject(theExpression);
		case UNION_TEST:
			return translateUnionTest(theExpression);
		case POWER:
			return translatePower(theExpression);
		case LAMBDA:
			return translateLambda(theExpression);
		// have not beenS supported operators
		case BIT_AND:
		case BIT_NOT:
		case BIT_OR:
		case BIT_SHIFT_LEFT:
		case BIT_SHIFT_RIGHT:
		case BIT_XOR:
		case DERIV:
		case DIFFERENTIABLE:
		default:
			throw new SARLException("So far the translation of " + op
					+ " to why3 has not been implemented.");
		}
	}

	private String translateAnd(SymbolicExpression expr) {
		String[] arguments = translateArgumentList(expr.getArguments(),
				expr.numArguments());
		// add parenthesis:
		return wrap(interpolateOperator(arguments, Why3Primitives.land));
	}

	private String translateAdd(SymbolicExpression expr) {
		String[] arguments = translateArgumentList(expr.getArguments(),
				expr.numArguments());

		if (expr.type().isInteger())
			return wrap(interpolateOperator(arguments, Why3Primitives.plus));
		else {
			return Why3Primitives.recursiveCalling(arguments,
					Why3Primitives.real_plus);
		}
	}

	private String translateArray(SymbolicExpression concreteArray) {
		Why3Type type = translateType(concreteArray.type());
		String arrayIdentifier = createIdentifier(type);
		String[] elements = translateArgumentList(concreteArray.getArguments(),
				concreteArray.numArguments());
		String result = arrayIdentifier;

		for (int i = 0; i < elements.length; i++)
			result = Why3Primitives.mapSet.call(result, "" + i, elements[i]);
		return result;
	}

	private String translateArrayRead(SymbolicExpression arrayRead) {
		String[] array_index = translateArgumentList(arrayRead.getArguments(),
				arrayRead.numArguments());

		return Why3Primitives.mapGet.call(array_index[0], array_index[1]);
	}

	private String translateArrayWrite(SymbolicExpression arrayWrite) {
		String[] array_index_value = translateArgumentList(
				arrayWrite.getArguments(), arrayWrite.numArguments());

		return Why3Primitives.mapSet.call(array_index_value[0],
				array_index_value[1], array_index_value[2]);
	}

	/**
	 * A function declaration and a function call
	 * 
	 * @return
	 */
	private String translateApply(SymbolicExpression expr) {
		SymbolicExpression func = (SymbolicExpression) expr.argument(0);

		// Special handling for sum:
		if (universe.isSigmaExpression(expr))
			return translateSigma(expr);

		SymbolicFunctionType symbolicFuncType = (SymbolicFunctionType) func
				.type();
		@SuppressWarnings("unchecked")
		String[] args = translateArgumentList(
				(Iterable<? extends SymbolicObject>) expr.argument(1),
				symbolicFuncType.inputTypes().numTypes());
		String funcText = translate(func);

		return Why3Primitives.why3FunctionCall(funcText, args);
	}

	/**
	 * cast in why3 : <code>expr : type</code>
	 */
	private String translateCast(SymbolicExpression expr) {
		String value = translate((SymbolicExpression) expr.argument(0));
		Why3Type castedType = translateType(expr.type());

		return wrap(Why3Primitives.why3cast(value, castedType));
	}

	/**
	 * translates to literal why3 terms
	 */
	private String translateConcrete(SymbolicExpression expr) {
		return literal(expr, expr.type());
	}

	/**
	 * conditional expression in why3 :
	 * <code>if cond then term else term </code>
	 */
	private String translateCond(SymbolicExpression expr) {
		String cond_true_false[] = translateArgumentList(expr.getArguments(),
				expr.numArguments());

		return Why3Primitives.why3IfThenElse(cond_true_false[0],
				cond_true_false[1],
				cond_true_false.length == 3 ? cond_true_false[2] : null);
	}

	/**
	 * translates A sequence of ARRAY_WRITES
	 */
	private String translateDenseArrayWrite(SymbolicExpression expr) {
		String array = translate((SymbolicExpression) expr.argument(0));
		@SuppressWarnings("unchecked")
		String[] elements = translateArgumentList(
				(Iterable<? extends SymbolicObject>) expr.argument(1));

		for (int i = 0; i < elements.length; i++)
			if (elements[i] != NULL)
				array = Why3Primitives.mapSet.call(array, "" + i, elements[i]);

		return array;
	}

	/**
	 * division for real numbers in why3 is <code>numerator / denominator</code>
	 */
	private String translateRealDivision(SymbolicExpression expr) {
		String[] numer_denomi = translateArgumentList(expr.getArguments(),
				expr.numArguments());

		return wrap(
				interpolateOperator(numer_denomi, Why3Primitives.real_divide));
	}

	/**
	 * equal for numbers in why3 is <code>left = right</code>
	 */
	private String translateNumEquals(SymbolicExpression expr) {
		String[] args = translateArgumentList(expr.getArguments(),
				expr.numArguments());

		return wrap(interpolateOperator(args, Why3Primitives.num_equals));
	}

	/**
	 * EXISTS in why3 is <code>exists ident-list : type /\ predicate</code>
	 */
	protected String translateExists(SymbolicExpression expr) {
		SymbolicConstant var = (SymbolicConstant) expr.argument(0);
		Why3Type type = translateType(var.type());
		String boundIdentifier = symbolicConstant2Name(var);

		state.pushQuantifiedContext(boundIdentifier);

		String predicate = translate((SymbolicExpression) expr.argument(1));
		String result;

		state.popQuantifiedContext();
		result = Why3Primitives.why3BoundVarDecl(boundIdentifier, type);
		result = Why3Primitives.why3Exists(result, predicate.toString());
		return wrap(result);
	}

	/**
	 * Forall in why3 is <code>forall ident-list : type -> predicate</code>
	 */
	protected String translateForall(SymbolicExpression expr) {
		SymbolicConstant var = (SymbolicConstant) expr.argument(0);
		Why3Type type = translateType(var.type());
		String boundIdentifier = symbolicConstant2Name(var);

		state.pushQuantifiedContext(boundIdentifier);

		String predicate = translate((SymbolicExpression) expr.argument(1));
		String result;

		state.popQuantifiedContext();
		result = Why3Primitives.why3BoundVarDecl(boundIdentifier, type);
		result = Why3Primitives.why3Forall(result, predicate.toString());
		return wrap(result);
	}

	/**
	 * LAMBDA in Why3 is just a function with body
	 */
	private String translateLambda(SymbolicExpression expr) {
		SymbolicConstant var = (SymbolicConstant) expr.argument(0);
		SymbolicExpression body = (SymbolicExpression) expr.argument(1);
		Why3Type type[] = { translateType(var.type()) };
		String boundIdentifier = symbolicConstant2Name(var);
		String funcDecl;

		// TODO: maybe the symbolic constant should be pushed as well ?
		state.pushQuantifiedContext(boundIdentifier);

		String bodyText = translate(body);
		String result;

		state.popQuantifiedContext();

		// create function for lambda:
		Why3Type bodyType = translateType(body.type());
		Why3FunctionType funcType = Why3Primitives.why3FunctionType(bodyType,
				type);

		result = state.getLambdaFunctionName(expr);
		funcDecl = Why3Primitives.why3FunctionDecl(
				state.getLambdaFunctionName(expr), funcType, bodyText,
				boundIdentifier);
		state.addDeclaration(result, funcDecl);
		return result;
	}

	/**
	 * The idea of translating ARRAY_LAMBDA is creating an array constant
	 * <code>a</code> and adds an axiom stating that each element of a equals to
	 * each element of the ARRAY_LAMBDA. Some other details can be found at
	 * {@link Why3TranslationState#pushArrayLambdaContext(String)}
	 * 
	 * @param expr
	 * @return
	 */
	private String translateArrayLambda(SymbolicExpression expr) {
		SymbolicArrayType arrayType = (SymbolicArrayType) expr.type();
		Why3Type why3ArrayType = translateType(arrayType);
		String why3arrayIdent = createIdentifier(why3ArrayType);
		int dims = arrayType.dimensions();

		// create a number of dims bound variables for the universal axiom...
		NumericSymbolicConstant boundVars[] = new NumericSymbolicConstant[dims];
		SymbolicExpression lambdaElement = expr;
		String why3boundVarIdents[] = new String[dims];
		String why3arrayElement = why3arrayIdent;

		for (int i = 0; i < dims; i++) {
			boundVars[i] = (NumericSymbolicConstant) universe.symbolicConstant(
					universe.stringObject(state.newIdentifierName()),
					universe.integerType());
			why3boundVarIdents[i] = symbolicConstant2Name(boundVars[i]);
			state.pushQuantifiedContext(why3boundVarIdents[i]);
			why3arrayElement = Why3Primitives.mapGet.call(why3arrayElement,
					why3boundVarIdents[i]);
			lambdaElement = universe.arrayRead(lambdaElement, boundVars[i]);
		}

		// axiom : for all why3arrayElement equals to lambdaElement ...
		String why3LambdaElement = translate(lambdaElement);
		String eqOperands[] = { why3LambdaElement, why3arrayElement };
		String result;

		if (!lambdaElement.type().isNumeric())
			// TODO: equal for other types than numerical ...
			// TODO: check for other equals
			throw new SARLException(
					"Translation of ARRAY_LAMBDA whose leaf-elements have no"
							+ " numerical types has not implemented yet ...");
		result = interpolateOperator(eqOperands, Why3Primitives.num_equals);
		// Axiom : forall ... result
		result = translateArrayLambdaWorker_addRestriction(arrayType,
				why3boundVarIdents, result);
		for (int i = dims - 1; i >= 0; i--)
			result = Why3Primitives.why3Forall(Why3Primitives.why3BoundVarDecl(
					why3boundVarIdents[i], Why3Primitives.int_t), result);

		Axiom axiom = Why3Primitives.newAxiom(state.getLambdaFunctionName(expr),
				result);

		contexts.put(axiom.name, axiom);
		for (int i = 0; i < dims; i++)
			state.popQuantifiedContext();
		return why3arrayIdent;
	}

	/**
	 * Add restrictions for bound variables which represents array indices. The
	 * restriction state that each bound variable is in the range from 0 to the
	 * array extent minus one.
	 * 
	 * @param arrayType
	 * @param why3boundVarIdents
	 * @param predicate
	 * @return
	 */
	private String translateArrayLambdaWorker_addRestriction(
			SymbolicArrayType arrayType, String why3boundVarIdents[],
			String predicate) {
		int dims = arrayType.dimensions();
		String restriction = null;

		for (int i = 0; i < dims; i++) {
			if (arrayType.isComplete()) {
				NumericExpression extent = ((SymbolicCompleteArrayType) arrayType)
						.extent();
				String[] lteOperands = new String[3];

				lteOperands[0] = "0";
				lteOperands[1] = why3boundVarIdents[i];
				lteOperands[2] = translate(
						universe.subtract(extent, universe.oneInt()));
				if (restriction == null)
					restriction = interpolateOperator(lteOperands,
							Why3Primitives.lte);
				else {
					String[] landOperands = new String[2];

					landOperands[0] = restriction;
					landOperands[1] = interpolateOperator(lteOperands,
							Why3Primitives.lte);
					restriction = interpolateOperator(landOperands,
							Why3Primitives.land);
				}
			}
		}
		if (restriction != null) {
			String[] operands = { restriction, predicate };

			predicate = wrap(
					interpolateOperator(operands, Why3Primitives.implies));
		}
		return predicate;
	}

	/**
	 * INT_DIV in why3 is <code>(div numer denomi)</code>
	 */
	private String translateIntDivision(SymbolicExpression expr) {
		String[] args = translateArgumentList(expr.getArguments(),
				expr.numArguments());
		String result = Why3Primitives.int_divide.call(args[0], args[1]);

		state.addLibrary(Why3Lib.INT_DIV_MOD);
		return result;
	}

	/**
	 * MODULO in why3 is <code>(mod numer denomi)</code>
	 */
	private String translateIntModulo(SymbolicExpression expr) {
		String args[] = translateArgumentList(expr.getArguments(),
				expr.numArguments());
		String result = Why3Primitives.int_mod.call(args[0], args[1]);

		state.addLibrary(Why3Lib.INT_DIV_MOD);
		return result;
	}

	/**
	 * get length from array type.
	 */
	private String translateArrayLength(SymbolicExpression expr) {
		SymbolicType arrayType = ((SymbolicExpression) expr.argument(0)).type();

		if (arrayType instanceof SymbolicCompleteArrayType) {
			SymbolicExpression length = ((SymbolicCompleteArrayType) arrayType)
					.extent();

			return translate(length);
		}
		throw new SARLInternalException(
				"Attempt to get length from an expression which does not have a complete array type");
	}

	/**
	 * translate LESS_THAN to why3
	 */
	private String translateLessThan(SymbolicExpression expr) {
		String[] args = translateArgumentList(expr.getArguments(),
				expr.numArguments());
		SymbolicType arg0Type = ((SymbolicExpression) expr.argument(0)).type();

		// test argument type
		if (arg0Type.isInteger())
			return wrap(interpolateOperator(args, Why3Primitives.lt));
		else
			return wrap(Why3Primitives.recursiveCalling(args,
					Why3Primitives.real_lt));
	}

	/**
	 * translate LESS_THAN_EQUALS to why3
	 */
	private String translateLessThanEquals(SymbolicExpression expr) {
		String[] args = translateArgumentList(expr.getArguments(),
				expr.numArguments());
		SymbolicType arg0Type = ((SymbolicExpression) expr.argument(0)).type();

		// test argument type
		if (arg0Type.isInteger())
			return wrap(interpolateOperator(args, Why3Primitives.lte));
		else
			return wrap(Why3Primitives.recursiveCalling(args,
					Why3Primitives.real_lte));
	}

	/**
	 * translate Multiplication to why3
	 */
	private String translateMultiply(SymbolicExpression expr) {
		String[] args = translateArgumentList(expr.getArguments(),
				expr.numArguments());

		if (expr.type().isInteger())
			return wrap(interpolateOperator(args, Why3Primitives.times));
		else
			return Why3Primitives.recursiveCalling(args,
					Why3Primitives.real_times);
	}

	/**
	 * translate negative to why3
	 */
	private String translateNegative(SymbolicExpression expr) {
		String arg = translate((SymbolicExpression) expr.argument(0));

		if (expr.type().isInteger())
			return wrap(Why3Primitives.negative.call(arg));
		else
			return Why3Primitives.real_negative.call(arg);
	}

	/**
	 * translate NOT to why3
	 */
	private String translateNot(SymbolicExpression expr) {
		String arg = translate((SymbolicExpression) expr.argument(0));
		String result = Why3Primitives.not.call(wrap(arg));

		return result;
	}

	/**
	 * translate NOT_EQUAL to why3
	 */
	private String translateNotEqual(SymbolicExpression expr) {
		String[] args = translateArgumentList(expr.getArguments(),
				expr.numArguments());

		return Why3Primitives.not.call(
				wrap(interpolateOperator(args, Why3Primitives.num_equals)));
	}

	/**
	 * translate SUBTRACT to why3
	 */
	private String translateSubtract(SymbolicExpression expr) {
		String[] args = translateArgumentList(expr.getArguments(),
				expr.numArguments());

		if (expr.type().isInteger())
			return wrap(interpolateOperator(args, Why3Primitives.subtract));
		else
			return Why3Primitives.recursiveCalling(args,
					Why3Primitives.real_subtract);
	}

	/**
	 * translate logical OR to why3
	 */
	private String translateOr(SymbolicExpression expr) {
		String[] args = translateArgumentList(expr.getArguments(),
				expr.numArguments());

		return wrap(interpolateOperator(args, Why3Primitives.lor));
	}

	protected String translateSymbolicConstants(SymbolicConstant var) {
		String name = symbolicConstant2Name(var);

		if (state.inQuantifiedContext(name))
			return name;

		Why3Type type = translateType(var.type());
		String declaration;

		if (!type.isFunctionType())
			declaration = Why3Primitives.constantDecl(name, type);
		else {
			declaration = Why3Primitives.why3UninterpretedFunctionDecl(name,
					(Why3FunctionType) type);
		}

		state.addDeclaration(name, declaration);
		return name;
	}

	/**
	 * Tuple is a first-class type in Why3 {_t0 : type, _t1 : type, ...}
	 */
	private String translateTuple(SymbolicExpression expr) {
		Why3Type type = translateType(expr.type());
		String identifier = createIdentifier(type);
		String fieldValueTexts[] = translateArgumentList(expr.getArguments(),
				expr.numArguments());
		String fieldNameTexts[] = new String[fieldValueTexts.length];

		for (int i = 0; i < fieldNameTexts.length; i++)
			fieldNameTexts[i] = nthFieldName(i);
		return Why3Primitives.why3TupleDenseUpdate(identifier, fieldNameTexts,
				fieldValueTexts, fieldNameTexts.length);
	}

	private String translateDenseTupleWrite(SymbolicExpression expr) {
		@SuppressWarnings("unchecked")
		String[] fieldValueTexts = translateArgumentList(
				(Iterable<? extends SymbolicObject>) expr.argument(1));
		String tuple = translate((SymbolicExpression) expr.argument(0));
		String nonEmptyFieldValueTexts[] = new String[fieldValueTexts.length];
		String fieldNameTexts[] = new String[fieldValueTexts.length];
		int counter = 0;

		for (int i = 0; i < fieldNameTexts.length; i++) {
			if (fieldValueTexts[i] != NULL) {
				fieldNameTexts[counter] = nthFieldName(counter);
				nonEmptyFieldValueTexts[counter++] = fieldValueTexts[i];
			}
		}
		return Why3Primitives.why3TupleDenseUpdate(tuple, fieldNameTexts,
				nonEmptyFieldValueTexts, counter);
	}

	/**
	 * Tuple read in why3 <code>tuple.field</code>
	 */
	private String translateTupleRead(SymbolicExpression expr) {
		String tuple = translate((SymbolicExpression) expr.argument(0));
		int fieldIdx = ((IntObject) expr.argument(1)).getInt();
		String[] tupleTexts = new String[2];

		tupleTexts[0] = tuple;
		tupleTexts[1] = nthFieldName(fieldIdx);
		return interpolateOperator(tupleTexts, Why3Primitives.tuple_read);
	}

	/**
	 * Tuple write in why3 <code>{tuple with field = newValue}</code>
	 */
	private String translateTupleWrite(SymbolicExpression expr) {
		String tuple = translate((SymbolicExpression) expr.argument(0));
		int fieldIdx = ((IntObject) expr.argument(1)).getInt();
		String newValue = translate((SymbolicExpression) expr.argument(2));

		return Why3Primitives.why3TupleUpdate(tuple, nthFieldName(fieldIdx),
				newValue);
	}

	/**
	 * Same as tuple but if the reading field is not significant, the behavior
	 * is undefined.
	 */
	private String translateUnionExtract(SymbolicExpression expr) {
		// The real field idx should increase by one to skip the flag field
		int fieldIdx = ((IntObject) expr.argument(0)).getInt() + 1;
		SymbolicExpression unionVal = (SymbolicExpression) expr.argument(1);
		String union = translate(unionVal);
		String flag, cond;
		String[] unionTexts = { union, nthFieldName(union_flag_field) };

		// read the first field
		flag = interpolateOperator(unionTexts, Why3Primitives.tuple_read);
		// compare with the value in the first field:
		unionTexts[0] = flag;
		unionTexts[1] = "" + fieldIdx;
		cond = interpolateOperator(unionTexts, Why3Primitives.num_equals);
		unionTexts[0] = union;
		unionTexts[1] = nthFieldName(fieldIdx);

		Why3TupleType unionType = (Why3TupleType) translateType(
				unionVal.type());
		String alias = state.getTupleTypeAlias(unionType);

		addUnionExtractUninterpretedFunctionDeclaration(alias, unionType,
				fieldIdx);
		return Why3Primitives.why3IfThenElse(cond,
				interpolateOperator(unionTexts, Why3Primitives.tuple_read),
				Why3Primitives.why3FunctionCall(
						union_extract_undefined_function_name, union,
						"" + fieldIdx));
	}

	/**
	 * Set both the field and the flag field.
	 */
	private String translateUnionInject(SymbolicExpression expr) {
		// The real field idx should increase by one to skip the flag field
		int fieldIdx = ((IntObject) expr.argument(0)).getInt() + 1;
		SymbolicExpression newValue = (SymbolicExpression) expr.argument(1);
		String value = translate(newValue);
		Why3Type unionType = translateType(newValue.type());
		String unionTmpVar = state.newIdentifierName();

		state.addDeclaration(unionTmpVar,
				Why3Primitives.constantDecl(unionTmpVar, unionType));
		// write the flag field first:
		unionTmpVar = Why3Primitives.why3TupleUpdate(unionTmpVar,
				nthFieldName(0), "" + fieldIdx);
		// the write the real field:
		return Why3Primitives.why3TupleUpdate(unionTmpVar,
				nthFieldName(fieldIdx), value);
	}

	private String translateUnionTest(SymbolicExpression expr) {
		SymbolicExpression union = (SymbolicExpression) expr.argument(1);
		int fieldIdx = ((IntObject) expr.argument(0)).getInt();
		String[] unionText = { translate(union),
				nthFieldName(union_flag_field) };

		unionText[0] = interpolateOperator(unionText,
				Why3Primitives.tuple_read);
		unionText[1] = fieldIdx + "";
		return wrap(interpolateOperator(unionText, Why3Primitives.num_equals));
	}

	private String translatePower(SymbolicExpression expr) {
		SymbolicExpression base = (SymbolicExpression) expr.argument(0);
		Why3Type baseType = translateType(base.type());

		if (baseType == Why3Primitives.int_t)
			state.addLibrary(Why3Primitives.Why3Lib.POWER_INT);
		else if (baseType == Why3Primitives.real_t)
			state.addLibrary(Why3Primitives.Why3Lib.POWER_REAL);
		else
			throw new SARLException(
					"Cannot translate a power expression whose base has neither INT nor REAL type.");

		SymbolicObject exp = expr.argument(1);
		String expText;
		String baseText = this.translate(base);

		if (exp instanceof SymbolicExpression)
			expText = translate((SymbolicExpression) exp);
		else {
			NumberObject concExp = (NumberObject) exp;
			if (concExp.isReal())
				expText = concExp.toString();
			else {
				int concVal = ((IntegerNumber) concExp.getNumber()).intValue();
				String[] bases = new String[concVal];

				for (int i = 0; i < concVal; i++)
					bases[i] = baseText;
				return wrap(interpolateOperator(bases, Why3Primitives.times));
			}
		}
		return Why3Primitives.power.call(baseText, expText);
	}

	/**
	 * SIGMA : <code>\sigma(l, h, \lambda t : integer; f(t))</code>
	 * 
	 * <p>
	 * Translation: <code>
	 * function sigma0 (low high : int) (all-bound-vars-in-f : T) : T'
	 * 
	 * predicate _AX_sigma0 =  
	 * forall low high : int, all-bound-vars-in-f : T. 
	 * if (low >= high) then (sigma0 low high ...) = 0
	 * else (sigma0 low high ...) = (sigma0 low+1 high ...) + f(low)
	 * 
	 * </code>
	 * </p>
	 * 
	 */
	private String translateSigma(SymbolicExpression expr) {
		@SuppressWarnings("unchecked")
		SymbolicSequence<SymbolicExpression> sigmaArguments = (SymbolicSequence<SymbolicExpression>) expr
				.argument(1);
		// find out all additional inputs (bound vars)
		SymbolicExpression lambda = (SymbolicExpression) sigmaArguments.get(2);
		SymbolicConstant[] extraInputs = findBoundVarsInFunctionBody(state,
				(SymbolicExpression) lambda.argument(1));

		// creating a sum function that associates to the lambda expression
		String sigmaName = state.getSigmaName(lambda);
		String formals[] = new String[extraInputs.length + 2];
		Why3Type formalTypes[] = new Why3Type[formals.length];

		if (sigma_low == null)
			sigma_low = (NumericSymbolicConstant) universe.symbolicConstant(
					universe.stringObject(sigma_low_name),
					universe.integerType());
		if (sigma_high == null)
			sigma_high = (NumericSymbolicConstant) universe.symbolicConstant(
					universe.stringObject(sigma_high_name),
					universe.integerType());
		// formal parameters: low high and extras
		formals[0] = symbolicConstant2Name(sigma_low);
		formals[1] = symbolicConstant2Name(sigma_high);
		formalTypes[0] = Why3Primitives.int_t;
		formalTypes[1] = Why3Primitives.int_t;
		for (int i = 0; i < extraInputs.length; i++) {
			formalTypes[i + 2] = translateType(extraInputs[i].type());
			formals[i + 2] = symbolicConstant2Name(extraInputs[i]);
		}

		String sigmaFuncDecl = Why3Primitives.why3UninterpretedFunctionDecl(
				sigmaName, Why3Primitives.why3FunctionType(
						translateType(expr.type()), formalTypes));

		state.addDeclaration(sigmaName, sigmaFuncDecl);

		String baseLowCase = translate(
				universe.apply(lambda, Arrays.asList(sigma_low)));
		String baseHighCase = translate(universe.apply(lambda, Arrays
				.asList(universe.subtract(sigma_high, universe.oneInt()))));
		Axiom sigmaAxiom = Why3Primitives.sigmaAxiom(sigmaName, formals,
				formalTypes, baseLowCase, baseHighCase);

		contexts.put(sigmaAxiom.name, sigmaAxiom);

		NumericExpression actualHigh,
				actualLow = (NumericExpression) sigmaArguments.get(0);

		// actuall parameters, SARL sigma is higher-inclusive while translation
		// is not:
		actualHigh = universe.add((NumericExpression) sigmaArguments.get(1),
				universe.oneInt());
		formals[0] = translate(actualLow);
		formals[1] = translate(actualHigh);
		return Why3Primitives.why3FunctionCall(sigmaName, formals);
	}

	private SymbolicConstant[] findBoundVarsInFunctionBody(
			Why3TranslationState state, SymbolicExpression body) {
		Set<SymbolicConstant> allVars = universe.getFreeSymbolicConstants(body);
		List<SymbolicConstant> results = new LinkedList<>();

		for (SymbolicConstant var : allVars) {
			if (state.inQuantifiedContext(symbolicConstant2Name(var)))
				results.add(var);
		}

		SymbolicConstant ret[] = new SymbolicConstant[results.size()];

		ret = results.toArray(ret);
		return ret;
	}

	/* ****************** type translation ********************* */
	protected Why3Type translateType(SymbolicType type) {
		Why3Type result = state.getCachedType(type);

		if (result == null) {
			result = translateTypeWorker(type);
			state.cacheType(type, result);
		}
		return result;
	}

	private Why3Type translateTypeWorker(SymbolicType type) {
		SymbolicTypeKind kind = type.typeKind();

		switch (kind) {
		case ARRAY:
			SymbolicArrayType arrayType = (SymbolicArrayType) type;
			SymbolicType elementType = arrayType.elementType();
			Why3Type why3ElementType = translateType(elementType);

			state.addLibrary(Why3Lib.MAP);
			return Why3Primitives.why3ArrayType(why3ElementType);
		case BOOLEAN:
			state.addLibrary(Why3Lib.BOOL);
			return Why3Primitives.bool_t;
		case CHAR:
		case INTEGER:
			state.addLibrary(Why3Lib.INT);
			return Why3Primitives.int_t;
		case MAP:
			SymbolicMapType mapType = (SymbolicMapType) type;

			state.addLibrary(Why3Lib.MAP);
			return Why3Primitives.why3MapType(translateType(mapType.keyType()),
					translateType(mapType.valueType()));
		case REAL:
			state.addLibrary(Why3Lib.REAL);
			return Why3Primitives.real_t;
		case TUPLE:
			Why3TupleType tupleType = makeWhy3TupleType(
					((SymbolicTupleType) type).sequence());
			String alias = state.getTupleTypeAlias(tupleType);

			state.addTypeAliasDeclaration(alias,
					Why3Primitives.why3TypeAlias(alias, tupleType));
			return new Why3Primitives.Why3Type(alias);
		case UNION:
			tupleType = makeWhy3TupleType(
					((SymbolicUnionType) type).sequence());
			alias = state.getTupleTypeAlias(tupleType);
			state.addTypeAliasDeclaration(alias,
					Why3Primitives.why3TypeAlias(alias, tupleType));
			return new Why3Primitives.Why3Type(alias);
		case FUNCTION:
			SymbolicFunctionType funcType = (SymbolicFunctionType) type;
			Why3Type retType = translateType(funcType.outputType());
			Why3Type formals[] = new Why3Type[funcType.inputTypes().numTypes()];
			int idx = 0;

			for (SymbolicType formal : funcType.inputTypes())
				formals[idx++] = translateType(formal);
			return Why3Primitives.why3FunctionType(retType, formals);
		case SET:
		default:
			throw new SARLException("translating " + kind
					+ " type has not been supported yet.");
		}
	}

	/**
	 * Create a {@link Why3TupleType}
	 * 
	 * @param typeSequence
	 *            The list of types of fields
	 * @return the {@link Why3TupleType}
	 */
	private Why3TupleType makeWhy3TupleType(SymbolicTypeSequence typeSequence) {
		int fieldCounter = 0;
		int size = typeSequence.numTypes();
		Why3Type types[] = new Why3Type[size];
		String fieldNames[] = new String[size];

		for (SymbolicType fieldType : typeSequence) {
			types[fieldCounter] = translateType(fieldType);
			fieldNames[fieldCounter] = this.nthFieldName(fieldCounter++);
		}
		return Why3Primitives.why3TupleType(null, fieldNames, types);
	}

	/* ****************** other helper methods ****************** */
	private String literal(SymbolicExpression concExpr, SymbolicType type) {
		SymbolicTypeKind kind = type.typeKind();
		SymbolicObject object = concExpr.argument(0);
		String result;

		switch (kind) {
		case BOOLEAN:
			state.addLibrary(Why3Lib.BOOL);
			result = ((BooleanObject) object).getBoolean() ? "true" : "false";
			break;
		case CHAR:
			state.addLibrary(Why3Lib.INT);
			result = String.valueOf(
					Character.getNumericValue((object.toString().charAt(0))));
			break;
		case INTEGER:
			state.addLibrary(Why3Lib.INT);
			result = object.toString();
			break;
		case REAL: {
			RationalNumber number = (RationalNumber) ((NumberObject) object)
					.getNumber();
			String numerator, denominator;
			boolean negative = number.signum() < 0;

			// get absolute value first
			if (negative)
				number = (RationalNumber) universe.numberFactory().abs(number);
			numerator = number.numerator().toString() + ".0";
			denominator = number.denominator().toString() + ".0";
			if (denominator.equals("1.0"))
				result = numerator;
			else {
				result = numerator + Why3Primitives.real_divide.text
						+ denominator;
				result = wrap(result);
			}
			// avoid "-" (minus) conflict against integer "-":S
			if (negative)
				result = Why3Primitives.real_negative.call(result);
			break;
		}
		default:
			throw new SARLInternalException(
					"Unknown concrete object: " + concExpr);
		}
		return result.toString();

	}

	private String createIdentifier(Why3Type type) {
		String newName;
		String decl;

		newName = state.newIdentifierName();
		decl = Why3Primitives.constantDecl(newName, type);
		state.addDeclaration(newName, decl);
		return newName;
	}

	private String nthFieldName(int fieldIdx) {
		return tuple_field_prefix + fieldIdx;
	}

	private void addUnionExtractUninterpretedFunctionDeclaration(
			String unionTypeAlias, Why3Type unionType, int fieldIdx) {
		String declName = union_extract_undefined_function_name + unionTypeAlias
				+ fieldIdx;
		Why3Type formals[] = { unionType, Why3Primitives.int_t };
		String decl = Why3Primitives.why3UninterpretedFunctionDecl(declName,
				Why3Primitives.why3FunctionType(
						unionType.nthArgumentType(fieldIdx), formals));

		state.addDeclaration(declName, decl);
	}

	/**
	 * Perform simple processing when the translation has done.
	 * 
	 * @param string
	 *            The input {@link String}
	 * @return the processed {@link String}
	 */
	private String stringPostProcess(String string) {
		return string.replace('$', '_');
	}

	private String symbolicConstant2Name(SymbolicConstant var) {
		return "_" + var.name().getString();
	}
}
