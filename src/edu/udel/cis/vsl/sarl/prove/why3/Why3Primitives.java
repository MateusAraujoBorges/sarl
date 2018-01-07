package edu.udel.cis.vsl.sarl.prove.why3;

import java.util.Arrays;

import edu.udel.cis.vsl.sarl.IF.SARLException;

/**
 * This class provides a set of Why3 primitives, including types and operations,
 * to help the translation.
 * 
 * @author ziqingluo
 */
public class Why3Primitives {

	/**
	 * Libraries in Why3.
	 * 
	 * @author ziqingluo
	 */
	public static enum Why3Lib {
		INT, REAL, BOOL, MAP, INT_DIV_MOD, POWER_INT, POWER_REAL
	}

	/* ************* Classes of Why3 operators and types ************* */

	/**
	 * A class represents an infix operator in Why3
	 * 
	 * @author ziqingluo
	 */
	static class Why3InfixOperator {
		String text;

		Why3InfixOperator(String text) {
			this.text = text;
		}
	}

	/**
	 * A class represents pre-defined functions in Why3
	 * 
	 * @author ziqingluo
	 */
	static class Why3BuiltinFunction {
		private String name;
		final int numArgs;

		Why3BuiltinFunction(String name, int numArgs) {
			this.name = name;
			this.numArgs = numArgs;
			// number of arguments must greater than 0
			assert numArgs > 0;
		}

		String call(String... expressions) {
			assert expressions.length == numArgs;
			String result = "(" + name;

			for (int i = 0; i < numArgs; i++)
				result += " " + expressions[i];
			result += ")";
			return result;
		}
	}

	/**
	 * A class represents all types in Why3.
	 * 
	 * @author ziqingluo
	 */
	static class Why3Type {
		/**
		 * Name of this type. (null if the type doesn't have a name).
		 */
		private String name;

		/**
		 * Argument types
		 */
		private Why3Type typeArgs[];

		/**
		 * The translated text.
		 */
		protected String text;

		private Why3Type(String typeName, boolean wrap, Why3Type... typeArgs) {
			this.name = typeName;
			this.typeArgs = typeArgs;
			text = name;
			for (int i = 0; i < typeArgs.length; i++)
				text += " " + typeArgs[i].text;
			if (wrap)
				text = "(" + text + ")";
		}

		Why3Type(String typeName) {
			assert typeName != null;
			this.text = typeName;
		}

		Why3Type nthArgumentType(int idx) {
			return typeArgs[idx];
		}

		@Override
		public int hashCode() {
			return (int) (text.hashCode() * 3.1415926)
					^ Arrays.hashCode(typeArgs);
		}

		/**
		 * @return True iff this is a function type.
		 */
		public boolean isFunctionType() {
			return false;
		}

		/**
		 * @return True iff this is a tuple type.
		 */
		public boolean isTupleType() {
			return false;
		}
	}

	/**
	 * This class represents a tuple type in Why3. Tuple type has no name.
	 * 
	 * @author ziqingluo
	 */
	static class Why3TupleType extends Why3Type {
		private Why3TupleType(String typeName, boolean wrap,
				String fieldNames[], Why3Type[] typeArgs) {
			super(typeName, wrap, typeArgs);
			this.text = "{";
			for (int i = 0; i < fieldNames.length; i++)
				this.text += fieldNames[i] + " : " + typeArgs[i].text + ";";
			this.text += "}";
		}

		@Override
		public boolean isTupleType() {
			return true;
		}
	}

	/**
	 * This class represents a function type in Why3. Function type has no name.
	 * 
	 * @author ziqingluo
	 */
	static class Why3FunctionType extends Why3Type {
		/**
		 * Return type of the function.
		 */
		private Why3Type returnType;

		private Why3FunctionType(Why3Type returnType, Why3Type[] formal) {
			super("", false, formal);
			this.returnType = returnType;
			this.text = "";
			for (int i = 0; i < formal.length; i++)
				this.text += "(" + formal[i].text + ")";
			this.text += " : " + returnType.text;
		}

		@Override
		public boolean isFunctionType() {
			return true;
		}
	}

	/* ****** Pre-defined static infix operators ****** */

	public static Why3InfixOperator plus = new Why3InfixOperator(" + ");

	public static Why3InfixOperator subtract = new Why3InfixOperator(" - ");

	public static Why3InfixOperator times = new Why3InfixOperator(" * ");

	public static Why3InfixOperator real_divide = new Why3InfixOperator(" :- ");

	public static Why3InfixOperator land = new Why3InfixOperator(" && ");

	public static Why3InfixOperator lor = new Why3InfixOperator(" || ");

	public static Why3InfixOperator lt = new Why3InfixOperator(" < ");

	public static Why3InfixOperator lte = new Why3InfixOperator(" <= ");

	public static Why3InfixOperator num_equals = new Why3InfixOperator(" = ");

	public static Why3InfixOperator tuple_read = new Why3InfixOperator(".");

	public static Why3InfixOperator implies = new Why3InfixOperator(" -> ");

	/* ****** Pre-defined static functions ****** */

	public static Why3BuiltinFunction mapGet = new Why3BuiltinFunction("get",
			2);

	public static Why3BuiltinFunction mapSet = new Why3BuiltinFunction("set",
			3);

	public static Why3BuiltinFunction int_divide = new Why3BuiltinFunction(
			"div", 2);

	public static Why3BuiltinFunction int_mod = new Why3BuiltinFunction("mod",
			2);

	public static Why3BuiltinFunction negative = new Why3BuiltinFunction("-",
			1);

	public static Why3BuiltinFunction not = new Why3BuiltinFunction("not", 1);

	public static Why3BuiltinFunction int_power = new Why3BuiltinFunction(
			"power", 2);

	public static Why3BuiltinFunction real_power = new Why3BuiltinFunction(
			"SR.sarl_power", 2);

	public static Why3BuiltinFunction real_plus = new Why3BuiltinFunction(
			"SR.add", 2);

	public static Why3BuiltinFunction real_subtract = new Why3BuiltinFunction(
			"SR.sub", 2);

	public static Why3BuiltinFunction real_times = new Why3BuiltinFunction(
			"SR.mul", 2);

	public static Why3BuiltinFunction real_lt = new Why3BuiltinFunction("SR.lt",
			2);

	public static Why3BuiltinFunction real_lte = new Why3BuiltinFunction(
			"SR.lte", 2);

	public static Why3BuiltinFunction real_negative = new Why3BuiltinFunction(
			"SR.neg", 1);

	/* ****** Pre-defined static why3 types ****** */

	public static Why3Type int_t = new Why3Type("int");

	public static Why3Type real_t = new Why3Type("real");

	public static Why3Type bool_t = new Why3Type("bool");

	/**
	 * array type in why3 logic is a integer-indexed map type
	 */
	public static Why3Type array_int_t = new Why3Type("map", true, int_t,
			int_t);

	/**
	 * array type in why3 logic is a integer-indexed map type
	 */
	public static Why3Type array_real = new Why3Type("map", true, int_t,
			real_t);

	/* *********** Why3 keywords *********** */

	public static String keyword_constant = "constant";

	public static String keyword_exists = "exists";

	public static String keyword_forall = "forall";

	public static String keyword_function = "function";

	public static String keyword_predicate = "predicate";

	public static String keyword_type = "type";

	public static String keyword_goal = "goal";

	public static String keyword_theory = "theory";

	public static String keyword_end = "end";

	/* ********* Why3 specific helper methods ********** */
	/**
	 * @return A why3 constant declaration.
	 */
	public static String constantDecl(String ident, Why3Type type) {
		return keyword_constant + " " + ident + " : " + type.text + "\n";
	}

	/**
	 * @return A why3 cast operation.
	 */
	public static String why3cast(String expr, Why3Type type) {
		return expr + " : " + type;
	}

	/**
	 * @return A why3 if-then-else operation. The "falseTerm" can be null.
	 */
	public static String why3IfThenElse(String cond, String trueTerm,
			String falseTerm) {
		return falseTerm == null ? "(if " + cond + " then " + trueTerm + ")"
				: "(if " + cond + " then " + trueTerm + " else " + falseTerm
						+ ")";
	}

	/**
	 * @return A why3 bound variable declaration.
	 */
	public static String why3BoundVarDecl(String identifier, Why3Type type) {
		return identifier + " : " + type.text + ".";
	}

	/**
	 * @return A why3 bound variable declarations.
	 */
	public static String why3BoundVarDecl(String[] identifiers,
			Why3Type[] types) {
		String result = "";

		for (int i = 0; i < types.length - 1; i++)
			result += identifiers[i] + " : " + types[i].text + ", ";
		result += identifiers[types.length - 1] + " : "
				+ types[types.length - 1].text + ". ";
		return result;
	}

	/**
	 * @return A why3 exists quantified expression.
	 */
	public static String why3Exists(String decl, String predicate) {
		return keyword_exists + " " + decl + " " + predicate;
	}

	/**
	 * 
	 * @return A why3 forall quantified expression.
	 */
	public static String why3Forall(String decl, String predicate) {
		return keyword_forall + " " + decl + " " + predicate;
	}

	/**
	 * @return A why3 tuple update operation.
	 */
	public static String why3TupleUpdate(String tuple, String field,
			String newValue) {
		return "{" + tuple + " with " + field + " = " + newValue + "}";
	}

	/**
	 * @return A why3 tuple dense update.
	 */
	public static String why3TupleDenseUpdate(String tuple, String fields[],
			String newValues[], int length) {
		assert fields.length >= length && newValues.length >= length;
		String result = "{" + tuple + " with ";

		for (int i = 0; i < length; i++)
			result += fields[i] + " = " + newValues[i] + "; ";
		return result += "}";
	}

	/**
	 * @return A why3 function calls operation.
	 */
	public static String why3FunctionCall(String functionName, String... args) {
		String result = "(" + functionName + " ";

		for (int i = 0; i < args.length; i++)
			result += args[i] + " ";
		result += ")";
		return result;
	}

	/**
	 * @return A why3 uninterpreted function declaration.
	 */
	public static String why3UninterpretedFunctionDecl(String funcName,
			Why3FunctionType type) {
		return keyword_function + " " + funcName + " " + type.text;
	}

	/**
	 * 
	 * @return A why3 function (with-body) declaration.
	 */
	public static String why3FunctionDecl(String funcName,
			Why3FunctionType type, String bodyText, String... formalParams) {
		String formals = "";

		for (int i = 0; i < formalParams.length; i++)
			formals += "(" + formalParams[i] + " : "
					+ type.nthArgumentType(i).text + ")";
		formals += " : " + type.returnType.text;
		return keyword_function + " " + funcName + " " + formals + " = "
				+ bodyText;
	}

	/**
	 * @return A why3 type aliasing declaration.
	 */
	public static String why3TypeAlias(String alias, Why3Type type) {
		return keyword_type + " " + alias + " = " + type.text + "\n";
	}

	/* ******** Helpers methods for creating derived Why3 types ******* */
	public static Why3Type why3ArrayType(Why3Type elementType) {
		return new Why3Type("map", true, int_t, elementType);
	}

	public static Why3Type why3MapType(Why3Type keyType, Why3Type valueType) {
		return new Why3Type("map", true, keyType, valueType);
	}

	public static Why3TupleType why3TupleType(String nameAliasOpt,
			String fieldNames[], Why3Type fieldTypes[]) {
		return new Why3TupleType(null, false, fieldNames, fieldTypes);
	}

	public static Why3FunctionType why3FunctionType(Why3Type returnType,
			Why3Type formals[]) {
		return new Why3FunctionType(returnType, formals);
	}

	/**
	 * Return a alias type which use the alias name as a type text.
	 */
	public static Why3Type why3AliasType(String alias) {
		return new Why3Type(alias);
	}

	/**
	 * A theory for avoiding operator conflict between REAL and INT.
	 */
	static public String REAL_NAME_SPACE = "theory SARL_REAL\n"
			+ "use import real.Real\n"
			+ "function add (a b : real) : real = a + b\n"
			+ "function sub (a b : real) : real = a - b\n"
			+ "function mul (a b : real) : real = a * b\n"
			+ "function neg (a : real) : real = (-a)\n"
			+ "function (:-) (a b : real) : real = a / b\n"
			+ "predicate lt (a b : real) = a < b\n"
			+ "predicate lte (a b : real) = a <= b\n"
			+ "clone import int.Exponentiation as POWREAL with type t = real\n"
			+ "function sarl_power (a : real) (b : int) : real = (POWREAL.power a b)\n"
			+ "end\n";

	static private String IMPORT_REAL_NAME_SPACE = "use import SARL_REAL as SR\n";

	/**
	 * @return The text for importing a library.
	 */
	public static String importText(Why3Lib lib) {
		switch (lib) {
		case BOOL:
			return "use import bool.Bool\n";
		case INT_DIV_MOD:
			return "use import int.EuclideanDivision\n";
		case POWER_INT:
			return "clone import int.Exponentiation as POWINT with type t = int\n";
		case POWER_REAL:
			return "clone import int.Exponentiation as POWREAL with type t = real\n";
		case INT:
			return "use import int.Int\n";
		case MAP:
			return "use import map.Map\n";
		case REAL:
			return IMPORT_REAL_NAME_SPACE;
		default:
			throw new SARLException("Unknown WHY3_IMPORT record.");
		}
	}

	/* ****** Others ******* */
	static String recursiveCalling(String operands[],
			Why3BuiltinFunction func) {
		assert func.numArgs > 1 : "it doesn't make sense when "
				+ "recursively calling function whose number of "
				+ "arguments less than one";
		String result = "";
		String prefix = "", suffix = "";

		// a + b + c + d -> b c
		// prefix (add (add (add
		// suffix ) c) d
		// end )
		int step = func.numArgs - 1;

		for (int i = 0; i < func.numArgs; i++)
			result += " " + operands[i];
		for (int i = func.numArgs; i < operands.length; i += step) {
			suffix += ")";
			for (int j = 0; j < step; j++)
				suffix += " " + operands[i + j];
		}
		suffix += ")";
		for (int i = func.numArgs; i < operands.length + step; i += step) {
			prefix += " ( " + func.name;
		}
		return prefix + result + suffix;
	}

	public static class Axiom {
		final String name;
		final String axiom;
		final String text;

		Axiom(String name, String axiom) {
			this.name = "_Ax" + name;
			this.axiom = axiom;
			this.text = keyword_predicate + " " + this.name + " = " + axiom
					+ "\n";
		}
	}

	public static Axiom newAxiom(String name, String axiom) {
		return new Axiom(name, axiom);
	}

	/**
	 * 
	 * @param sigmaFuncName
	 *            The name of the sigma function.
	 * @param params
	 *            The first two parameters are lower and higher bounds. Rests
	 *            are extra parameters.
	 * @param paramTypes
	 *            The first two parameter types are integer types. Rests are
	 *            types of extra parameters.
	 * @param baseLowCase
	 *            The base case where the "lower bound" is applied.
	 * @param baseHighCase
	 *            The base case where the "higher bound" is applied.
	 * @return
	 */
	static public Axiom sigmaAxiom(String sigmaFuncName, String[] params,
			Why3Type[] paramTypes, String baseLowCase, String baseHighCase) {
		String sigmaCall = Why3Primitives.why3FunctionCall(sigmaFuncName,
				params);
		String low = params[0], high = params[1];
		String sigmaCall_l_plus_one = Why3Primitives.why3FunctionCall(
				sigmaFuncName, "(" + params[0] + "+1)", params[1]);
		String sigmaCall_h_minus_one = Why3Primitives.why3FunctionCall(
				sigmaFuncName, params[0], "(" + params[1] + "-1)");
		String axiom = keyword_forall + " "
				+ Why3Primitives.why3BoundVarDecl(params, paramTypes);
		String generalCases = sigmaCall + " = " + sigmaCall_l_plus_one + " + "
				+ baseLowCase + land.text + sigmaCall + " = "
				+ sigmaCall_h_minus_one + " + " + baseHighCase;

		axiom += Why3Primitives.why3IfThenElse(low + " >= " + high,
				sigmaCall + " = 0", generalCases);
		return new Axiom(sigmaFuncName, axiom);
	}
}
