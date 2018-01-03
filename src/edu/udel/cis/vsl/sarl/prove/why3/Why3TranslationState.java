package edu.udel.cis.vsl.sarl.prove.why3;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.prove.why3.Why3Primitives.Why3Lib;
import edu.udel.cis.vsl.sarl.prove.why3.Why3Primitives.Why3TupleType;
import edu.udel.cis.vsl.sarl.prove.why3.Why3Primitives.Why3Type;

/**
 * This class manages all stateful informations that are needed during the
 * translation from SARL to Why3.
 * 
 * @author ziqingluo
 */
public class Why3TranslationState {

	/**
	 * A sigma expression will be translated to a function. The function name is
	 * associated with the lambda expression in the sigma expression.
	 */
	private Map<SymbolicExpression, String> sigmaNameMap = null;

	/**
	 * Map from SARL lambda expression to a unique artificial function name.
	 * 
	 * <p>
	 * A lambda function is a function who has a body.
	 * </p>
	 */
	private Map<SymbolicExpression, String> lambdaFunctionMap;

	/**
	 * Map from Why3 tuple type to its' alias name.
	 * 
	 * There must be a type aliasing declaration that is associated to an alias
	 * name in {@link #declarations}.
	 */
	private Map<Why3Type, String> tupleTypeAliasMap;

	/**
	 * Mapping of SARL symbolic type to corresponding {@link Why3Type}. Used to
	 * cache results of type translation.
	 */
	private Map<SymbolicType, Why3Type> typeMap;

	/**
	 * the cache for translated expressions
	 */
	private Map<SymbolicExpression, String> translationCache;

	/**
	 * Library declarations that are needed for the theory
	 */
	private Set<Why3Lib> libraries;

	/**
	 * translated all kinds of declarations in Why3 logic language: constant and
	 * function declaration.
	 */
	private Map<String, String> declarations;

	/**
	 * type aliasing declarations
	 */
	private Map<String, String> typeAliasingDeclarations;

	/**
	 * The name of the bound variable at each recursive level of a quantified
	 * expression (or lambda expression).
	 * 
	 * <p>
	 * One bound variable per level
	 * </p>
	 */
	private Stack<String> quantifiedContexts;

	/**
	 * a counter for generating names of "goal"s.
	 */
	private int goalNameCounter = 0;

	/**
	 * a counter for generated identifiers.
	 */
	private int identNameCounter = 0;

	/**
	 * a counter for generated identifiers for tuple type.
	 */
	private int tupleAliasCounter = 0;

	/**
	 * a counter for generated identifiers of lambda functions.
	 */
	private int lambdaNameCounter = 0;

	private int sigmaCounter = 0;

	/* **************** Constructor ****************** */
	public Why3TranslationState() {
		this.declarations = new HashMap<>();
		this.tupleTypeAliasMap = new HashMap<>();
		this.typeAliasingDeclarations = new HashMap<>();
		this.translationCache = new HashMap<>();
		this.typeMap = new HashMap<>();
		this.tupleTypeAliasMap = new HashMap<>();
		this.lambdaFunctionMap = new HashMap<>();
		this.tupleTypeAliasMap = new HashMap<>();
		this.libraries = new HashSet<>();
		this.quantifiedContexts = new Stack<>();
	}

	/**
	 * @return a new name for a goal
	 */
	public String newGoalIdentifier() {
		return "G" + goalNameCounter++;
	}

	/**
	 * @return a new name for a generated identifier
	 */
	public String newIdentifierName() {
		return "_sc_" + identNameCounter++;
	}

	/**
	 * @return The cached result or null
	 */
	public String getCachedExpressionTranslation(SymbolicExpression expr) {
		return translationCache.get(expr);
	}

	/**
	 * Cache the expression translation result
	 */
	public void cacheExpressionTranslation(SymbolicExpression expr,
			String translation) {
		translationCache.putIfAbsent(expr, translation);
	}

	/**
	 * @return the cached {@link Why3Type} of the given {@link SymbolicType}.
	 */
	public Why3Type getCachedType(SymbolicType type) {
		return typeMap.get(type);
	}

	/**
	 * Cache the type translation result
	 */
	public void cacheType(SymbolicType type, Why3Type typeTranslation) {
		typeMap.put(type, typeTranslation);
	}

	/**
	 * @return An alias of a {@link Why3TupleType}. There is a unique alias
	 *         corresponds to a tuple type.
	 */
	public String getTupleTypeAlias(Why3TupleType tupleType) {
		String alias = tupleTypeAliasMap.get(tupleType);

		if (alias == null) {
			alias = "_tuple_" + tupleAliasCounter++;
			tupleTypeAliasMap.put(tupleType, alias);
		}
		return alias;
	}

	/**
	 * @return An generated function name for a lambda function. There is a
	 *         unique function name corresponds to a lambda
	 *         {@link SymbolicExpression}.
	 */
	public String getLambdaFunctionName(SymbolicExpression lambda) {
		String ret = lambdaFunctionMap.get(lambda);

		if (ret == null) {
			ret = "_anon_" + lambdaNameCounter++;
			lambdaFunctionMap.put(lambda, ret);
		}
		return ret;
	}

	/**
	 * @return All declarations.
	 */
	public Iterable<String> getDeclaration() {
		List<String> result = new LinkedList<>(
				typeAliasingDeclarations.values());

		result.addAll(declarations.values());
		return result;
	}

	/**
	 * Adds a declaration at the end of the declaration list.
	 */
	public void addDeclaration(String identifier, String declaration) {
		declarations.putIfAbsent(identifier, declaration);
	}

	/**
	 * Inserts a declaration at the beginning of the declaration list.
	 */
	public void addTypeAliasDeclaration(String alias, String declaration) {
		typeAliasingDeclarations.putIfAbsent(alias, declaration);
	}

	/**
	 * @return All libraries that are needed for the translation
	 */
	public Iterable<Why3Lib> getLibraries() {
		return this.libraries;
	}

	/**
	 * Adds a {@link Why3Lib}.
	 */
	public void addLibrary(Why3Lib lib) {
		libraries.add(lib);
	}

	/**
	 * Push a quantified (or lambda) context into this state.
	 * 
	 * @param boundIdent
	 *            The name of the bound variable that is associated with the
	 *            context.
	 */
	public void pushQuantifiedContext(String boundIdent) {
		this.quantifiedContexts.push(boundIdent);
	}

	/**
	 * Pop a quantified (or lambda) context out of this state.
	 */
	public void popQuantifiedContext() {
		this.quantifiedContexts.pop();
	}

	/**
	 * @return True if and only if the current state is in a quantified (or
	 *         lambda) context AND the given boundIdent matches the name of the
	 *         bound variable that is associated with the context.
	 */
	public boolean inQuantifiedContext(String boundIdent) {
		if (quantifiedContexts.isEmpty())
			return false;

		for (String var : quantifiedContexts)
			if (var.equals(boundIdent))
				return true;
		return false;
	}

	/**
	 * Return a unique sigma function name for the given lambda expression
	 * 
	 * @return
	 */
	public String getSigmaName(SymbolicExpression lambda) {
		if (sigmaNameMap == null)
			sigmaNameMap = new HashMap<>();

		String name = sigmaNameMap.get(lambda);

		if (name == null) {
			name = "_sigma" + sigmaCounter++;
			sigmaNameMap.put(lambda, name);
		}
		return name;
	}
}
