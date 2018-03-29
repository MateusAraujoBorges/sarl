package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;

import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.util.Pair;

/**
 * <p>
 * This class simplifies symbolic expressions of tuple type that are
 * non-concrete to concrete tuple expressions. A concrete tuple expression is
 * <ol>
 * <li>a symbolic expression whose {@link SymbolicOperator} equals to
 * {@link SymbolicOperator#TUPLE}</li>
 * <li>recursively that each tuple component must be either a concrete value or
 * a symbolic expression whose operator is
 * {@link SymbolicOperator#SYMBOLIC_CONSTANT} or
 * {@link SymbolicOperator#APPLY}</li>
 * </ol>
 * </p>
 * 
 * @author ziqingluo
 */
public class SymbolicTupleSimplifier {

	/**
	 * A reference to {@link #PreUniverse}
	 */
	private PreUniverse universe;

	/**
	 * <p>
	 * A queue of entries that have not been processed.
	 * </p>
	 * <p>
	 * The process of each entry is mainly analyzing that if the key of this
	 * entry is a component of a non-concrete tuple and simplify the
	 * non-concrete tuple once all of its components have a value that is either
	 * concrete or is a symbolic constant.
	 * </p>
	 */
	private LinkedList<Pair<SymbolicExpression, SymbolicExpression>> workingEntries;

	/**
	 * A map from non-concrete tuples to their concrete equivalences.
	 */
	private Map<SymbolicExpression, SymbolicExpression> tupleSubstitutions;

	/**
	 * A map from non-concrete tuples to their component values. For each
	 * component value, it can only be NULL, a concrete value or a symbolic
	 * constant (or an APPLY expression).
	 */
	private Map<SymbolicExpression, SymbolicExpression[]> tupleComponentsMap;

	SymbolicTupleSimplifier(Context context) {
		this.workingEntries = new LinkedList<>();
		this.tupleSubstitutions = new HashMap<>();
		this.tupleComponentsMap = new HashMap<>();
		this.universe = context.info.universe;
		// initialize:
		for (Entry<SymbolicExpression, SymbolicExpression> entry : context.subMap
				.entrySet())
			workingEntries.add(new Pair<>(entry.getKey(), entry.getValue()));
		simplify();
	}

	/**
	 * @return a map from non-concrete tuples to their concrete equivalences.
	 */
	Map<SymbolicExpression, SymbolicExpression> getTupleSubstitutionMap() {
		return tupleSubstitutions;
	}

	/**
	 * Collecting concrete component values for tuples from entries of the
	 * {@link Context#subMap}. Add entries to {@link #tupleSubstitutions} once a
	 * non-concrete tuple can be simplified to a concrete one.
	 */
	private void simplify() {
		while (!workingEntries.isEmpty()) {
			Pair<SymbolicExpression, SymbolicExpression> equation = workingEntries
					.removeFirst();
			SymbolicExpression key = equation.left;
			SymbolicExpression value = equation.right;

			if (key.operator() == SymbolicOperator.TUPLE_READ)
				simplifyTupleRead(key, value);
			else if (key.operator() == SymbolicOperator.ADD && value.isZero())
				simplifyEquation(key);
		}
	}

	/**
	 * <p>
	 * Given a TUPLE_READ expression : <code>tuple.field</code> that has a
	 * concrete value <code>val</code>, updates the {@link #tupleComponentsMap}
	 * by updating the corresponding component value to <code>val</code>.
	 * </p>
	 * 
	 * <p>
	 * If all components of the tuple have concrete values (or symbolic constant
	 * values), updates the {@link #tupleSubstitutions} map and add a new
	 * entry<code>tuple = {...} </code> to {@link #workingEntries}.
	 * </p>
	 */
	private void simplifyTupleRead(SymbolicExpression tupleRead,
			SymbolicExpression concreteValue) {
		SymbolicExpression tuple = (SymbolicExpression) tupleRead.argument(0);
		IntObject fieldIdx = (IntObject) tupleRead.argument(1);
		SymbolicExpression tupleComponents[];

		if (tuple.operator() == SymbolicOperator.TUPLE)
			return;
		tupleComponents = tupleComponentsMap.get(tuple);
		if (tupleComponents == null) {
			SymbolicTupleType tupleType = (SymbolicTupleType) tuple.type();
			int numTypes = tupleType.sequence().numTypes();

			tupleComponents = new SymbolicExpression[numTypes];
			Arrays.fill(tupleComponents, null);
		}
		tupleComponents[fieldIdx.getInt()] = concreteValue;

		boolean complete = true;

		for (int i = 0; i < tupleComponents.length; i++)
			if (tupleComponents[i] == null) {
				complete = false;
				break;
			}
		if (complete) {
			SymbolicExpression concreteTuple = universe
					.tuple((SymbolicTupleType) tuple.type(), tupleComponents);

			tupleSubstitutions.put(tuple, concreteTuple);
			tupleComponentsMap.remove(tuple);
			workingEntries.add(new Pair<>(tuple, concreteTuple));
		} else
			tupleComponentsMap.put(tuple, tupleComponents);
	}

	/**
	 * Process an expression expr of the pattern:
	 * <code>tuple.field + e = 0 </code>. In such a case, the tuple component
	 * has value <code>(-1) * e</code>. Now if
	 * <ul>
	 * <li><code>(-1) * e</code> is a symbolic constant, update
	 * {@link #tupleComponentsMap} for the tuple.</li>
	 * <li><code>tuple.field</code> matches the pattern <code>tuple.0</code> and
	 * <code>(-1) * e</code> matches the pattern <code>c.0</code> where
	 * <code>c</code> is a symbolic constant (or an APPLY expression) and both
	 * <code>c</code> and <code>tuple</code> have the same tuple type with exact
	 * one field, add entry <code>tuple = c</code> to
	 * {@link #workingEntries}</li>
	 * </ul>
	 */
	private void simplifyEquation(SymbolicExpression add) {
		SymbolicExpression op0 = (SymbolicExpression) add.argument(0);
		SymbolicExpression op1 = (SymbolicExpression) add.argument(1);

		op1 = universe.minus((NumericExpression) op1);
		if (op0.operator() == SymbolicOperator.TUPLE_READ
				&& op1.operator() == SymbolicOperator.SYMBOLIC_CONSTANT) {
			simplifyTupleRead(op0, op1);
			return;
		}
		if (op1.operator() == SymbolicOperator.TUPLE_READ
				&& op0.operator() == SymbolicOperator.SYMBOLIC_CONSTANT) {
			simplifyTupleRead(op1, op0);
			return;
		}
		if (op0.operator() == SymbolicOperator.TUPLE_READ
				&& op1.operator() == SymbolicOperator.TUPLE_READ) {
			SymbolicExpression tuple0, tuple1;
			SymbolicTupleType tupleType;

			tuple0 = (SymbolicExpression) op0.argument(0);
			tuple1 = (SymbolicExpression) op1.argument(0);
			tupleType = (SymbolicTupleType) tuple0.type();
			if (tupleType.sequence().numTypes() != 1)
				return;
			if (!tuple0.type().equals(tuple1.type()))
				return;
			if (tuple0.operator() == SymbolicOperator.SYMBOLIC_CONSTANT
					|| tuple0.operator() == SymbolicOperator.APPLY) {
				this.workingEntries.add(new Pair<>(tuple1, tuple0));
				return;
			}
			if (tuple1.operator() == SymbolicOperator.SYMBOLIC_CONSTANT
					|| tuple1.operator() == SymbolicOperator.APPLY) {
				this.workingEntries.add(new Pair<>(tuple0, tuple1));
				return;
			}
		}
	}
}
