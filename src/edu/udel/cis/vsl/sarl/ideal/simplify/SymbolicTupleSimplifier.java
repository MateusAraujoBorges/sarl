package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;

import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.util.Pair;

public class SymbolicTupleSimplifier {

	/**
	 * A reference to {@link #PreUniverse}
	 */
	private PreUniverse universe;

	/**
	 * A queue of equations that have not been processed. To process each
	 * equation x == v, where v is a concrete value,
	 * <ul>
	 * <li>if x is a TUPLE_READ operation, x == v will be processed and the
	 * {@link #tupleComponentsMap} map will be updated correspondingly, then
	 * remove the equation.</li>
	 * <li>if v is zero and x has the form <code>R.0 + (-1)*Y</code>, where R is
	 * a {@link ReferenceExpression}, the {@link #tupleSubstitutions} map will
	 * be updated by adding an entry <code><Y, R></code>, then remove the
	 * equation.</li>
	 * <li>otherwise, ignore and remove equation x == v.</li>
	 * </ul>
	 */
	private LinkedList<Pair<SymbolicExpression, SymbolicExpression>> workingEquations;

	/**
	 * A map from symbolic expressions that have tuple types but whose operators
	 * are not TUPLE to symbolic expressions whose operators are TUPLE and
	 * components have concrete values. In other words, this is a map from
	 * non-concrete tuples to concrete tuples.
	 */
	private Map<SymbolicExpression, SymbolicExpression> tupleSubstitutions;

	/**
	 * A map from symbolic expressions that have tuple types but whose operators
	 * are not TUPLE (i.e. non-concrete tuples) to their component values. For
	 * each non-concrete tuple, if all of its component values can be simplified
	 * to some concrete values, the non-concrete tuple can be simplified to a
	 * concrete tuple.
	 */
	private Map<SymbolicExpression, SymbolicExpression[]> tupleComponentsMap;

	SymbolicTupleSimplifier(Context context) {
		this.workingEquations = new LinkedList<>();
		this.tupleSubstitutions = new HashMap<>();
		this.tupleComponentsMap = new HashMap<>();
		this.universe = context.info.universe;
		// initialize:
		for (Entry<SymbolicExpression, SymbolicExpression> entry : context.subMap
				.entrySet())
			workingEquations.add(new Pair<>(entry.getKey(), entry.getValue()));
		simplify();
	}

	Map<SymbolicExpression, SymbolicExpression> getTupleSubstitutionMap() {
		return tupleSubstitutions;
	}

	private void simplify() {
		while (!workingEquations.isEmpty()) {
			Pair<SymbolicExpression, SymbolicExpression> equation = workingEquations
					.removeFirst();
			SymbolicExpression key = equation.left;
			SymbolicExpression value = equation.right;

			if (key.operator() == SymbolicOperator.TUPLE_READ)
				simplifyTupleRead(key, value);
			else if (key.operator() == SymbolicOperator.ADD && value.isZero())
				simplifyReference(key);
		}
	}

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
			workingEquations.add(new Pair<>(tuple, concreteTuple));
		} else
			tupleComponentsMap.put(tuple, tupleComponents);
	}

	private void simplifyReference(SymbolicExpression add) {
		SymbolicExpression op0 = (SymbolicExpression) add.argument(0);
		SymbolicExpression op1 = (SymbolicExpression) add.argument(1);
		SymbolicExpression tuple, reference;

		op1 = universe.minus((NumericExpression) op1);
		if (op0.operator() == SymbolicOperator.TUPLE_READ
				&& op1.operator() == SymbolicOperator.TUPLE_READ) {
			tuple = (SymbolicExpression) op0.argument(0);
			reference = (SymbolicExpression) op1.argument(0);
			if (tuple instanceof ReferenceExpression
					&& !(reference instanceof ReferenceExpression)) {
				reference = tuple;
				tuple = (SymbolicExpression) op1.argument(0);
			} else if (!(reference instanceof ReferenceExpression
					&& !(tuple instanceof ReferenceExpression)))
				return;
			this.tupleSubstitutions.put(tuple, reference);
			this.workingEquations.add(new Pair<>(tuple, reference));
		}
	}
}
