package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
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
	 * {@link #tupleComponents} map will be updated correspondingly, then remove
	 * the equation.</li>
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
	private Map<SymbolicExpression, SymbolicExpression[]> tupleComponents;

	SymbolicTupleSimplifier(Context context) {
		this.workingEquations = new LinkedList<>();
		this.tupleSubstitutions = new HashMap<>();
		this.universe = context.info.universe;
	}
}
