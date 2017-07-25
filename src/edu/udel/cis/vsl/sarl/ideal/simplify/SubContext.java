package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.Map;
import java.util.TreeMap;

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.simplify.LinearSolver.LinearSolverInfo;
import edu.udel.cis.vsl.sarl.simplify.IF.Range;

/**
 * A sub-context represents a boolean expression that holds within the context
 * of some other assumption. Hence everything in the super-context is assumed to
 * hold, in addition to everything in the sub-context. This is used to provide
 * scoping to contexts.
 * 
 * @author siegel
 */
public class SubContext extends Context2 {

	/**
	 * The super-context.
	 */
	private ContextIF superContext;

	/**
	 * Creates new sub-context with given super-context.
	 * 
	 * @param superContext
	 *            the (non-{@code null}) context containing this one
	 */
	public SubContext(ContextIF superContext) {
		super(superContext.getInfo());
		this.superContext = superContext;
	}

	/**
	 * Creates new sub-context and initializes it using the given assumption.
	 * 
	 * @param superContext
	 *            the (non-{@code null}) context containing this one
	 * @param assumption
	 *            the boolean expression to be represented by this sub-context
	 */
	public SubContext(ContextIF superContext, BooleanExpression assumption) {
		this(superContext);
		this.originalAssumption = assumption;
		initialize(assumption);
	}

	/**
	 * Returns the global monic constant map, obtained by starting with the
	 * super-context's global monic constant map, and then adding entries from
	 * this sub-context. If there is an entry in this sub-context with the same
	 * key as that in the super-context, the one in this sub-context overrides
	 * the one in the super-context.
	 * 
	 * @return the global monic constant map mapping {@link Monic}s to their
	 *         known constant values
	 */
	@Override
	public Map<Monic, Number> getMonicConstantMap() {
		Map<Monic, Number> map = superContext.getMonicConstantMap();

		addMonicConstantsToMap(map); // overwrites any previous entries
		return map;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * <p>
	 * Looks first in this sub-context for an entry in the range map for the
	 * given monic. If none is found, then looks in the super-context.
	 * </p>
	 * 
	 * @return the range associated to {@code monic}, or {@code null}
	 */
	@Override
	public Range getRange(Monic monic) {
		Range result = super.getRange(monic);

		if (result != null)
			return result;
		result = superContext.getRange(monic);
		return result;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * <p>
	 * Looks first in this sub-context for an entry in the sub map for the given
	 * key. If none is found, then looks in the super-context.
	 * </p>
	 * 
	 * @return the simplified expression that should replace {@code key}, or
	 *         {@code null}
	 */
	@Override
	public SymbolicExpression getSub(SymbolicExpression key) {
		SymbolicExpression result = super.getSub(key);

		if (result != null)
			return result;
		result = superContext.getSub(key);
		return result;
	}

	/**
	 * Returns the super-context of this sub-context, which will not be
	 * {@code null}
	 * 
	 * @return the super-context of this context
	 */
	public ContextIF getSuperContext() {
		return superContext;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * <p>
	 * For this sub-context, a form of "relative" Gaussian elimination is
	 * performed. The linear equalities of this sub-context are simplified using
	 * the information from the super-context before ordinary Gaussian
	 * elimination is performed.
	 * </p>
	 * 
	 * @return whether a change took place
	 */
	protected boolean gauss() throws InconsistentContextException {
		Map<Monic, Number> superConstantMap = superContext
				.getMonicConstantMap();
		Map<Monic, Number> oldConstantMap = new TreeMap<>(info.monicComparator),
				newConstantMap = new TreeMap<>(info.monicComparator);

		addMonicConstantsToMap(oldConstantMap);

		LinearSolverInfo lsi = LinearSolver.reduceRelativeConstantMap(
				info.idealFactory, superConstantMap, oldConstantMap,
				newConstantMap);

		return gaussHelper(lsi, oldConstantMap, newConstantMap);
	}

}
