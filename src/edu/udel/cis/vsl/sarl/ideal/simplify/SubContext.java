package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.HashMap;
import java.util.Map;
import java.util.TreeMap;

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.simplify.IF.Range;
import edu.udel.cis.vsl.sarl.util.WorkMap;

/**
 * A sub-context represents a boolean expression that holds within the context
 * of some other assumption. Hence everything in the super-context is assumed to
 * hold, in addition to everything in the sub-context. This is used to provide
 * scoping to contexts.
 * 
 * @author siegel
 */
public class SubContext extends Context {

	/**
	 * The super-context.
	 */
	private Context superContext;

	/**
	 * Creates new sub-context and initializes it using the given assumption.
	 * 
	 * @param superContext
	 *            the (non-{@code null}) context containing this one
	 * @param assumption
	 *            the boolean expression to be represented by this sub-context
	 */
	protected SubContext(Context superContext, BooleanExpression assumption) {
		super(superContext.getInfo(), superContext.backwardsSub);
		this.superContext = superContext;
		initialize(assumption);
	}

	@Override
	protected void addSubsToMap(
			Map<SymbolicExpression, SymbolicExpression> map) {
		superContext.addSubsToMap(map);
		map.putAll(subMap);
	}

	@Override
	protected Map<SymbolicExpression, SymbolicExpression> getFullSubMap() {
		Map<SymbolicExpression, SymbolicExpression> map = new HashMap<>();

		addSubsToMap(map);
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
	protected Range getRange(Monic monic) {
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
	protected SymbolicExpression getSub(SymbolicExpression key) {
		SymbolicExpression result = super.getSub(key);

		if (result != null)
			return result;
		result = superContext.getSub(key);
		return result;
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
	 * @return a linear solver based on relative Gaussian elimination that can
	 *         be used to simplify the substitution map of this sub-context
	 *         assuming all substitutions in the super context
	 */
	@Override
	protected LinearSolver getLinearSolver() {
		if (subMap.isEmpty())
			return null;

		Map<SymbolicExpression, SymbolicExpression> superSubMap = superContext
				.getFullSubMap();
		LinearSolver ls = LinearSolver.reduceRelative(info, superSubMap, subMap,
				info.monicComparator, backwardsSub);

		return ls;
	}

	/**
	 * Collapses this {@link SubContext} and all its super-contexts into a
	 * single {@link Context}. The collapsed context is equivalent to this
	 * sub-context but is not an instance of {@link SubContext}.
	 * 
	 * @return a new {@link Context} that is not a {@link SubContext} and
	 *         contains all the mappings specified by this {@link SubContext}
	 *         and its ancestors, with the sub-context mappings take precedence
	 *         (overwriting) those of the parent
	 */
	@Override
	protected Context collapse() {
		Context superCollapsed = superContext.collapse();
		Map<SymbolicExpression, SymbolicExpression> map1 = new TreeMap<>(
				info.universe.comparator());

		map1.putAll(superCollapsed.subMap);
		map1.putAll(subMap);

		WorkMap<Monic, Range> map2 = new WorkMap<>(
				info.idealFactory.monicComparator());

		map2.putAll(superCollapsed.rangeMap);
		map2.putAll(rangeMap);

		Context collapse = new Context(info, map1, map2, this.backwardsSub);

		return collapse;
	}

	@Override
	protected SymbolicExpression simplify(SymbolicExpression expr) {
		if (isEmpty()) {
			// this case is to provide a base case in an otherwise
			// infinite recursion
			return new IdealSimplifierWorker(superContext)
					.simplifyExpressionWork(expr, true);
		} else {
			return new IdealSimplifierWorker(this.collapse())
					.simplifyExpressionWork(expr, false);
		}
	}

	/**
	 * Returns the super-context of this sub-context, which will not be
	 * {@code null}
	 * 
	 * @return the super-context of this context
	 */
	public Context getSuperContext() {
		return superContext;
	}
}
