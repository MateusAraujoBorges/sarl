package edu.udel.cis.vsl.sarl.reason.common;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProver;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProverFactory;
import edu.udel.cis.vsl.sarl.prove.why3.RobustWhy3ProvePlatformFactory;
import edu.udel.cis.vsl.sarl.reason.IF.ReasonerFactory;
import edu.udel.cis.vsl.sarl.simplify.IF.Simplifier;
import edu.udel.cis.vsl.sarl.simplify.IF.SimplifierFactory;

/**
 * A factory for producing instances of {@link ContextMinimizingReasoner}.
 * 
 * @author Stephen F. Siegel
 */
public class ContextMinimizingReasonerFactory implements ReasonerFactory {

	/**
	 * Factory used to produce new {@link TheoremProver}s, which will be used by
	 * the reasoners to check validity.
	 */
	private TheoremProverFactory proverFactory;

	/**
	 * Factory used to produce new why3 provers, which will be used by the
	 * reasoners to check validity. why3 is a prove platform and is suppose to
	 * be more expensive than other provers. This factory is null if no why3 is
	 * installed.
	 */
	private TheoremProverFactory why3Factory = null;

	/**
	 * Factory used to produce new {@link Simplifier}s, which will be used by
	 * the reasoners to simplify expressions.
	 */
	private SimplifierFactory simplifierFactory;

	/**
	 * Symbolic universe used to produce new symbolic expressions.
	 */
	private PreUniverse universe;

	/**
	 * Caches the {@link Reasoner}s associated to each boolean expression. In
	 * this way there is at most one {@link Reasoner} associated to each
	 * equivalence class of {@link BooleanExpression}, where the equivalence
	 * relation is determined by the {@link BooleanExpression#equals(Object)}
	 * method.
	 */
	private Map<BooleanExpression, ContextMinimizingReasoner> reasonerMap = new ConcurrentHashMap<>();

	/**
	 * Creates new factory based on the given symbolic universe, theorem prover
	 * factory, and simplifier factory. Those objects will be used by the
	 * reasoners produced by this factory.
	 * 
	 * @param universe
	 *            symbolic universe used to produce new symbolic expressions
	 * @param proverFactory
	 *            used to produce new {@link TheoremProver}s, which will be used
	 *            by the reasoners to check validity
	 * @param simplifierFactory
	 *            used to produce new {@link Simplifier}s, which will be used by
	 *            the reasoners to simplify expressions
	 */
	public ContextMinimizingReasonerFactory(PreUniverse universe,
			TheoremProverFactory proverFactory,
			SimplifierFactory simplifierFactory,
			RobustWhy3ProvePlatformFactory why3Factory) {
		this.universe = universe;
		this.proverFactory = proverFactory;
		this.simplifierFactory = simplifierFactory;
		this.universe = universe;
		this.why3Factory = why3Factory;
	}

	@Override
	public ContextMinimizingReasoner getReasoner(BooleanExpression context,
			boolean useBackwardSubstitution) {
		assert context.isCanonic();

		ContextMinimizingReasoner result = reasonerMap.get(context);

		if (result == null) {
			ContextMinimizingReasoner newContextMinimizingReasoner = new ContextMinimizingReasoner(
					this, context, useBackwardSubstitution);

			result = reasonerMap.putIfAbsent(context,
					newContextMinimizingReasoner);
			return result == null ? newContextMinimizingReasoner : result;
		}
		return result;
	}

	/**
	 * Returns the symbolic universe associated to this factory.
	 * 
	 * @return the symbolic universe associated to this factory
	 */
	PreUniverse getUniverse() {
		return universe;
	}

	/**
	 * Returns the simplifier factory associated to this factory.
	 * 
	 * @return the simplifier factory associated to this factory
	 */
	SimplifierFactory getSimplifierFactory() {
		return simplifierFactory;
	}

	@Override
	public TheoremProverFactory getTheoremProverFactory() {
		return proverFactory;
	}

	@Override
	public TheoremProverFactory getWhy3ProvePlatformFactory() {
		// If there is no why3 installed, use regular proverFactory:
		return why3Factory == null ? proverFactory : why3Factory;
	}
}
