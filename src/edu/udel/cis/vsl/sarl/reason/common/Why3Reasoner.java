package edu.udel.cis.vsl.sarl.reason.common;

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.prove.IF.ProverPredicate;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProver;

/**
 * A sub-class of {@link ContextMinimizingReasoner} that calls Why3 prove
 * platform only iff Why3 is installed. If Why3 is not installed, this object
 * shall not be created.
 * 
 * @author ziqing
 *
 */
public class Why3Reasoner extends ContextMinimizingReasoner {

	/**
	 * A list of {@link ProverPredicate}s that is needed for calling why3
	 * prover. A prover predicate factors a common part of complex boolean
	 * expressions.
	 */
	protected ProverPredicate[] proverPredicates = null;

	public Why3Reasoner(ContextMinimizingReasonerFactory factory,
			BooleanExpression context, boolean useBackwardSubstitution,
			ProverPredicate[] proverPredicates) {
		super(factory, context, useBackwardSubstitution);
		this.proverPredicates = proverPredicates;
		assert this.proverPredicates != null;
	}

	@Override
	protected synchronized TheoremProver getProver(boolean createNewProver,
			BooleanExpression context) {
		if (prover == null || createNewProver)
			prover = factory.getTheoremProverFactory().newProver(context,
					proverPredicates);
		return prover;
	}

	@Override
	/**
	 * Get a {@link Why3Reasoner} from the reasoner factory. Override from the
	 * super class so that {@link ProverPredicate}s can be used.
	 */
	protected ContextMinimizingReasoner getReasoner(BooleanExpression context,
			boolean useBackwardsSubstitution) {
		return factory.getReasoner(context, useBackwardsSubstitution,
				proverPredicates);
	}
}
