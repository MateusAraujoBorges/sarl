package edu.udel.cis.vsl.sarl.reason.common;

import java.util.Map;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;

import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.prove.IF.ProverFunctionInterpretation;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProverFactory;
import edu.udel.cis.vsl.sarl.prove.why3.RobustWhy3ProvePlatformFactory;
import edu.udel.cis.vsl.sarl.reason.IF.ReasonerFactory;
import edu.udel.cis.vsl.sarl.simplify.IF.SimplifierFactory;

/**
 * A factory that generates new {@link Why3Reasoner}s. For a unique pair of a
 * boolean typed context and a set of {@link ProverFunctionInterpretation}s (see
 * {@link Why3ReasonerCacheKey} as well), there is suppose to be only one
 * Why3Reasoner object.
 * 
 * @author ziqing
 *
 */
public class Why3ReasonerFactory extends ContextMinimizingReasonerFactory
		implements ReasonerFactory {

	/**
	 * Cached results of previous creation of Why3 @{link Reasoner}s. The idea
	 * is to have at most one Why3 {@link Reasoner} for each boolean expression
	 * ("context").
	 */
	private Map<Why3ReasonerCacheKey, Why3Reasoner> why3ReasonerCache = null;

	/**
	 * Factory used to produce new why3 provers, which will be used by the
	 * reasoners to check validity. why3 is a prove platform and is suppose to
	 * be more expensive than other provers
	 */
	private TheoremProverFactory why3Factory = null;

	public Why3ReasonerFactory(PreUniverse universe,
			SimplifierFactory simplifierFactory,
			RobustWhy3ProvePlatformFactory why3Factory) {
		super(universe, why3Factory, simplifierFactory);
		this.why3Factory = why3Factory;
		why3ReasonerCache = new ConcurrentHashMap<>();
	}

	@Override
	public TheoremProverFactory getTheoremProverFactory() {
		return why3Factory;
	}

	@Override
	public Why3Reasoner getReasoner(BooleanExpression context,
			boolean useBackwardSubstitution,
			ProverFunctionInterpretation[] proverPredicates) {
		TreeSet<ProverFunctionInterpretation> ppredSetOfKey = new TreeSet<>();

		for (ProverFunctionInterpretation ppred : proverPredicates)
			ppredSetOfKey.add(ppred);

		Why3ReasonerCacheKey key = new Why3ReasonerCacheKey(context,
				ppredSetOfKey);
		Why3Reasoner result = why3ReasonerCache.get(key);

		if (result == null) {
			Why3Reasoner newReasoner = new Why3Reasoner(this, context,
					useBackwardSubstitution, proverPredicates);

			result = why3ReasonerCache.putIfAbsent(key, newReasoner);
			return result == null ? newReasoner : result;
		}
		return result;
	}

	/**
	 * The key of cached {@link Why3Reasoner}s
	 * 
	 * @author ziqing
	 *
	 */
	private static class Why3ReasonerCacheKey {
		final private BooleanExpression context;

		final private TreeSet<ProverFunctionInterpretation> proverPredicates;

		Why3ReasonerCacheKey(BooleanExpression context,
				TreeSet<ProverFunctionInterpretation> proverPredicates) {
			this.context = context;
			this.proverPredicates = proverPredicates;
		}

		@Override
		public int hashCode() {
			return context.hashCode() ^ proverPredicates.hashCode() ^ 3063907;
		}

		@Override
		public boolean equals(Object obj) {
			if (obj instanceof Why3ReasonerCacheKey) {
				Why3ReasonerCacheKey otherKey = (Why3ReasonerCacheKey) obj;

				if (otherKey.context.equals(context))
					return proverPredicates.equals(otherKey.proverPredicates);
			}
			return false;
		}
	}
}
