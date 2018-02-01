package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.HashMap;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.ThreadLocalRandom;
import java.util.function.Consumer;

import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.ideal.IF.Polynomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Primitive;
import edu.udel.cis.vsl.sarl.ideal.simplify.ConcurrentRandomPoint32Evaluator.RandomPoint32Evaluation;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;

public class ConcurrentRandomPoint32Evaluator
		implements Consumer<RandomPoint32Evaluation> {
	private final Polynomial poly;
	private final Primitive ps[];
	private final PreUniverse universe;

	public ConcurrentRandomPoint32Evaluator(Polynomial poly, Primitive ps[],
			PreUniverse universe) {
		this.poly = poly;
		this.ps = ps;
		this.universe = universe;
	}

	public static class RandomPoint32Evaluation {
		private NumericExpression result = null;

		public NumericExpression value() {
			assert result != null;
			return result;
		}

		public void setValue(NumericExpression value) {
			this.result = value;
		}
	}

	@Override
	public void accept(RandomPoint32Evaluation t) {
		Map<SymbolicExpression, SymbolicExpression> map = new HashMap<>();
		Random random = ThreadLocalRandom.current();

		for (Primitive p : ps) {
			int randomInt = random.nextInt();
			SymbolicExpression concrete = p.type().isInteger()
					? universe.integer(randomInt)
					: universe.rational(randomInt);

			map.put(p, concrete);
		}

		t.setValue(
				(NumericExpression) universe.mapSubstituter(map).apply(poly));
	}
}
