package edu.udel.cis.vsl.sarl.ideal.simplify;

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.simplify.IF.Range;

public class SubContext extends Context2 {

	private ContextIF superContext;

	public SubContext(SimplifierInfo info, ContextIF superContext) {
		super(info);
		this.superContext = superContext;
	}

	public SubContext(SimplifierInfo info, ContextIF superContext,
			BooleanExpression assumption) {
		this(info, superContext);
		initialize(assumption);
	}

	@Override
	public Range getRange(Monic monic) {
		Range result = super.getRange(monic);

		if (result != null)
			return result;
		result = superContext.getRange(monic);
		return result;
	}

	@Override
	public SymbolicExpression getSub(SymbolicExpression key) {
		SymbolicExpression result = super.getSub(key);

		if (result != null)
			return result;
		result = superContext.getSub(key);
		return result;
	}

}
