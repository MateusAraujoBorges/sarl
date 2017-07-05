package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.simplify.IF.Range;

public class SubContext extends Context2 {

	private Context2 superContext;

	public SubContext(Context2 superContext) {
		super(superContext.info);
		this.superContext = superContext;
	}

	public SubContext(Context2 superContext, BooleanExpression assumption) {
		this(superContext);
		this.originalAssumption = assumption;
		initialize(assumption);
	}

	@Override
	protected Map<Monic, Number> getMonicConstantMap() {
		Map<Monic, Number> map = superContext.getMonicConstantMap();

		addMonicConstantsToMap(map); // overwrites any previous entries
		return map;
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

	public ContextIF getSuperContext() {
		return superContext;
	}

}
