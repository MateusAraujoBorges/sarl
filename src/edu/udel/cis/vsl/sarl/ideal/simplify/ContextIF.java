package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.simplify.IF.Range;

/**
 * An object which provides some constraints on symbolic expressions and which
 * can be used as a "simplification context" when simplifying expressions.
 * 
 * @author siegel
 *
 */
public interface ContextIF {

	SimplifierInfo getInfo();

	BooleanExpression getOriginalAssumption();

	/**
	 * Retrieves the range associated to <code>key</code>.
	 * 
	 * @param key
	 *            a non-<code>null</code> {@link Monic}
	 * @return the range associated to <code>key</code> or <code>null</code> if
	 *         there is no such range
	 */
	Range getRange(Monic key);

	SymbolicExpression getSub(SymbolicExpression key);

	SymbolicObject getSimplification(SymbolicObject key);

	void cacheSimplification(SymbolicObject key, SymbolicObject value);

	void clearSimplificationCache();

	Range computeRange(NumericExpression expression);

	Map<Monic, Number> getMonicConstantMap();

	SymbolicExpression simplify(SymbolicExpression expr);

	BooleanExpression getReducedAssumption();

	BooleanExpression getFullAssumption();

	boolean isInconsistent();
	
	boolean isInitialized();

}
