package edu.udel.cis.vsl.sarl.simplify.common;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject.SymbolicObjectKind;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicSequence;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.simplify.IF.Simplifier;

/**
 * A partial implementation of {@link Simplifier}. This class uses a partial
 * implementation of {@link SimplifierWorker} to simplify symbolic expressions
 * in a generic way.
 * 
 * @author siegel
 */
public abstract class CommonSimplifier implements Simplifier {

	// Static fields...

	/**
	 * Where to print debugging information.
	 */
	public final static PrintStream out = System.out;

	/**
	 * Print general debugging information?
	 */
	public final static boolean debug = false;

	/**
	 * Keeps count of the number of simplifications performed, for performance
	 * debugging.
	 */
	public static int simplifyCount = 0;

	// Instance fields...

	/**
	 * Cached simplification results. A key is some canonic symbolic object, and
	 * the value is the canonic, simplified version of that object.
	 */
	private Map<SymbolicObject, SymbolicObject> simplifyMap = new HashMap<SymbolicObject, SymbolicObject>();

	/**
	 * The symbolic universe used to make new expressions.
	 */
	protected PreUniverse universe;

	protected UnaryOperator<SymbolicExpression> boundCleaner;

	/**
	 * Factory used for producing {@link SymbolicSequence}s.
	 */
	protected ObjectFactory objectFactory;

	/**
	 * Constructs new {@link CommonSimplifier} with given universe and with
	 * {@link #objectFactory} obtained from universe.
	 * 
	 * @param universe
	 *            the universe that will be used to construct new expressions
	 */
	public CommonSimplifier(PreUniverse universe) {
		assert universe != null;
		this.universe = universe;
		this.boundCleaner = universe.newBoundCleaner();
		this.objectFactory = universe.objectFactory();
	}

	// Abstract methods ...

	/**
	 * The method that will be used to produce a new worker to simplify a
	 * symbolic expression. It will be invoked each time {@link #apply} is
	 * called. Typically, the client is expected to extend
	 * {@link CommonSimplifierWorker} and implement this method to produce an
	 * instance of that extended
	 * 
	 * @return a new worker that will be used to simplify a symbolic expression
	 */
	protected abstract CommonSimplifierWorker newWorker();

	// Protected methods ...

	protected SymbolicObject getCachedSimplification(SymbolicObject key) {
		return simplifyMap.get(key);
	}

	protected SymbolicObject cacheSimplification(SymbolicObject key,
			SymbolicObject value) {
		assert key.isCanonic();
		assert value.isCanonic();
		return simplifyMap.put(key, value);
	}

	protected void clearSimplificationCache() {
		simplifyMap.clear();
	}

	// Methods specified in {@link Simplifier} ...

	@Override
	public SymbolicExpression apply(SymbolicExpression x) {
		// some optimizations...no need to create new worker in these
		// basic cases...
		if (x.isNull())
			return x;

		SymbolicOperator operator = x.operator();

		if (operator == SymbolicOperator.CONCRETE) {
			SymbolicObject object = (SymbolicObject) x.argument(0);
			SymbolicObjectKind kind = object.symbolicObjectKind();

			switch (kind) {
			case BOOLEAN:
			case INT:
			case NUMBER:
			case STRING:
				return x;
			default:
			}
		}
		simplifyCount++;
		// rename bound variables with counts starting from where the
		// original assumption renaming left off. This ensures that
		// all bound variables in the assumption and x are unique, but
		// two different x's can have same bound variables (thus
		// improving canonicalization)...
		x = universe.cloneBoundCleaner(boundCleaner).apply(x);
		return newWorker().simplifyExpression(x);
	}

	@Override
	public PreUniverse universe() {
		return universe;
	}

}
