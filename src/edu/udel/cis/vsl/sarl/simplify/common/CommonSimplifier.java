package edu.udel.cis.vsl.sarl.simplify.common;

import java.io.PrintStream;

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
	 * The symbolic universe used to make new expressions.
	 */
	protected PreUniverse universe;

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

	// Methods specified in {@link Simplifier} ...

	@Override
	public PreUniverse universe() {
		return universe;
	}

}
