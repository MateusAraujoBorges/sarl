package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.util.Pair;

public class LinearVariableSet {

	private IdealFactory idealFactory;

	/**
	 * The set of integer "variables" in the system of linear equations.
	 */
	private Set<Monic> intMonicSet = new HashSet<Monic>();

	/**
	 * The set of real "variables" in the system of linear equations.
	 */
	private Set<Monic> realMonicSet = new HashSet<Monic>();

	/**
	 * The elements of {@link #intMonicSet}, ordered using the total order on
	 * {@link Monic}s provided by the {@link IdealFactory#monicComparator()}.
	 */
	private Monic[] intMonics;

	/**
	 * The elements of {@link #realMonicSet}, ordered using the total order on
	 * {@link Monic}s provided by the {@link IdealFactory#monicComparator()}.
	 */
	private Monic[] realMonics;

	/**
	 * Maps an integer {@link Monic} to its index in the array
	 * {@link #intMonics}.
	 */
	private Map<Monic, Integer> intIdMap;

	/**
	 * Maps a real {@link Monic} to its index in the array {@link #realMonics}.
	 */
	private Map<Monic, Integer> realIdMap;

	public LinearVariableSet(IdealFactory idealFactory) {
		this.idealFactory = idealFactory;
	}

	/**
	 * Extracts the monics that are used in the map and initializes data
	 * structures. The following are initialized: {@link #intMonicSet},
	 * {@link #realMonicSet}, {@link #intMonics}, {@link #realMonics},
	 * {@link #intIdMap}, {@link #realIdMap}.
	 */
	public Pair<Integer, Integer> addKeys(Set<Monic> monicSet) {
		int numIntConstraints = 0, numRealConstraints = 0;

		for (Monic key : monicSet) {
			Set<Monic> monics;

			if (key.type().isInteger()) {
				numIntConstraints++;
				monics = intMonicSet;

			} else {
				numRealConstraints++;
				monics = realMonicSet;
			}
			for (Monomial term : key.termMap(idealFactory)) {
				Monic monic = term.monic(idealFactory);

				// polynomials should not have constant term:
				assert !monic.isOne();
				monics.add(monic);
			}
		}
		return new Pair<>(numIntConstraints, numRealConstraints);
	}

	public void finalize() {
		int numIntMonics, numRealMonics, i;

		numIntMonics = intMonicSet.size();
		numRealMonics = realMonicSet.size();
		intMonics = new Monic[numIntMonics];
		realMonics = new Monic[numRealMonics];
		intIdMap = new HashMap<Monic, Integer>(numIntMonics);
		realIdMap = new HashMap<Monic, Integer>(numRealMonics);

		i = 0;
		for (Monic monic : intMonicSet)
			intMonics[i++] = monic;
		i = 0;
		for (Monic monic : realMonicSet)
			realMonics[i++] = monic;
		Arrays.sort(intMonics, idealFactory.monicComparator());
		Arrays.sort(realMonics, idealFactory.monicComparator());
		for (i = 0; i < numIntMonics; i++)
			intIdMap.put(intMonics[i], i);
		for (i = 0; i < numRealMonics; i++)
			realIdMap.put(realMonics[i], i);
	}
	
	public int numRealMonics() {
		return realMonics.length;
	}
	
	public int numIntMonics() {
		return intMonics.length;
	}
	
	public int getIntId(Monic key) {
		return intIdMap.get(key);
	}
	
	public int getRealId(Monic key) {
		return realIdMap.get(key);
	}
	
	public Monic[] getIntMonics() {
		return intMonics;
	}
	
	public Monic[] getRealMonics() {
		return realMonics;
	}

}
