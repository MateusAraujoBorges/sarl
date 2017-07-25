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

/**
 * A structured representation of a set of {@link Monic}s. The {@link Monic}s
 * are divided into two types: integer and real. In each case, the {@link Monic}
 * s are ordered in an array, the order coming from the
 * {@link IdealFactory#monicComparator()}. Each monic is assigned an ID number,
 * unique among the monics of its type in this set. The numbers start from 0.
 * There are methods to go back and forth between the ID numbers and the
 * {@link Monic}s, and other methods.
 * 
 * This representation is build in a series of stages. First, it is instantiated
 * and the set of monics is empty. Then, the client invokes method
 * {@link #addKeys(Set)} some number of times to add {@link Monic}s to this set.
 * There may be repeated entries; entries after the first will simply be
 * ignored. When the client is finished, it must call {@link #finish()}. Then it
 * can use the other methods to get ID numbers, etc.
 * 
 * @author siegel
 */
public class LinearVariableSet {

	/**
	 * The factory used to get the total order on the {@link Monic}s.
	 */
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

	/**
	 * Sort and organize the monics that have been added to this set. Should be
	 * called only after all keys have been added using method
	 * {@link #addKeys(Set)}.
	 */
	public void finish() {
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

	/**
	 * Computes the number of {@link Monic}s of real type in this set.
	 * 
	 * @return the number of {@link Monic}s of real type in this set
	 */
	public int numRealMonics() {
		return realMonics.length;
	}

	/**
	 * Computes the number of {@link Monic}s of integer type in this set.
	 * 
	 * @return the number of {@link Monic}s of integer type in this set
	 */
	public int numIntMonics() {
		return intMonics.length;
	}

	/**
	 * Given a {@link Monic} {@code key} of integer type in this set, returns
	 * its ID number.
	 * 
	 * @param key
	 *            a {@link Monic} of integer type that has been added to this
	 *            set
	 * @return the ID number of {@code key}
	 */
	public int getIntId(Monic key) {
		return intIdMap.get(key);
	}

	/**
	 * Given a {@link Monic} {@code key} of real type in this set, returns its
	 * ID number.
	 * 
	 * @param key
	 *            a {@link Monic} of real type that has been added to this set
	 * @return the ID number of {@code key}
	 */
	public int getRealId(Monic key) {
		return realIdMap.get(key);
	}

	/**
	 * Returns the array of all {@link Monic}s of integer type in this set,
	 * sorted by increasing order of {@link Monic}. This set is backed by the
	 * array, so don't modify the array.
	 * 
	 * @return the sorted array of integer {@link Monic}s in this set
	 */
	public Monic[] getIntMonics() {
		return intMonics;
	}

	/**
	 * Returns the array of all {@link Monic}s of real type in this set, sorted
	 * by increasing order of {@link Monic}. This set is backed by the array, so
	 * don't modify the array.
	 * 
	 * @return the sorted array of real {@link Monic}s in this set
	 */
	public Monic[] getRealMonics() {
		return realMonics;
	}

}
