/*******************************************************************************
 * Copyright (c) 2013 Stephen F. Siegel, University of Delaware.
 * 
 * This file is part of SARL.
 * 
 * SARL is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free
 * Software Foundation, either version 3 of the License, or (at your option) any
 * later version.
 * 
 * SARL is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE. See the GNU Lesser General Public License for more
 * details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with SARL. If not, see <http://www.gnu.org/licenses/>.
 ******************************************************************************/
package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.util.Map;
import java.util.Map.Entry;

import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.ideal.IF.Monic;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Polynomial;
import edu.udel.cis.vsl.sarl.util.Pair;

/**
 * <p>
 * A class used to simplify a constant map. This take as input a map which
 * associates constant values to {@link Monic}s. Some of these monics may be
 * instances of {@link Polynomial}, in which case they will be in
 * pseudo-primitive form: no constant term, leading coefficient is positive,
 * leading coefficient is 1 (for real type), or GCD of absolute value of
 * coefficients is 1 (for integer type). We will use the word "polynomial" to
 * refer to all entries in the map, whether or not they are instances of
 * {@link Polynomial}. The {@link Monic}s which are not instances of
 * {@link Polynomial} may be considered a polynomial with one term which has a
 * coefficient of 1.
 * </p>
 * 
 * <p>
 * It simplifies this map by performing Gaussian elimination (aka, Gauss-Jordan
 * elimination) on the coefficient matrix formed by the terms, i.e., the
 * "variables" are considered to be the {@link Monic}s which occur in the terms
 * and the "coefficients" are the monomial coefficients of those {@link Monic}s.
 * </p>
 * 
 * <p>
 * Specifically, it separates out the integer and the real entries and works on
 * each separately. In each case, it constructs a matrix in which the rows
 * correspond to map entries and columns correspond to the monics of the terms
 * (of the appropriate type) which occur anywhere in the map. The entry in a
 * column is the coefficient of that monic in the polynomial which occurs as the
 * key in the map entry. It then performs Gaussian elimination on these matrices
 * to reduce to reduced row echelon form. It then re-constructs the maps in this
 * reduced form.
 * </p>
 * 
 * <p>
 * There is an extra column on the right of the matrix for the constant
 * associated to the polynomial.
 * </p>
 * 
 * <p>
 * If an inconsistency exists ( for example, X+Y maps to 0, X maps to 0, Y maps
 * to 1) in the map, this will be discovered in the elimination. In this case,
 * the object returned has a boolean field which indicates the inconsistency
 * exists. Another field indicates whether any non-trivial change was made.
 * </p>
 * 
 * <p>
 * The interface for this class are the three static methods
 * {@link #reduceConstantMap(IdealFactory, Map)},
 * {@link #reduceConstantMap(IdealFactory, Map, Map) and
 * {@link #reduceRelativeConstantMap(IdealFactory, Map, Map, Map)}. The latter
 * performs a relative form of simplification. Everything else is private.
 * </p>
 */
public class OldLinearSolver {

	// Public static members: the interface for this class...

	/**
	 * An object providing information on the result of a linear reduction.
	 * 
	 * @author siegel
	 */
	public static class LinearSolverInfo {

		/**
		 * Is it the case that the output map is not equal to the input map?
		 */
		public boolean change = false;

		/**
		 * Was the map not determined to be inconsistent? This field is only
		 * used if {@link #change} is {@code true}. If there is no change,
		 * consistency is not checked.
		 */
		public boolean consistent = true;

		/**
		 * Construct new instance from given two fields.
		 * 
		 * @param change
		 *            output map differs from input map?
		 * @param consistent
		 *            no inconsistency discovered?
		 */
		public LinearSolverInfo(boolean change, boolean consistent) {
			this.change = change;
			this.consistent = consistent;
		}
	}

	/**
	 * Given a constant map, performs Gauss-Jordan Elimination to produce the
	 * new equivalent map in a reduced, simplified form. The map is viewed as a
	 * matrix in which there is one row for each entry, the monic of that entry
	 * is interpreted as a linear combination of monics, and a final column
	 * represents the constant value of that monic.
	 * 
	 * @param idealFactory
	 *            the numeric factory used to deconstruct and construct
	 *            polynomials, etc.
	 * @param inMap
	 *            the given map, mapping a monic to a number which is the known
	 *            value of that monic. This map will not be modified.
	 * @param outMap
	 *            the resulting simplified map. This should be an empty map at
	 *            entry; it will be populated by this method if there is any
	 *            change to make to the original map. If there is no change, the
	 *            {@code outMap} will not be modified.
	 * @return a {@link LinearSolverInfo} object which provides information on
	 *         the result of the simplification
	 */
	public static LinearSolverInfo reduceConstantMap(IdealFactory idealFactory,
			Map<Monic, Number> inMap, Map<Monic, Number> outMap) {
		LinearVariableSet keySet = new LinearVariableSet(idealFactory);
		Pair<Integer, Integer> sizes = keySet.addKeys(inMap.keySet());

		keySet.finish();

		OldLinearSolver solver = new OldLinearSolver(idealFactory, keySet,
				inMap, sizes);
		NumberFactory numberFactory = idealFactory.numberFactory();
		boolean change = numberFactory.gaussianElimination(solver.intMatrix);

		change = numberFactory.gaussianElimination(solver.realMatrix) || change;
		if (change) {
			boolean consistent = solver.rebuildMaps(outMap);

			return new LinearSolverInfo(true, consistent);
		} else {
			return new LinearSolverInfo(false, true);
		}
	}

	/**
	 * Performs simplification of a constant map in place. Same as
	 * {@link #reduceConstantMap(IdealFactory, Map, Map)}, but there is only one
	 * map, which is modified.
	 * 
	 * @param idealFactory
	 *            the numeric factory used to deconstruct and construct
	 *            polynomials, etc.
	 * @param map
	 *            the constant map, mapping a monic to a number which is the
	 *            known value of that monic. This map may be modified.
	 * @return a {@link LinearSolverInfo} object which provides information on
	 *         the result of the simplification
	 */
	public static LinearSolverInfo reduceConstantMap(IdealFactory idealFactory,
			Map<Monic, Number> map) {
		LinearVariableSet keySet = new LinearVariableSet(idealFactory);
		Pair<Integer, Integer> sizes = keySet.addKeys(map.keySet());

		keySet.finish();

		OldLinearSolver solver = new OldLinearSolver(idealFactory, keySet, map,
				sizes);
		NumberFactory numberFactory = idealFactory.numberFactory();
		boolean change = numberFactory.gaussianElimination(solver.intMatrix);

		change = numberFactory.gaussianElimination(solver.realMatrix) || change;
		if (change) {
			map.clear();

			boolean consistent = solver.rebuildMaps(map);

			return new LinearSolverInfo(true, consistent);
		} else {
			return new LinearSolverInfo(false, true);
		}
	}

	/**
	 * Performs a reduction of constant map {@code map2} relative to
	 * {@code map1}. The equations of {@code map1} are considered to be the
	 * background context and are used to simplify the equations of {@code map2}
	 * ; {@code map1} is not modified. This uses method
	 * {@link NumberFactory#relativeGaussianElimination(RationalNumber[][], RationalNumber[][])}
	 * .
	 * 
	 * @param idealFactory
	 *            the numeric factory used to deconstruct and construct
	 *            polynomials, etc.
	 * @param map1
	 *            the background constant map; will not be modified.
	 * @param map2
	 *            the constant map that should be simplified against the
	 *            background of {@code map1}; will not be modified.
	 * @param out2
	 *            the result of simplifying {@code map2}. Should be initially
	 *            empty. Will only be modified if change is made (as indicated
	 *            in the {@link LinearSolverInfo#change} returned by this
	 *            method).
	 * 
	 * @return a {@link LinearSolverInfo} object which provides information on
	 *         the result of the simplification
	 */
	public static LinearSolverInfo reduceRelativeConstantMap(
			IdealFactory idealFactory, Map<Monic, Number> map1,
			Map<Monic, Number> map2, Map<Monic, Number> out2) {
		NumberFactory numberFactory = idealFactory.numberFactory();
		LinearVariableSet keySet = new LinearVariableSet(idealFactory);
		Pair<Integer, Integer> sizes1 = keySet.addKeys(map1.keySet());
		Pair<Integer, Integer> sizes2 = keySet.addKeys(map2.keySet());
		keySet.finish();

		OldLinearSolver solver1 = new OldLinearSolver(idealFactory, keySet,
				map1, sizes1);
		OldLinearSolver solver2 = new OldLinearSolver(idealFactory, keySet,
				map2, sizes2);
		boolean change = numberFactory.relativeGaussianElimination(
				solver1.intMatrix, solver2.intMatrix);

		change = numberFactory.relativeGaussianElimination(solver1.realMatrix,
				solver2.realMatrix) || change;
		if (change) {
			boolean consistent = solver2.rebuildMaps(out2);

			return new LinearSolverInfo(true, consistent);
		} else {
			return new LinearSolverInfo(false, true);
		}
	}

	// Private instance fields ...

	/**
	 * The number factory used to perform infinite precision rational
	 * arithmetic.
	 */
	private NumberFactory numberFactory;

	/**
	 * The factory used to manipulate {@link Monic}s, {@link Polynomial}s, etc.
	 */
	private IdealFactory idealFactory;

	/**
	 * An organized view of a set of "variables", which are actually
	 * {@link Monic}s. Places a total order on the set, assigns an ID number to
	 * each element, and so on.
	 */
	private LinearVariableSet keySet;

	/**
	 * The matrix of coefficients in the integer system of equations. There is
	 * one row for each integer constraint, and one column for each integer
	 * "variable" (actually, a {@link Monic}), and one additional column for the
	 * right hand side of the equation.
	 */
	private RationalNumber[][] intMatrix;

	/**
	 * The matrix of coefficients in the real system of equations. There is one
	 * row for each real constraint, and one column for each real "variable"
	 * (actually, a {@link Monic}), and one additional column for the right hand
	 * side of the equation.
	 */
	private RationalNumber[][] realMatrix;

	/**
	 * The number of integer entries in {@link #map}.
	 */
	private int numIntConstraints = 0;

	/**
	 * The number of real entries in {@link #map}.
	 */
	private int numRealConstraints = 0;

	// Constructor ...

	/**
	 * <p>
	 * Constructs new instance with given fields. The maps is analyzed and used
	 * to produce an integer matrix of coefficients {@link #intMatrix} and a
	 * real matrix of coefficients {@link #realMatrix}.
	 * </p>
	 * 
	 * <p>
	 * While the {@code numConstraints} can be determined from the {@code map},
	 * they are provided here for performance reasons since they were probably
	 * already computed earlier, so no need to re-compute them.
	 * </p>
	 * 
	 * <p>
	 * The map is not modified.
	 * </p>
	 * 
	 * @param idealFactory
	 *            the factory used to manipulate {@link Monic}s,
	 *            {@link Polynomial}s, etc.
	 * 
	 * @param keySet
	 *            an organized view of a set of "variables", which are actually
	 *            {@link Monic}s. Places a total order on the set, assigns an ID
	 *            number to each element, and so on. This key set must contain
	 *            at least all the variables occurring in {@code map}, but it
	 *            may contain more variables
	 * @param map
	 *            the map that is being reduced; will not be modified
	 * @param numConstraints
	 *            a pair in which the left component is the number of integer
	 *            entries in {@code map} and the right component is the number
	 *            of real entrie.
	 */
	private OldLinearSolver(IdealFactory idealFactory, LinearVariableSet keySet,
			Map<Monic, Number> map, Pair<Integer, Integer> numConstraints) {
		this.idealFactory = idealFactory;
		this.numberFactory = idealFactory.numberFactory();
		this.keySet = keySet;
		this.numIntConstraints = numConstraints.left;
		this.numRealConstraints = numConstraints.right;
		buildMatrices(map);
	}

	// Private methods...

	/**
	 * Builds the matrix representations of the maps. For the integer
	 * constraints, there is one row for each integer entry in the map and one
	 * column for each monic which occurs as a term in some key, of integer
	 * type, plus one additional column to hold the value associated to the
	 * constant value associated to the map entry. The real map is similar.
	 * 
	 * @param map
	 *            the constant map that is to be reduced. It will be used to
	 *            build the {@link #intMatrix} and {@link #realMatrix}.
	 * 
	 */
	private void buildMatrices(Map<Monic, Number> map) {
		int numIntMonics = keySet.numIntMonics();
		int numRealMonics = keySet.numRealMonics();
		int intConstraintId = 0, realConstraintId = 0;

		intMatrix = new RationalNumber[numIntConstraints][numIntMonics + 1];
		realMatrix = new RationalNumber[numRealConstraints][numRealMonics + 1];
		for (int i = 0; i < numIntConstraints; i++)
			for (int j = 0; j < numIntMonics; j++)
				intMatrix[i][j] = numberFactory.zeroRational();
		for (int i = 0; i < numRealConstraints; i++)
			for (int j = 0; j < numRealMonics; j++)
				realMatrix[i][j] = numberFactory.zeroRational();
		for (Entry<Monic, Number> entry : map.entrySet()) {
			Monic key = entry.getKey();
			Number value = entry.getValue();

			if (key.type().isInteger()) {
				intMatrix[intConstraintId][numIntMonics] = numberFactory
						.rational(value);
				for (Monomial term : key.termMap(idealFactory)) {
					Monic monic = term.monic(idealFactory);
					Number coefficient = term.monomialConstant(idealFactory)
							.number();

					intMatrix[intConstraintId][keySet.getIntId(
							monic)] = numberFactory.rational(coefficient);
				}
				intConstraintId++;
			} else {
				realMatrix[realConstraintId][numRealMonics] = (RationalNumber) value;

				for (Monomial term : key.termMap(idealFactory)) {
					Monic monic = term.monic(idealFactory);
					Number coefficient = term.monomialConstant(idealFactory)
							.number();

					realMatrix[realConstraintId][keySet
							.getRealId(monic)] = (RationalNumber) coefficient;
				}
				realConstraintId++;
			}
		}
	}

	/**
	 * Experimental method of Ziqing; builds a matrix m for a linear system. see
	 * {@link #buildMatrices()}.
	 * 
	 * Modify m to m' so that the column c which represents the given
	 * "leadingMonic" will be the first column and the a row r has a non-zero
	 * value at c will be the first row.
	 * 
	 * If the "leadingMonic" doesn't exist, m == m'<br>
	 * If such a row r doesn't exist, m == m'
	 * 
	 * @param leadingMonic
	 */
	private void buildMatrices(Monic leadingMonic, Map<Monic, Number> map) {
		buildMatrices(map);

		int originalIdx = -1, nonzeroRow = -1, numRow;
		boolean isInteger = leadingMonic.type().isInteger();
		RationalNumber[][] matrix = isInteger ? intMatrix : realMatrix;
		Monic[] columns = isInteger ? keySet.getIntMonics()
				: keySet.getRealMonics();

		numRow = matrix.length;
		for (int i = 0; i < columns.length; i++)
			if (columns[i].equals(leadingMonic))
				originalIdx = i;
		if (originalIdx < 0)
			return;
		for (int i = 0; i < numRow; i++)
			if (!matrix[i][originalIdx].isZero())
				nonzeroRow = i;
		if (nonzeroRow < 0)
			return;

		// switch columns:
		Monic tmpMonic = columns[originalIdx];

		columns[originalIdx] = columns[0];
		columns[0] = tmpMonic;
		// switch columns of matrix:
		for (int i = 0; i < numRow; i++) {
			RationalNumber tmpColumn = matrix[i][originalIdx];

			matrix[i][originalIdx] = matrix[i][0];
			matrix[i][0] = tmpColumn;
		}

		// switch rows:
		RationalNumber[] tmp = matrix[nonzeroRow];

		matrix[nonzeroRow] = matrix[0];
		matrix[0] = tmp;
	}

	/**
	 * Adds to {@link #map} entries corresponding to the rows of the
	 * {@link #intMatrix}.
	 * 
	 * @param map
	 *            the map to modify; entries are added to it corresponding to
	 *            the rows in the {@link #intMatrix}
	 * 
	 * @return {@code false} if an inconsistency is discovered, else
	 *         {@code true}
	 */
	private boolean rebuildIntMap(Map<Monic, Number> map) {
		Monic[] intMonics = keySet.getIntMonics();
		int numIntMonics = intMonics.length;

		for (int i = 0; i < numIntConstraints; i++) {
			Monomial poly = idealFactory.zeroInt();
			IntegerNumber lcm = numberFactory.oneInteger();

			// clear the denominators in row i by multiplying
			// every entry in the row by the LCM
			for (int j = 0; j <= numIntMonics; j++) {
				RationalNumber a = intMatrix[i][j];

				if (!a.isZero()) {
					IntegerNumber denominator = numberFactory.denominator(a);

					if (!denominator.isOne())
						lcm = numberFactory.lcm(lcm, denominator);
				}
			}
			for (int j = 0; j < numIntMonics; j++) {
				RationalNumber a = intMatrix[i][j];

				if (!a.isZero()) {
					IntegerNumber coefficient = numberFactory
							.multiply(numberFactory.numerator(a), numberFactory
									.divide(lcm, numberFactory.denominator(a)));

					poly = idealFactory.addMonomials(poly,
							idealFactory.monomial(
									idealFactory.constant(coefficient),
									intMonics[j]));
				}
			}

			IntegerNumber value = numberFactory.multiply(
					numberFactory.numerator(intMatrix[i][numIntMonics]),
					numberFactory.divide(lcm, numberFactory
							.denominator(intMatrix[i][numIntMonics])));

			if (poly.isZero()) {
				if (!value.isZero()) { // inconsistency
					return false;
				}
			} else {
				Monic key;

				if (poly instanceof Monic) {
					key = (Monic) poly;
				} else {
					IntegerNumber c = (IntegerNumber) poly
							.monomialConstant(idealFactory).number();

					if (!numberFactory
							.mod((IntegerNumber) numberFactory.abs(value),
									(IntegerNumber) numberFactory.abs(c))
							.isZero()) {
						return false; // inconsistency
					}
					key = poly.monic(idealFactory);
					value = numberFactory.divide(value, c);
				}
				map.put(key, value);
			}
		}
		return true;
	}

	/**
	 * Adds to {@link #map} entries corresponding to the rows of the
	 * {@link #realMatrix}.
	 * 
	 * @param map
	 *            the map to modify
	 * 
	 * @return {@code false} if an inconsistency is discovered, else
	 *         {@code true}
	 */
	private boolean rebuildRealMap(Map<Monic, Number> map) {
		Monic[] realMonics = keySet.getRealMonics();
		int numRealMonics = realMonics.length;

		for (int i = 0; i < numRealConstraints; i++) {
			Monomial poly = idealFactory.zeroReal();
			RationalNumber value = realMatrix[i][numRealMonics];

			for (int j = 0; j < numRealMonics; j++) {
				RationalNumber a = realMatrix[i][j];

				if (a.signum() != 0) {
					poly = idealFactory.addMonomials(poly, idealFactory
							.monomial(idealFactory.constant(a), realMonics[j]));
				}
			}
			if (poly.isZero()) {
				if (!value.isZero()) { // inconsistency
					return false;
				}
			} else {
				// leading coefficient is 1 because of reduced row-echelon form
				// there is no constant term, so poly is in pseudo-primitive
				// form
				Monic key;

				if (poly instanceof Monic) {
					key = (Monic) poly;
				} else {
					key = poly.monic(idealFactory);
					value = (RationalNumber) numberFactory.divide(value,
							poly.monomialConstant(idealFactory).number());
				}
				map.put(key, value);
			}
		}
		return true;
	}

	/**
	 * Experimental method of Ziqing.
	 * 
	 * Build a new {@link Map<Monic, Monic>} from the old {@link Map<Monic,
	 * Number>}.
	 * 
	 * The basic idea is : For a general row in the reduced row echelon matrix:
	 * <code>
	 * 0, ..., t, a<sub>0</sub>, a<sub>1</sub>, ..., a<sub>n</sub>, c
	 * </code>
	 * 
	 * The key of the entry is t. The value of the entry is all right-hand side
	 * polynomials: e.g.
	 * <code>c - (a<sub>0</sub> + a<sub>1</sub> + ... + a<sub>n</sub>)</code>
	 * 
	 * @param output
	 * @return
	 */
	private boolean buildIntMap(Map<Monic, Monic> output) {
		Monic[] intMonics = keySet.getIntMonics();
		int numIntMonics = intMonics.length;

		for (int i = 0; i < numIntConstraints; i++) {
			Monomial rhs = idealFactory.zeroInt();
			Monomial leading = idealFactory.zeroInt();
			IntegerNumber lcm = numberFactory.oneInteger();
			int leadingCol = -1;

			// clear the denominators in row i by multiplying
			// every entry in the row by the LCM
			for (int j = i; j <= numIntMonics; j++) {
				RationalNumber a = intMatrix[i][j];

				if (!a.isZero()) {
					IntegerNumber denominator = numberFactory.denominator(a);

					if (leadingCol < 0)
						leadingCol = j;
					if (!denominator.isOne())
						lcm = numberFactory.lcm(lcm, denominator);
				}
			}

			// The i-th row can be represented as:
			// 0, .. 0, leading, a_0, a_1, ..., a_n = c
			// What we need is leading = c - a_0 - a_1 - ... - a_n.
			for (int j = leadingCol; j < numIntMonics; j++) {
				RationalNumber a = intMatrix[i][j];

				if (!a.isZero()) {
					IntegerNumber coefficient = numberFactory
							.multiply(numberFactory.numerator(a), numberFactory
									.divide(lcm, numberFactory.denominator(a)));

					if (j == leadingCol)
						leading = idealFactory.addMonomials(leading,
								idealFactory.monomial(
										idealFactory.constant(coefficient),
										intMonics[j]));
					else
						rhs = idealFactory.addMonomials(rhs,
								idealFactory.monomial(
										idealFactory.constant(coefficient),
										intMonics[j]));
				}
			}

			IntegerNumber constant = numberFactory.multiply(
					numberFactory.numerator(intMatrix[i][numIntMonics]),
					numberFactory.divide(lcm, numberFactory
							.denominator(intMatrix[i][numIntMonics])));

			// check consistency:
			if (rhs.isZero() && leading.isZero())
				if (!constant.isZero())
					return false;
			// t = c - rhs:
			rhs = idealFactory.multiplyConstantMonomial(
					idealFactory.intConstant(-1), rhs);
			rhs = idealFactory.addMonomials(idealFactory.constant(constant),
					rhs);

			// put the entry:
			Monic key;
			Monic value;

			if (leading instanceof Monic) {
				key = (Monic) leading;
				value = rhs.monic(idealFactory);
			} else {
				IntegerNumber keyConstant = (IntegerNumber) leading
						.monomialConstant(idealFactory).number();
				IntegerNumber rhsConstant = (IntegerNumber) rhs
						.monomialConstant(idealFactory).number();

				// The equivalent consistency checking as the one in
				// "rebuildIntMap":
				// polynomial * c == n where n % c must be 0.
				// TODO: However, is this condition correct ?
				// If there is "polynomial * 2 == 3", 3 % 2 != 0 and you cannot
				// reduce it to "polynomial == 3 / 2" because we are now in a
				// integer context.
				if (!numberFactory
						.mod((IntegerNumber) numberFactory.abs(rhsConstant),
								(IntegerNumber) numberFactory.abs(keyConstant))
						.isZero()) {
					return false; // inconsistency
				}
				key = leading.monic(idealFactory);
				value = rhs.monic(idealFactory);
			}
			output.put(key, value);
		}
		return true;
	}

	/**
	 * Experimental method of Ziqing.
	 * 
	 * The method does the same thing as {@link #buildIntMap(Map)} but for real
	 * numbers
	 */
	private boolean buildRealMap(Map<Monic, Monic> output) {
		Monic[] realMonics = keySet.getRealMonics();
		int numRealMonics = realMonics.length;

		for (int i = 0; i < numRealConstraints; i++) {
			Monomial rhs = idealFactory.zeroReal();
			Monomial leading = idealFactory.zeroReal();
			RationalNumber constant = realMatrix[i][numRealMonics];
			int leadingCol = -1;

			for (int j = i; j < numRealMonics; j++) {
				RationalNumber a = realMatrix[i][j];

				if (a.signum() != 0) {
					if (leadingCol < 0) {
						leadingCol = j;
						leading = idealFactory.monomial(
								idealFactory.constant(a), realMonics[j]);
					} else
						rhs = idealFactory.addMonomials(rhs,
								idealFactory.monomial(idealFactory.constant(a),
										realMonics[j]));
				}
			}
			if (rhs.isZero() && leading.isZero()) {
				if (!constant.isZero()) { // inconsistency
					return false;
				}
			} else {
				// leading coefficient is 1 because of reduced row-echelon form
				// there is no constant term, so poly is in pseudo-primitive
				// form
				Monic key;
				Monic value;
				RationalNumber negOne = numberFactory
						.negate(numberFactory.oneRational());

				rhs = idealFactory.monomial(idealFactory.constant(negOne),
						rhs.monic(idealFactory));
				value = idealFactory
						.addMonomials(idealFactory.constant(constant), rhs)
						.monic(idealFactory);

				if (rhs instanceof Monic) {
					key = (Monic) rhs;
				} else
					key = leading.monic(idealFactory);
				output.put(key, value);
			}
		}
		return true;
	}

	/**
	 * Experimental method added by Ziqing.
	 * 
	 * @param output
	 * @param leadingMonic
	 * @return
	 */
	@SuppressWarnings("unused")
	private boolean reduce(Map<Monic, Number> map, Map<Monic, Monic> output,
			Monic leadingMonic) {
		// Step 1: extract monics. Uses map. Yields intIdMap, realIdMap,
		// intMonics, realMonics.

		// Step 2: build matrices. Uses intIdMap, realIdMap, intMonics,
		// realMonics, map. Yields intMatrix[][], realMatrix[][].

		// Step 3. perform Gauss-Jordan elimination on matrices.

		// Step 4. build a new output map. Uses map, intMonics, realMonics,
		// intMatrix, realMatrix.

		// keySet = new LinearVariableSet(idealFactory);

		Pair<Integer, Integer> numbers = keySet.addKeys(map.keySet());

		numIntConstraints = numbers.left;
		numRealConstraints = numbers.right;
		keySet.finish();
		if (leadingMonic != null)
			buildMatrices(leadingMonic, map);
		else
			buildMatrices(map);
		map.clear();
		numberFactory.gaussianElimination(intMatrix);
		numberFactory.gaussianElimination(realMatrix);
		if (!buildIntMap(output))
			return false;
		if (!buildRealMap(output))
			return false;
		return true;
	}

	/**
	 * Invokes {@link #rebuildIntMap(Map)} and {@link #buildRealMap(Map)} on the
	 * given map. Does not clear the given map first. Typically, {@code output}
	 * will be empty when this method is called.
	 * 
	 * @return {@code false} if an inconsistency is discovered, else
	 *         {@code true}
	 */
	private boolean rebuildMaps(Map<Monic, Number> output) {
		return rebuildIntMap(output) && rebuildRealMap(output);
	}
}
