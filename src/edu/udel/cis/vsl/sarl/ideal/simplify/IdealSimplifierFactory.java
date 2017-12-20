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

import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.ideal.IF.IdealFactory;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.simplify.IF.Simplifier;
import edu.udel.cis.vsl.sarl.simplify.IF.SimplifierFactory;

/**
 * A factory for producing new instances of {@link OldIdealSimplifier}.
 * 
 * @author Stephen F. Siegel (siegel)
 */
public class IdealSimplifierFactory implements SimplifierFactory {

	/**
	 * Should we use the new {@link Context}? Eventually the old simplifier
	 * will go away, at which point this field should be removed.
	 */
	public final static boolean useNewSimplifier = true;

	/**
	 * A structure which packages references to several other factories and
	 * commonly-used objects that will be used by the {@link OldIdealSimplifier}s
	 * produced by this factory.
	 */
	private SimplifierInfo info;

	/**
	 * Constructs new {@link IdealSimplifierFactory} based on the given
	 * {@link IdealFactory} and {@link PreUniverse}.
	 * 
	 * @param idealFactory
	 *            the factory used for producing "ideal" mathematical symbolic
	 *            expressions
	 * @param universe
	 *            the symbolic universe for producing general symbolic
	 *            expressions
	 */
	public IdealSimplifierFactory(IdealFactory idealFactory,
			PreUniverse universe) {
		info = new SimplifierInfo(universe, idealFactory);
		info.universe = universe;
		info.affineFactory = new AffineFactory(idealFactory);
		info.booleanFactory = idealFactory.booleanFactory();
		info.falseExpr = (BooleanExpression) universe.bool(false);
		info.trueExpr = (BooleanExpression) universe.bool(true);
		info.idealFactory = idealFactory;
		info.numberFactory = universe.numberFactory();
		info.out = System.out;
		info.verbose = false; // true;
	}

	@Override
	public Simplifier newSimplifier(BooleanExpression assumption) {
		if (useNewSimplifier)
			return new IdealSimplifier(info, assumption);
		else
			return new OldIdealSimplifier(info, assumption);
	}

}
