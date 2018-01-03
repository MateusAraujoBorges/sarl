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
package edu.udel.cis.vsl.sarl.reason.IF;

import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProverFactory;
import edu.udel.cis.vsl.sarl.prove.why3.RobustWhy3ProvePlatformFactory;
import edu.udel.cis.vsl.sarl.reason.common.ContextMinimizingReasonerFactory;
import edu.udel.cis.vsl.sarl.simplify.IF.SimplifierFactory;

/**
 * Provides a static method for producing a new {@link ReasonerFactory}.
 * 
 * @author siegel
 *
 */
public class Reason {

	/**
	 * Create a reasoner factory
	 * 
	 * @param universe
	 *            A reference to a {@link PreUniverse}
	 * @param simplifierFactory
	 *            A reference to a {@link SimplifierFactory}
	 * @param proverFactory
	 *            A reference to a {@link TheoremProverFactory}
	 * @param why3Factory
	 *            A reference to a {@link RobustWhy3ProvePlatformFactory},
	 *            optional, can be null.
	 * @return
	 */
	public static ReasonerFactory newReasonerFactory(PreUniverse universe,
			SimplifierFactory simplifierFactory,
			TheoremProverFactory proverFactory,
			RobustWhy3ProvePlatformFactory why3Factory) {
		ReasonerFactory result = new ContextMinimizingReasonerFactory(universe,
				proverFactory, simplifierFactory, why3Factory);

		return result;
	}
}
