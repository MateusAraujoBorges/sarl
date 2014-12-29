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
package edu.udel.cis.vsl.sarl.prove.cvc;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;

import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.config.ProverInfo;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.prove.Prove;
import edu.udel.cis.vsl.sarl.prove.IF.TheoremProver;
import edu.udel.cis.vsl.sarl.util.FastList;

/**
 * An implementation of {@link TheoremProver} using the automated theorem prover
 * CVC4, and in which CVC4 is run in a separate process for each query.
 * Transforms a theorem proving query into the language of CVC4, invokes CVC4
 * through its command line interface, and interprets the output.
 * 
 * @author siegel
 */
public class RobustCVC4TheoremProver implements TheoremProver {

	// more robust preconditioning: rename all symbolic constants
	// find out which parts of the assumption are relevant.
	// canonicalize order of symbolic constants:

	// consider assumption as conjunction of boolean expressions (b).
	// undirected graph:
	// nodes: all free (not bound) symbolic constants occurring in
	// the predicate and assumption.
	// edges: {u,v} if for some b, u,v occur in b.
	// N0=all free symbolic constants occurring in the predicate
	// (N,E)=all nodes, edges reachable from N0 in graph.
	// ignore: all edges, nodes not in (N,E).

	// This is common to all theorem provers.
	// step 1: given context, store it as now in TheoremProver
	// step 2: when predicate comes in, perform graph computation,
	// yielding reduced context (for this predicate).
	// step 3: canonicalize variable names across both reduced
	// context and predicate, using graph structure.
	// order N0 (put predicate in BNF, use type, etc).
	// then order edges in graph
	// (by kind of constraint, degree, etc.). This puts total
	// order on DFS o

	// ************************** Static Fields *************************** //

	public final static String prompt = "CVC4> ";

	public final static char[] promptChars = prompt.toCharArray();

	public final static PrintStream err = System.err;

	// ****************************** Fields ****************************** //

	private ProverInfo info;

	private ProcessBuilder processBuilder;

	/**
	 * The symbolic universe used for managing symbolic expressions. Initialized
	 * by constructor and never changes.
	 */
	private PreUniverse universe;

	/**
	 * The translation of the given context to a CVC4 expression. Created once
	 * during instantiation and never modified.
	 */
	private CVC4Translator assumptionTranslator;

	// *************************** Constructors *************************** //

	/**
	 * Constructs new CVC4 theorem prover with given symbolic universe.
	 * 
	 * @param universe
	 *            the controlling symbolic universe
	 * @param context
	 *            the assumption(s) the prover will use for queries
	 */
	RobustCVC4TheoremProver(PreUniverse universe, BooleanExpression context,
			ProverInfo info) {
		assert universe != null;
		assert context != null;
		assert info != null;
		this.universe = universe;
		this.info = info;
		// The following is apparently necessary since the same bound symbolic
		// constant can be used in different scopes in the context; CVC4
		// requires that these map to distinct variables.
		context = (BooleanExpression) universe.cleanBoundVariables(context);
		this.assumptionTranslator = new CVC4Translator(universe, context);
		// set up process builder with command
		// also try "--use-theory=idl"
		// make these options part of the config?
		this.processBuilder = new ProcessBuilder(info.getPath()
				.getAbsolutePath(), "--rewrite-divk", "--quiet",
				"--interactive", "--lang=cvc4");
	}

	@Override
	public PreUniverse universe() {
		return universe;
	}

	private ValidityResult readCVCOutput(BufferedReader in) {
		try {
			String line = in.readLine();

			// debug:
			// System.out.println(line);
			// System.out.flush();
			line = line.replace(prompt, "");
			line = line.trim();
			if ("valid".equals(line))
				return Prove.RESULT_YES;
			if ("invalid".equals(line))
				return Prove.RESULT_NO;
			if (info.getShowInconclusives()) {
				StringBuffer sb = new StringBuffer(line);
				int promptpos = 0;
				int read;

				sb.append('\n');
				while (true) {
					read = in.read();
					if (read == -1)
						break;
					if (read == promptChars[promptpos]) {
						promptpos++;
						if (promptpos >= promptChars.length)
							break;
					} else {
						for (int j = 0; j < promptpos; j++)
							sb.append(promptChars[j]);
						promptpos = 0;
						sb.append((char) read);
					}
				}
				err.println("CVC4 inconclusive with message: " + sb);
			}
			return Prove.RESULT_MAYBE;
		} catch (IOException e) {
			if (info.getShowErrors())
				err.println("I/O error reading CVC4 output: " + e.getMessage());
			return Prove.RESULT_MAYBE;
		}
	}

	@Override
	public ValidityResult valid(BooleanExpression predicate) {
		// TODO: clean bound vars on predicate?
		PrintStream out = universe.getOutputStream();
		int id = universe.numProverValidCalls();
		FastList<String> assumptionDecls = assumptionTranslator
				.getDeclarations();
		FastList<String> assumptionText = assumptionTranslator.getTranslation();
		Process process = null;
		ValidityResult result;
		boolean show = universe.getShowProverQueries() || info.getShowQueries();

		universe.incrementProverValidCount();
		if (show) {
			out.println();
			out.print("CVC4 assumptions " + id + ":\n");
			assumptionDecls.print(out);
			assumptionText.print(out);
			out.flush();
		}
		try {
			process = processBuilder.start();
		} catch (IOException e) {
			if (info.getShowErrors())
				err.println("I/O exception reading CVC4 output: "
						+ e.getMessage());
			result = Prove.RESULT_MAYBE;
		}

		PrintStream stdin = new PrintStream(process.getOutputStream());
		BufferedReader stdout = new BufferedReader(new InputStreamReader(
				process.getInputStream()));

		assumptionDecls.print(stdin);
		stdin.print("ASSERT ");
		assumptionText.print(stdin);
		stdin.println(";");

		CVC4Translator translator = new CVC4Translator(assumptionTranslator,
				predicate);
		FastList<String> predicateDecls = translator.getDeclarations();
		FastList<String> predicateText = translator.getTranslation();

		predicateDecls.print(stdin);
		stdin.print("QUERY ");
		predicateText.print(stdin);
		stdin.println(";\n");
		stdin.flush();
		if (show) {
			out.print("\nCVC4 predicate   " + id + ":\n");
			predicateDecls.print(out);
			predicateText.print(out);
			out.println();
			out.flush();
		}
		result = readCVCOutput(stdout);
		if (show) {
			out.println("CVC4 result      " + id + ": " + result);
			out.flush();
		}
		if (process != null)
			process.destroy();
		return result;
	}

	@Override
	public ValidityResult validOrModel(BooleanExpression predicate) {
		return Prove.RESULT_MAYBE;
	}

	@Override
	public String toString() {
		return "RobustCVC4TheoremProver";
	}
}
