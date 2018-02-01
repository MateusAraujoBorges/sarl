package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.io.PrintStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Random;

import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.IF.object.NumberObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;

/**
 * An object used to determine whether an expression is equivalent to 0 within
 * some probability. Real type only. Integer type should be easier.
 * 
 * @author siegel
 */
public class FastEvaluator3 {

	/**
	 * Print debugging output?
	 */
	public final static boolean debug = false;

	/**
	 * Where to print the debugging output.
	 */
	public final static PrintStream out = System.out;

	/**
	 * The number factory.
	 */
	private NumberFactory nf;

	/**
	 * The root node of the tree.
	 */
	final EvalNode root;

	/**
	 * The number of variable nodes in the tree.
	 */
	protected int numVars;

	/**
	 * The variable nodes in the tree.
	 */
	protected VarNode[] varNodes;

	/**
	 * Upper bound on total degree of the original polynomial after expansion.
	 */
	protected IntegerNumber totalDegree;

	protected Map<Monomial, EvalNode> exprMap = new HashMap<>();

	private ArrayList<VarNode> varNodeList = new ArrayList<>();

	// any value from 1 to 32, except for 31. Why? Because
	// range of int is [-2^31,2^31-1]. For r less
	// than 32, the domain is [0,2^r) and must be specified
	// using an int 2^r. The case r=32 is special and the domain
	// is all ints.
	private int randBits = 32;

	/**
	 * 2^randBits, or -1.
	 */
	private int randBound;

	/**
	 * The number of elements in the random domain. The random number generator
	 * chooses one element from that domain ... all with equal probability.
	 */
	private RationalNumber randSize;

	/**
	 * Random number generator ---- produces sequence of random Java {@code int}
	 * s.
	 */
	private Random random;

	/**
	 * 
	 * @param random
	 *            a random number generator
	 * @param nf
	 *            the number factory
	 * @param monomial
	 *            the monomial being tested for zero-ness
	 * @param totalDegree
	 *            an upper bound on the total degree of the monomial after
	 *            expansion
	 */
	public FastEvaluator3(Random random, NumberFactory nf, Monomial monomial,
			IntegerNumber totalDegree) {
		if (debug) {
			out.println("FastEvaluator3: testing zero-ness of");
			monomial.printCompressedTree(out);
			out.println();
			out.println("Total degree: " + totalDegree);
			assert totalDegree == monomial.totalDegree(nf);
		}
		this.random = random;
		this.nf = nf;
		this.root = makeNode(monomial);
		this.numVars = varNodeList.size();
		this.varNodes = varNodeList.toArray(new VarNode[numVars]);
		this.totalDegree = totalDegree;
		if (randBits < 1 || randBits == 31 || randBits > 32) {
			throw new SARLException("Illegal randBits: " + randBits);
		} else if (randBits < 31) {
			this.randBound = 1 << randBits;
			this.randSize = nf.rational(nf.integer(randBound));
		} else if (randBits == 32) {
			this.randBound = -1;
			this.randSize = nf.rational(nf.power(nf.integer(2), 32));
		}
		// out.println("FAST3: randBoundNumber = " + randSize);
	}

	/**
	 * Constructs a new fast evaluator, computing the total degree of the
	 * monomial.
	 * 
	 * @param random
	 * @param nf
	 * @param monomial
	 */
	public FastEvaluator3(Random random, NumberFactory nf, Monomial monomial,
			SimplifierInfo info) {
		this(random, nf, monomial, monomial.totalDegree(nf));
	}

	private EvalNode makeNode(Monomial expr) {
		EvalNode result = exprMap.get(expr);

		if (result != null)
			return result;

		switch (expr.operator()) {
		case ADD: {
			int numArgs = expr.numArguments();
			EvalNode[] children = new EvalNode[numArgs];

			for (int i = 0; i < numArgs; i++)
				children[i] = makeNode((Monomial) expr.argument(i));
			result = new AddNode(children);
			break;
		}
		case MULTIPLY: {
			int numArgs = expr.numArguments();
			EvalNode[] children = new EvalNode[numArgs];

			for (int i = 0; i < numArgs; i++)
				children[i] = makeNode((Monomial) expr.argument(i));
			result = new MultiplyNode(children);
			break;
		}
		case CONCRETE: {
			RationalNumber number = (RationalNumber) ((NumberObject) expr
					.argument(0)).getNumber();
			Rat rat = new Rat(number);

			result = new ConstantNode(rat);
			break;
		}
		case POWER: {
			SymbolicObject exp = expr.argument(1);

			if (exp instanceof NumberObject) {
				EvalNode base = makeNode((Monomial) expr.argument(0));
				IntegerNumber expNum = (IntegerNumber) ((NumberObject) exp)
						.getNumber();

				result = new PowerNode(base, expNum.bigIntegerValue());
				break;
			}
			// flow right into default case...
		}
		default: // variable
			result = new VarNode();
			varNodeList.add((VarNode) result);
		}
		exprMap.put(expr, result);
		return result;
	}

	private void next() {
		for (int i = 0; i < varNodes.length; i++) {
			int randomInt = randBits == 32 ? random.nextInt()
					: random.nextInt(randBound);
			BigInteger big = new BigInteger("" + randomInt);
			Rat value = new Rat(big);

			this.varNodes[i].setValue(value);
		}
	}

	/**
	 * Attempts to determine if the expression represented by this object is
	 * equivalent to zero, with probability of error at most {@code epsilon}.
	 * 
	 * @param epsilon
	 *            upper bound on probability of error (e.g., 1/2^{128}).
	 * @return if this method returns {@code false}, the expression is not
	 *         equivalent to zero, otherwise, it probably is equivalent to zero
	 */
	public boolean isZero(RationalNumber epsilon) {
		RationalNumber prob = nf.oneRational();
		RationalNumber ratio = nf.divide(nf.rational(totalDegree), randSize);

		do {
			next();
			if (!root.evaluate().isZero())
				return false;
			prob = nf.multiply(prob, ratio);
		} while (nf.compare(epsilon, prob) < 0);
		return true;
	}

	/**
	 * Print all kinds of informations of the polynomial tree
	 * 
	 * @param ps
	 */
	public void printTreeInformation(PrintStream ps) {
		ps.printf(
				"depth     #vars     degree     #descents(b)            #compressed_descents        \n");
		ps.printf("%-10d%-10d%-11d", root.depth(), numVars,
				totalDegree.intValue());
		ps.printf("%-24.6f %-20d\n",
				((double) root.numDescendants() / 1000000000), exprMap.size());
	}
}
