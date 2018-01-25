package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Random;

import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.IF.object.NumberObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Primitive;

/**
 * Object used to evaluate a polynomial .
 * 
 * @author siegel
 *
 */
public class FastEvaluator2 {

	public final static boolean debug = true;

	public final static PrintStream out = System.out;

	abstract class EvalNode {

		protected NumericExpression expr; // for debugging

		protected Number value = null;

		protected List<EvalNode> parents = new LinkedList<>();

		public EvalNode(NumericExpression expr) {
			this.expr = expr;
		}

		void addParent(EvalNode parent) {
			parents.add(parent);
		}

		Collection<EvalNode> getParents() {
			return parents;
		}

		void nullifyValue() {
			if (value != null) {
				value = null;
				for (EvalNode parent : parents)
					parent.nullifyValue();
			}
		}

		abstract Number evaluate();

	}

	class AddNode extends EvalNode {
		private EvalNode[] children;

		AddNode(NumericExpression expr, EvalNode[] children) {
			super(expr);
			assert children.length >= 1;
			this.children = children;
			for (EvalNode child : children)
				child.addParent(this);
		}

		Number evaluate() {
			if (value == null) {
				value = children[0].evaluate();
				for (int i = 1; i < children.length; i++)
					value = nf.add(value, children[i].evaluate());
			}
			return value;
		}
	}

	class MultiplyNode extends EvalNode {
		private EvalNode[] children;

		MultiplyNode(NumericExpression expr, EvalNode[] children) {
			super(expr);
			assert children.length >= 1;
			this.children = children;
			for (EvalNode child : children)
				child.addParent(this);
		}

		Number evaluate() {
			if (value == null) {
				value = children[0].evaluate();
				for (int i = 1; i < children.length; i++)
					value = nf.multiply(value, children[i].evaluate());
			}
			return value;
		}
	}

	class PowerNode extends EvalNode {
		private EvalNode base;
		private IntegerNumber exponent;

		PowerNode(NumericExpression expr, EvalNode base,
				IntegerNumber exponent) {
			super(expr);
			assert exponent.numericalCompareTo(nf.integer(2)) >= 0;
			this.base = base;
			this.exponent = exponent;
			base.addParent(this);
		}

		Number evaluate() {
			if (value == null) {
				value = nf.power(base.evaluate(), exponent);
			}
			return value;
		}
	}

	class ConstantNode extends EvalNode {

		ConstantNode(NumericExpression expr, Number value) {
			super(expr);
			this.value = value;
		}

		Number evaluate() {
			return value;
		}
	}

	class VarNode extends EvalNode {

		VarNode(Primitive primitive) {
			super(primitive);
		}

		public void setValue(Number value) {
			this.value = value;
			for (EvalNode parent : getParents()) {
				parent.nullifyValue();
			}
		}

		Number evaluate() {
			return value;
		}
	}

	private NumberFactory nf;

	private boolean isInteger;

	private EvalNode root;

	private int numVars;

	private VarNode[] varNodes;

	private IntegerNumber totalDegree;

	private Map<Monomial, EvalNode> exprMap = new HashMap<>();

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

	private Random random;

	public FastEvaluator2(Random random, NumberFactory nf, Monomial monomial,
			IntegerNumber totalDegree) {
		this.random = random;
		this.nf = nf;
		this.isInteger = monomial.type().isInteger();
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
		out.println("randBound = " + randBound);
		out.println("randBoundNumber = " + randSize);
	}

	public FastEvaluator2(Random random, NumberFactory nf, Monomial monomial) {
		this(random, nf, monomial, monomial.totalDegree(nf));
	}

	// private void print(IntegerNumber[] array) {
	// int n = array.length;
	//
	// out.print("[");
	// for (int i = 0; i < n; i++) {
	// if (i > 0)
	// out.print(",");
	// out.print(array[i]);
	// }
	// out.print("]");
	// }

	@SuppressWarnings("unused")
	private void print(int[] array) {
		int n = array.length;

		out.print("[");
		for (int i = 0; i < n; i++) {
			if (i > 0)
				out.print(",");
			out.print(array[i]);
		}
		out.print("]");
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
			result = new AddNode(expr, children);
			break;
		}
		case MULTIPLY: {
			int numArgs = expr.numArguments();
			EvalNode[] children = new EvalNode[numArgs];

			for (int i = 0; i < numArgs; i++)
				children[i] = makeNode((Monomial) expr.argument(i));
			result = new MultiplyNode(expr, children);
			break;
		}
		case CONCRETE: {
			result = new ConstantNode(expr,
					((NumberObject) expr.argument(0)).getNumber());
			break;
		}
		case POWER: {
			// depends: int object or real
			SymbolicObject exp = expr.argument(1);

			if (exp instanceof NumberObject) {
				EvalNode base = makeNode((Monomial) expr.argument(0));

				result = new PowerNode(expr, base,
						(IntegerNumber) ((NumberObject) exp).getNumber());
				break;
			}
			// flow right into default case...
		}
		default: // variable
			result = new VarNode((Primitive) expr);
			varNodeList.add((VarNode) result);
		}
		exprMap.put(expr, result);
		return result;
	}

	private void next() {
		for (int i = 0; i < varNodes.length; i++) {
			int randomInt = randBits == 32 ? random.nextInt()
					: random.nextInt(randBound);
			Number value = isInteger ? nf.integer(randomInt)
					: nf.rational(nf.integer(randomInt));

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

}
