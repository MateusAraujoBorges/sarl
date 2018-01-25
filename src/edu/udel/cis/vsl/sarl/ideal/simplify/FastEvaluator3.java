package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.io.PrintStream;
import java.math.BigInteger;
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
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.number.RationalNumber;
import edu.udel.cis.vsl.sarl.IF.object.NumberObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Primitive;

/**
 * Object used to evaluate a polynomial. Real type only. Integer type should be
 * easier.
 * 
 * @author siegel
 *
 */
public class FastEvaluator3 {

	public final static boolean debug = true;

	public final static PrintStream out = System.out;

	/**
	 * Mutable infinite precision rational number.
	 * 
	 * @author siegel
	 *
	 */
	class Rat {
		BigInteger a; // numerator
		BigInteger b; // denominator

		Rat(BigInteger a, BigInteger b) {
			this.a = a;
			this.b = b;
			normalize();
		}

		Rat(BigInteger a) {
			this.a = a;
			this.b = BigInteger.ONE;
		}

		Rat(Rat that) {
			a = that.a;
			b = that.b;
		}

		Rat(RationalNumber num) {
			a = num.numerator();
			b = num.denominator();
		}

		private void normalize() {
			int signum = b.signum();

			if (signum == 0) {
				throw new ArithmeticException("Division by 0");
			}
			// ensures any negation is in numerator
			if (signum < 0) {
				a = a.negate();
				b = b.negate();
			}
			// canonical form for 0 is 0/1 :
			if (a.signum() == 0) {
				b = BigInteger.ONE;
			} else if (!b.equals(BigInteger.ONE)) {
				BigInteger gcd = a.gcd(b);

				if (!gcd.equals(BigInteger.ONE)) {
					a = a.divide(gcd);
					b = b.divide(gcd);
				}
			}
		}

		// void set(Rat that) {
		// a = that.a;
		// b = that.b;
		// }

		void add(Rat that) {
			a = a.multiply(that.b).add(b.multiply(that.a));
			b = b.multiply(that.b);
			normalize();
		}

		void multiply(Rat that) {
			a = a.multiply(that.a);
			b = b.multiply(that.b);
			normalize();
		}

		void power(int exponent) {
			a = a.pow(exponent);
			b = b.pow(exponent);
			// no need to normalize: (a,b)=1 --> (a^e,b^e)=1
		}

		void power(BigInteger exp) {
			try {
				power(exp.intValueExact());
				return;
			} catch (ArithmeticException e) {
				throw new SARLException("to be implemented");
				// need basic implementation using multiplication
			}
		}

		boolean isZero() {
			return a.signum() == 0;
		}
	}

	abstract class EvalNode {

		protected NumericExpression expr; // for debugging

		protected Rat value = null;

		protected List<EvalNode> parents = new LinkedList<>();

		protected int evalCount = 0; // number of times evaluate called

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

		abstract Rat evaluate();

		Rat clearOnCount() {
			evalCount++;
			if (evalCount == parents.size()) {
				Rat result = value;

				value = null;
				return result;
			} else {
				return value;
			}
		}
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

		Rat evaluate() {
			if (value == null) {
				value = new Rat(children[0].evaluate());
				for (int i = 1; i < children.length; i++)
					value.add(children[i].evaluate());
			}
			return clearOnCount();
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

		Rat evaluate() {
			if (value == null) {
				value = new Rat(children[0].evaluate());
				for (int i = 1; i < children.length; i++)
					value.multiply(children[i].evaluate());
			}
			return clearOnCount();
		}
	}

	class PowerNode extends EvalNode {
		private EvalNode base;
		private BigInteger exponent;

		PowerNode(NumericExpression expr, EvalNode base, BigInteger exponent) {
			super(expr);
			this.base = base;
			this.exponent = exponent;
			base.addParent(this);
		}

		Rat evaluate() {
			if (value == null) {
				value = new Rat(base.evaluate());
				value.power(exponent);
			}
			return clearOnCount();
		}
	}

	class ConstantNode extends EvalNode {

		ConstantNode(NumericExpression expr, Rat value) {
			super(expr);
			this.value = value;
		}

		Rat evaluate() {
			return value;
		}
	}

	class VarNode extends EvalNode {

		VarNode(Primitive primitive) {
			super(primitive);
		}

		public void setValue(Rat value) {
			this.value = value;
			for (EvalNode parent : getParents()) {
				parent.nullifyValue();
			}
		}

		Rat evaluate() {
			return value;
		}
	}

	private NumberFactory nf;

	// private boolean isInteger;

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

	public FastEvaluator3(Random random, NumberFactory nf, Monomial monomial,
			IntegerNumber totalDegree) {
		this.random = random;
		this.nf = nf;
		// this.isInteger = monomial.type().isInteger();
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
		out.println("FAST3: randBoundNumber = " + randSize);
	}

	public FastEvaluator3(Random random, NumberFactory nf, Monomial monomial) {
		this(random, nf, monomial, monomial.totalDegree(nf));
	}

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
			RationalNumber number = (RationalNumber) ((NumberObject) expr
					.argument(0)).getNumber();
			Rat rat = new Rat(number);

			result = new ConstantNode(expr, rat);
			break;
		}
		case POWER: {
			// depends: int object or real
			SymbolicObject exp = expr.argument(1);

			if (exp instanceof NumberObject) {
				EvalNode base = makeNode((Monomial) expr.argument(0));
				IntegerNumber expNum = (IntegerNumber) ((NumberObject) exp)
						.getNumber();

				result = new PowerNode(expr, base, expNum.bigIntegerValue());
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

}
