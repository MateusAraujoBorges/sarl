package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.io.PrintStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Random;

import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
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
	public final static boolean debug = true;

	/**
	 * Where to print the debugging output.
	 */
	public final static PrintStream out = System.out;

	/**
	 * A mutable infinite precision rational number.
	 * 
	 * @author siegel
	 */
	class Rat {
		BigInteger a; // numerator
		BigInteger b; // denominator

		/**
		 * Construct new rational number from numerator a and denominator b.
		 * Place it into canonical form: b>0; a/b=0 iff (a=0 and b=1);
		 * gcd(a,b)=1.
		 * 
		 * @param a
		 *            the numerator
		 * @param b
		 *            the denominator
		 */
		Rat(BigInteger a, BigInteger b) {
			this.a = a;
			this.b = b;
			normalize();
		}

		/**
		 * Constructs new rational number a=a/1.
		 * 
		 * @param a
		 *            the big integer value
		 */
		Rat(BigInteger a) {
			this.a = a;
			this.b = BigInteger.ONE;
		}

		/**
		 * Constructs new rational number copying the numerator and denominator
		 * from the given rational number.
		 * 
		 * @param that
		 *            the other rational number
		 */
		Rat(Rat that) {
			a = that.a;
			b = that.b;
		}

		/**
		 * Constructs new rational number from a SARL {@link RationalNumber},
		 * which uses the same canonical form. (The reason why we aren't using
		 * SARL {@link RationalNumber}s is because they are all flyweighted
		 * (cached), which is too expensive for the huge numbers we need in this
		 * class.)
		 * 
		 * @param that
		 *            the SARL number to copy
		 */
		Rat(RationalNumber that) {
			a = that.numerator();
			b = that.denominator();
		}

		/**
		 * Places this rational number into canonic form.
		 */
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

		/**
		 * Add that number to this one. Modifies this number so that its new
		 * value is the sum of its old value and that. Does not modify that.
		 * 
		 * @param that
		 *            the other value
		 */
		void add(Rat that) {
			a = a.multiply(that.b).add(b.multiply(that.a));
			b = b.multiply(that.b);
			normalize();
		}

		/**
		 * Modifies this number so that its new value is the product of its old
		 * value and that. Does not modify that.
		 * 
		 * @param that
		 *            the other value
		 */
		void multiply(Rat that) {
			a = a.multiply(that.a);
			b = b.multiply(that.b);
			normalize();
		}

		/**
		 * Modifies this number by raising it to the {@code exponent} power.
		 * 
		 * @param exponent
		 *            a positive int
		 */
		void power(int exponent) {
			a = a.pow(exponent);
			b = b.pow(exponent);
			// no need to normalize: (a,b)=1 --> (a^e,b^e)=1
		}

		/**
		 * Modifies this number by raising it to the {@code exp} power.
		 * 
		 * @param exp
		 *            a positive big integer
		 */
		void power(BigInteger exp) {
			try {
				power(exp.intValueExact());
				return;
			} catch (ArithmeticException e) {
				throw new SARLException("to be implemented");
				// need basic implementation using multiplication
			}
		}

		/**
		 * Is this rational number equal to 0?
		 * 
		 * @return {@code true} iff this is 0
		 */
		boolean isZero() {
			return a.signum() == 0;
		}
	}

	/**
	 * A node in the "tree" used to represent the polynomial. Leaf nodes are
	 * either constants or variables. Non-leaf nodes represent either addition,
	 * multiplication, or exponentiation. It's not really a tree, because we
	 * allow sharing. So it's a DAG.
	 * 
	 * @author siegel
	 *
	 */
	abstract class EvalNode {

		/**
		 * The cached result of evaluating this node.
		 */
		protected Rat value = null;

		/**
		 * The parent nodes of this node, i.e., all nodes in the tree that have
		 * this node as a child. (So, it isn't really a tree.)
		 */
		protected List<EvalNode> parents = new LinkedList<>();

		/**
		 * The number of times method {@link #evaluate()} has been called.
		 */
		protected int evalCount = 0;

		protected int hashCode = -1;

		/**
		 * Add the given node to the parent list of this node.
		 * 
		 * @param parent
		 *            the node to make a parent
		 */
		void addParent(EvalNode parent) {
			parents.add(parent);
		}

		/**
		 * Returns the set of parents.
		 * 
		 * @return the parents of this node
		 */
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

		/**
		 * Computes the value of this node, a concrete rational number. Might
		 * return a cached value.
		 * 
		 * @return the result of evaluating this node
		 */
		abstract Rat evaluate();

		/**
		 * Increments the evaluation count; if that count then equals the number
		 * of parents of this node, sets the {@link #value} to {@code null} so
		 * the {@link BigInteger}s can be swept up by the garbage collector.
		 * 
		 * @return the {@link #value} in the pre-state (before possibly setting
		 *         it to {@code null})
		 */
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

		int depth() {
			return 1;
		}

		long numDescendants() {
			return 1;
		}

		public int numChildren() {
			return 0;
		}

		public EvalNode[] getChildren() {
			return null;
		}

		public abstract SymbolicOperator operator();

	}

	/**
	 * A node representing the sum of its children.
	 * 
	 * @author siegel
	 */
	class AddNode extends EvalNode {
		private EvalNode[] children;

		private int depth = -1;

		private long numDescendants = -1;

		AddNode(EvalNode[] children) {
			assert children.length >= 1;
			this.children = children;
			for (EvalNode child : children)
				child.addParent(this);
		}

		@Override
		Rat evaluate() {
			if (value == null) {
				value = new Rat(children[0].evaluate());
				for (int i = 1; i < children.length; i++)
					value.add(children[i].evaluate());
			}
			return clearOnCount();
		}

		@Override
		int depth() {
			if (depth < 0) {
				int maxChildDepth = 0;

				for (EvalNode child : children) {
					int childDepth = child.depth();

					maxChildDepth = childDepth > maxChildDepth ? childDepth
							: maxChildDepth;
				}
				depth = 1 + maxChildDepth;
			}
			return depth;
		}

		@Override
		long numDescendants() {
			if (numDescendants < 0) {
				numDescendants = children.length;

				for (int i = 0; i < children.length; i++)
					numDescendants += children[i].numDescendants();
			}
			return numDescendants;
		}

		@Override
		public int hashCode() {
			if (hashCode == -1) {
				int[] childrenHashCodes = new int[children.length];

				for (int i = 0; i < children.length; i++)
					childrenHashCodes[i] = children[i].hashCode();
				hashCode = 1777773
						* (Arrays.hashCode(childrenHashCodes)
								^ SymbolicOperator.ADD.hashCode())
						+ parents.size();
			}
			return hashCode;
		}

		@Override
		public SymbolicOperator operator() {
			return SymbolicOperator.ADD;
		}

		@Override
		public int numChildren() {
			return children.length;
		}

		@Override
		public EvalNode[] getChildren() {
			return children;
		}
	}

	/**
	 * A node representing the product of its children
	 * 
	 * @author siegel
	 */
	class MultiplyNode extends EvalNode {
		private EvalNode[] children;

		private int depth = -1;

		private long numDescendants = -1;

		MultiplyNode(EvalNode[] children) {
			assert children.length >= 1;
			this.children = children;
			for (EvalNode child : children)
				child.addParent(this);
		}

		@Override
		Rat evaluate() {
			if (value == null) {
				value = new Rat(children[0].evaluate());
				for (int i = 1; i < children.length; i++)
					value.multiply(children[i].evaluate());
			}
			return clearOnCount();
		}

		@Override
		int depth() {
			if (depth < 0) {
				int maxChildDepth = 0;

				for (EvalNode child : children) {
					int childDepth = child.depth();

					maxChildDepth = childDepth > maxChildDepth ? childDepth
							: maxChildDepth;
				}
				depth = 1 + maxChildDepth;
			}
			return depth;
		}

		@Override
		long numDescendants() {
			if (numDescendants < 0) {
				numDescendants = children.length;

				for (int i = 0; i < children.length; i++)
					numDescendants += children[i].numDescendants();
			}
			return numDescendants;
		}

		@Override
		public int hashCode() {
			if (hashCode == -1) {
				int[] childrenHashCodes = new int[children.length];

				for (int i = 0; i < children.length; i++)
					childrenHashCodes[i] = children[i].hashCode();
				hashCode = 1777773
						* (Arrays.hashCode(childrenHashCodes)
								^ SymbolicOperator.MULTIPLY.hashCode())
						+ parents.size();
			}
			return hashCode;
		}

		@Override
		public SymbolicOperator operator() {
			return SymbolicOperator.MULTIPLY;
		}

		@Override
		public int numChildren() {
			return children.length;
		}

		@Override
		public EvalNode[] getChildren() {
			return children;
		}
	}

	/**
	 * A node representing a power operation: a base raised to some fixed power.
	 * This node has one child, the base. The exponent is a constant number, so
	 * a field in this node.
	 * 
	 * @author siegel
	 */
	class PowerNode extends EvalNode {
		private EvalNode base;
		private BigInteger exponent;

		PowerNode(EvalNode base, BigInteger exponent) {
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

		@Override
		public int hashCode() {
			if (hashCode == -1) {
				hashCode = base.hashCode() ^ exponent.hashCode()
						^ SymbolicOperator.POWER.hashCode() + parents.size();
			}
			return hashCode;
		}

		@Override
		public SymbolicOperator operator() {
			return SymbolicOperator.POWER;
		}
	}

	/**
	 * A constant node. This is a leaf node in the tree.
	 * 
	 * @author siegel
	 */
	class ConstantNode extends EvalNode {
		ConstantNode(Rat value) {
			this.value = value;
		}

		Rat evaluate() {
			return value;
		}

		@Override
		public int hashCode() {
			if (hashCode == -1) {
				BigInteger bigIntArray[] = { value.a, value.b };
				hashCode = 345
						* (Arrays.hashCode(bigIntArray)
								^ SymbolicOperator.CONCRETE.hashCode())
						+ parents.size();
			}
			return hashCode;
		}

		@Override
		public SymbolicOperator operator() {
			return SymbolicOperator.CONCRETE;
		}
	}

	/**
	 * A variable node. This is a leaf node in the tree.
	 * 
	 * @author siegel
	 */
	class VarNode extends EvalNode {
		/**
		 * Sets the value of this variable. This automatically nullifies all
		 * ancestor nodes of this node, since their values depend on this value.
		 * 
		 * @param value
		 *            the value to associate to this node
		 */
		public void setValue(Rat value) {
			this.value = value;
			for (EvalNode parent : getParents()) {
				parent.nullifyValue();
			}
		}

		@Override
		Rat evaluate() {
			return value;
		}

		@Override
		public int hashCode() {
			return 345 * SymbolicOperator.SYMBOLIC_CONSTANT.hashCode()
					+ parents.size();
		}

		@Override
		public SymbolicOperator operator() {
			return SymbolicOperator.SYMBOLIC_CONSTANT;
		}
	}

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
	private int numVars;

	/**
	 * The variable nodes in the tree.
	 */
	private VarNode[] varNodes;

	/**
	 * Upper bound on total degree of the original polynomial after expansion.
	 */
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
	public FastEvaluator3(Random random, NumberFactory nf, Monomial monomial) {
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
}
