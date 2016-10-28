package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.NumberObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.ideal.IF.Monomial;
import edu.udel.cis.vsl.sarl.ideal.IF.Primitive;

/**
 * Object used to evaluate a polynomial at a grid of points.
 * 
 * @author siegel
 *
 */
public class FastEvaluator {

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

	private IntegerNumber[] maxDegrees;

	private IntegerNumber[] varVals;

	private Map<Monomial, EvalNode> exprMap = new HashMap<>();

	private ArrayList<VarNode> varNodeList = new ArrayList<>();

	public FastEvaluator(NumberFactory nf, Monomial monomial) {
		this.nf = nf;
		this.isInteger = monomial.type().isInteger();
		this.root = makeNode(monomial);
		this.numVars = varNodeList.size();
		this.varNodes = varNodeList.toArray(new VarNode[numVars]);
		this.varVals = new IntegerNumber[numVars];
		this.maxDegrees = new IntegerNumber[numVars];
		for (int i = 0; i < varNodes.length; i++) {
			this.maxDegrees[i] = monomial.maxDegreeOf(nf,
					(Primitive) varNodes[i].expr);
			this.varVals[i] = nf.zeroInteger();
			this.varNodes[i]
					.setValue(isInteger ? nf.zeroInteger() : nf.zeroRational());
		}
	}

	private void print(IntegerNumber[] array) {
		int n = array.length;

		out.print("[");
		for (int i = 0; i < n; i++) {
			if (i > 0)
				out.print(",");
			out.print(array[i]);
		}
		out.print("]");
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
			result = new ConstantNode(expr,
					((NumberObject) expr.argument(0)).getNumber());
			break;
		}
		case POWER: {
			// depends: int object or real
			SymbolicObject exp = expr.argument(1);

			if (exp instanceof IntObject) {
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

	private boolean next() {
		for (int i = 0; i < numVars; i++) {
			IntegerNumber val = varVals[i];

			if (val.numericalCompareTo(maxDegrees[i]) < 0) {
				val = nf.increment(val);
				varVals[i] = val;
				varNodes[i]
						.setValue(isInteger ? val : nf.integerToRational(val));
				return true;
			} else {
				varVals[i] = nf.zeroInteger();
				varNodes[i]
						.setValue(isInteger ? val : nf.integerToRational(val));
			}
		}
		return false;
	}

	public boolean isZero() {
		if (debug) {
			out.println(
					"Testing zeroness of expression with number of variables: "
							+ numVars);
			out.print("maxDegrees: ");
			print(maxDegrees);
			out.println();
			out.flush();
		}
		while (true) {
			// if (debug) {
			// out.print("Values: ");
			// print(varVals);
			// out.println();
			// out.flush();
			// }
			if (!root.evaluate().isZero())
				return false;
			if (!next())
				return true;
		}
	}

}
