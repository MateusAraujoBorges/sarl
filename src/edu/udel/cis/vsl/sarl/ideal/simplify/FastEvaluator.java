package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
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
		private int exponent;

		PowerNode(NumericExpression expr, EvalNode base, int exponent) {
			super(expr);
			assert exponent >= 2;
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

	private int[] maxDegrees;

	private int[] varVals;

	private Map<Monomial, EvalNode> exprMap = new HashMap<>();

	private ArrayList<VarNode> varNodeList = new ArrayList<>();

	public FastEvaluator(NumberFactory nf, Monomial monomial) {
		this.nf = nf;
		this.isInteger = monomial.type().isInteger();
		this.root = makeNode(monomial);
		this.numVars = varNodeList.size();
		this.varNodes = varNodeList.toArray(new VarNode[numVars]);
		this.varVals = new int[numVars];
		this.maxDegrees = new int[numVars];
		for (int i = 0; i < varNodes.length; i++) {
			this.maxDegrees[i] = monomial
					.maxDegreeOf((Primitive) varNodes[i].expr);
			this.varVals[i] = 0;
			this.varNodes[i]
					.setValue(isInteger ? nf.zeroInteger() : nf.zeroRational());
		}
	}

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

				result = new PowerNode(expr, base, ((IntObject) exp).getInt());
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
			int val = varVals[i];

			if (val < maxDegrees[i]) {
				val++;
				varVals[i] = val;
				varNodes[i].setValue(isInteger ? nf.integer(val)
						: nf.integerToRational(nf.integer(val)));
				return true;
			} else {
				varVals[i] = 0;
				varNodes[i].setValue(
						isInteger ? nf.zeroInteger() : nf.zeroRational());
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
