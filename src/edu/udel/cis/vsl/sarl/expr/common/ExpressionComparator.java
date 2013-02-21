package edu.udel.cis.vsl.sarl.expr.common;

import java.util.Comparator;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.expr.IF.NumericExpression;

/**
 * Comparator of symbolic expressions.
 * 
 * Creation order: first create ObjectComparator oc. Then create
 * NumericComparator nc using oc. Then create ExpressionComparator ec using oc
 * and nc.
 * 
 * @author siegel
 * 
 */
public class ExpressionComparator implements Comparator<SymbolicExpression> {

	private Comparator<SymbolicObject> objectComparator;

	private Comparator<SymbolicType> typeComparator;

	private Comparator<NumericExpression> numericComparator;

	public ExpressionComparator(Comparator<NumericExpression> numericComparator) {
		this.numericComparator = numericComparator;
	}

	public void setObjectComparator(Comparator<SymbolicObject> c) {
		objectComparator = c;
	}

	public void setTypeComparator(Comparator<SymbolicType> c) {
		typeComparator = c;
	}

	public Comparator<SymbolicObject> objectComparator() {
		return objectComparator;
	}

	public Comparator<SymbolicType> typeComparator() {
		return typeComparator;
	}

	public Comparator<NumericExpression> numericComparator() {
		return numericComparator;
	}

	/**
	 * Numerics first, then everything else. For everything else: first compare
	 * types, then operator, then number of arguments, the compare arguments.
	 * 
	 */
	@Override
	public int compare(SymbolicExpression o1, SymbolicExpression o2) {
		SymbolicType t1 = o1.type();
		SymbolicType t2 = o2.type();

		if (t1.isNumeric()) {
			if (t2.isNumeric())
				return numericComparator.compare((NumericExpression) o1,
						(NumericExpression) o2);
			else
				return -1;
		} else if (t2.isNumeric())
			return 1;
		else { // neither is numeric
			int result = typeComparator.compare(t1, t2);

			if (result != 0)
				return result;
			result = o1.operator().compareTo(o2.operator());
			if (result != 0)
				return result;
			else {
				int numArgs = o1.numArguments();

				result = numArgs - o2.numArguments();
				if (result != 0)
					return result;
				for (int i = 0; i < numArgs; i++) {
					result = objectComparator.compare(o1.argument(i),
							o2.argument(i));
					if (result != 0)
						return result;
				}
				return 0;
			}
		}
	}
}
