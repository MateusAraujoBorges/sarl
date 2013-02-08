package edu.udel.cis.vsl.sarl.ideal;

import edu.udel.cis.vsl.sarl.IF.collections.SymbolicMap;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.symbolic.CommonSymbolicExpression;

/**
 * A non-trivial primitive power represents a Primitive expression raised to
 * some concrete integer exponent; the exponent is at least 2.
 * 
 * @author siegel
 * 
 */
public class NTPrimitivePower extends CommonSymbolicExpression implements
		PrimitivePower {

	protected NTPrimitivePower(NumericPrimitive primitive, IntObject exponent) {
		super(SymbolicOperator.POWER, primitive.type(), primitive, exponent);
		assert exponent.getInt() >= 2;
	}

	public NumericPrimitive primitive() {
		return (NumericPrimitive) argument(0);
	}

	@Override
	public SymbolicMap monicFactors(IdealFactory factory) {
		return factory.singletonMap(primitive(), this);
	}

	@Override
	public Constant monomialConstant(IdealFactory factory) {
		return factory.one(type());
	}

	@Override
	public Monic monic(IdealFactory factory) {
		return this;
	}

	@Override
	public SymbolicMap termMap(IdealFactory factory) {
		return factory.singletonMap(this, this);
	}

	@Override
	public IntObject primitivePowerExponent(IdealFactory factory) {
		return exponent();
	}

	public IntObject exponent() {
		return (IntObject) argument(1);
	}

	@Override
	public Monomial factorization(IdealFactory factory) {
		return this;
	}

	@Override
	public Polynomial numerator(IdealFactory factory) {
		return this;
	}

	@Override
	public Polynomial denominator(IdealFactory factory) {
		return factory.one(type());
	}

	@Override
	public Monomial leadingTerm() {
		return this;
	}

	@Override
	public NumericPrimitive primitive(IdealFactory factory) {
		return (NumericPrimitive) argument(0);
	}

	@Override
	public boolean isTrivialMonic() {
		return false;
	}

	@Override
	public Polynomial expand(IdealFactory factory) {
		NumericPrimitive primitive = primitive();
		Polynomial expandedPrimitive = primitive.expand(factory);

		if (primitive.equals(expandedPrimitive))
			return this;
		return (Polynomial) factory.power(expandedPrimitive, exponent());
	}

	@Override
	public boolean isZero() {
		return false;
	}

	@Override
	public boolean isOne() {
		return false;
	}

}
