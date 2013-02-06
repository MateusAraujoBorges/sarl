package edu.udel.cis.vsl.sarl.ideal;

import edu.udel.cis.vsl.sarl.IF.collections.SymbolicMap;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTypeIF;
import edu.udel.cis.vsl.sarl.symbolic.CommonSymbolicExpression;

/**
 * Empty monic: equivalent to 1.
 * 
 * @author siegel
 * 
 */
public class TrivialMonic extends CommonSymbolicExpression implements Monic {

	protected TrivialMonic(SymbolicTypeIF type, SymbolicMap emptyMap) {
		super(SymbolicOperator.MULTIPLY, type, emptyMap);
		assert emptyMap.isEmpty();
		assert emptyMap.isSorted();
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
	public Monomial leadingTerm() {
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
	public NumericExpression plus(IdealFactory factory, NumericExpression expr) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SymbolicMap monicFactors(IdealFactory factory) {
		return (SymbolicMap) argument(0);
	}

	@Override
	public boolean isTrivialMonic() {
		return true;
	}

	@Override
	public Monomial factorization(IdealFactory factory) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Polynomial expand(IdealFactory factory) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public NumericExpression times(IdealFactory factory, NumericExpression expr) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public NumericExpression negate(IdealFactory factory) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Polynomial intDivide(IdealFactory factory, Polynomial expr) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Polynomial modulo(IdealFactory factory, Polynomial expr) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public NumericExpression invert(IdealFactory factory) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isZero() {
		return false;
	}

	@Override
	public boolean isOne() {
		return true;
	}

}
