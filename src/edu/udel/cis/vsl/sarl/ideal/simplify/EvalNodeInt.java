package edu.udel.cis.vsl.sarl.ideal.simplify;

import java.math.BigInteger;

/**
 * The parent of all {@link EvalNodeInt} nodes
 * 
 * @author ziqing
 *
 */
public abstract class EvalNodeInt extends EvalNode<BigInteger> {
	@Override
	abstract BigInteger evaluate();
}
