package edu.udel.cis.vsl.sarl.ideal.simplify;

/**
 * The parent of all {@link EvalNodeRat} nodes
 * 
 * @author ziqing
 *
 */
public abstract class EvalNodeRat extends EvalNode<Rat> {
	@Override
	abstract Rat evaluate();
}
