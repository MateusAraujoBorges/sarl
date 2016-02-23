package edu.udel.cis.vsl.sarl.ideal2.common;

import java.util.Comparator;

import edu.udel.cis.vsl.sarl.ideal2.IF.Primitive;

public class PrimitiveComparator implements Comparator<Primitive> {

	private IdealComparator ic;

	public PrimitiveComparator(IdealComparator ic) {
		this.ic = ic;
	}

	@Override
	public int compare(Primitive o1, Primitive o2) {
		return ic.comparePrimitives(o1, o2);
	}

}