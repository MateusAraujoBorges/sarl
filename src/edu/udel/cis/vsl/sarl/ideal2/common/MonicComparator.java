package edu.udel.cis.vsl.sarl.ideal2.common;

import java.util.Comparator;

import edu.udel.cis.vsl.sarl.ideal2.IF.Monic;

public class MonicComparator implements Comparator<Monic> {

	private IdealComparator ic;

	public MonicComparator(IdealComparator ic) {
		this.ic = ic;
	}

	@Override
	public int compare(Monic o1, Monic o2) {
		return ic.compareMonics(o1, o2);
	}

}
