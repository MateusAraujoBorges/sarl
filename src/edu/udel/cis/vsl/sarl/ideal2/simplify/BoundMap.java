package edu.udel.cis.vsl.sarl.ideal2.simplify;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.ideal2.IF.Monic;

public class BoundMap {

	private Map<Monic, Interval> map;

	private SimplifierInfo info;

	private BoundMap(SimplifierInfo info, Map<Monic, Interval> map) {
		this.info = info;
		this.map = map;
	}

	public BoundMap(SimplifierInfo info) {
		this(info, new HashMap<>());
	}

	public void set(Monic key, Interval bound) {
		map.put(key, bound);
	}

	public void set(Monic key, Number value) {
		set(key, info.numberFactory.singletonInterval(value));
	}

	public Interval get(Monic key) {
		return map.get(key);
	}

	public Set<Entry<Monic, Interval>> entrySet() {
		return map.entrySet();
	}

	public Interval remove(Monic key) {
		return map.remove(key);
	}

	public boolean isEmpty() {
		return map.isEmpty();
	}

	public int size() {
		return map.size();
	}

	public Interval restrict(Monic key, Interval bound) {
		Interval original = map.get(key), result;

		if (original == null) {
			result = bound;
			map.put(key, result);
		} else {
			result = info.numberFactory.intersection(original, bound);
			if (!result.equals(original))
				map.put(key, result);
		}
		return result;
	}

	public Interval enlarge(Monic key, Interval bound) {
		Interval original = map.get(key), result;

		if (original == null) {
			result = bound;
			map.put(key, result);
		} else {
			result = info.numberFactory.join(original, bound);
			if (!result.equals(original))
				map.put(key, result);
		}
		return result;
	}

	public Interval restrictLower(Monic key, Number value, boolean strict) {
		Interval original = map.get(key), result;
		boolean isIntegral = key.type().isInteger();

		if (original == null) {
			result = info.numberFactory.newInterval(isIntegral, value, strict,
					null, true);
			map.put(key, result);
		} else {
			result = info.numberFactory.restrictLower(original, value, strict);
			if (!result.equals(original))
				map.put(key, result);
		}
		return result;
	}

	public Interval restrictUpper(Monic key, Number value, boolean strict) {
		Interval original = map.get(key), result;
		boolean isIntegral = key.type().isInteger();

		if (original == null) {
			result = info.numberFactory.newInterval(isIntegral, null, true,
					value, strict);
			map.put(key, result);
		} else {
			result = info.numberFactory.restrictUpper(original, value, strict);
			if (!result.equals(original))
				map.put(key, result);
		}
		return result;
	}
	
	// TODO: add methods to say monic==value, monic!=value

	public void print(PrintStream out) {
		for (Entry<Monic, Interval> entry : map.entrySet())
			out.println(entry.getKey() + " : " + entry.getValue());
		out.flush();
	}

	@Override
	public BoundMap clone() {
		@SuppressWarnings("unchecked")
		Map<Monic, Interval> newMap = (HashMap<Monic, Interval>) ((HashMap<?, ?>) map)
				.clone();

		return new BoundMap(info, newMap);
	}
}
