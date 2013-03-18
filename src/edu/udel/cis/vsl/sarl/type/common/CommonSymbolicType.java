package edu.udel.cis.vsl.sarl.type.common;

import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.object.common.CommonSymbolicObject;

/**
 */
public abstract class CommonSymbolicType extends CommonSymbolicObject implements
		SymbolicType {

	private SymbolicTypeKind kind;

	/**
	 * Constructs new SymbolicType object with given kind and ID number -1.
	 */
	CommonSymbolicType(SymbolicTypeKind kind) {
		super(SymbolicObjectKind.TYPE);
		assert kind != null;
		this.kind = kind;
	}

	/**
	 * Is the given symbolic type equal to this one---assuming the given
	 * symbolic type is of the same kind as this one? Must be defined in any
	 * concrete subclass.
	 * 
	 * @param that
	 *            a symbolic type of the same kind as this one
	 * @return true iff they define the same type
	 */
	protected abstract boolean typeEquals(CommonSymbolicType that);

	@Override
	public boolean intrinsicEquals(SymbolicObject object) {
		if (this == object)
			return true;
		if (object instanceof CommonSymbolicType) {
			CommonSymbolicType that = (CommonSymbolicType) object;

			if (kind != that.kind)
				return false;
			return typeEquals(that);
		}
		return false;
	}

	@Override
	public SymbolicTypeKind typeKind() {
		return kind;
	}

	@Override
	public boolean isInteger() {
		return kind == SymbolicTypeKind.INTEGER;
	}

	@Override
	public boolean isBoolean() {
		return kind == SymbolicTypeKind.BOOLEAN;
	}

	@Override
	public boolean isReal() {
		return kind == SymbolicTypeKind.REAL;
	}

	@Override
	public boolean isNumeric() {
		return kind == SymbolicTypeKind.INTEGER
				|| kind == SymbolicTypeKind.REAL;
	}

	/**
	 * Note: returns false, since that is usually the case. This method must be
	 * overridden by any concrete class that actually is a Herbrand type.
	 */
	@Override
	public boolean isHerbrand() {
		return false;
	}

	/**
	 * Note: returns false, since that is usually the case. This method must be
	 * overridden by any concrete class that actually is an Ideal numeric type.
	 */
	@Override
	public boolean isIdeal() {
		return false;
	}

	/**
	 * For now, toStringBufferLong = toStringBuffer(false), for types.
	 */
	@Override
	public StringBuffer toStringBufferLong() {
		return toStringBuffer(false);
	}
}
