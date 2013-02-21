package edu.udel.cis.vsl.sarl.type.common;

import java.util.Comparator;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicFunctionType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType.SymbolicTypeKind;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTypeSequence;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;
import edu.udel.cis.vsl.sarl.object.IF.ObjectFactory;
import edu.udel.cis.vsl.sarl.type.IF.SymbolicTypeFactory;

public class CommonSymbolicTypeFactory implements SymbolicTypeFactory {

	private ObjectFactory objectFactory;

	private TypeComparator typeComparator;

	private TypeSequenceComparator typeSequenceComparator;

	private CommonSymbolicPrimitiveType booleanType, integerType, realType;

	public CommonSymbolicTypeFactory(ObjectFactory objectFactory) {
		this.objectFactory = objectFactory;
		typeComparator = new TypeComparator();
		typeSequenceComparator = new TypeSequenceComparator();
		typeComparator.setTypeSequenceComparator(typeSequenceComparator);
		typeSequenceComparator.setTypeComparator(typeComparator);
		booleanType = (CommonSymbolicPrimitiveType) objectFactory
				.canonic(new CommonSymbolicPrimitiveType(SymbolicTypeKind.BOOLEAN));
		integerType = (CommonSymbolicPrimitiveType) objectFactory
				.canonic(new CommonSymbolicPrimitiveType(SymbolicTypeKind.INTEGER));
		realType = (CommonSymbolicPrimitiveType) objectFactory
				.canonic(new CommonSymbolicPrimitiveType(SymbolicTypeKind.REAL));
	}

	public ObjectFactory objectFactory() {
		return objectFactory;
	}

	public CommonSymbolicPrimitiveType booleanType() {
		return booleanType;
	}

	public CommonSymbolicPrimitiveType integerType() {
		return integerType;
	}

	public CommonSymbolicPrimitiveType realType() {
		return realType;
	}

	public SymbolicTypeSequence sequence(Iterable<SymbolicType> elements) {
		return new CommonSymbolicTypeSequence(elements);
	}

	public SymbolicTypeSequence sequence(SymbolicType[] elements) {
		return new CommonSymbolicTypeSequence(elements);
	}

	public SymbolicTypeSequence singletonSequence(SymbolicType type) {
		return new CommonSymbolicTypeSequence(new SymbolicType[] { type });
	}

	public SymbolicArrayType arrayType(SymbolicType elementType) {
		return new CommonSymbolicArrayType(elementType);
	}

	public SymbolicCompleteArrayType arrayType(SymbolicType elementType,
			SymbolicExpression extent) {
		return new CommonSymbolicCompleteArrayType(elementType, extent);
	}

	public SymbolicTupleType tupleType(StringObject name,
			SymbolicTypeSequence fieldTypes) {
		return new CommonSymbolicTupleType(name, fieldTypes);
	}

	public SymbolicUnionType unionType(StringObject name,
			SymbolicTypeSequence memberTypes) {
		return new CommonSymbolicUnionType(name, memberTypes);
	}

	public SymbolicFunctionType functionType(
			SymbolicTypeSequence inputTypes, SymbolicType outputType) {
		return new CommonSymbolicFunctionType(inputTypes, outputType);
	}

	public TypeComparator typeComparator() {
		return typeComparator;
	}

	public TypeSequenceComparator typeSequenceComparator() {
		return typeSequenceComparator;
	}

	@Override
	public void setExpressionComparator(Comparator<SymbolicExpression> c) {
		typeComparator.setExpressionComparator(c);
	}

	@Override
	public void init() {
		assert typeComparator.expressionComparator() != null;
	}

}
