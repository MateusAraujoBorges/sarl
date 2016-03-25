package edu.udel.cis.vsl.sarl.preuniverse.common;

import java.util.List;

import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class Transformation {
	/**
	 * store the transformation result
	 */
	private SymbolicExpression result;
	
	/**
	 * dose the transformation contain any transformation from Division Or Module
	 */
	private Boolean containDivOrModule;
	
	/**
	 * if the translation comes from division or module,
	 * side-effects will be generated, then the side effects
	 * will be conjunct as a single fast list:
	 * e.g.
	 * the side effects of x%y will be:
	 * (y*t__0 + t__1 = x) && (sign(x) = sign(t__1) || t__1=0) && (|t__1| < |y|)
	 * 
	 * sign(t__1) = sign(x) ==>
	 * (t__1>0 && x>0) || (t__1<0 && x<0)
	 * 
	 *|t__1| < |y| ==>
	 *(
	 *(t__1 >0 && y>0 && y>t__1) ||
	 *(t__1 >0 && y<0 && 0 - y > t__1) ||
	 *(t__1 <0 && y<0 && t__1 > y) ||
	 *(t__1<0 && y>0 && 0 - y < t__1)
	 *)
	 * 
	 */
	private SymbolicExpression auxConstraints;
	
	/**
	 * store all the aux vars generated and used in the result and
	 * side effects.
	 */
	private List<SymbolicConstant> auxVars;
	
	public Transformation(){
		result = null;
		containDivOrModule = false;
		auxConstraints = null;
		auxVars = null;
	}
	
	public Transformation(SymbolicExpression res){
		result = res;
		containDivOrModule = false;
		auxConstraints = null;
		auxVars = null;
	}
	
	public Transformation(SymbolicExpression res, Boolean containDvOrMo, 
			SymbolicExpression auxConstraints, List<SymbolicConstant> auxVars){
		result = res;
		containDivOrModule = containDvOrMo;
		this.auxConstraints = auxConstraints;
		this.auxVars = auxVars;
	}

	public SymbolicExpression getResult() {
		return result;
	}

	public void setResult(SymbolicExpression result) {
		this.result = result;
	}

	public Boolean getContainDivOrModule() {
		return containDivOrModule;
	}

	public void setContainDivOrModule(Boolean containDivOrModule) {
		this.containDivOrModule = containDivOrModule;
	}

	public SymbolicExpression getAuxConstraints() {
		return auxConstraints;
	}

	public void setAuxConstraints(SymbolicExpression auxConstraints) {
		this.auxConstraints = auxConstraints;
	}

	public List<SymbolicConstant> getAuxVars() {
		return auxVars;
	}

	public void setAuxVars(List<SymbolicConstant> auxVars) {
		this.auxVars = auxVars;
	}
	
	@Override
	public String toString() {
		return result.toString();
	}
}
