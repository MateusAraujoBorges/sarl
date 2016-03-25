package edu.udel.cis.vsl.sarl.prove.cvc;

import java.util.List;

import edu.udel.cis.vsl.sarl.util.FastList;

public class Translation {
	/**
	 * store the translation result
	 */
	private FastList<String> result;
	/**
	 * is the translation coming from division or module?
	 */
	private Boolean isDivOrModule;
	
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
	private FastList<String> auxConstraints;
	/**
	 * store all the aux vars generated and used in the result and
	 * side effects.
	 */
	private List<FastList<String>> auxVars;
	
	public Translation(){
		result = new FastList<String>();
		isDivOrModule = false;
		auxConstraints = null;
		auxVars = null;
	}
	
	public Translation(FastList<String> res){
		result = res;
		isDivOrModule = false;
		auxConstraints = null;
		auxVars = null;
	}
	
	public Translation(FastList<String> res, Boolean isDvOrMo, 
			FastList<String> auxConstraints, List<FastList<String>> auxVars){
		result = res;
		isDivOrModule = isDvOrMo;
		this.auxConstraints = auxConstraints;
		this.auxVars = auxVars;
	}
	
	public FastList<String> getResult() {
		return result;
	}



	public Boolean getIsDivOrModule() {
		return isDivOrModule;
	}



	public void setIsDivOrModule(Boolean isDivOrModule) {
		this.isDivOrModule = isDivOrModule;
	}



	public FastList<String> getAuxConstraints() {
		return auxConstraints;
	}



	public void setAuxConstraints(FastList<String> auxConstraints) {
		this.auxConstraints = auxConstraints;
	}



	public List<FastList<String>> getAuxVars() {
		return auxVars;
	}



	public void setAuxVars(List<FastList<String>> auxVars) {
		this.auxVars = auxVars;
	}

	public Translation clone(){
		FastList<String> constraints = this.auxConstraints == null ? null :
				this.auxConstraints.clone();
		Translation translation = new Translation(this.result.clone(),
				this.isDivOrModule, 
				constraints, 
				this.auxVars);
		return translation;
	}

	@Override
	public String toString() {
		return result.toString();
	}
}
