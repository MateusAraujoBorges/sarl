package edu.udel.cis.vsl.sarl.prove.cvc;

import java.io.PrintStream;
import java.math.BigInteger;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.FunctionType;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Rational;
import edu.nyu.acsys.CVC4.RealType;
import edu.nyu.acsys.CVC4.SExpr;
import edu.nyu.acsys.CVC4.SmtEngine;
import edu.nyu.acsys.CVC4.vectorExpr;

public class LittleCVC4Example {

	static {
		System.loadLibrary("cvc4jni");
	}

	private static PrintStream out = System.out;

	private static ExprManager em;

	private static SmtEngine smt;

	private static RealType realType;

	private static Expr zero;

	public static void main(String[] args) {
		FunctionType fType;
		Expr x, y, f, fx, fy, xeqy, fxeqfy, fxeq0;

		Rational negOne = new Rational(BigInteger.valueOf(-1));

		out.println("negOne = " + negOne);

		out.println("Starting little CVC4 example...");
		em = new ExprManager();
		smt = new SmtEngine(em);
		// the following is necessary if you are going to make
		// multiple verify calls with the same SmtEngine:
		// (this may change in the future)
		smt.setOption("incremental", new SExpr(true));
		// the following is needed to use method getAssertions:
		smt.setOption("interactive-mode", new SExpr(true));
		realType = em.realType();
		fType = em.mkFunctionType(realType, realType);
		zero = em.mkConst(new Rational(0));
		x = em.mkVar("x", realType); // real variable x
		y = em.mkVar("y", realType); // real variable y
		f = em.mkVar("f", fType); // function from real to real
		fx = em.mkExpr(Kind.APPLY_UF, f, x); // f(x)
		fy = em.mkExpr(Kind.APPLY_UF, f, y); // f(y)
		xeqy = em.mkExpr(Kind.EQUAL, x, y); // x=y
		fxeqfy = em.mkExpr(Kind.EQUAL, fx, fy); // f(x)=f(y)
		fxeq0 = em.mkExpr(Kind.EQUAL, fx, zero); // f(x)=0
		out.println("The formula f(x)=0 is " + fxeq0);
		out.flush();
		out.println("Asserting x=y: " + xeqy);
		smt.assertFormula(xeqy);

		vectorExpr assertions = smt.getAssertions();

		out.println("Does f(x)=f(y)? " + smt.query(fxeqfy));
		// answer should be "valid" since x=y => f(x)=f(y)
		out.flush();
		out.println("Does f(x)=0? " + smt.query(fxeq0));
		out.flush();
	}

}
