/* *********************************************************************
 * ECE351 
 * Department of Electrical and Computer Engineering 
 * University of Waterloo 
 * Term: Fall 2021 (1219)
 *
 * The base version of this file is the intellectual property of the
 * University of Waterloo. Redistribution is prohibited.
 *
 * By pushing changes to this file I affirm that I am the author of
 * all changes. I affirm that I have complied with the course
 * collaboration policy and have not plagiarized my work. 
 *
 * I understand that redistributing this file might expose me to
 * disciplinary action under UW Policy 71. I understand that Policy 71
 * allows for retroactive modification of my final grade in a course.
 * For example, if I post my solutions to these labs on GitHub after I
 * finish ECE351, and a future student plagiarizes them, then I too
 * could be found guilty of plagiarism. Consequently, my final grade
 * in ECE351 could be retroactively lowered. This might require that I
 * repeat ECE351, which in turn might delay my graduation.
 *
 * https://uwaterloo.ca/secretariat-general-counsel/policies-procedures-guidelines/policy-71
 * 
 * ********************************************************************/

package ece351.common.ast;

import java.util.List;

import ece351.common.visitor.ExprVisitor;

public final class NaryOrExpr extends NaryExpr {

	public NaryOrExpr(final Expr... exprs) {
		super(exprs);
	}
	
	public NaryOrExpr(final List<Expr> children) {
		super(children);
	}
	
	@Override
	public NaryExpr newNaryExpr(final List<Expr> children) {
		return new NaryOrExpr(children);
	}

	@Override
	public String operator() {
		return Constants.OR;
	}

	@Override
	public ConstantExpr getAbsorbingElement() {
		return ConstantExpr.TrueExpr;
	}

	@Override
	public ConstantExpr getIdentityElement() {
		return ConstantExpr.FalseExpr;
	}
	
	@Override
	protected Class<? extends NaryExpr> getThatClass() {
		return NaryAndExpr.class;
	}

	@Override
	public Expr accept(ExprVisitor v) { return v.visitNaryOr(this); }

}
