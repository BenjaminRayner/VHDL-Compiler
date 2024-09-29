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

package ece351.v;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Map;

import org.parboiled.common.ImmutableList;

import ece351.common.ast.AndExpr;
import ece351.common.ast.AssignmentStatement;
import ece351.common.ast.ConstantExpr;
import ece351.common.ast.EqualExpr;
import ece351.common.ast.Expr;
import ece351.common.ast.NAndExpr;
import ece351.common.ast.NOrExpr;
import ece351.common.ast.NaryAndExpr;
import ece351.common.ast.NaryOrExpr;
import ece351.common.ast.NotExpr;
import ece351.common.ast.OrExpr;
import ece351.common.ast.Statement;
import ece351.common.ast.VarExpr;
import ece351.common.ast.XNOrExpr;
import ece351.common.ast.XOrExpr;
import ece351.common.visitor.PostOrderExprVisitor;
import ece351.util.CommandLine;
import ece351.v.ast.Architecture;
import ece351.v.ast.Component;
import ece351.v.ast.DesignUnit;
import ece351.v.ast.IfElseStatement;
import ece351.v.ast.Process;
import ece351.v.ast.VProgram;

/**
 * Inlines logic in components to architecture body.
 */
public final class Elaborator extends PostOrderExprVisitor {

	private final Map<String, String> current_map = new LinkedHashMap<String, String>();
	
	public static void main(String[] args) {
		System.out.println(elaborate(args));
	}
	
	public static VProgram elaborate(final String[] args) {
		return elaborate(new CommandLine(args));
	}
	
	public static VProgram elaborate(final CommandLine c) {
        final VProgram program = DeSugarer.desugar(c);
        return elaborate(program);
	}
	
	public static VProgram elaborate(final VProgram program) {
		final Elaborator e = new Elaborator();
		return e.elaborateit(program);
	}

	private VProgram elaborateit(final VProgram root) {

		// our ASTs are immutable. so we cannot mutate root.
		// we need to construct a new AST that will be the return value.
		// it will be like the input (root), but different.
		VProgram result = new VProgram();
		int compCount = 0;

		// iterate over all of the designUnits in root.
		// for each one, construct a new architecture.
		// Architecture a = du.arch.varyComponents(ImmutableList.<Component>of());
		// this gives us a copy of the architecture with an empty list of components.
		// now we can build up this Architecture with new components.
			// In the elaborator, an architectures list of signals, and set of statements may change (grow)
						//populate dictionary/map	
						//add input signals, map to ports
						//add output signals, map to ports
						//add local signals, add to signal list of current designUnit						
						//loop through the statements in the architecture body		
							// make the appropriate variable substitutions for signal assignment statements
							// i.e., call changeStatementVars
							// make the appropriate variable substitutions for processes (sensitivity list, if/else body statements)
							// i.e., call expandProcessComponent
			 // append this new architecture to result
		for (DesignUnit du : root.designUnits) {
			Architecture a = du.arch.varyComponents(ImmutableList.<Component>of());

			for (Component c : du.arch.components) {
				++compCount;

				//Get design unit that is being instantiated
				DesignUnit du_inst = null;
				for (DesignUnit du_res : result.designUnits) {
					if (c.entityName.equals(du_res.identifier)) { du_inst = du_res; break; }
				}
				if (du_inst == null) { a = a.appendComponent(c); continue; }

				//Map entity ports to signals in port map
				LinkedList<String> entity_pins = new LinkedList<String>();
				entity_pins.addAll(du_inst.entity.input);
				entity_pins.addAll(du_inst.entity.output);
				for (int i = 0; i < c.signalList.size(); ++i) {
					current_map.put(entity_pins.get(i), c.signalList.get(i));
				}

				//Add all internal signals + mapping
				for (String signal : du_inst.arch.signals) {
					a = a.appendSignal("comp" + compCount + "_" + signal);
					current_map.put(signal, "comp" + compCount + "_" + signal);
				}

				//Add statements from institiated design unit
				for (Statement statement : du_inst.arch.statements) {
					if (statement.getClass() == AssignmentStatement.class) {
						AssignmentStatement astmt = (AssignmentStatement) statement;
						a = a.appendStatement(changeStatementVars(astmt));
					}
					if (statement.getClass() == Process.class) {
						Process proc = (Process) statement;
						a = a.appendStatement(expandProcessComponent(proc));
					}
				}

				current_map.clear();
			}

			result = result.append(new DesignUnit(a, du.entity));
		}

		assert result.repOk();
		return result;
	}
	
	private Process expandProcessComponent(final Process process) {
		
		Process result = new Process();
		for (String sens : process.sensitivityList) {
			result = result.appendSensitivity(current_map.get(sens));
		}

		for (Statement statement : process.sequentialStatements) {
			
			if (statement.getClass() == AssignmentStatement.class) {
				AssignmentStatement astmt = (AssignmentStatement) statement;
				result = result.appendStatement(changeStatementVars(astmt));
			}
			if (statement.getClass() == IfElseStatement.class) {
				IfElseStatement ifelse = (IfElseStatement) statement;
				result = result.appendStatement(changeIfVars(ifelse));
			}
			
		}

		return result;
	}
	
	private  IfElseStatement changeIfVars(final IfElseStatement s) {
		IfElseStatement result = new IfElseStatement(traverseExpr(s.condition));

		for (Statement statement : s.ifBody) {
			AssignmentStatement astmt = (AssignmentStatement) statement;
			result = result.appendToTrueBlock(changeStatementVars(astmt));
		}

		for (Statement statement : s.elseBody) {
			AssignmentStatement astmt = (AssignmentStatement) statement;
			result = result.appendToElseBlock(changeStatementVars(astmt));
		}

		return result;
	}

	private AssignmentStatement changeStatementVars(final AssignmentStatement s) {
		AssignmentStatement astmt = new AssignmentStatement(current_map.get(s.outputVar.identifier), s.expr);
		return traverseAssignmentStatement(astmt);
	}
	
	@Override
	public Expr visitVar(VarExpr e) {
		return new VarExpr(current_map.get(e.identifier));
	}
	
	// do not rewrite these parts of the AST
	@Override public Expr visitConstant(ConstantExpr e) { return e; }
	@Override public Expr visitNot(NotExpr e) { return e; }
	@Override public Expr visitAnd(AndExpr e) { return e; }
	@Override public Expr visitOr(OrExpr e) { return e; }
	@Override public Expr visitXOr(XOrExpr e) { return e; }
	@Override public Expr visitEqual(EqualExpr e) { return e; }
	@Override public Expr visitNAnd(NAndExpr e) { return e; }
	@Override public Expr visitNOr(NOrExpr e) { return e; }
	@Override public Expr visitXNOr(XNOrExpr e) { return e; }
	@Override public Expr visitNaryAnd(NaryAndExpr e) { return e; }
	@Override public Expr visitNaryOr(NaryOrExpr e) { return e; }
}
