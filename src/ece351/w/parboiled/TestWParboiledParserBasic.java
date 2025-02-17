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

package ece351.w.parboiled;

import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.parboiled.common.ImmutableList;

import ece351.util.BaseTest351;
import ece351.util.ExaminableProperties;
import ece351.w.ast.WProgram;
import ece351.w.ast.Waveform;

public class TestWParboiledParserBasic extends BaseTest351 {

	@Test
	public void test() {
		// explicitly construct an AST
		final Waveform x = new Waveform(ImmutableList.of("0"), "X");
		final Waveform y = new Waveform(ImmutableList.of("1"), "Y");
		final WProgram wp1 = new WProgram(ImmutableList.of(x).append(y));
		
		// now parse a string that should construct it
		final WProgram wp2 = WParboiledParser.parse("X: 0; Y: 1;");
		
		// compare
		assertTrue("ASTs not equals", wp1.equals(wp2));
		assertTrue("ASTs not isomorphic", wp1.isomorphic(wp2));
		assertTrue("ASTs not equivalent", wp1.equivalent(wp2));

		// sanity
		ExaminableProperties.checkAllUnary(wp1);
		ExaminableProperties.checkAllUnary(wp2);
		ExaminableProperties.checkAllBinary(wp1, wp2);
	}

}
