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

package ece351.w.svg;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;
import java.lang.Math;

import org.parboiled.common.ImmutableList;

import ece351.w.ast.WProgram;
import ece351.w.ast.Waveform;


public final class TransformSVG2W {
	
	/**
	 * Transforms an instance of WSVG to an instance of WProgram.
	 * Write this algorithm in whatever way you wish.
	 * Remember that the AST is immutable.
	 * You might want to build up some mutable temporary structures.
	 * ImmutableList can be used as a "mutable" temporary structure if the 
	 * local variable is not final: just re-assign the local variable to the new list.
	 * 
	 * We used to give more detailed comments on the staff algorithm,
	 * but many students in several offerings of this course found
	 * those comments confusing, and asked for them to be removed.
	 * 
	 * @see #COMPARE_Y_X 
	 * @see #transformLinesToWaveform(List, List)
	 * @see java.util.ArrayList
	 * @see java.util.LinkedHashSet
	 */
	public static final WProgram transform(final PinsLines pinslines) {
		final List<Line> lines = new ArrayList<Line>(pinslines.segments);
		final List<Pin> pins = new ArrayList<Pin>(pinslines.pins);

		//Pins and lines will both be ordered in the Y-direction.
		//i.e., first pin is first set of lines, second pin is second set...
		lines.sort(COMPARE_Y_X);
		pins.sort(COMPARE_Y);

		//Iterator used to save position in sorted list
		ListIterator<Line> lineIterator = lines.listIterator();
		ImmutableList<Waveform> waveforms = ImmutableList.of();
		for (Pin pin : pins) {
			waveforms = waveforms.append(transformLinesToWaveform(lineIterator, pin));
		}

		return new WProgram(waveforms);
	}

	/**
	 * Transform a list of Line to an instance of Waveform.
	 * The concept of a y-midpoint might be useful: 1 is a line above; 0 is a line below.
	 * What to do about "dots"?
	 * ImmutableList can be used as a "mutable" temporary structure if the 
	 * local variable is not final: just re-assign the local variable to the new list.
	 * 
	 * We used to give more detailed comments on the staff algorithm,
	 * but many students in several offerings of this course found
	 * those comments confusing, and asked for them to be removed.
	 * 
	 * @see #COMPARE_X
	 * @see #transform(PinsLines)
	 * @see Pin#id
	 */
	private static Waveform transformLinesToWaveform(ListIterator<Line> lineIterator, final Pin pin) {
		
		//Add all lines associated with this pin to a list. (Ignoring vetical lines)
		List<Line> pin_lines = new ArrayList<Line>();
		while (lineIterator.hasNext()) {
			Line line = lineIterator.next();
			if (line.x1 == line.x2) continue;
			if (Math.abs(line.y1 - pin.y) > 50) {
				lineIterator.previous();
				break;
			}
			if ((line.y1 == line.y2)) {
				pin_lines.add(line);
			}
		}

		//Convert lines associated with pin to a list of ordered bits.
		pin_lines.sort(COMPARE_X);
		ImmutableList<String> bits = ImmutableList.of();
		for (Line line : pin_lines) {
			if (line.y1 > pin.y) {
				bits = bits.append("0");
			}
			else if (line.y1 < pin.y) {
				bits = bits.append("1");
			}
		}
		
		return new Waveform(bits, pin.id);
	}

	/**
	 * Sort a list of pins according to their y position.
	 * 
	 * @see java.util.Comparator
	 */
	public final static Comparator<Pin> COMPARE_Y = new Comparator<Pin>() {
		@Override
		public int compare(final Pin p1, final Pin p2) {
			if(p1.y < p2.y) return -1;
			if(p1.y > p1.y) return 1;
			return 0;
		}
	};

	/**
	 * Sort a list of lines according to their x position.
	 * 
	 * @see java.util.Comparator
	 */
	public final static Comparator<Line> COMPARE_X = new Comparator<Line>() {
		@Override
		public int compare(final Line l1, final Line l2) {
			if(l1.x1 < l2.x1) return -1;
			if(l1.x1 > l2.x1) return 1;
			if(l1.x2 < l2.x2) return -1;
			if(l1.x2 > l2.x2) return 1;
			return 0;
		}
	};

	/**
	 * Sort a list of lines according to their y position first, and then x position second.
	 * 
	 * @see java.util.Comparator
	 */
	public final static Comparator<Line> COMPARE_Y_X = new Comparator<Line>() {
		@Override
		public int compare(final Line l1, final Line l2) {
			final double y_mid1 = (double) (l1.y1 + l1.y2) / 2.0f;
			final double y_mid2 = (double) (l2.y1 + l2.y2) / 2.0f;
			final double x_mid1 = (double) (l1.x1 + l1.x2) / 2.0f;
			final double x_mid2 = (double) (l2.x1 + l2.x2) / 2.0f;
			if (y_mid1 < y_mid2) return -1;
			if (y_mid1 > y_mid2) return 1;
			if (x_mid1 < x_mid2) return -1;
			if (x_mid1 > x_mid2) return 1;
			return 0;
		}
	};

}
