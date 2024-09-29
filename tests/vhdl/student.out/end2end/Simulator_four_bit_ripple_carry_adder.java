import java.util.*;
import ece351.w.ast.*;
import ece351.w.parboiled.*;
import static ece351.util.Boolean351.*;
import ece351.util.CommandLine;
import java.io.File;
import java.io.FileWriter;
import java.io.StringWriter;
import java.io.PrintWriter;
import java.io.IOException;
import ece351.util.Debug;

public final class Simulator_four_bit_ripple_carry_adder {
    public static void main(final String[] args) {
        // read the input F program
        // write the output
        // read input WProgram
        final CommandLine cmd = new CommandLine(args);
        final String input = cmd.readInputSpec();
        final WProgram wprogram = WParboiledParser.parse(input);
        // construct storage for output
        Map<String,StringBuilder> output = new LinkedHashMap<String,StringBuilder>();
        output.put("four_bit_ripple_carry_adderCout", new StringBuilder());
        output.put("four_bit_ripple_carry_adderV", new StringBuilder());
        output.put("four_bit_ripple_carry_addersum0", new StringBuilder());
        output.put("four_bit_ripple_carry_addersum1", new StringBuilder());
        output.put("four_bit_ripple_carry_addersum2", new StringBuilder());
        output.put("four_bit_ripple_carry_addersum3", new StringBuilder());
        output.put("full_adderCout", new StringBuilder());
        output.put("full_adderS", new StringBuilder());
        output.put("half_adderC", new StringBuilder());
        output.put("half_adderS", new StringBuilder());
        // loop over each time step
        final int timeCount = wprogram.timeCount();
        for (int time = 0; time < timeCount; time++) {
            // values of input variables at this time step
            final boolean in_four_bit_ripple_carry_adderCin = wprogram.valueAtTime("four_bit_ripple_carry_adderCin", time);
            final boolean in_four_bit_ripple_carry_addera0 = wprogram.valueAtTime("four_bit_ripple_carry_addera0", time);
            final boolean in_four_bit_ripple_carry_addera1 = wprogram.valueAtTime("four_bit_ripple_carry_addera1", time);
            final boolean in_four_bit_ripple_carry_addera2 = wprogram.valueAtTime("four_bit_ripple_carry_addera2", time);
            final boolean in_four_bit_ripple_carry_addera3 = wprogram.valueAtTime("four_bit_ripple_carry_addera3", time);
            final boolean in_four_bit_ripple_carry_adderb0 = wprogram.valueAtTime("four_bit_ripple_carry_adderb0", time);
            final boolean in_four_bit_ripple_carry_adderb1 = wprogram.valueAtTime("four_bit_ripple_carry_adderb1", time);
            final boolean in_four_bit_ripple_carry_adderb2 = wprogram.valueAtTime("four_bit_ripple_carry_adderb2", time);
            final boolean in_four_bit_ripple_carry_adderb3 = wprogram.valueAtTime("four_bit_ripple_carry_adderb3", time);
            final boolean in_full_adderA = wprogram.valueAtTime("full_adderA", time);
            final boolean in_full_adderB = wprogram.valueAtTime("full_adderB", time);
            final boolean in_full_adderCin = wprogram.valueAtTime("full_adderCin", time);
            final boolean in_half_adderA = wprogram.valueAtTime("half_adderA", time);
            final boolean in_half_adderB = wprogram.valueAtTime("half_adderB", time);
            // values of output variables at this time step
            final String out_four_bit_ripple_carry_adderCout = four_bit_ripple_carry_adderCout(in_four_bit_ripple_carry_addera0, in_four_bit_ripple_carry_adderb0, in_four_bit_ripple_carry_adderCin, in_four_bit_ripple_carry_addera1, in_four_bit_ripple_carry_adderb1, in_four_bit_ripple_carry_addera2, in_four_bit_ripple_carry_adderb2, in_four_bit_ripple_carry_addera3, in_four_bit_ripple_carry_adderb3) ? "1 " : "0 ";
            final String out_four_bit_ripple_carry_adderV = four_bit_ripple_carry_adderV(in_four_bit_ripple_carry_addera0, in_four_bit_ripple_carry_adderb0, in_four_bit_ripple_carry_adderCin, in_four_bit_ripple_carry_addera1, in_four_bit_ripple_carry_adderb1, in_four_bit_ripple_carry_addera2, in_four_bit_ripple_carry_adderb2, in_four_bit_ripple_carry_addera3, in_four_bit_ripple_carry_adderb3) ? "1 " : "0 ";
            final String out_four_bit_ripple_carry_addersum0 = four_bit_ripple_carry_addersum0(in_four_bit_ripple_carry_addera0, in_four_bit_ripple_carry_adderb0, in_four_bit_ripple_carry_adderCin) ? "1 " : "0 ";
            final String out_four_bit_ripple_carry_addersum1 = four_bit_ripple_carry_addersum1(in_four_bit_ripple_carry_addera0, in_four_bit_ripple_carry_adderb0, in_four_bit_ripple_carry_adderCin, in_four_bit_ripple_carry_addera1, in_four_bit_ripple_carry_adderb1) ? "1 " : "0 ";
            final String out_four_bit_ripple_carry_addersum2 = four_bit_ripple_carry_addersum2(in_four_bit_ripple_carry_addera0, in_four_bit_ripple_carry_adderb0, in_four_bit_ripple_carry_adderCin, in_four_bit_ripple_carry_addera1, in_four_bit_ripple_carry_adderb1, in_four_bit_ripple_carry_addera2, in_four_bit_ripple_carry_adderb2) ? "1 " : "0 ";
            final String out_four_bit_ripple_carry_addersum3 = four_bit_ripple_carry_addersum3(in_four_bit_ripple_carry_addera0, in_four_bit_ripple_carry_adderb0, in_four_bit_ripple_carry_adderCin, in_four_bit_ripple_carry_addera1, in_four_bit_ripple_carry_adderb1, in_four_bit_ripple_carry_addera2, in_four_bit_ripple_carry_adderb2, in_four_bit_ripple_carry_addera3, in_four_bit_ripple_carry_adderb3) ? "1 " : "0 ";
            final String out_full_adderCout = full_adderCout(in_full_adderA, in_full_adderB, in_full_adderCin) ? "1 " : "0 ";
            final String out_full_adderS = full_adderS(in_full_adderA, in_full_adderB, in_full_adderCin) ? "1 " : "0 ";
            final String out_half_adderC = half_adderC(in_half_adderA, in_half_adderB) ? "1 " : "0 ";
            final String out_half_adderS = half_adderS(in_half_adderA, in_half_adderB) ? "1 " : "0 ";
            // store outputs
            output.get("four_bit_ripple_carry_adderCout").append(out_four_bit_ripple_carry_adderCout);
            output.get("four_bit_ripple_carry_adderV").append(out_four_bit_ripple_carry_adderV);
            output.get("four_bit_ripple_carry_addersum0").append(out_four_bit_ripple_carry_addersum0);
            output.get("four_bit_ripple_carry_addersum1").append(out_four_bit_ripple_carry_addersum1);
            output.get("four_bit_ripple_carry_addersum2").append(out_four_bit_ripple_carry_addersum2);
            output.get("four_bit_ripple_carry_addersum3").append(out_four_bit_ripple_carry_addersum3);
            output.get("full_adderCout").append(out_full_adderCout);
            output.get("full_adderS").append(out_full_adderS);
            output.get("half_adderC").append(out_half_adderC);
            output.get("half_adderS").append(out_half_adderS);
        }
        try {
            final File f = cmd.getOutputFile();
            f.getParentFile().mkdirs();
            final PrintWriter pw = new PrintWriter(new FileWriter(f));
            // write the input
            System.out.println(wprogram.toString());
            pw.println(wprogram.toString());
            // write the output
            System.out.println(f.getAbsolutePath());
            for (final Map.Entry<String,StringBuilder> e : output.entrySet()) {
                System.out.println(e.getKey() + ":" + e.getValue().toString()+ ";");
                pw.write(e.getKey() + ":" + e.getValue().toString()+ ";\n");
            }
            pw.close();
        } catch (final IOException e) {
            Debug.barf(e.getMessage());
        }
    }
    // methods to compute values for output pins
    public static boolean four_bit_ripple_carry_adderCout(final boolean four_bit_ripple_carry_addera0, final boolean four_bit_ripple_carry_adderb0, final boolean four_bit_ripple_carry_adderCin, final boolean four_bit_ripple_carry_addera1, final boolean four_bit_ripple_carry_adderb1, final boolean four_bit_ripple_carry_addera2, final boolean four_bit_ripple_carry_adderb2, final boolean four_bit_ripple_carry_addera3, final boolean four_bit_ripple_carry_adderb3) { return or(and(or(and(or(and(or(and(or(and(not(four_bit_ripple_carry_addera0) , four_bit_ripple_carry_adderb0) , and(not(four_bit_ripple_carry_adderb0) , four_bit_ripple_carry_addera0) ) , four_bit_ripple_carry_adderCin) , and(four_bit_ripple_carry_addera0, four_bit_ripple_carry_adderb0) ) , or(and(not(four_bit_ripple_carry_addera1) , four_bit_ripple_carry_adderb1) , and(not(four_bit_ripple_carry_adderb1) , four_bit_ripple_carry_addera1) ) ) , and(four_bit_ripple_carry_addera1, four_bit_ripple_carry_adderb1) ) , or(and(not(four_bit_ripple_carry_addera2) , four_bit_ripple_carry_adderb2) , and(not(four_bit_ripple_carry_adderb2) , four_bit_ripple_carry_addera2) ) ) , and(four_bit_ripple_carry_addera2, four_bit_ripple_carry_adderb2) ) , or(and(not(four_bit_ripple_carry_addera3) , four_bit_ripple_carry_adderb3) , and(not(four_bit_ripple_carry_adderb3) , four_bit_ripple_carry_addera3) ) ) , and(four_bit_ripple_carry_addera3, four_bit_ripple_carry_adderb3) ) ;}
    public static boolean four_bit_ripple_carry_adderV(final boolean four_bit_ripple_carry_addera0, final boolean four_bit_ripple_carry_adderb0, final boolean four_bit_ripple_carry_adderCin, final boolean four_bit_ripple_carry_addera1, final boolean four_bit_ripple_carry_adderb1, final boolean four_bit_ripple_carry_addera2, final boolean four_bit_ripple_carry_adderb2, final boolean four_bit_ripple_carry_addera3, final boolean four_bit_ripple_carry_adderb3) { return or(and(or(and(or(and(or(and(or(and(or(and(not(four_bit_ripple_carry_addera0) , four_bit_ripple_carry_adderb0) , and(not(four_bit_ripple_carry_adderb0) , four_bit_ripple_carry_addera0) ) , four_bit_ripple_carry_adderCin) , and(four_bit_ripple_carry_addera0, four_bit_ripple_carry_adderb0) ) , or(and(not(four_bit_ripple_carry_addera1) , four_bit_ripple_carry_adderb1) , and(not(four_bit_ripple_carry_adderb1) , four_bit_ripple_carry_addera1) ) ) , and(four_bit_ripple_carry_addera1, four_bit_ripple_carry_adderb1) ) , or(and(not(four_bit_ripple_carry_addera2) , four_bit_ripple_carry_adderb2) , and(not(four_bit_ripple_carry_adderb2) , four_bit_ripple_carry_addera2) ) ) , and(four_bit_ripple_carry_addera2, four_bit_ripple_carry_adderb2) ) , or(and(not(four_bit_ripple_carry_addera3) , four_bit_ripple_carry_adderb3) , and(not(four_bit_ripple_carry_adderb3) , four_bit_ripple_carry_addera3) ) ) , and(four_bit_ripple_carry_addera3, four_bit_ripple_carry_adderb3) ) , not(or(and(or(and(or(and(or(and(not(four_bit_ripple_carry_addera0) , four_bit_ripple_carry_adderb0) , and(not(four_bit_ripple_carry_adderb0) , four_bit_ripple_carry_addera0) ) , four_bit_ripple_carry_adderCin) , and(four_bit_ripple_carry_addera0, four_bit_ripple_carry_adderb0) ) , or(and(not(four_bit_ripple_carry_addera1) , four_bit_ripple_carry_adderb1) , and(not(four_bit_ripple_carry_adderb1) , four_bit_ripple_carry_addera1) ) ) , and(four_bit_ripple_carry_addera1, four_bit_ripple_carry_adderb1) ) , or(and(not(four_bit_ripple_carry_addera2) , four_bit_ripple_carry_adderb2) , and(not(four_bit_ripple_carry_adderb2) , four_bit_ripple_carry_addera2) ) ) , and(four_bit_ripple_carry_addera2, four_bit_ripple_carry_adderb2) ) ) ) , and(or(and(or(and(or(and(or(and(not(four_bit_ripple_carry_addera0) , four_bit_ripple_carry_adderb0) , and(not(four_bit_ripple_carry_adderb0) , four_bit_ripple_carry_addera0) ) , four_bit_ripple_carry_adderCin) , and(four_bit_ripple_carry_addera0, four_bit_ripple_carry_adderb0) ) , or(and(not(four_bit_ripple_carry_addera1) , four_bit_ripple_carry_adderb1) , and(not(four_bit_ripple_carry_adderb1) , four_bit_ripple_carry_addera1) ) ) , and(four_bit_ripple_carry_addera1, four_bit_ripple_carry_adderb1) ) , or(and(not(four_bit_ripple_carry_addera2) , four_bit_ripple_carry_adderb2) , and(not(four_bit_ripple_carry_adderb2) , four_bit_ripple_carry_addera2) ) ) , and(four_bit_ripple_carry_addera2, four_bit_ripple_carry_adderb2) ) , not(or(and(or(and(or(and(or(and(or(and(not(four_bit_ripple_carry_addera0) , four_bit_ripple_carry_adderb0) , and(not(four_bit_ripple_carry_adderb0) , four_bit_ripple_carry_addera0) ) , four_bit_ripple_carry_adderCin) , and(four_bit_ripple_carry_addera0, four_bit_ripple_carry_adderb0) ) , or(and(not(four_bit_ripple_carry_addera1) , four_bit_ripple_carry_adderb1) , and(not(four_bit_ripple_carry_adderb1) , four_bit_ripple_carry_addera1) ) ) , and(four_bit_ripple_carry_addera1, four_bit_ripple_carry_adderb1) ) , or(and(not(four_bit_ripple_carry_addera2) , four_bit_ripple_carry_adderb2) , and(not(four_bit_ripple_carry_adderb2) , four_bit_ripple_carry_addera2) ) ) , and(four_bit_ripple_carry_addera2, four_bit_ripple_carry_adderb2) ) , or(and(not(four_bit_ripple_carry_addera3) , four_bit_ripple_carry_adderb3) , and(not(four_bit_ripple_carry_adderb3) , four_bit_ripple_carry_addera3) ) ) , and(four_bit_ripple_carry_addera3, four_bit_ripple_carry_adderb3) ) ) ) ) ;}
    public static boolean four_bit_ripple_carry_addersum0(final boolean four_bit_ripple_carry_addera0, final boolean four_bit_ripple_carry_adderb0, final boolean four_bit_ripple_carry_adderCin) { return or(and(or(and(not(four_bit_ripple_carry_addera0) , four_bit_ripple_carry_adderb0) , and(not(four_bit_ripple_carry_adderb0) , four_bit_ripple_carry_addera0) ) , not(four_bit_ripple_carry_adderCin) ) , and(not(or(and(not(four_bit_ripple_carry_addera0) , four_bit_ripple_carry_adderb0) , and(not(four_bit_ripple_carry_adderb0) , four_bit_ripple_carry_addera0) ) ) , four_bit_ripple_carry_adderCin) ) ;}
    public static boolean four_bit_ripple_carry_addersum1(final boolean four_bit_ripple_carry_addera0, final boolean four_bit_ripple_carry_adderb0, final boolean four_bit_ripple_carry_adderCin, final boolean four_bit_ripple_carry_addera1, final boolean four_bit_ripple_carry_adderb1) { return or(and(or(and(or(and(not(four_bit_ripple_carry_addera0) , four_bit_ripple_carry_adderb0) , and(not(four_bit_ripple_carry_adderb0) , four_bit_ripple_carry_addera0) ) , four_bit_ripple_carry_adderCin) , and(four_bit_ripple_carry_addera0, four_bit_ripple_carry_adderb0) ) , not(or(and(not(four_bit_ripple_carry_addera1) , four_bit_ripple_carry_adderb1) , and(not(four_bit_ripple_carry_adderb1) , four_bit_ripple_carry_addera1) ) ) ) , and(or(and(not(four_bit_ripple_carry_addera1) , four_bit_ripple_carry_adderb1) , and(not(four_bit_ripple_carry_adderb1) , four_bit_ripple_carry_addera1) ) , not(or(and(or(and(not(four_bit_ripple_carry_addera0) , four_bit_ripple_carry_adderb0) , and(not(four_bit_ripple_carry_adderb0) , four_bit_ripple_carry_addera0) ) , four_bit_ripple_carry_adderCin) , and(four_bit_ripple_carry_addera0, four_bit_ripple_carry_adderb0) ) ) ) ) ;}
    public static boolean four_bit_ripple_carry_addersum2(final boolean four_bit_ripple_carry_addera0, final boolean four_bit_ripple_carry_adderb0, final boolean four_bit_ripple_carry_adderCin, final boolean four_bit_ripple_carry_addera1, final boolean four_bit_ripple_carry_adderb1, final boolean four_bit_ripple_carry_addera2, final boolean four_bit_ripple_carry_adderb2) { return or(and(or(and(or(and(or(and(not(four_bit_ripple_carry_addera0) , four_bit_ripple_carry_adderb0) , and(not(four_bit_ripple_carry_adderb0) , four_bit_ripple_carry_addera0) ) , four_bit_ripple_carry_adderCin) , and(four_bit_ripple_carry_addera0, four_bit_ripple_carry_adderb0) ) , or(and(not(four_bit_ripple_carry_addera1) , four_bit_ripple_carry_adderb1) , and(not(four_bit_ripple_carry_adderb1) , four_bit_ripple_carry_addera1) ) ) , and(four_bit_ripple_carry_addera1, four_bit_ripple_carry_adderb1) ) , not(or(and(not(four_bit_ripple_carry_addera2) , four_bit_ripple_carry_adderb2) , and(not(four_bit_ripple_carry_adderb2) , four_bit_ripple_carry_addera2) ) ) ) , and(or(and(not(four_bit_ripple_carry_addera2) , four_bit_ripple_carry_adderb2) , and(not(four_bit_ripple_carry_adderb2) , four_bit_ripple_carry_addera2) ) , not(or(and(or(and(or(and(not(four_bit_ripple_carry_addera0) , four_bit_ripple_carry_adderb0) , and(not(four_bit_ripple_carry_adderb0) , four_bit_ripple_carry_addera0) ) , four_bit_ripple_carry_adderCin) , and(four_bit_ripple_carry_addera0, four_bit_ripple_carry_adderb0) ) , or(and(not(four_bit_ripple_carry_addera1) , four_bit_ripple_carry_adderb1) , and(not(four_bit_ripple_carry_adderb1) , four_bit_ripple_carry_addera1) ) ) , and(four_bit_ripple_carry_addera1, four_bit_ripple_carry_adderb1) ) ) ) ) ;}
    public static boolean four_bit_ripple_carry_addersum3(final boolean four_bit_ripple_carry_addera0, final boolean four_bit_ripple_carry_adderb0, final boolean four_bit_ripple_carry_adderCin, final boolean four_bit_ripple_carry_addera1, final boolean four_bit_ripple_carry_adderb1, final boolean four_bit_ripple_carry_addera2, final boolean four_bit_ripple_carry_adderb2, final boolean four_bit_ripple_carry_addera3, final boolean four_bit_ripple_carry_adderb3) { return or(and(or(and(or(and(or(and(or(and(not(four_bit_ripple_carry_addera0) , four_bit_ripple_carry_adderb0) , and(not(four_bit_ripple_carry_adderb0) , four_bit_ripple_carry_addera0) ) , four_bit_ripple_carry_adderCin) , and(four_bit_ripple_carry_addera0, four_bit_ripple_carry_adderb0) ) , or(and(not(four_bit_ripple_carry_addera1) , four_bit_ripple_carry_adderb1) , and(not(four_bit_ripple_carry_adderb1) , four_bit_ripple_carry_addera1) ) ) , and(four_bit_ripple_carry_addera1, four_bit_ripple_carry_adderb1) ) , or(and(not(four_bit_ripple_carry_addera2) , four_bit_ripple_carry_adderb2) , and(not(four_bit_ripple_carry_adderb2) , four_bit_ripple_carry_addera2) ) ) , and(four_bit_ripple_carry_addera2, four_bit_ripple_carry_adderb2) ) , not(or(and(not(four_bit_ripple_carry_addera3) , four_bit_ripple_carry_adderb3) , and(not(four_bit_ripple_carry_adderb3) , four_bit_ripple_carry_addera3) ) ) ) , and(or(and(not(four_bit_ripple_carry_addera3) , four_bit_ripple_carry_adderb3) , and(not(four_bit_ripple_carry_adderb3) , four_bit_ripple_carry_addera3) ) , not(or(and(or(and(or(and(or(and(not(four_bit_ripple_carry_addera0) , four_bit_ripple_carry_adderb0) , and(not(four_bit_ripple_carry_adderb0) , four_bit_ripple_carry_addera0) ) , four_bit_ripple_carry_adderCin) , and(four_bit_ripple_carry_addera0, four_bit_ripple_carry_adderb0) ) , or(and(not(four_bit_ripple_carry_addera1) , four_bit_ripple_carry_adderb1) , and(not(four_bit_ripple_carry_adderb1) , four_bit_ripple_carry_addera1) ) ) , and(four_bit_ripple_carry_addera1, four_bit_ripple_carry_adderb1) ) , or(and(not(four_bit_ripple_carry_addera2) , four_bit_ripple_carry_adderb2) , and(not(four_bit_ripple_carry_adderb2) , four_bit_ripple_carry_addera2) ) ) , and(four_bit_ripple_carry_addera2, four_bit_ripple_carry_adderb2) ) ) ) ) ;}
    public static boolean full_adderCout(final boolean full_adderA, final boolean full_adderB, final boolean full_adderCin) { return or(and(or(and(not(full_adderA) , full_adderB) , and(not(full_adderB) , full_adderA) ) , full_adderCin) , and(full_adderA, full_adderB) ) ;}
    public static boolean full_adderS(final boolean full_adderA, final boolean full_adderB, final boolean full_adderCin) { return or(and(or(and(not(full_adderA) , full_adderB) , and(not(full_adderB) , full_adderA) ) , not(full_adderCin) ) , and(not(or(and(not(full_adderA) , full_adderB) , and(not(full_adderB) , full_adderA) ) ) , full_adderCin) ) ;}
    public static boolean half_adderC(final boolean half_adderA, final boolean half_adderB) { return and(half_adderA, half_adderB) ;}
    public static boolean half_adderS(final boolean half_adderA, final boolean half_adderB) { return not(or(half_adderA, half_adderB) ) ;}
}
