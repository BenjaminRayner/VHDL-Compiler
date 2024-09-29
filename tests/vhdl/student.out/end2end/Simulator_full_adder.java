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

public final class Simulator_full_adder {
    public static void main(final String[] args) {
        // read the input F program
        // write the output
        // read input WProgram
        final CommandLine cmd = new CommandLine(args);
        final String input = cmd.readInputSpec();
        final WProgram wprogram = WParboiledParser.parse(input);
        // construct storage for output
        Map<String,StringBuilder> output = new LinkedHashMap<String,StringBuilder>();
        output.put("full_adderCout", new StringBuilder());
        output.put("full_adderS", new StringBuilder());
        // loop over each time step
        final int timeCount = wprogram.timeCount();
        for (int time = 0; time < timeCount; time++) {
            // values of input variables at this time step
            final boolean in_full_adderA = wprogram.valueAtTime("full_adderA", time);
            final boolean in_full_adderB = wprogram.valueAtTime("full_adderB", time);
            final boolean in_full_adderCin = wprogram.valueAtTime("full_adderCin", time);
            // values of output variables at this time step
            final String out_full_adderCout = full_adderCout(in_full_adderA, in_full_adderB, in_full_adderCin) ? "1 " : "0 ";
            final String out_full_adderS = full_adderS(in_full_adderA, in_full_adderB, in_full_adderCin) ? "1 " : "0 ";
            // store outputs
            output.get("full_adderCout").append(out_full_adderCout);
            output.get("full_adderS").append(out_full_adderS);
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
    public static boolean full_adderCout(final boolean full_adderA, final boolean full_adderB, final boolean full_adderCin) { return or(and(or(and(not(full_adderA) , full_adderB) , and(not(full_adderB) , full_adderA) ) , full_adderCin) , and(full_adderA, full_adderB) ) ;}
    public static boolean full_adderS(final boolean full_adderA, final boolean full_adderB, final boolean full_adderCin) { return or(and(or(and(not(full_adderA) , full_adderB) , and(not(full_adderB) , full_adderA) ) , not(full_adderCin) ) , and(not(or(and(not(full_adderA) , full_adderB) , and(not(full_adderB) , full_adderA) ) ) , full_adderCin) ) ;}
}
