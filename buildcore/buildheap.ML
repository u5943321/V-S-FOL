val _ = use "buildcore/Systeml.sig";
val _ = use "buildcore/Systeml.sml";
val _ = use "buildcore/QuoteFilter.sml";
val _ = use "buildcore/QFRead.sig";
val _ = use "buildcore/QFRead.sml";
val _ = use "buildcore/holrepl.ML";

fun main() = let
  val diag = case CommandLine.arguments() of
                 ["-d"] => (fn s => TextIO.output(TextIO.stdErr, s ^ "\n"))
               | _ => (fn s => ())
in
  PolyML.print_depth 100;
  HOL_REPL.sigint_handler();
  diag "Starting REPL";
  HOL_REPL.topLevel diag {startExec = fn () => (),
                          endExec = fn () => (),
                          exitLoop = fn () => false,
                          exitOnError = false,
                          isInteractive = true,
                          nameSpace = PolyML.globalNameSpace}
end
