structure Systeml :> Systeml = struct

structure CompilerSpecific :>
  sig
    val quietbind : string -> unit
  end
= struct

fun reader s =
    let
      val i = ref 0
      val sz = String.size s
      fun r () = if !i < sz then SOME (String.sub(s,!i)) before i := !i + 1
                 else NONE
    in
      r
    end

fun quietbind s =
    let open PolyML.Compiler
    in
      PolyML.compiler (reader s, [CPOutStream (fn _ => ())]) ()
    end

end

(* This is the UNIX implementation of the Systeml functionality.  It is the
   very first thing compiled by the HOL build process so it absolutely
   can not depend on any other HOL source code. *)

structure Path =  OS.Path
structure Process = OS.Process
structure FileSys = OS.FileSys

open Process
fun concat_wspaces munge strl = String.concatWith " " (map munge strl)

val unix_meta_chars = [#"'", #"\"", #"|", #" ", #">", #"\t", #"\n", #"<",
                       #"\\", #"#"]
fun is_meta c = List.exists (fn y => c = y) unix_meta_chars
fun is_meta_string(s,i) = if i >= size s then false
                          else if is_meta (String.sub(s,i)) then true
                          else is_meta_string(s, i + 1)
fun unix_trans c = if is_meta c then "\\" ^ str c else str c

fun protect s = if is_meta_string(s,0) then String.translate unix_trans s
                else s

val systeml = system o concat_wspaces protect

fun systeml_out {outfile} c =
    system (concat_wspaces protect c ^ " > " ^ protect outfile ^ " 2>&1")

val system_ps = Process.system
(* see winNT-systeml.sml for an explanation of why what is a synonym under
     unix needs to be slightly different on Windows. *)

val OS = case List.find (fn (k,v) => k = "sysname") (Posix.ProcEnv.uname()) of
             NONE => "unknown"
           | SOME p => #2 p

fun exec (x as (comm,args)) =
    (* macos execv fails if the calling process is multi-threaded. *)
    (* Can't lift the check out of the function body because of the value
       restriction *)
    if OS <> "Darwin" then Posix.Process.exec x
    else OS.Process.exit (systeml (comm::tl args))

fun get_first f [] = NONE
  | get_first f (h::t) = case f h of NONE => get_first f t
                                   | x => x


fun find_my_path () = let
  (* assumes directory hasn't been changed yet *)
  val myname = CommandLine.name()
  val {dir,file} = Path.splitDirFile myname
in
  if dir = "" then let
    val pathdirs = String.tokens (fn c => c = #":")
                                 (valOf (Process.getEnv "PATH"))
    open FileSys
    fun checkdir d = let
      val f = Path.concat(d,file)
    in
      if access(f, [A_READ, A_EXEC]) then SOME f else NONE
    end
  in
    valOf (get_first checkdir pathdirs)
  end
  else
    Path.mkAbsolute {path = myname,relativeTo = FileSys.getDir()}
end

fun xable_string s = s

fun mk_xable file =
    let
      val r = systeml ["chmod", "a+x", file]
    in
      if Process.isSuccess r then r
      else if FileSys.access (file,[FileSys.A_EXEC]) then
        (* if we can execute it, then continue with a warning *)
        (print ("Non-fatal warning: couldn't set world execute permission on "^
                file^
                ",\n  but continuing anyway since at least the current user \
                \has execute permission.\n");
         OS.Process.success)
      else (print ("unable to set execute permission on "^file^".\n");
            OS.Process.failure)
    end


fun normPath s = Path.toString(Path.fromString s)

fun fullPath slist =
    normPath (List.foldl (fn (p1,p2) => Path.concat(p2,p1))
                         (hd slist) (tl slist))


val pointer_eq = PolyML.pointerEq

fun bindstr mlcode =
    "val _ = CompilerSpecific.quietbind \"" ^ String.toString mlcode ^ "\""

val release = "VSFOL"
val version = 0

end; (* struct *)
