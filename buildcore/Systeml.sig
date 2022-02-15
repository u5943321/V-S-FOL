signature Systeml =
sig

  val systeml : string list -> OS.Process.status
  val system_ps : string -> OS.Process.status
  val systeml_out : {outfile:string} -> string list -> OS.Process.status
  val exec : string * string list -> 'a
  val protect : string -> string
  val xable_string : string -> string
  val mk_xable : string -> OS.Process.status
  val OS : string

  val find_my_path : unit -> string

  val pointer_eq : 'a * 'a -> bool
  val bindstr : string -> string
   (* emits code that tries to quietly emulate the action of the argument
      when fed to the compiler.  For MoscowML, this is the identity function
      (and it won't be quiet). *)

  (* canonical source of version information *)
  val release : string
  val version : int

end
