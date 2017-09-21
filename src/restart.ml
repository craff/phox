open Unix
open Sys


let restart () = exit 3

let all_signals = [
  sigabrt;   (* Abnormal termination *)
  sigalrm;   (* Timeout *)
  sigfpe;    (* Arithmetic exception *)
  sighup;    (* Hangup on controlling terminal *)
  sigill;    (* In id hardware instruction *)
  sigint;    (* Interactive interrupt (ctrl-C) *)
  sigkill;   (* Termination (cannot be ignored) *)
  sigpipe;   (* Broken pipe *)
  sigquit;   (* Interactive termination *)
  sigsegv;   (* In id memory reference *)
  sigterm;   (* Termination *)
  sigusr1;   (* Application-defined signal 1 *)
  sigusr2;   (* Application-defined signal 2 *)
(*  sigchld;       Child process terminated, do not ignore that one !*)
  sigcont;   (* Continue *)
  sigstop;   (* Stop *)
  sigtstp;   (* Interactive stop *)
  sigttin;   (* Terminal read from background process *)
  sigttou;   (* Terminal write from background process *)
  sigvtalrm; (* Timeout in virtual time *)
  sigprof   (* Profiling interrupt *)
]

let ignore_all_signals () =
  let previous = List.map (fun s -> try signal s Signal_ignore with Sys_error _ -> Signal_ignore) all_signals in
  fun () ->
    List.iter2 (fun s b -> try set_signal s b with Sys_error _ -> ()) all_signals previous
  
  
let _ = 
  let restore_signals = ignore_all_signals () in
  try
    while true do
      let pid = fork () in
      if pid = 0 then raise Exit else
      match waitpid [] pid with
  	_, WEXITED 3 -> ()
      | _, WEXITED n -> exit n
      | _, _ -> exit 1
    done
  with Exit -> restore_signals ()


