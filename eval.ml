#use "translator.ml";;

let eval () =
  print_string "\n";
  try
  while true do
    print_string "[ocamlshell@454]$ ";
    let line = read_line () in
    let tree = ast_ize_P (parse ecg_parse_table line) in
    let input = read_line () in
    print_string (interpret tree input)
  done
  with End_of_file -> print_string ("Bye :)\n");;

(* Execute function "eval" iff run as a stand-alone program. *)
if !Sys.interactive then () else eval ();;
