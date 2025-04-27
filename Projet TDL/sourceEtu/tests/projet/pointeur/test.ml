open Rat
open Compilateur
open Exceptions

exception ErreurNonDetectee

(* Changer le chemin d'accès du jar. *)
let runtamcmde = "java -jar ../../../../../tests/runtam.jar"
(* let runtamcmde = "java -jar /mnt/n7fs/.../tools/runtam/runtam.jar" *)

(* Execute the TAM code obtained from the rat file and return the ouptut of this code *)
let runtamcode cmde ratfile =
  let tamcode = compiler ratfile in
  let (tamfile, chan) = Filename.open_temp_file "test" ".tam" in
  output_string chan tamcode;
  close_out chan;
  let ic = Unix.open_process_in (cmde ^ " " ^ tamfile) in
  let printed = input_line ic in
  close_in ic;
  Sys.remove tamfile;    (* à commenter si on veut étudier le code TAM. *)
  String.trim printed

(* Compile and run ratfile, then print its output *)
let runtam ratfile =
  print_string (runtamcode runtamcmde ratfile)

(****************************************)
(** Chemin d'accès aux fichiers de test *)
(****************************************)

let pathFichiersRat = "../../../../../tests/projet/pointeur/fichiersRat/"
  (*"/home/haf6850/Bureau/2A/TDL/TP2-6/sourceEtu/tests/pointeur/fichiersRat/"*)


(**********)
(*  TESTS *)
(**********)

(* Tests de pointeurs *)

let%expect_test "test_exemple_projet" =
  runtam (pathFichiersRat^"test_exemple_projet.rat");
  [%expect{| 423 |}]

  let%expect_test "test_def_rat" =
  runtam (pathFichiersRat^"test_def_rat.rat");
  [%expect{| [5/2] |}]


  let%expect_test "test_def_int" =
  runtam (pathFichiersRat^"test_def_int.rat");
  [%expect{| 5 |}]


  let%expect_test "test_def_null" =
  runtam (pathFichiersRat^"test_def_null.rat");
  [%expect{| 0 |}]
 

 let%expect_test "test_new_int" =
  runtam (pathFichiersRat^"test_new_int.rat");
  [%expect{| 444 |}]

  let%expect_test "test_mauvaise_def" =
  try let _ = runtam (pathFichiersRat^"test_mauvaise_def.rat")
  in raise ErreurNonDetectee 
  with 
  | TypeInattendu _ -> ();
  [%expect{| |}]

