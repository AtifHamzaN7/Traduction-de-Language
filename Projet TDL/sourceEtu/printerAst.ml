open Ast
open Type

(* Interface d'affichage des arbres abstraits *)
module type PrinterAst =
sig
  module A:Ast

(* string_of_expression :  expression -> string *)
(* transforme une expression en chaîne de caractère *)
val string_of_expression : A.expression -> string

(* string_of_instruction :  instruction -> string *)
(* transforme une instruction en chaîne de caractère *)
val string_of_instruction : A.instruction -> string

(* string_of_fonction :  fonction -> string *)
(* transforme une fonction en chaîne de caractère *)
val string_of_fonction : A.fonction -> string

(* string_of_ast :  ast -> string *)
(* transforme un ast en chaîne de caractère *)
val string_of_programme : A.programme -> string

(* print_ast :  ast -> unit *)
(* affiche un ast *)
val print_programme : A.programme -> unit

end

(*Module d'affiche des AST issus de la phase d'analyse syntaxique *)
module PrinterAstSyntax : PrinterAst with module A = AstSyntax =
struct

  module A = AstSyntax
  open A

  (* Conversion des opérateurs unaires *)
  let string_of_unaire op =
    match op with
    | Numerateur -> "num "
    | Denominateur -> "denom "
    
  (* Conversion des opérateurs binaires *)
  let string_of_binaire b =
    match b with
    | Fraction -> "/ " (* not used *)
    | Plus -> "+ "
    | Mult -> "* "
    | Equ -> "= "
    | Inf -> "< "

    (* Conversion des affectations *)
    let rec string_of_affectable a = 
    match a with
    (*| Deref a -> string_of_affectation a*)
    | Ident n -> n^" "
    | Deref na -> "*" ^ (string_of_affectable na)
  (* Conversion des expressions *)
  let rec string_of_expression e =
    match e with
    | AppelFonction (n,le) -> "call "^n^"("^((List.fold_right (fun i tq -> (string_of_expression i)^tq) le ""))^") "
    | Affectable a -> string_of_affectable a
    | Booleen b -> if b then "true " else "false "
    | Entier i -> (string_of_int i)^" "
    | Unaire (op,e1) -> (string_of_unaire op) ^ (string_of_expression e1)^" "
    | Binaire (b,e1,e2) ->
        begin
          match b with
          | Fraction -> "["^(string_of_expression e1)^"/"^(string_of_expression e2)^"] "
          | _ -> (string_of_expression e1)^(string_of_binaire b)^(string_of_expression e2)^" "
        end
    | Null -> "null"
    | New p -> "(new "^(string_of_type p)^")"
    | Adresse id -> "& "^id^" "
  (* Conversion des instructions *)
  let rec string_of_instruction i =
    match i with
    | Declaration (t, n, e) -> "Declaration  : "^(string_of_type t)^" "^n^" = "^(string_of_expression e)^"\n"
    | Affectation (n,e) ->  "Affectation  : "^(string_of_affectable n)^" = "^(string_of_expression e)^"\n"
    | Constante (n,i) ->  "Constante  : "^n^" = "^(string_of_int i)^"\n"
    | Affichage e ->  "Affichage  : "^(string_of_expression e)^"\n"
    | Conditionnelle (c,t,e) ->  "Conditionnelle  : IF "^(string_of_expression c)^"\n"^
                                  "THEN \n"^((List.fold_right (fun i tq -> (string_of_instruction i)^tq) t ""))^
                                  "ELSE \n"^((List.fold_right (fun i tq -> (string_of_instruction i)^tq) e ""))^"\n"
    | TantQue (c,b) -> "TantQue  : TQ "^(string_of_expression c)^"\n"^
                                  "FAIRE \n"^((List.fold_right (fun i tq -> (string_of_instruction i)^tq) b ""))^"\n"
    | Retour (e) -> "Retour  : RETURN "^(string_of_expression e)^"\n"

    |Staticlocal(t,n,e) -> "Variable Locale : Static" ^(string_of_type t)^" "^n^" = "^(string_of_expression e)^"\n"

  (* Conversion des fonctions *)
  let string_of_fonction (Fonction(t, n, lp, li)) =
    (string_of_type t) ^ " " ^ n ^ " (" ^
    ((List.fold_right (fun (typ, nom, def) tq ->
        (* Ici, tu gères le champ defaut *)
        let def_str = match def with
          | Some _ -> " (par défaut)"  (* Tu peux choisir ce qui est affiché en cas de valeur par défaut *)
          | None -> ""  (* Aucun paramètre par défaut *)
        in
        (string_of_type typ) ^ " " ^ nom ^ def_str ^ " " ^ tq
    ) lp "") ^ ") = \n" ^
    ((List.fold_right (fun i tq -> (string_of_instruction i) ^ tq) li "")) ^ "\n")
  


  let string_of_static (Static(t, s, e)) = "static " ^ string_of_type t ^ " " ^ s ^ " = " ^ string_of_expression e ^ " ;"                                  
  (* Conversion d'un programme Rat *)
  let string_of_programme (Programme (vars,fonctions, instruction)) =
    (* Convertir les variables globales (si nécessaire) *)
    (List.fold_right (fun v tq -> (string_of_static v) ^ tq) vars "" )^
    (List.fold_right (fun f tq -> (string_of_fonction f)^tq) fonctions "")^
    (List.fold_right (fun i tq -> (string_of_instruction i)^tq) instruction "")

  (* Affichage d'un programme Rat *)
  let print_programme programme =
    print_string "AST : \n";
    print_string (string_of_programme programme);
    flush_all ()

end
