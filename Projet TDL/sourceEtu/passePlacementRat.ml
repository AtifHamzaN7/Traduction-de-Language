(* Module de la passe de placement mémoire *)
(* doit être conforme à l'interface Passe *)
open Tds
open Ast
open Type

type t1 = Ast.AstType.programme
type t2 = Ast.AstPlacement.programme



(* analyse_placement_instruction : AstType.instruction -> int -> string -> (AstPlacement.instruction * int) *)
(* Paramètre i : l'instruction à analyser *)
(* Paramètre depl : le déplacement (adresse) de la variable *)
(* Paramètre reg : le registre où la variable est stockée *)
(* Retourne une paire composée d'une instruction transformée (AstPlacement.instruction) et de la taille de la variable associée (int) *)

let rec analyse_placement_instruction i depl reg =
  match i with
  | AstType.Declaration (info, e) ->
    begin
    match info_ast_to_info info with
    |InfoVar(_,t,_,_) -> modifier_adresse_variable depl reg info;
                        (AstPlacement.Declaration(info,e), getTaille t)
    |_ -> failwith  "Erreur interne"
    end
      
  | AstType.Affectation (ia,e) ->
           (AstPlacement.Affectation(ia,e),0)
    
  
  | AstType.AffichageInt e ->
          (AstPlacement.AffichageInt e,0)

  | AstType.AffichageRat e ->
          (AstPlacement.AffichageRat e,0)

  | AstType.AffichageBool e ->
          (AstPlacement.AffichageBool e,0)



  | AstType.Conditionnelle (e,bt,be) ->
      let nbt = analyse_placement_bloc bt depl reg in
      let nbe = analyse_placement_bloc be depl reg in
      (AstPlacement.Conditionnelle(e,nbt,nbe),0)

  | AstType.TantQue (e,bt) ->
     let nbt = analyse_placement_bloc bt depl reg in
     (AstPlacement.TantQue(e,nbt),0)

  | AstType.Retour (e, ia) ->
    begin
      match info_ast_to_info ia with
      |InfoFun(_,tr,tp) -> 
        let listetaille = List.map getTaille tp in
        let sommetaille = List.fold_left (+) 0 listetaille in
                    (AstPlacement.Retour(e, getTaille tr,sommetaille),0)
      |_ -> failwith  "Erreur interne"

    end

  | AstType.Empty -> (AstPlacement.Empty,0)
    
  

(* analyse_placement_bloc : AstType.bloc -> int -> string -> AstPlacement.bloc *)
(* Paramètre b : le bloc à analyser *)
(* Paramètre depl : le déplacement (adresse) de la variable *)
(* Paramètre reg : le registre où la variable est stockée *)
(* Retourne un bloc transformé de type AstPlacement.bloc *)


and analyse_placement_bloc li depl reg =
  match li with
  |[] -> ([],0)
  |i::q ->let (ni,ti) = analyse_placement_instruction i depl reg in
          let (nli,tb) = analyse_placement_bloc q (ti + depl) reg in
          (ni::nli, ti + tb)


(* analyse_placement_param : parametre list -> int *)
(* Paramètre lp : la liste des paramètres à analyser. *)
(* Retourne la taille totale des paramètres dans le bloc, après avoir mis à jour les adresses des variables. *)

let rec analyse_placement_param lp =
  begin
  match lp with
  |[] -> 0
  |i::q -> let tailleq = analyse_placement_param q in
            begin
              match info_ast_to_info i with
              |InfoVar(_,t,_,_) -> let taillei = getTaille t in         
               modifier_adresse_variable (-tailleq -taillei) "LB" i; (taillei + tailleq)
              |_ -> failwith "Erreur Interne"
            end 
  end
(* analyse_placement_fonction : AstType.fonction -> AstPlacement.fonction *)
(* Paramètre : la fonction à analyser sous forme de `AstType.Fonction`. *)
(* Retourne la fonction transformée sous forme de `AstPlacement.Fonction`. *)
(* Vérifie la bonne utilisation des identifiants dans les paramètres et le corps de la fonction. *)

let analyse_placement_fonction  (AstType.Fonction(info,lp,li))  =
  let _ = analyse_placement_param (lp) in
  let nb = analyse_placement_bloc li 3 "LB" in
  AstPlacement.Fonction(info,lp,nb)

 
(* analyse_variableglobale : AstType.var list -> string -> (AstPlacement.var list * int) *)
(* Paramètres : *)
(* - vars : la liste des variables globales à analyser. *)
(* - reg : le registre dans lequel les variables sont placées (généralement "SB"). *)
(* Retourne : *)
(* - La liste des variables transformées. *)
(* - Le déplacement final après l'analyse des variables globales. *)
let analyse_variable_globale vars reg =
  List.fold_left (fun (vars_acc, current_depl) var ->
    match var with
    | AstType.Static (info, e) -> 
      begin
        match info_ast_to_info info with
        | InfoVar (_, t, _, _) -> 
            (* Modifier l'adresse de la variable globale *)
            modifier_adresse_variable current_depl reg info;
           (* print_endline ("Placement mémoire pour la variable à l'adresse : " ^ reg ^ " avec déplacement : " ^ string_of_int current_depl);*)
            (* Créer la variable transformée et calculer son déplacement *)
            let nvar = AstPlacement.Static (info, e) in
            let var_taille = getTaille t in
            (nvar :: vars_acc, current_depl + var_taille)
        | _ -> failwith "Erreur interne"
      end
  ) ([], 0) vars

(* analyser : AstType.programme -> AstPlacement.programme *)
(* Paramètre : le programme à analyser sous forme de `AstType.Programme`. *)
(* Retourne le programme transformé sous forme de `AstPlacement.Programme`. *)
(* Effectue l'analyse des fonctions et du bloc principal du programme. *)
let analyser (AstType.Programme (vars,lf,bloc)) =
 (* Analyse des variables globales *)
 let nvars, final_depl = analyse_variable_globale vars "SB" in

 (* Analyser les fonctions avec les paramètres et les instructions *)
 let nilf = List.map analyse_placement_fonction lf in

 (* Analyser le bloc principal avec le déplacement actuel et le registre utilisé pour le corps *)
 let nb = analyse_placement_bloc bloc final_depl "SB" in

 (* Retourner le programme transformé avec les variables globales et les autres informations *)
 AstPlacement.Programme (nvars, nilf, nb)
 
 
 
 
  
  

  
