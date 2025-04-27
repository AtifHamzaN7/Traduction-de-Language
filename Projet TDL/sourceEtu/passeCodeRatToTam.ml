(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)
open Tds
open Ast
open Type
open Code
open Tam


type t1 = Ast.AstPlacement.programme
type t2 = string


(* analyse_code_affectable : AstType.affectable -> bool -> (typ * string) *)
(* Paramètre a : l'affectable à analyser *)
(* Paramètre modif : indique si l'affectable est modifiable (true) ou non (false) *)
(* Retourne un couple composé du type de l'affectable et du code TAM correspondant *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_code_affectable a modif =
  match a with
  |AstType.Ident ia -> 
    begin
      match info_ast_to_info  ia with 
      |InfoVar(_, t, dep,reg) ->
        let taille_type =  getTaille t in 
        if modif then 
          let code  = store taille_type dep reg in (t, code)
      else 
        let code = load taille_type dep reg in (t, code)
      |InfoConst (_,n) ->
        let code = loadl_int n in (Int, code )
      |_ -> failwith"Erreur Interne"
      end
  |AstType.Deref  aff -> 
    let (t, code ) = analyse_code_affectable aff false in
    let taille_type =  getTaille t in
    if modif then 
      (t, code ^ (storei taille_type))
    else 
      (t, code ^ loadi taille_type)
  
    


(* analyse_code_expression : AstType.expression -> string *)
(* Paramètre e : l'expression à analyser *)
(* Retourne le code TAM correspondant à l'expression *)

let rec analyse_code_expression e = 
  match e with

  | AstType.AppelFonction (ia, le) ->
    begin
    match info_ast_to_info ia with
    |InfoFun(n,_,_) -> (List.fold_right (fun e c -> (analyse_code_expression e) ^ c) le "" )^
                       call "LB" n
    |_ -> failwith "Erreur Interne"
    end
  
  | AstType.Binaire(b, e1, e2) ->
    let code =
      match b with
      | PlusInt -> subr "IAdd"
      | PlusRat -> call "LB" "RAdd"
      | MultInt -> subr "IMul"
      | MultRat -> call "LB" "RMul"
      | EquBool -> subr "IEq"
      | EquInt -> subr "IEq"
      | Inf -> subr "ILss"
      | Fraction -> call "ST" "norm"
    in 
    analyse_code_expression e1 ^ analyse_code_expression e2 ^ code

  | AstType.Unaire(b, e1) ->
    let code = 
      match b with 
      |Numerateur -> pop 0 1
      |Denominateur -> pop 1 1
    in 
    analyse_code_expression e1 ^ code

  | AstType.Booleen b ->
    if b then loadl_int 1 else loadl_int 0 
    

  | AstType.Entier i -> loadl_int i

  | AstType.Null -> loadl_int (-1)

  | AstType.Adresse a -> 
    begin 
      match info_ast_to_info a with 
          | InfoVar(_,_,dep,reg)-> loada dep reg
          | _ -> failwith"error"
    end

  | AstType.New t ->
      loadl_int (getTaille t) ^
      subr "Malloc" 

  | AstType.Affectable a ->
    let (_,code) = analyse_code_affectable a false in code

(* analyse_code_instruction : AstType.instruction -> string *)
(* Paramètre i : l'instruction à analyser *)
(* Retourne le code TAM correspondant à l'instruction *)

let rec analyse_code_instruction i =
  match i with
  | AstPlacement.Declaration (info, e) ->
    begin
      match info_ast_to_info info with
      |InfoVar(_,t,dep,reg) -> let taille = (getTaille t) in
                            push (taille ) ^
                            analyse_code_expression e ^
                            store taille dep reg                       
      |_ -> failwith  "Erreur interne"
    end
      
  | AstPlacement.Affectation (aff,e) ->
    let code1 = analyse_code_expression e in 
    let (_,code2) = analyse_code_affectable aff true in 
    code1 ^ code2  
  
  | AstPlacement.AffichageInt e ->
    analyse_code_expression e ^
    subr "IOut"

  | AstPlacement.AffichageRat e ->
    analyse_code_expression e ^
    call "ST" "ROut"
          

  | AstPlacement.AffichageBool e ->
    analyse_code_expression e ^
    subr "BOut"


  | AstPlacement.Conditionnelle (e,bt,be) ->
    let etiquetteE = getEtiquette () in
    let etiquetteFin = getEtiquette () in
    analyse_code_expression e ^
    jumpif 0 etiquetteE ^
    analyse_code_bloc bt ^
    jump etiquetteFin ^
    etiquetteE ^ "\n" ^
    analyse_code_bloc be ^
    etiquetteFin ^ "\n"

  | AstPlacement.TantQue (e,bt) ->
    let etiquettedeb = getEtiquette () in
    let etiquetteFin = getEtiquette () in
    etiquettedeb ^ "\n" ^
    analyse_code_expression e ^
    jumpif 0 etiquetteFin ^
    analyse_code_bloc bt ^
    jump etiquettedeb ^
    etiquetteFin ^ "\n" 


  | AstPlacement.Retour (e, tret, tparam) ->
    analyse_code_expression e ^
    return tret tparam


  | AstPlacement.Empty -> ""
    
  

(* analyse_code_bloc : AstType.bloc -> string *)
(* Paramètre b : le bloc à analyser *)
(* Retourne le code TAM correspondant au bloc *)

and analyse_code_bloc (li,taille) =
  List.fold_right (fun i q -> (analyse_code_instruction i) ^ q) li "" ^ 
  pop 0 taille


(* analyse_code_fonction : AstType.fonction -> string *)
(* Paramètre f : la fonction à analyser *)
(* Retourne le code TAM correspondant à la fonction *)

let analyse_code_fonction  (AstPlacement.Fonction(info,_,b))  =
match info_ast_to_info info with
|InfoFun(nom, tr , _) -> 
  nom ^ "\n" ^
  analyse_code_bloc ((fst b) , ((snd b) + getTaille tr)) ^
  "HALT\n"
|_ -> failwith "Erreur Interne"

(* analyse_code_vars : AstPlacement.var -> string *)
(* Paramètre v : la variable à analyser *)
(* Retourne le code TAM correspondant à la variable *)
let analyse_code_vars (AstPlacement.Static (info, e)) =
  begin
    match info_ast_to_info info with
    |InfoVar(_,t,dep,reg) -> let taille = (getTaille t) in
                          (*print_endline ("Génération de code pour la variable à l'adresse : " ^ reg ^ " avec déplacement : " ^ string_of_int dep);*)
                          push (taille ) ^
                          analyse_code_expression e ^
                          store taille dep reg                       
    |_ -> failwith  "Erreur interne"
  end
(* analyser : AstType.programme -> string *)
(* Paramètre : le programme à analyser *)
(* Retourne le code TAM correspondant au programme *)

let analyser (AstPlacement.Programme (vars, lf, bloc)) =
 
  getEntete() ^
  
  List.fold_right(fun f c -> analyse_code_fonction f ^ c ) lf "" ^
  "main\n" ^ 
  List.fold_right(fun var c -> analyse_code_vars var ^ c ) vars "" ^
  analyse_code_bloc bloc ^
  "HALT\n"
  
  

  
