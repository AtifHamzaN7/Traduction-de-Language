(* Module de la passe de typage *)
(* doit être conforme à l'interface Passe *)
open Tds
open Exceptions
open Ast
open Type

type t1 = Ast.AstTds.programme
type t2 = Ast.AstType.programme
(* getType : info_ast -> typ *)
(* Paramètre info : l'information associée à un identifiant *)
(* Renvoie le type de l'identifiant *)
let getType info = 
  match info_ast_to_info info with
  | InfoVar (_,t,_,_) -> t
  | InfoConst _ -> Int
  | InfoFun (_,t,_) -> t

(* analyse_type_affectable : AstTds.affectable -> AstType.affectable * typ *)
(* Paramètre a : l'affectable à analyser *)
(* Vérifie la bonne utilisation des types et transforme l'affectable en un affectable de type AstType.affectable *)
(* Renvoie un couple composé de l'affectable transformé et de son type *)
(* Erreur si mauvaise utilisation des types *)
let rec analyse_type_affectable a =
match a with 
(* Si c'est un identifiant, on retourne le type de l'identifiant. *)
  | AstTds.Ident info_ast -> 
        begin 
          match info_ast_to_info info_ast with 
            | InfoVar(_,t,_,_) -> ((AstType.Ident info_ast),t)
            | InfoConst(_,_) -> ((AstType.Ident info_ast),Int )
            | _ -> failwith ("Erreur Interne")
        end
  | AstTds.Deref aff ->
  (* Analyse de l'affectable *)
  let (naff, t) = analyse_type_affectable aff in
  begin
  match t with
    | Pointeur(t) ->
      (* Si l'affectable est de type Pointeur, renvoie d'un couple composé du type
      de l'affectable et du nouveau DeRef *)
      ( AstType.Deref(naff), t)
    | _ ->  raise (TypeInattendu (t,Pointeur Undefined))
   end
  


(* analyse_type_expression : AstTds.expression -> AstType.expression * typ *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des types et transforme l'expression en une expression de type AstType.expression *)
(* Renvoie un couple composé de l'expression transformée et de son type *)
(* Erreur si mauvaise utilisation des types *)
let rec analyse_type_expression e = 
  match e with

  | AstTds.AppelFonction (info, le) ->
    begin
    match  info_ast_to_info info with
    |InfoFun(_,tr,ltp) -> 
      let nlet = List.map analyse_type_expression le in
      let nlt = List.map snd nlet in 
      let nle = List.map fst nlet in
      if est_compatible_list ltp nlt then (AstType.AppelFonction(info, nle), tr)
      else raise (TypesParametresInattendus(nlt,ltp))
    |_ -> failwith "Erreur Interne"
    end

  | AstTds.Affectable aff -> 
    let (na,typ) = analyse_type_affectable aff in
      (AstType.Affectable(na),typ)
  
   

  | AstTds.Binaire(op, e1, e2) ->
    begin
    let (ne1, t1) = analyse_type_expression  e1 in
    let (ne2, t2) = analyse_type_expression  e2 in
    match (op, t1, t2) with 
    |Plus, Int, Int -> (AstType.Binaire(PlusInt, ne1, ne2), Int)
    |Plus, Rat, Rat -> (AstType.Binaire(PlusRat, ne1, ne2), Rat)
    |Mult, Int, Int -> (AstType.Binaire(MultInt, ne1, ne2), Int)
    |Mult, Rat, Rat -> (AstType.Binaire(MultRat, ne1, ne2), Rat)
    |Equ, Int, Int -> (AstType.Binaire(EquInt, ne1, ne2), Bool)
    |Equ, Bool, Bool -> (AstType.Binaire(EquBool, ne1, ne2), Bool)
    |Fraction, Int, Int -> (AstType.Binaire(Fraction, ne1, ne2), Rat)
    |Inf, Int, Int -> (AstType.Binaire(Inf, ne1, ne2), Bool)
    |_ -> raise(TypeBinaireInattendu (op ,t1 ,t2))
    end

  | AstTds.Unaire(op, e1) ->
    begin
    let unaire = 
      match op with
      |AstSyntax.Numerateur -> AstType.Numerateur
      |AstSyntax.Denominateur -> AstType.Denominateur
    in
    let (ne, te) = analyse_type_expression e1 in
    if est_compatible te Rat then (AstType.Unaire(unaire, ne), Int)
    else raise (TypeInattendu(te , Rat))
    end

  | AstTds.Booleen b ->
    ( AstType.Booleen b, Bool)

  | AstTds.Entier i ->
    (AstType.Entier i, Int)

  | AstTds.New t -> (AstType.New t, Pointeur(t))

  |AstTds.Adresse a -> 
    begin
      match info_ast_to_info a with
      |InfoVar(_,t,_,_)-> (AstType.Adresse a, Pointeur t )
      | _ -> failwith "Erreur Interne"
    end
  | AstTds.Null -> (AstType.Null, Pointeur(Undefined))  


(* analyse_type_instruction : AstTds.instruction -> AstType.instruction *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des types et transforme l'instruction en une instruction de type AstType.instruction *)
(* Erreur si mauvaise utilisation des types *)
let rec analyse_type_instruction i =
  match i with
  | AstTds.Declaration (t, info, e) ->
    begin
    let (ne,te) = analyse_type_expression e in
    if est_compatible t te then
      begin
      modifier_type_variable t info; 
      AstType.Declaration(info,ne)
      end
    else raise (TypeInattendu(te, t))
    end
      
  | AstTds.Affectation (aff,e) ->
    let (na, ta) = analyse_type_affectable aff in
    let (ne, te) = analyse_type_expression e in
      if est_compatible ta te then 
        AstType.Affectation(na, ne)
      else
        raise (TypeInattendu (te, ta))
    
  | AstTds.Affichage e ->
    begin
    let (ne,te) = analyse_type_expression e in
    match te with
    |Int -> AstType.AffichageInt ne
    |Rat -> AstType.AffichageRat ne
    |Bool -> AstType.AffichageBool ne
    |_ -> raise (TypeInattendu(te,Bool))
    end


  | AstTds.Conditionnelle (e,bt,be) ->
    begin
    let (ne,te) = analyse_type_expression e in
    match te with
    |Bool -> let nbt = analyse_type_bloc bt in  
              let nbe = analyse_type_bloc be in  
              AstType.Conditionnelle(ne, nbt, nbe)
    |_ -> raise (TypeInattendu(te, Bool))
    end

  | AstTds.TantQue (e,bt) ->
    begin
    let (ne,te) = analyse_type_expression e in
    match te with
    |Bool -> let nbt = analyse_type_bloc bt in  
              AstType.TantQue(ne, nbt)
    |_ -> raise (TypeInattendu(te, Bool))
    end

  | AstTds.Retour (e, ia) ->
    begin
    let (ne,te) = analyse_type_expression e in
    match info_ast_to_info ia with 
    |InfoFun(_, tr, _) -> if est_compatible tr te then AstType.Retour(ne, ia)
                           else raise (TypeInattendu(te,tr))
    | _ -> raise RetourDansMain
    end

  | AstTds.Staticlocal (_, _, _) ->
      AstType.Empty
  

  | AstTds.Empty -> AstType.Empty
    


(* analyse_type_bloc : AstTds.bloc -> AstType.bloc *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc en un bloc de type AstTds.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_type_bloc li =
 List.map analyse_type_instruction li 



(* analyse_type_fonction : AstTds.fonction -> AstType.fonction  *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_type_fonction  (AstTds.Fonction(t,info,lp,li))  =
  let lptype = List.map fst lp in
  modifier_type_fonction t lptype info;
  let infoanalyse = List.map( fun (x,y) -> modifier_type_variable x y; (x,y) ) lp in
  let lpi = List.map snd infoanalyse in
  let nli = analyse_type_bloc li in
  AstType.Fonction(info, lpi, nli)


let analyse_type_fonctions lf =
  List.map analyse_type_fonction lf


  (* staticlocal_to_global : AstTds.instruction -> AstTds.var option *)
(* Paramètre i : l'instruction Staticlocal à convertir *)
(* Renvoie une option contenant une variable globale ou None si l'instruction n'est pas une Staticlocal *)
let staticlocal_to_global i =
  match i with
  | AstTds.Staticlocal (t, info, e) ->
    Some (AstTds.Static (t, info, e))
  | _ -> None

(* staticlocals_from_bloc : AstTds.bloc -> AstTds.var list *)
(* Paramètre li : le bloc d'instructions à analyser *)
(* Renvoie la liste des variables statiques locales converties en globales *)
let staticlocals_from_bloc li =
  List.filter_map staticlocal_to_global li

  (* staticlocals_from_fonctions : AstTds.fonction list -> AstTds.var list *)
  (* Paramètre lf : la liste des fonctions à analyser *)
  (* Renvoie la liste des variables statiques locales converties en globales pour toutes les fonctions *)
  let staticlocals_from_fonctions lf =
    List.flatten (List.map (fun (AstTds.Fonction(_, _, _, li)) -> staticlocals_from_bloc li) lf)

  (* analyse_type_variable :  AstTds.var -> AstType.var *)
(* Paramètre v : la variable globale à analyser *)
(* Vérifie le bon typage *)
(* Erreur si mauvais typage *)
  let analyse_type_variable (AstTds.Static (t, info, e)) =
    let (ne,te) = analyse_type_expression e in
    if est_compatible t te then
      begin
      modifier_type_variable t info; 
      (* le type est déjà dans l'infovar de la variable globale dans la passe d'avant puisque on savait son type*)
      AstType.Static(info,ne)  
      end  
    else raise (TypeInattendu(te, t))
    

(* analyser : AstTds.programme -> AstType.programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme
en un programme de type AstTds.programme *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstTds.Programme (vars,fs,prog)) =
  (* Collecter les Staticlocal dans le bloc principal *)
  let staticlocals =  staticlocals_from_fonctions fs in
  let all_vars = vars @ staticlocals in
  let nvars = List.map analyse_type_variable all_vars in 
  let tf = analyse_type_fonctions fs in
  let nf = analyse_type_bloc prog in
  AstType.Programme(nvars ,tf, nf)

  