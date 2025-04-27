(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)
open Tds
open Exceptions
open Ast

type t1 = Ast.AstSyntax.programme
type t2 = Ast.AstTds.programme

(* analyse_tds_affectable : tds -> AstSyntax.affectable -> bool -> AstTds.affectable *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre a : l'affectable à analyser *)
(* Paramètre modif : indique si l'affectable est à gauche (true) ou à droite (false) d'une instruction *)
(* Vérifie la bonne utilisation des identifiants et transforme l'affectable en une affectable de type AstTds.affectable *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_affectable tds a modif =
  match a with
  |AstSyntax.Ident id -> 
    begin
      match chercherGlobalement tds id with
      |None -> raise (IdentifiantNonDeclare id)
      |Some ia -> (
        match info_ast_to_info ia with
        |InfoVar _ ->  AstTds.Ident ia 
        |InfoFun _ -> raise (MauvaiseUtilisationIdentifiant id)
        |InfoConst _ -> 
          if modif then raise (MauvaiseUtilisationIdentifiant id) else (AstTds.Ident ia)

      )
    end
  |AstSyntax.Deref aff -> let naff = analyse_tds_affectable tds aff modif in
                AstTds.Deref(naff)

(* analyse_tds_expression : tds -> AstSyntax.expression -> (tds * (string, AstSyntax.expression option) Hashtbl.t) -> AstTds.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Paramètre (maintds, param_defaut) : un tuple contenant la table des symboles principale et une hashmap des paramètres par défaut des fonctions *)
(* Vérifie la bonne utilisation des identifiants et transforme l'expression en une expression de type AstTds.expression *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_expression tds e (maintds ,param_defaut) = 
  match e with

  | AstSyntax.AppelFonction (id, le) ->
    begin
    match chercherGlobalement tds id with 
  |None ->  raise (IdentifiantNonDeclare id)
  |Some i -> 
    begin  
    match info_ast_to_info i with
    |InfoFun(_,_,_) -> 
      let analyse_args = List.map (fun e -> analyse_tds_expression tds e (maintds, param_defaut)) le in
      let defaut_liste = Hashtbl.find param_defaut id in
      let liste_complete = param_complet maintds param_defaut analyse_args defaut_liste in
      AstTds.AppelFonction (i, liste_complete)
    | _ -> raise (MauvaiseUtilisationIdentifiant id) 
        end
    end

  |AstSyntax.Affectable aff -> 
      begin
        let naff =  analyse_tds_affectable tds aff false in
        AstTds.Affectable naff
      end

  | AstSyntax.Binaire(b, e1, e2) ->
    let e1tds = analyse_tds_expression tds e1 (maintds ,param_defaut) in
    let e2tds = analyse_tds_expression tds e2 (maintds ,param_defaut) in
    AstTds.Binaire(b, e1tds, e2tds)


  | AstSyntax.Unaire(op, e1) ->
    let e1tds = analyse_tds_expression tds e1 (maintds ,param_defaut) in
    AstTds.Unaire(op, e1tds)


  | AstSyntax.Booleen b ->
    AstTds.Booleen b

  | AstSyntax.Entier i ->
    AstTds.Entier i

  | AstSyntax.New t -> AstTds.New t

  | AstSyntax.Null -> AstTds.Null

  |AstSyntax.Adresse a -> 
    begin 
      match chercherGlobalement tds a with
      |Some ia -> (match info_ast_to_info ia with
            |InfoVar _ -> AstTds.Adresse ia
            |_ -> raise (MauvaiseUtilisationIdentifiant a)
            )
      |None ->  raise (IdentifiantNonDeclare a)
    end

(* param_complet : tds -> (string, AstSyntax.expression option) Hashtbl.t -> AstTds.expression list -> AstSyntax.expression option list -> AstTds.expression list *)
(* Paramètre tds : la table des symboles racine (On utilise la table racine pour éviter l'utilisation d'autres variables que celles globales) *)
(* Paramètre param_defaut : dictionnaire des paramètres par défaut des fonctions *)
(* Paramètre args : la liste des arguments analysés *)
(* Paramètre defaut_liste : la liste des paramètres par défaut de la fonction *)
(* Renvoie la liste des arguments complétée avec les paramètres par défaut *)
and param_complet tds_main param_defaut args defaut_liste =
  match (defaut_liste, args) with
    | [], [] -> []
    | (Some (AstSyntax.Defaut(e)))::q, [] ->
        (analyse_tds_expression tds_main e (tds_main, param_defaut)) :: param_complet tds_main param_defaut [] q
    | None :: q, [] -> param_complet tds_main param_defaut [] q 
    | _:: q, arg :: args_q ->
        arg :: param_complet tds_main param_defaut args_q q
    | [], t :: q -> t :: param_complet tds_main param_defaut q []


(* analyse_tds_instruction : tds -> info_ast option -> AstSyntax.instruction -> (tds * (string, AstSyntax.expression option) Hashtbl.t) -> AstTds.instruction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre oia : None si l'instruction i est dans le bloc principal,
                   Some ia où ia est l'information associée à la fonction dans laquelle est l'instruction i sinon *)
(* Paramètre i : l'instruction à analyser *)
(* Paramètre (maintds, param_defaut) : un tuple contenant la table des symboles principale et une hashmap des paramètres par défaut des fonctions *)
(* Vérifie la bonne utilisation des identifiants et transforme l'instruction en une instruction de type AstTds.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_instruction tds oia i (maintds ,param_defaut) =
  match i with
  | AstSyntax.Declaration (t, n, e) ->
      begin
        match chercherLocalement tds n with
        | None ->
            (* L'identifiant n'est pas trouvé dans la tds locale,
            il n'a donc pas été déclaré dans le bloc courant *)
            (* Vérification de la bonne utilisation des identifiants dans l'expression *)
            (* et obtention de l'expression transformée *)
            let ne = analyse_tds_expression tds e  (maintds ,param_defaut) in
            (* Création de l'information associée à l'identfiant *)
            let info = InfoVar (n,Undefined, 0, "") in
            (* Création du pointeur sur l'information *)
            let ia = info_to_info_ast info in
            (* Ajout de l'information (pointeur) dans la tds *)
            ajouter tds n ia;
            (* Renvoie de la nouvelle déclaration où le nom a été remplacé par l'information
            et l'expression remplacée par l'expression issue de l'analyse *)
            AstTds.Declaration (t, ia, ne)
        | Some _ ->
            (* L'identifiant est trouvé dans la tds locale,
            il a donc déjà été déclaré dans le bloc courant *)
            raise (DoubleDeclaration n)
      end
  | AstSyntax.Affectation (aff,e) ->
    let naff = analyse_tds_affectable tds aff true in
    let ne = analyse_tds_expression tds e (maintds ,param_defaut) in
    Affectation (naff, ne)
    
  | AstSyntax.Constante (n,v) ->
      begin
        match chercherLocalement tds n with
        | None ->
          (* L'identifiant n'est pas trouvé dans la tds locale,
             il n'a donc pas été déclaré dans le bloc courant *)
          (* Ajout dans la tds de la constante *)
          ajouter tds n (info_to_info_ast (InfoConst (n,v)));
          (* Suppression du noeud de déclaration des constantes devenu inutile *)
          AstTds.Empty
        | Some _ ->
          (* L'identifiant est trouvé dans la tds locale,
          il a donc déjà été déclaré dans le bloc courant *)
          raise (DoubleDeclaration n)
      end
  | AstSyntax.Affichage e ->
      (* Vérification de la bonne utilisation des identifiants dans l'expression *)
      (* et obtention de l'expression transformée *)
      let ne = analyse_tds_expression tds e (maintds ,param_defaut) in
      (* Renvoie du nouvel affichage où l'expression remplacée par l'expression issue de l'analyse *)
      AstTds.Affichage (ne)
  | AstSyntax.Conditionnelle (c,t,e) ->
      (* Analyse de la condition *)
      let nc = analyse_tds_expression tds c (maintds ,param_defaut) in
      (* Analyse du bloc then *)
      let tast = analyse_tds_bloc tds oia t  (maintds ,param_defaut) in
      (* Analyse du bloc else *)
      let east = analyse_tds_bloc tds oia e (maintds ,param_defaut) in
      (* Renvoie la nouvelle structure de la conditionnelle *)
      AstTds.Conditionnelle (nc, tast, east)
  | AstSyntax.TantQue (c,b) ->
      (* Analyse de la condition *)
      let nc = analyse_tds_expression tds c (maintds ,param_defaut) in
      (* Analyse du bloc *)
      let bast = analyse_tds_bloc tds oia b (maintds ,param_defaut) in
      (* Renvoie la nouvelle structure de la boucle *)
      AstTds.TantQue (nc, bast)
  | AstSyntax.Retour (e) ->
      begin
      (* On récupère l'information associée à la fonction à laquelle le return est associée *)
      match oia with
        (* Il n'y a pas d'information -> l'instruction est dans le bloc principal : erreur *)
      | None -> raise RetourDansMain
        (* Il y a une information -> l'instruction est dans une fonction *)
      | Some ia ->
        (* Analyse de l'expression *)
        let ne = analyse_tds_expression tds e (maintds ,param_defaut) in
        AstTds.Retour (ne,ia)
      end
  | AstSyntax.Staticlocal (t, n, e) -> 
    begin
      match chercherLocalement tds n with
      | None ->   
          let ne = analyse_tds_expression tds e (maintds ,param_defaut) in       
          let info = InfoVar (n,Undefined, 0, "") in     
          let ia = info_to_info_ast info in    
          ajouter tds n ia;  
          AstTds.Staticlocal (t, ia, ne)
      | Some _ ->
          raise (DoubleDeclaration n)
    end



(* analyse_tds_bloc : tds -> info_ast option -> AstSyntax.bloc -> AstTds.bloc *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre oia : None si le bloc li est dans le programme principal,
                   Some ia où ia est l'information associée à la fonction dans laquelle est le bloc li sinon *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc en un bloc de type AstTds.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_tds_bloc tds oia li (maintds, defaut) =
  (* Entrée dans un nouveau bloc, donc création d'une nouvelle tds locale
  pointant sur la table du bloc parent *)
  let tdsbloc = creerTDSFille tds in
  (* Analyse des instructions du bloc avec la tds du nouveau bloc.
     Cette tds est modifiée par effet de bord *)
     let nli = List.map (fun i -> analyse_tds_instruction tdsbloc oia i (maintds, defaut)) li in
     
     nli

(* get_liste_param_defaut : (typ * string * AstSyntax.defaut option) list -> bool -> AstSyntax.defaut option list *)
(* Paramètre params : la liste des paramètres à analyser *)
(* Paramètre defaut_present : booléen indiquant si un paramètre par défaut a déjà été rencontré *)
(* Vérifie la bonne utilisation des paramètres par défaut et renvoie la liste des paramètres par défaut *)
(* Erreur si mauvaise utilisation des paramètres par défaut *)
let rec get_liste_param_defaut params defaut_present =
  match params with
  | [] -> []
  | (_, _, Some d) :: q ->
      (* Si un paramètre par défaut est présent, on continue avec defaut_present à true *)
      Some d :: get_liste_param_defaut q true
  | (_, p, None) :: q ->
      (* Si un paramètre sans valeur par défaut est rencontré après un paramètre par défaut, erreur *)
      if defaut_present then
        raise (ParamDefautnonfin p)
      else
        None :: get_liste_param_defaut q false

(* analyse_tds_fonction : tds -> Hashtbl -> AstSyntax.fonction -> AstTds.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre param_defaut : dictionnaire des paramètres par défaut des fonctions *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_tds_fonction maintds param_defaut (AstSyntax.Fonction(t,n,lp,li)) =
  match chercherGlobalement maintds n with
  | Some _ -> raise (DoubleDeclaration n)
  | None ->
    (*Récupération des paramètres par default*)
    let defaut_liste = get_liste_param_defaut lp false in
    Hashtbl.add param_defaut n defaut_liste;

    (*Gestion de la déclaration de la fonction*)
    let info = InfoFun (n, t, List.map (fun (t, _, _) -> t) lp) in
    let info_ast_fonction = info_to_info_ast info in
    ajouter maintds n info_ast_fonction;
    (*Création de la tds locale pour la fonction*)
    let tds = creerTDSFille maintds in
    let nlp = List.map (fun (typ, nom, _) ->
      begin
        match chercherLocalement tds nom with
        | Some _ -> raise (DoubleDeclaration nom)
        | None ->
          let info = InfoVar (nom, typ, 0, "") in
          let info_ast_arg = info_to_info_ast info in
          ajouter tds nom info_ast_arg;
          (typ, info_ast_arg)
      end
    ) lp in
    let nli = analyse_tds_bloc tds (Some info_ast_fonction) li (maintds, param_defaut) in
    AstTds.Fonction(t, info_ast_fonction, nlp, nli)


(* analyse_tds_variable : tds -> (string, AstSyntax.expression option) Hashtbl.t -> AstSyntax.var -> AstTds.var *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre param_defaut : dictionnaire des paramètres par défaut des fonctions *)
(* Paramètre v : la variable globale à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme la variable en une variable de type AstTds.var *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_tds_variable tds param_defaut (AstSyntax.Static (typ, nom, expr)) =
  match chercherGlobalement tds nom with
  | None ->
      (* La variable n'est pas encore déclarée *)
      (* Analyse de l'expression associée *)
      let nexpr = analyse_tds_expression tds expr (tds, param_defaut) in
      (* Création de l'information associée à la variable *)
      let info = InfoVar (nom, Undefined, 0, "") in
      (* Création du pointeur sur l'information *)
      let ia = info_to_info_ast info in
      (* Ajout de la variable dans la TDS *)
      ajouter tds nom ia;
      (* Renvoie la variable analysée *)
      AstTds.Static (typ, ia, nexpr)
  | Some _ ->
      (* La variable est déjà déclarée dans la TDS globale *)
      raise (DoubleDeclaration nom)


(* analyser : AstSyntax.programme -> AstTds.programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme
en un programme de type AstTds.programme *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstSyntax.Programme (vars,fonctions,prog)) =
  let tds = creerTDSMere () in
  let param_defaut = Hashtbl.create 20 in 
  let nvars = List.map (analyse_tds_variable tds param_defaut) vars in
  let nf = List.map (analyse_tds_fonction tds param_defaut) fonctions in
  let nb = analyse_tds_bloc tds None prog (tds, param_defaut) in
  AstTds.Programme (nvars, nf,nb)
