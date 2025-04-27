/* Imports. */

%{

open Type
open Ast.AstSyntax
%}


%token <int> ENTIER
%token <string> ID
%token RETURN
%token VIRG
%token PV
%token AO
%token AF
%token PF
%token PO
%token EQUAL
%token CONST
%token PRINT
%token IF
%token ELSE
%token WHILE
%token BOOL
%token INT
%token RAT
%token CO
%token CF
%token SLASH
%token NUM
%token DENOM
%token TRUE
%token FALSE
%token PLUS
%token MULT
%token INF
%token EOF
// Pointeurs
%token NULL
%token NEW
%token PER
//Variable globale
%token STATIC



(* Type de l'attribut synthétisé des non-terminaux *)
%type <programme> prog
%type <instruction list> bloc
%type <fonction> fonc
%type <instruction> i
%type <typ> typ
%type <typ*string*defaut option> param
%type <expression> e 
%type <var> var
%type <defaut> d

(* Type et définition de l'axiome *)
%start <Ast.AstSyntax.programme> main

%%

main : lfi=prog EOF     {lfi}

prog : vars=var* fonc=fonc* ID bloc=bloc { Programme (vars, fonc, bloc) }
//variable globale
var : STATIC t=typ n=ID EQUAL e=e PV { Static(t, n, e) }  (* Déclaration d'une variable globale avec static *)

fonc : t=typ n=ID PO lp=separated_list(VIRG,param) PF li=bloc {Fonction(t,n,lp,li)}

d : EQUAL e=e {Defaut(e)}

param : t=typ n=ID d=option(d)  {(t,n,d)}

bloc : AO li=i* AF      {li}



i :
| t=typ n=ID EQUAL e1=e PV          {Declaration (t,n,e1)}
| n=af EQUAL e1=e PV                {Affectation (n,e1)}
| CONST n=ID EQUAL e=ENTIER PV      {Constante (n,e)}
| PRINT e1=e PV                     {Affichage (e1)}
| IF exp=e li1=bloc ELSE li2=bloc   {Conditionnelle (exp,li1,li2)}
| WHILE exp=e li=bloc               {TantQue (exp,li)}
| RETURN exp=e PV                   {Retour (exp)}
//variables statiques locales
| STATIC t=typ n=ID EQUAL e=e PV    {Staticlocal(t, n, e)}  (* Déclaration d'une variable static local  *)


typ :
| BOOL                      {Bool}
| INT                       {Int}
| RAT                       {Rat}
| t=typ MULT                {Pointeur t}



e : 
| n=ID PO lp=separated_list(VIRG,e) PF   {AppelFonction (n,lp)}
| CO e1=e SLASH e2=e CF   {Binaire(Fraction,e1,e2)}
| n=af                     {Affectable n}
| TRUE                    {Booleen true}
| FALSE                   {Booleen false}
| e=ENTIER                {Entier e}
| NUM e1=e                {Unaire(Numerateur,e1)}
| DENOM e1=e              {Unaire(Denominateur,e1)}
| PO e1=e PLUS e2=e PF    {Binaire (Plus,e1,e2)}
| PO e1=e MULT e2=e PF    {Binaire (Mult,e1,e2)}
| PO e1=e EQUAL e2=e PF   {Binaire (Equ,e1,e2)}
| PO e1=e INF e2=e PF     {Binaire (Inf,e1,e2)}
| PO exp=e PF             {exp}
//Pointeurs
| PER n = ID               {Adresse n}
| PO NEW p = typ PF        {New p}
| NULL                     {Null}

af :
|n = ID                  {Ident (n)}
|PO MULT a=af PF         {Deref a}



