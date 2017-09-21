# $State: Exp $ $Date: 2005/02/28 14:10:08 $ $Revision: 0.16

# extrait les informations utiles d'un fichier PhoX, noms des axiomes,
# théorèmes, règles d'introduction ..., voir la déclaration de la variable
# clefs ci-dessous. Ne tient pas compte des commentaires, mais suppose qu'il
# n'y a pas plus d'un commentaire par "ligne" (une ligne étant soit une
# ligne réelle ne contenant pas de "." suivi d'espaces, soit une portion de
# ligne réelle entre le début de ligne et un point suivi d'espaces, soit une
# portion entre un point suivi d'espaces et un point suivi d'espaces.
# Les commentaires imbriqués sont possibles.

BEGIN{
#----------------------------------------------------------------------------

DOCNAME = "doc"

#-----------------------------------------------------------------------------
# variables modifiables
#
# Déclaration des mots clefs 
# (commandes PhoX à conserver ou interpreter pour l'aide) :

# Pour le moment la valeur du tableau ne sert à rien.

DEF["cst"] = "New constant"
DEF["Cst"] = "New higher-order constant"
DEF["pred"] = "New predicate symbol"
DEF["def"] = "Definition"
DEF["Sort"] = "Sort"

CLEF["claim"] = "axiom"
CLEF["prop"] = "proposition"
CLEF["lem"] = "lemma"
CLEF["theo"] = "theorem"
CLEF["fact"] = "fact"
CLEF["cor"] = "corollary"

HINT["new_equation"] = "New equation :"
HINT["new_intro"] = "New introduction rule :"
HINT["new_elim"] = "New elimination rule :"

#
# Les mots clefs en début de commentaire et leur correspondance en ascii:
#
# Indicateur de début de groupe, doivent être suivis de (*end 
GROUP["axiom"]="axiom"
GROUP["claim"]="axiom"
GROUP["lem"] = "lemma"
GROUP["fact"] = "fact"
GROUP["prop"] = "proposition"
GROUP["theo"] = "theorem"
GROUP["cor"] = "corollary"
GROUP["def"] = "definition"
GROUP["def_thlist"] = "definition"
GROUP["cst"] =  "constant"
GROUP["Cst"] =  "constant"
GROUP["pred"] =  "constant"
GROUP["Sort"] =  "sort"

# Indique que le texte en commentaire doit apparaître
TABLE["texte"] = ""
TABLE["note"] = ""
TABLE["ascii"] = ""
# à enlever pour l'ascii
TABLE["tex"] = ""

# indique que la commande doit apparaître telle quelle (peut-être inutile)
ASIS["tex_syntax"]=""
ASIS["Import"]=""
ASIS["Use"]=""

# syntaxe des defs
SYNTAXE["Infix"]=""
SYNTAXE["lInfix"]=""
SYNTAXE["rInfix"]=""
SYNTAXE["Prefix"]=""
SYNTAXE["Postfix"]=""


# for (mot in TABLE){print mot}
#-----------------------------------------------------------------------------
#
# Les compteurs pour les sections :
#
SECT_COUNT = 0 ; SSECT_COUNT = 0 ; SSSEC_COUNT = 0; PSEC_COUNT = 0 ;
#
#-----------------------------------------------------------------------------
#
#La fin d'une section
ENDSECT="\n"
#-----------------------------------------------------------------------------
#
# séparateur de record, le contenu de l'expression matchée
# est dans la variable  RT. 
RS="[ \t]*\n|([.][ \t]+)"    # entrée
ORS=""                # sortie
# ATTENTION : RS, ORS RT : ce n'est pas du awk pur, il faut gnu awk
#
#-----------------------------------------------------------------------------
#
# cuisine interne

  ISPROOF = 0 ; GOAL ="" ; ISGROUP = 0 ; ORT="\n"

#
#-----------------------------------------------------------------------------
}

# la fin de ligne adéquate

function ort(){
if(RT ~ /\./){return ".\n"} else {return "\n"}}


# inutile ?
function appartient(element, tableau){
  for (i in tableau)
    if(tableau[i] == element){ return i ; break};
  return 0}

function app_subs(element, tableau){
  for (i in tableau)
    if(i == element){ return i ; break};
  return 0}

function app_subs_match(element, tableau){
  for (i in tableau)
    if(index(element,i) == 1){ return i ; break};
  return 0}

function app_subs_any_match(element, tableau){
  for (i in tableau)
    if(index(element,i)){ return i ; break};
  return 0}

# enlever le dernier caractère quand c'est un point

function tronque(chaine){
if(RT ~ /\./){return chaine} else {return substr(chaine, 1, length(chaine)-1)}}

# lire une commande :

function lit_commande(){
  var = $0;
  while( $NF !~ /.*\.[ \t]*$/ && RT !~ /\./){
    if (getline <= 0) {
      m = "unexpected EOF,  \".\" expected (end of a command)";
      m = (m "/ " ERRNO);
      print m > "/dev/stderr";
      exit
	}    
    var = var "\n" $0}
  return var
}


# lit un commentaire : valeur retournéee : le contenu du commentaire, les
# début et fin de commentaire sont éliminés. Si le début du commentaire est
# de la forme "(*mot", (pas d'espace) le mot est aussi éliminé.  Modifie $0
# : début de la première ligne avant le commentaire, puis fin de la dernière
# ligne après le commentaire.

function lit_commentaire(){
  var = "";
  if ((t = index($0, "(*")) != 0){
    begline = substr($0, 1, t - 1);
    $0 = substr($0,t);
    $1="";
    d = 1 ;
    u = index($0, "*)");
    if(u!=0){d=d - 1};
    while(d){
#      var = var $0 " " RT;
      var = var $0 RT;
      if (getline <= 0) {
        m = "unexpected EOF, \"*)\" expected (end of comment)";
	m = (m "/ " ERRNO);
	print m > "/dev/stderr";
	exit
	};
      if (index($0, "(*")!= 0){d=d+1};
      u = index($0, "*)");
      if(u!=0){d=d - 1};
      }
    var = var substr($0,0, u - 1)
    $0 = begline substr($0, u +2)
   } 
  gsub(/\\\[/, "OPEN_BRACK@@" , var)
  gsub(/\\\]/, "CLOSED_BRACK@@" , var)
  gsub(/\\\$/, "DOLLAR@@" , var)
  gsub(/\\\#/, "DASH@@" , var)
  gsub(/\[/, "\\[ " , var)
  gsub(/\]/, " \\]" , var)
  gsub(/\$[^ \t\n.]+(\.[^ \t\n.]+)*/, "\\[ & \\]" , var)
  gsub(/\#[^#]+\#/, "\\verb&" , var)
  gsub(/OPEN_BRACK@@/, "[" , var)
  gsub(/CLOSED_BRACK@@/, "]" , var)
  gsub(/DOLLAR@@/, "$" , var)
  gsub(/DASH@@/, "#" , var)
  return var
}

function stc(){
    if (ISGROUP == 0){
	print "(*!" DOCNAME "\n"}
}

function etc(){
    if (ISGROUP == 0){
	print "\n*)\n" }
}
#-----------------------------------------------------------------------------

# titre et sections


($1 ~ /\(\*header[.]*/){$2="";
print "tex " lit_commentaire() "\n documents = " DOCNAME "\n.\n";
match(FILENAME,/[^\/]*$/)
FILENAME=substr(FILENAME, RSTART, RLENGTH)
match(FILENAME,/[^\.]*/)
FILENAME=substr(FILENAME, RSTART, RLENGTH)
print "Import " FILENAME ".\n"
}


($1 ~ /\(\*\*\*\*\*[.]*/){
  stc() ; print "\\paragraph{" lit_commentaire() "}" ; etc()
}

($1 ~ /\(\*\*\*\*[.]*/){
  stc() ; print "\\subsubsection{" lit_commentaire() "}" ; etc()
}

($1 ~ /\(\*\*\*[.]*/){
  stc() ; print "\\subsection{" lit_commentaire() "}" ; etc()
}

($1 ~ /\(\*\*[.]*/){
  stc() ; print "\\section{" lit_commentaire() "}" ; etc()
  }



# lemmes définitions etc. (regroupement par (*lem *) (*end *))


($1 ~ /\(\*[[:alnum:]]+/ && ($1 !~/\(\*end.*/)) {
    if (mot = app_subs_any_match($1, GROUP)){
    stc();
    if (ISGROUP != 0){
	print "ERROR : a previous group > " ISGROUP " < was not closed with (*end *)">"/dev/stderr" ;
	exit}
    else {ISGROUP = mot};
    print "\\begin{" GROUP[mot] "}["  lit_commentaire() "]\\hspace{1cm}\n\\begin{itemize}\n"
    }
    if (mot = app_subs_any_match($1, TABLE)){
	stc();
	print "\n"; 
	texte = lit_commentaire() ;
	print texte;
	etc();
    }
}


($1~ /\(\*end/){
print "\n\\end{itemize}\n\\end{" GROUP[ISGROUP] "}"
if (ISGROUP == 0){print "ERROR : no more group to close" > "/dev/stderr" ; exit}
else{ISGROUP = 0}
etc()
}


# passer les commentaires sauf avec un def, prop, etc. en tête

# (! app_subs($1,CLEF)){lit_commentaire()}

#   proposition, lemma etc.

(mot = app_subs_match($1,CLEF)){
    com = lit_commentaire(); 
    nom = $2;   
    $1 = "";
    $2 = "";
    TO_WRITE = tronque(lit_commande());

    if (ISGROUP == 0) {
	stc();
	print "\\begin{" GROUP[mot] "}[\\[" nom "\\] ] " com "~\n";
	print "\\[[" TO_WRITE " \\]] \n";
	print "\\end{" GROUP[mot] "}\n";
	etc();
    } else {
	print "\\item \\[" nom "\\] : " com;
	print "{\\textwidth=10cm \\[[" TO_WRITE " \\]] }\n";
	}
}

(mot = app_subs_match($1,HINT)){
    com = lit_commentaire(); 
    command = tronque(lit_commande());
    command = substr(command, length(mot)+1);
    stc();
    print "\n\\noindent";
    if (mot == "new_elim") {
	i = match(command,/[^ \t\n.]+(\.[^ \t\n.]+)*[ \n\t]*$/);
	theo=substr(command, i);
        command=substr(command,0,i-1);
	i = match(command,/[^ \t\n.]+(\.[^ \t\n.]+)*[ \n\t]*$/);
	abb=substr(command, i);
        command=substr(command,0,i-1);
	i = match(command,/[^ \t\n.]+(\.[^ \t\n.]+)*[ \n\t]*$/);
	pred=substr(command, i);
        options=substr(command,0,i-1);
	print "\\[" theo "\\] added as elimination rule (abbrev: \\verb#" abb "#, options: \\verb#" options "#)";
    }
    if (mot == "new_intro") {
	i = match(command,/[^ \t\n.]+(\.[^ \t\n.]+)*[ \n\t]*$/);
	theo=substr(command, i);
        command=substr(command,0,i-1);
	i = match(command,/[^ \t\n.]+(\.[^ \t\n.]+)*[ \n\t]*$/);
	abb=substr(command, i);
        options=substr(command,0,i-1);
	pred="";
	print "\\[" theo "\\] added as introduction rule (abbrev: \\verb#" abb "#, options: \\verb#" options "#)";
    }
    if (mot == "new_equation") {
	i = match(command,/[^ \t\n.]+(\.[^ \t\n.]+)*[ \n\t]*$/);
	theo=substr(command, i);
	options="";
        pred="";	
	print "\\[" theo "\\] added as equation";
     }
     print "\n\n";
     etc();
}

(mot = app_subs_match($1,DEF)){
    com = lit_commentaire(); 
    nom = $2;   
    if ($1 == "def_thlist") { mot = "def_thlist" };
    $1 = "";

    if (mot == "cst" || mot == "pred") {arity = $2; $2 = ""};
    
    TO_WRITE = tronque(lit_commande());
    if (mot == "Cst") {
	i = match(TO_WRITE,/:[a-zA-Z \n\t](.*)/);
	sort = substr(TO_WRITE, i+1);
        gsub(/->/,"$\\rightarrow$",sort);
    }
    if (mot == "Sort") {
        gsub(/->/,"$\\rightarrow$",TO_WRITE);
    }
    if (app_subs_any_match(TO_WRITE, SYNTAXE)){
      if (getline <= 0) {
	  m = "unexpected EOF, comment with description of " $1 " expected ";
	m = (m "/ " ERRNO);
	print m > "/dev/stderr";
	exit
	};
      sy = 1;
      TO_WRITE = lit_commentaire()
    } else {sy = 0; }

#    gsub(/::[^ \n\t]+/,"", TO_WRITE);

    if(mot== "def_thlist") {
      sub(/[ \n\t]=[ \n\t]/," := ", TO_WRITE);
      TO_WRITE = "List of theorems: " TO_WRITE;
    } else {
      if (mot == "def" || mot == "Sort") {sub(/[ \n\t]=[ \n\t]/," := ", TO_WRITE)};

      if (mot == "Cst" && sy == 0) {
	sub(/:[a-zA-Z \n\t](.*)/,"", TO_WRITE);
      };

      extras = TO_WRITE;
      if (mot == "def") {sub(/[ \n\t]*:=[ \n\t]* .*/,"", extras)};

      extras = "\\SaveVerb{Verb}\\{ " extras " \\} ";

      if (mot != "Sort") TO_WRITE = "\\[" TO_WRITE " \\]";

#      if (mot == "cst") {TO_WRITE = "constant of arity " arity ": " TO_WRITE}
#      if (mot == "pred") {TO_WRITE = "predicate of arity " arity ": " TO_WRITE}
      if (mot == "Cst") {TO_WRITE = TO_WRITE "  : " sort }
    }

    if (ISGROUP == 0) {
	stc();
#        sub(/\\\]/,"\\]]",TO_WRITE);
#        sub(/\\\[/,"\\[[",TO_WRITE);
	print "\\begin{" GROUP[mot] "}["  com "]~\n";
	print "\\begin{center}"; 
	print TO_WRITE "\n";
      	if (mot != "def_thlist" && mot != "Sort") {
	  print extras;
       	  print "\\marginpar{\\UseVerb{Verb}}";
	}
	print "\\end{center}"; 
	print "\\end{" GROUP[mot] "}\n";
	etc();
    } else {
	print "\\item " com TO_WRITE "\n"
       	if (mot != "def_thlist" && mot != "Sort") {
	  print extras;
       	  print "\\marginpar{\\UseVerb{Verb}}";
	}
    }
}






END{}


