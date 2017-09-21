
# extrait les informations utiles d'un fichier PhoX, noms des axiomes,
# théorèmes, règles d'introduction ..., voir la déclaration de la variable
# clefs ci-dessous. Ne tient pas compte des commentaires, mais suppose qu'il
# n'y a pas plus d'un commentaire par "ligne" (une ligne étant soit une
# ligne réelle ne contenant pas de "." suivi d'espaces, soit une portion de
# ligne réelle entre le début de ligne et un point suivi d'espaces, soit une
# portion entre un point suivi d'espaces et un point suivi d'espaces.
# Les commentaires imbriqués sont possibles.

BEGIN{
#-----------------------------------------------------------------------------
# variables modifiables
#
# Déclaration des mots clefs 
# (commandes PhoX à conserver ou interpreter pour l'aide) :

# Pour le moment la valeur du tableau ne sert à rien.

CLEF["cst"] = "New constant"
CLEF["Cst"] = "New higher-order constant"
CLEF["pred"] = "New predicate symbol"
CLEF["def"] = "Definition"
CLEF["claim"] = "Axiom"
CLEF["proposition"] = "Proposition"
CLEF["lemma"] = "Lemma"
CLEF["theorem"] = "Theorem"
CLEF["fact"] = "Fact"
CLEF["corollary"] = "Corollary"
CLEF["new_equation"] = "New equation :"
CLEF["new_intro"] = "New introduction rule :"
CLEF["new_elim"] = "New elimination rule :"

#
# Les mots clefs en début de commentaire et leur correspondance en ascii:
#
# Indicateur de début de groupe, doivent être suivis de (*end 
GROUP["axiom"]="Axiom"
GROUP["lem"] = "Lemma"
GROUP["fact"] = "Fact"
GROUP["prop"] = "Proposition"
GROUP["theo"] = "Theorem"
GROUP["cor"] = "Corollary"
GROUP["def"] = "Definition"
GROUP["cst"] =  "New Constants"

# Indique que le texte en commentaire doit apparaître
TABLE["texte"] = ""
TABLE["note"] = ""
TABLE["ascii"] = ""
# à enlever pour l'ascii
# TABLE["tex"] = ""
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
RS="[ \t]*\n|([\.][ \t]+)"    # entrée
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
  return var
}

#-----------------------------------------------------------------------------


# titre et sections


($1 ~ /\(\*header[.]*/){
print lit_commentaire()"\n"}


($1 ~ /\(\*\*\*\*\*[.]*/){
  PSEC_COUNT = PSEC_COUNT + 1  ; 
  print "\n"SEC_COUNT "." SSEC_COUNT "." SSSEC_COUNT "." PSEC_COUNT". "lit_commentaire() ENDSECT;
}

($1 ~ /\(\*\*\*\*[.]*/){
  SSSEC_COUNT = SSSEC_COUNT + 1  ; 
  print "\n"SEC_COUNT "." SSEC_COUNT "." SSSEC_COUNT". "lit_commentaire() 
        ENDSECT;
  PSEC_COUNT=0;
}

($1 ~ /\(\*\*\*[.]*/){
  SSEC_COUNT = SSEC_COUNT + 1  ; 
  print "\n"SEC_COUNT "." SSEC_COUNT ". "lit_commentaire() ENDSECT;
  SSSEC_COUNT=0; PSEC_COUNT=0;
}

($1 ~ /\(\*\*[.]*/){
  SEC_COUNT = SEC_COUNT + 1  ; 
  print "\n"SEC_COUNT "." lit_commentaire() ENDSECT;
  SSEC_COUNT=0 ; SSSEC_COUNT=0; PSEC_COUNT=0;
  }



# lemmes définitions etc. (regroupement par (*lem *) (*end *))

($1 ~ /\(\*[[:alnum:]]+/ && $1 !~/\(\*end.*/){
    if (mot = app_subs_match($1, GROUP)){
	if (ISGROUP != 0){
	    print "ERROR : a previous group > " ISGROUP " < was not closed with (*end *)">"/dev/stderr" ;
	    exit}
	else {ISGROUP = mot};
	print "\n+++++\n" ;
	TO_WRITE = GROUP[mot] "  "  lit_commentaire();
	sub(/[ \t\n]*$/,"",TO_WRITE)
	print  TO_WRITE "\n";
	for(i=1; i <= length(TO_WRITE) ; i++){print "-"};
	print "\n"
}

    if (mot = app_subs_match($1, TABLE)){
#    print mot  ;  print ">>"$1"<<>>" app_subs_match($1, TABLE) "<<"
	print TABLE[mot] " " lit_commentaire() "\n"}
# else{ print mot ;   print ">|"$1"||" app_subs_match($1, TABLE) "|<"}
}


($1~ /\(\*end/){
 print "-----\n" lit_commentaire() "\n" 
if (ISGROUP == 0){print "ERROR : no more group to close" > "/dev/stderr" ; exit}
else{ISGROUP = 0}
}


# passer les commentaires sauf avec un def, prop, etc. en tête

(! app_subs($1,CLEF)){lit_commentaire()}

#   proposition, lemma, new_equation etc.

(app_subs($1,CLEF)){
TETE = $1;   $1 = ""; 
print TETE " " lit_commande()  ort();
}


# l'ancienne syntaxe pour les théorèmes, 
# utile aussi quand on fabrique un fichier

($1 == "goal"){  $1 = "";
   GOAL = lit_commande() ; ORT = ort();
   ISPROOF =1 }

# ($1 == "save" && ISPROOF != 1){
#   print "Erreur : save non précédé de goal ?">"/dev/stderr"}

($1 == "save" && ISPROOF){
  print "Prop " tronque($2)  "  " GOAL  ORT;
  GOAL = "" ; 
  ISPROOF =0
     }




END{}
