
#  voir la d�claration de la variable
# clefs ci-dessous. Ne tient pas compte des commentaires, mais suppose qu'il
# n'y a pas plus d'un commentaire par "ligne" (une ligne �tant soit une
# ligne r�elle ne contenant pas de "." suivi d'espaces, soit une portion de
# ligne r�elle entre le d�but de ligne et un point suivi d'espaces, soit une
# portion entre un point suivi d'espaces et un point suivi d'espaces.
# Les commentaires imbriqu�s sont possibles.

BEGIN{
#-----------------------------------------------------------------------------
# variables modifiables
#
# D�claration des mots clefs 
# (commandes PhoX � conserver ou interpreter pour l'aide) :

# Pour le moment la valeur du tableau ne sert � rien.

CLEF["claim"] = "Axiom"
# CLEF["cst"] = "New Constant"
# CLEF["def"] = "Definition"
CLEF["proposition"] = "Proposition"
CLEF["lemma"] = "Lemma"
CLEF["theorem"] = "Theorem"
CLEF["fact"] = "Fact"
CLEF["corollary"] = "Corollary"
# CLEF["new_equation"] = "New equation :"
# CLEF["new_intro"] = "New introduction rule :"
# CLEF["new_elim"] = "New elimination rule :"

#
# Les mots clefs en d�but de commentaire et leur correspondance en ascii:
#
# Indicateur de d�but de groupe, doivent �tre suivis de (*end 
GROUP["axiom"]="Axiom"
GROUP["lem"] = "Lemma"
GROUP["fact"] = "Fact"
GROUP["prop"] = "Proposition"
GROUP["theo"] = "Theorem"
GROUP["cor"] = "Corollary"
GROUP["def"] = "Definition"
GROUP["cst"] =  "New Constants"

# Indique que le texte en commentaire doit appara�tre
TABLE["texte"] = ""
TABLE["note"] = ""
TABLE["ascii"] = ""
# � enlever pour l'ascii
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
# s�parateur de record, le contenu de l'expression match�e
# est dans la variable  RT. 
RS="[ \t]*\n|([.][ \t]+)"    # entr�e
ORS=""                # sortie
# ATTENTION : RS, ORS RT : ce n'est pas du awk pur, il faut gnu awk
#
#-----------------------------------------------------------------------------
#
# cuisine interne

  ISPROOF = 0 ; GOAL ="" ; ISGROUP = 0 ; ORT="\n"

#
#-----------------------------------------------------------------------------
LINEno=0
CHARno=0
SORTIE=""
}

function incrline(n){
if(RT ~ /\./){} else n=n+1; return n}


# la fin de ligne ad�quate

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

# enlever le dernier caract�re quand c'est un point

function tronque(chaine){
if(RT ~ /\./){return chaine} else {return substr(chaine, 1, length(chaine)-1)}}

# lire une commande (incr�mente LINEno et CHARno) :


function lit_commande(){
  var = $0;
  while( $NF !~ /.*\.[ \t]*$/ && RT !~ /\./){
    LINEno=LINEno + 1;
    if (getline <= 0) {
      m = "unexpected EOF,  \".\" expected (end of a command)";
      m = (m "/ " ERRNO);
      print m > "/dev/stderr";
      exit
	}    
    CHARno=CHARno + length($0) + length(RT);
    var = var RT $0
    ORIG= ORIG RT $0}
  return var
}


# lit un commentaire : valeur retourn�ee : le contenu du commentaire, les
# d�but et fin de commentaire sont �limin�s. Si le d�but du commentaire est
# de la forme "(*mot", (pas d'espace) le mot est aussi �limin�.  Modifie $0
# : d�but de la premi�re ligne avant le commentaire, puis fin de la derni�re
# ligne apr�s le commentaire.

function lit_commentaire(){
  var = "";
  ORIG = $0;
  if ((t = index($0, "(*")) != 0){
    begline = substr($0, 1, t - 1);
    $0 = substr($0,t);
    $1="";
    d = 1 ;
    u = index($0, "*)");
    if(u!=0){d=d - 1};
    while(d){
      var = var $0 RT;
      ORIG = ORIG RT $0
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


# (LINEno == 1){print FILENAME",\n"}


# (! app_subs($1,CLEF))
{LINEno = incrline(LINEno) ;
 CHARno=CHARno + length($0)+ length(RT) }

#   proposition, lemma, new_equation etc.

(app_subs($1,CLEF)){
# TETE = $1;   $1 = ""; 
lineno=LINEno
ORIG="";
COMMENT = lit_commentaire();
$1=""
COMMAND = lit_commande();
match(COMMAND,/[^ \t\n]+/);
NAME = substr(COMMAND, RSTART , RLENGTH);
ORIG = substr(ORIG, 1 , index(ORIG,NAME)+length(NAME) -1);
# CHARno= CHARno + length($0) + length(COMMENT) + length(RT);
SORTIE = SORTIE ORIG  "\177"NAME"" lineno","CHARno "\n" ;
# LINEno = incrline(LINEno)
     }


END{
print "\n"
print FILENAME","length(SORTIE)"\n"
print SORTIE
}
