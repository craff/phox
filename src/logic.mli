module type Logic =

  sig

    type formula

    exception Unif_fails

    type substitution

    type constraints

    val empty_constraints : unit -> constraints

    val apply_subst : substitution -> formula -> formula

    type unif_kind = Contraction of constraints | Unification of (constraints * constraints) | Subsume
      (* type qui indique dans quelles condition on fait de l'unification *)
      (* Dans le cas de la contraction, seule une contrainte est donnée : celle de la clause *)

    val unif : unif_kind -> formula -> formula -> int * substitution * unif_kind * constraints * formula * formula list 
	(* int est la taille de l'unif *)
	(* la liste de formules est la liste des formules conditionnelles sur l'unif *)
	(* la substitutions a été appliquée à ces formules *)
	(* la formule est la formule obtenue également après substitution *)
	(* lève l'exception Unif_fails en cas d'échec *)

    val size : formula -> int
	(* taille d'une formule *)

    val is_true : formula -> bool

    exception Metavar (* raised by the next function when the head of the formula is a metavariable *)

    val negative_formula : formula -> bool
	(* test si une formule est une négation par parité du nombre de négations *)
	(* attention : doit renvoyer true si la formule est false *)
	(* peut lever une exception Metavar dans le cas où l'on a une métavariable *)

    val negate_formula : formula -> formula
	(* rend la négation de la formule i.e. ajoute une négation (affichage) *)
	(* attention à vrai et faux... *)

    val elim_all_neg : formula -> formula
	(* élimine toute les négations d'une formule *)

    type renaming
	(* pour le renommage de variables *)

    val empty_renaming : unit -> renaming

    val get_renaming_formula : renaming -> formula -> renaming
	(* ajoute du renommage pour toutes les variables libres de la formule *)
	(* qui ne sont pas dans renaming *)

    val get_renaming_constraints : renaming -> constraints -> renaming

    val rename_formula : renaming -> formula -> formula
	(* fait le renommage d'une formule en ne renommant que celles qui *)
	(* sont dans renaming *)
	(* laisse les autres variables tel quel *)

    val rename_constraints : renaming -> constraints -> constraints

    type varset
	  (* ensemble de variables *)

    val empty_varset : varset

    val vars_of_formula : formula -> varset
	(* donne les variables libres d'une formule *)

    val vars_to_constants : varset -> substitution
	(* prend des variables d'unification *)
	(* renvoie une substitution qui transforme ces variables en constantes fraîches *)
	(* pour la subsomption (appliqué à la formule de droite temporairement) *)

    val is_empty_inter_varset : varset -> varset -> bool (* teste l'intersection vide d'ensembles de variables *)

    val union_varset : varset -> varset -> varset (* fait l'union d'ensemble de variables *)

    val get_rules : constraints -> formula -> bool -> ( string * int * substitution * constraints * formula list ) list
	(* donne la liste des règles associées au connecteur principal de la formule *)
	(* int est le 'poids' de la règle *)
	(* celui-ci est préférentiellement >=1 *)
	(* et est >= 2 pour les règles lourdes *)
	(* ou qui mènent à des décompositions infinies *)
	(* les règles peuvent avoir besoin de faire de l'unification d'où substitution *)
	(* string est le nom de la règle *)
	(* le booléen donné indique si formula est pos (true) ou neg (false) *)
	(* En effet le prouveur ne travaille qu'avec des formules positives *)

    val print_formula : formula -> unit

    val print_constraints : constraints -> unit

    val equal_formula : formula -> formula -> bool

    type head_symbol_type

    val head_symbol : formula -> head_symbol_type

    module FormHashType : (Hashtbl.HashedType with type t = (head_symbol_type * bool))
	(* module de type HashedType pour faire des tables de Hash *)
	(* à partir des symboles de tête et positivité des formules *)
	
    val indice_regle : string -> int
        (* donne un indice de réutilisation *)
	(* 0 indique que l'on peut l'utiliser sans restriction *)
        (* n=1 donne une très faible restriction, valeur par défaut *)
	(*  n>1 donne une restriction *)
	(* plus n est grand, moins on doit l'utiliser *)

  end
