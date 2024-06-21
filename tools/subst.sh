#!/bin/bash

subst="s/<->/↔/g; s/([^<])->/\1→/g; s/=>/⇒/g; s/!=/≠/g; s/[\\][/]/∃/g; s/[/][\\]/∀/g; s/([^\\])[\\]([^][\\])/\1λ\2/g; s/&/∧/g; s/([ $])or /\1∨ /g; s/~/¬/g; s/<=/⩽/g; s/>=/⩾/g; s/subset/⊂/g; s/([ $])union /\1∪ /g; s/([ $])inter /\1∩ /g; s/Union/⋃/g; s/Inter/⋂/g; s/([ $])[*] /\1× /g; "

sed -r "$subst" $*
