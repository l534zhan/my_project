import group_theory.subgroup

/-!
This file supplements two instances relavant to monoid homomorphisms
-/

namespace monoid_hom
variables {G N: Type*} [group G] [group N] 

/-- If the equality in `N` is decidable and `f : G →* N` is a `monoid_hom`, 
    then the membership of `f.ker.carrier` is decidable. -/
instance [decidable_eq N] (f : G →* N) (x : G) :
decidable (x ∈ f.ker.carrier) := f.decidable_mem_ker x

/-- If `G` is a finite type, and the equality in `N` is decidable, 
    and `f : G →* N` is a `monoid_hom`, then `f.ker.carrier` is a finite type. -/
instance [fintype G] [decidable_eq N] (f : G →* N) : 
fintype (f.ker.carrier) := set_fintype (f.ker.carrier)

/-
lemma fintype_card_ker_eq_card_ker_carrier [fintype G] [decidable_eq N] (f : G →* N) : 
fintype.card f.ker = fintype.card f.ker.carrier := 
by refl
-/

end monoid_hom