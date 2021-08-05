import group_theory.subgroup

namespace monoid_hom
variables {G N: Type*} [group G] [group N] 

instance [decidable_eq N] (f : G →* N) (x : G) :
decidable (x ∈ f.ker.carrier) := f.decidable_mem_ker x

instance [fintype G] [decidable_eq N] (f : G →* N) : 
fintype (f.ker.carrier) := set_fintype (f.ker.carrier)

--lemma fintype_card_ker_eq_card_ker_carrier [fintype G] [decidable_eq N] (f : G →* N) : 
--fintype.card f.ker = fintype.card f.ker.carrier := 
--by refl

end monoid_hom