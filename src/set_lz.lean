import tactic
import data.finset.basic
import data.fintype.card

local attribute [instance] set_fintype

open_locale big_operators

namespace set

variables {I : Type*} (S T U : set I) 

/-
lemma eq_self : (λ (x : I), x ∈ S) = S := rfl

def decidable_pred_self [decidable_pred S] : decidable_pred (λ (x : I), x ∈ S) := 
by {simp [set.eq_self], assumption}

def decidable_pred_self' [decidable_pred (λ (x : I), x ∈ S)] : decidable_pred S := 
by {simp [set.eq_self] at _inst_1, assumption}
-/

lemma union_compl : S ∪ set.compl S = @set.univ I := by ext; simp

lemma union_compl' : S ∪ (λ x, ¬ (S x)) = @set.univ I := 
by {ext, simp, exact em (S x)}

@[simp] lemma inter_eq_empty_of_compl : S ∩ S.compl = ∅ := by simp

@[simp] lemma inter_eq_empty_of_compl' : S ∩ (λ x, ¬ (S x)) = ∅ := by {ext, simp, tauto}

lemma disjoint_of_compl: disjoint S S.compl := by simp [set.disjoint_iff_inter_eq_empty]

lemma disjoint_of_compl': disjoint S (λ x, ¬ (S x)) := by simp [set.disjoint_iff_inter_eq_empty]


/-
--variables [fintype I]  

lemma coe_univ_eq_self : ↥(@set.univ I) = I := sorry
-/

def card [decidable_pred (λ (x : I), x ∈ S)] [fintype ↥S] : ℕ := S.to_finset.card 

lemma univ_card_eq_fintype_card [fintype I] : (@set.univ I).card = fintype.card I := 
by simp [card, fintype.card]

/-
lemma univ_to_finset_eq_finset_univ [fintype I] : (@set.univ I).to_finset = @finset.univ I _:=
set.to_finset_univ

@[simp] lemma coe_to_finset_eq_self [fintype ↥S] : 
↑ S.to_finset = S := coe_to_finset S
-/

#check set.to_finset_univ
#check coe_to_finset 

@[simp] lemma coe_union_to_finset
[decidable_eq I] [fintype ↥S] [fintype ↥T] : 
↑(S.to_finset ∪ T.to_finset) = S ∪ T :=
by ext; simp

#check set.to_finset_union
#check set.to_finset_inj

instance union_decidable (x : I) 
[decidable_pred (λ (x : I), x ∈ S)] [decidable_pred (λ (x : I), x ∈ T)] : 
decidable (x ∈ (S ∪ T)) := 
by {simp [set.mem_union x S T], exact or.decidable}

instance union_decidable_pred 
[decidable_pred (λ (x : I), x ∈ S)] [decidable_pred (λ (x : I), x ∈ T)] : 
decidable_pred (λ (x : I), x ∈ (S ∪ T)) := 
infer_instance

variables {S T U}

lemma to_finset_union_eq_iff [decidable_eq I] 
[fintype ↥S] [fintype ↥T] [fintype ↥U] : 
S.to_finset ∪ T.to_finset = U.to_finset ↔ S ∪ T = U :=
by simp [←to_finset_union, set.to_finset_inj]

#check finset.card_disjoint_union

#check set.to_finset_disjoint_iff

#check finset.disjoint_iff_disjoint_coe

lemma card_disjoint_union [decidable_eq I] 
[decidable_pred (λ (x : I), x ∈ S)] [fintype ↥S]
[decidable_pred (λ (x : I), x ∈ T)] [fintype ↥T]
(h : disjoint S T): 
(S ∪ T).card = S.card + T.card :=
begin
  have h' := to_finset_disjoint_iff.2 h,
  dsimp [card],
  rw [← finset.card_disjoint_union h', to_finset_union],
end

lemma card_disjoint_union' [decidable_eq I] 
[decidable_pred (λ (x : I), x ∈ S)] [fintype ↥S]
[decidable_pred (λ (x : I), x ∈ T)] [fintype ↥T]
[decidable_pred (λ (x : I), x ∈ U)] [fintype ↥U]
(d : disjoint S T) (u : S ∪ T = U) : 
(U).card = S.card + T.card :=
begin
  rw ← card_disjoint_union d,
  congr,
  rw u,
end

/-
instance union_fintype 
[decidable_pred (λ (x : I), x ∈ S)] [decidable_pred (λ (x : I), x ∈ T)] : 
fintype (S.union T) := set_fintype (set.union S T)

instance union_decidable_pred' 
[decidable_pred (λ (x : I), x ∈ S)] [decidable_pred (λ (x : I), x ∈ T)] 
(u : S ∪ T = U) : 
decidable_pred (λ (x : I), x ∈ U) := 
by {have h: decidable_pred (λ (x : I), x ∈ (S ∪ T)), {apply_instance}, rw u at h, assumption}
-/

end set

variables {α β I : Type*} [comm_monoid β] [fintype I]

open fintype finset

lemma finset.univ_eq_set_univ_to_finset : -- DO NOT use in simp!!!
finset.univ = (@set.univ I).to_finset := set.to_finset_univ.symm

lemma fintype.card_eq_finset_card_of_set (S : set α) 
[fintype ↥S] [decidable_pred (λ (x : α), x ∈ S)]:
fintype.card S = finset.card (set.to_finset S) := 
by simp only [set.to_finset_card]

variable (I)
lemma fintype.card_eq_finset_card_of_univ :
fintype.card I = finset.card (@finset.univ I _):= 
by simp only [fintype.card]

lemma fintype.card_eq_set_card_of_univ :
fintype.card I = (@set.univ I).card := 
by simp [set.card, fintype.card]

variable {I}

lemma finset.card_eq_sum_ones_ℚ {s : finset α}: (s.card : ℚ) = ∑ _ in s, 1 :=
by rw (finset.card_eq_sum_ones s); simp

@[to_additive]
lemma finset.prod_union' [decidable_eq α] {s₁ s₂ s : finset α} {f : α → β} 
(d : disjoint s₁ s₂) (u : s₁ ∪ s₂ = s):
(∏ x in s, f x) = (∏ x in s₁, f x) * (∏ x in s₂, f x) :=
by simp [*, ← finset.prod_union]

@[to_additive]
lemma set.prod_union' [decidable_eq α] {S T U : set α} {f : α → β} 
[fintype ↥S] [fintype ↥T] [fintype ↥U]
(d : disjoint S T) (u : S ∪ T = U):
(∏ x in U.to_finset, f x) = (∏ x in S.to_finset, f x) * (∏ x in T.to_finset, f x) :=
begin
  have d' := set.to_finset_disjoint_iff.2 d,
  have u' := set.to_finset_union_eq_iff.2 u,
  rw ← finset.prod_union' d' u',
end

lemma finset.card_erase_of_mem' [decidable_eq α] {a : α} {s : finset α} :
  a ∈ s →  finset.card s = finset.card (finset.erase s a) + 1:= 
begin
  intro ha,
  have h:= finset.card_pos.mpr ⟨a, ha⟩,
  simp [finset.card_erase_of_mem ha, *],
  exact (nat.succ_pred_eq_of_pos h).symm
end

attribute [to_additive] fintype.prod_dite

lemma fintype.sum_split {α} {β} [fintype α] [add_comm_monoid β] {f : α → β} (p : α → Prop) [decidable_pred p] :
  ∑ j, f j =
    ∑ j : {j : α // p j}, f j + ∑ j : {j : α //¬ p j}, f j :=
by simp [←fintype.sum_dite (λ a _, f a) (λ a _, f a)]

lemma finset.sum_split {α} {β} [add_comm_monoid β] (s : finset α) {f : α → β} (p : α → Prop) [decidable_pred p] :
  ∑ j in s, f j =
    ∑ j in filter p s, f j + ∑ j in filter (λ (x : α), ¬p x) s, f j :=
by simp [←finset.sum_ite (λ j, f j) (λ j, f j)]

@[simp]
lemma finset.sum_filter_one {β} [add_comm_monoid β] [decidable_eq I] 
(i : I) {f : I → β}: 
∑ (x : I) in filter (λ (x : I), x = i) univ, f x = f i :=
begin
  simp [finset.filter_eq'],
end

@[simp]
lemma finset.sum_filter_two {β} [add_comm_monoid β] [decidable_eq I] 
{i j : I} (h : i ≠ j) {f : I → β}: 
∑ (k : I) in filter (λ (k : I), k = i ∨ k = j) univ, f k = f i + f j  :=
begin
  rw [finset.sum_split _ (λ k, k = i)],
  simp [finset.filter_eq', finset.filter_ne'],
  have : ∑ (x : I) in (filter (λ (k : I), k = i ∨ k = j) univ).erase i, f x
       = ∑ (x : I) in filter (λ (x : I), x = j) univ, f x,
  { apply finset.sum_congr, 
    { ext, simp, split, 
      { rintros ⟨h₁, (h₂ | h₂)⟩, contradiction, assumption },
      { rintros rfl, use ⟨h.symm, or.inr rfl⟩ } },
    { rintros, refl } },
  simp [this],
end
