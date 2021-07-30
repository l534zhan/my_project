import tactic
import tactic.gptf
import algebra.field
import data.matrix.notation
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.trace
import data.fintype.card
import data.finset.basic
import algebra.big_operators
import linear_algebra.char_poly.basic

import finite_field_lz
import main1

set_option pp.beta true

--attribute [to_additive] fintype.prod_dite
--local attribute [-instance] set.has_coe_to_sort
local attribute [-instance] set.fintype_univ
local attribute [instance] set_fintype

open_locale big_operators

----------------------------------------------------------------------------
section pre 

variables {α β γ I J K L M N: Type*} (S T U : set α)
variables {R : Type*}
variables {m n: ℕ}
variables [fintype I] [fintype J] [fintype K] [fintype L] [fintype M] [fintype N]

attribute [simp]
private lemma set.union_to_finset 
[decidable_eq α] [fintype ↥S] [fintype ↥T] : 
S.to_finset ∪ T.to_finset = (S ∪ T).to_finset :=
(set.to_finset_union S T).symm

@[simp] lemma ite_nested (p : Prop) [decidable p] {a b c d : α}: 
ite p (ite p a b) (ite p c d)= ite p a d :=
by by_cases p; simp* at *

@[simp] lemma ite_eq [decidable_eq α] (a x : α) {f : α → β}: 
ite (x = a) (f a) (f x)= f x :=
by by_cases x=a; simp* at *

private lemma pick_elements (h : fintype.card I ≥ 3) : -- give citation
∃ i j k : I, i ≠ j ∧ i ≠ k ∧ j ≠ k := 
begin
  set n := fintype.card I with hn,
  have f := fintype.equiv_fin_of_card_eq hn,
  refine ⟨f.symm ⟨0, by linarith⟩, f.symm ⟨1, by linarith⟩, f.symm ⟨2, by linarith⟩,
    and.imp f.symm.injective.ne (and.imp f.symm.injective.ne f.symm.injective.ne) _⟩,
  dec_trivial,
end
end pre
----------------------------------------------------------------------------
namespace equiv 

variable {I : Type*}

def sum_self_equiv_prod_unit_sum_unit : I ⊕ I ≃  I × (unit ⊕ unit) := 
(equiv.trans (equiv.prod_sum_distrib I unit unit) 
             (equiv.sum_congr (equiv.prod_punit I) (equiv.prod_punit I))).symm

@[simp] lemma sum_self_equiv_prod_unit_sum_unit_symm_apply_left (a : unit) (i : I) : 
sum_self_equiv_prod_unit_sum_unit.symm (i, sum.inl a) = sum.inl i := rfl

@[simp] lemma sum_self_equiv_prod_unit_sum_unit_symm_apply_right (a : unit) (i : I) : 
sum_self_equiv_prod_unit_sum_unit.symm (i, sum.inr a) = sum.inr i := rfl

end equiv
----------------------------------------------------------------------------
namespace matrix

variables {α β γ I J K L M N: Type*}
variables {R : Type*}
variables {m n: ℕ}
variables [fintype I] [fintype J] [fintype K] [fintype L] [fintype M] [fintype N]
open_locale matrix

section matrix_pre

def all_one [has_one α]: matrix I J α := λ i, 1

def row_sum [add_comm_monoid α] (A : matrix I J α) (i : I) := ∑ j, A i j

def col_sum [add_comm_monoid α] (A : matrix I J α) (j : J) := ∑ i, A i j
 
@[simp] private 
lemma push_nag [add_group α] (A : matrix I J α) {i : I} {j : J} {a : α}: 
- A i j = a ↔ A i j = -a :=
⟨λ h, eq_neg_of_eq_neg (eq.symm h), λ h, neg_eq_iff_neg_eq.mp (eq.symm h)⟩

lemma col_one_mul_row_one [non_assoc_semiring α] : 
col (1 : I → α) ⬝ row (1 : I → α) = all_one :=
by ext; simp [matrix.mul, all_one]

lemma row_one_mul_col_one [non_assoc_semiring α] : 
row (1 : I → α) ⬝ col (1 : I → α) = fintype.card I • 1 :=
by {ext, simp [mul_apply, one_apply], congr,}

lemma dot_product_split_over_subtypes {R} [semiring R] 
(v w : I → R) (p : I → Prop) [decidable_pred p] :
dot_product v w =
∑ j : {j : I // p j}, v j * w j + ∑ j : {j : I // ¬ (p j)}, v j * w j :=
by { simp [dot_product], rw fintype.sum_split p}

lemma is_sym_of_block_conditions
{A : matrix I I α} {B : matrix I J α} {C : matrix J I α} {D : matrix J J α} :
(A.is_sym) ∧ (D.is_sym) ∧ (Bᵀ = C) → (A.from_blocks B C D).is_sym :=
begin
  rintros ⟨h1, h2, h3⟩, 
  have h4 : Cᵀ = B, {rw ← h3, simp},
  unfold matrix.is_sym,
  rw from_blocks_transpose,
  congr;
  assumption
end

lemma mul_transpose_self_is_sym [comm_semiring α] (A : matrix I I α) : 
(A ⬝ Aᵀ).is_sym :=
by simp [matrix.is_sym, transpose_mul]

def is_diagonal [has_zero α] (A : matrix I I α) : Prop := ∀ i j, i ≠ j → A i j = 0

def has_orthogonal_rows [has_mul α] [add_comm_monoid α] (A : matrix I J α) : Prop := 
∀ ⦃i₁ i₂⦄, i₁ ≠ i₂ → dot_product (A i₁) (A i₂) = 0

def has_orthogonal_clos [has_mul α] [add_comm_monoid α] (A : matrix I J α) : Prop := 
∀ ⦃i₁ i₂⦄, i₁ ≠ i₂ → dot_product (λ j, A  j i₁) (λ j, A j i₂) = 0

@[simp] lemma is_diagonal_apply [has_zero α] {A : matrix I I α} (ha : A.is_diagonal) {i j : I} (h : i ≠ j) : 
A i j = 0 := ha i j h

@[simp] lemma is_diagonal_of_unit [has_zero α] (A : matrix unit unit α) : (A : matrix unit unit α).is_diagonal :=
by {intros i j h, have h':= @unit.ext i j, simp* at *}

@[simp] lemma is_diagonal_of_zero [has_zero α] : (0 : matrix I I α).is_diagonal :=
λ i j h, by simp

@[simp] lemma is_diagonal_of_zero' [has_zero α] : is_diagonal (λ x y, 0 : matrix I I α) :=
λ i j h, rfl

@[simp] lemma is_diagonal_of_one [decidable_eq I] [has_zero α] [has_one α] : (1 : matrix I I α).is_diagonal :=
by {intros i j h, simp *}

@[simp] lemma is_sym_of_one [decidable_eq I] [has_zero α] [has_one α] : 
(1 : matrix I I α).is_sym := by {ext, simp}

lemma is_sym_of_one' [decidable_eq I] [has_zero α] [has_one α] (i j : I): 
(1 : matrix I I α) i j = (1 : matrix I I α) j i :=
by { have h := congr_fun (congr_fun (@is_sym_of_one α _ _ _ _ _) i) j, 
     rw [transpose_apply] at h,
     exact h.symm }

@[simp] lemma is_sym_of_neg_one [decidable_eq I] [has_zero α] [has_one α] [has_neg α] : 
(-1 : matrix I I α).is_sym := by {ext, simp}

@[simp] lemma is_diagonal_of_smul_one
[decidable_eq I] [monoid R] [add_monoid α] [has_one α] [distrib_mul_action R α] (k : R) : 
(k • (1 : matrix I I α)).is_diagonal := by {intros i j h, simp *}

@[simp] lemma is_sym_of_smul_one
[decidable_eq I] [monoid R] [add_monoid α] [has_one α] [distrib_mul_action R α] (k : R) : 
(k • (1 : matrix I I α)).is_sym := 
by { ext, simp, rw [is_sym_of_one' j i] }

@[simp] lemma is_diagonal_add [add_zero_class α] {A B : matrix I I α} (ha : A.is_diagonal) (hb : B.is_diagonal) :
(A + B).is_diagonal := by {intros i j h, simp *, rw [ha i j h, hb i j h], simp}

lemma is_diagonal_iff_diagonal [has_zero α] [decidable_eq I] (A : matrix I I α) : 
A.is_diagonal ↔ (∃ d, A = diagonal d):=
begin
  split,
  { intros h, use (λ i, A i i), 
    ext, 
    specialize h i j,
    by_cases i = j; 
    simp * at *, },
  { rintros ⟨d, rfl⟩ i j h, simp *}
end

lemma is_diagnoal_of_block_conditions [has_zero α] 
{A : matrix I I α} {B : matrix I J α} {C : matrix J I α} {D : matrix J J α} :
(A.is_diagonal) ∧ (D.is_diagonal) ∧ (B = 0) ∧ (C = 0) → (A.from_blocks B C D).is_diagonal:=
begin
  rintros h (i | i) (j | j) hij,
  any_goals {rcases h with ⟨ha, hd, hb, hc⟩, simp* at *},
  {have h' : i ≠ j, {simp* at *}, exact ha i j h'},
  {have h' : i ≠ j, {simp* at *}, exact hd i j h'},
end

lemma block_conditions_of_is_sym
{A : matrix I I α} {B : matrix I J α} {C : matrix J I α} {D : matrix J J α} :
(A.from_blocks B C D).is_sym → (A.is_sym) ∧ (D.is_sym) ∧ (Cᵀ = B) ∧ (Bᵀ = C) :=
begin
  rintros h, 
  unfold matrix.is_sym at h,
  rw from_blocks_transpose at h,
  have h1 : (Aᵀ.from_blocks Cᵀ Bᵀ Dᵀ).to_blocks₁₁ = (A.from_blocks B C D).to_blocks₁₁, {rw h},
  have h2 : (Aᵀ.from_blocks Cᵀ Bᵀ Dᵀ).to_blocks₁₂ = (A.from_blocks B C D).to_blocks₁₂, {rw h},
  have h3 : (Aᵀ.from_blocks Cᵀ Bᵀ Dᵀ).to_blocks₂₁ = (A.from_blocks B C D).to_blocks₂₁, {rw h},
  have h4 : (Aᵀ.from_blocks Cᵀ Bᵀ Dᵀ).to_blocks₂₂ = (A.from_blocks B C D).to_blocks₂₂, {rw h},
  simp at *,
  use ⟨h1, h4, h2, h3⟩
end

lemma is_diagnoal_of_sym_block_conditions [has_zero α] 
{A : matrix I I α} {B : matrix I J α} {C : matrix J I α} {D : matrix J J α}
(sym : (A.from_blocks B C D).is_sym) :
(A.is_diagonal) ∧ (D.is_diagonal) ∧ (B = 0) → (A.from_blocks B C D).is_diagonal:=
begin
  rintros h,
  apply is_diagnoal_of_block_conditions,
  refine ⟨h.1, h.2.1, h.2.2, _⟩,
  obtain ⟨g1, g2, g3, g4⟩ :=block_conditions_of_is_sym sym,
  simp [← g4, h.2.2]
end

lemma is_diagnoal_of_sym_block_conditions' [has_zero α] 
{A : matrix I I α} {B : matrix I J α} {C : matrix J I α} {D : matrix J J α}
{M : matrix (I ⊕ J) (I ⊕ J) α} (sym : M.is_sym) (h : M = A.from_blocks B C D) :
(A.is_diagonal) ∧ (D.is_diagonal) ∧ (B = 0) → M.is_diagonal:=
begin
  rw h at sym,
  convert is_diagnoal_of_sym_block_conditions sym,
  rw h,
end

lemma mul_tranpose_is_diagonal_iff_has_orthogonal_rows
[has_mul α] [add_comm_monoid α] (A : matrix I J α) :
(A ⬝ Aᵀ).is_diagonal ↔ A.has_orthogonal_rows :=
begin
  split,
  { rintros h i1 i2 hi,
    have h' := h i1 i2 hi,
    simp [dot_product, mul_apply,*] at *, },
  { intros ha i j h,
    have h':= ha h,
    simp [mul_apply, *, dot_product] at *,
  }
end

lemma tranpose_mul_is_diagonal_iff_has_orthogonal_cols
[has_mul α] [add_comm_monoid α] (A : matrix I J α) :
(Aᵀ ⬝ A).is_diagonal ↔ A.has_orthogonal_clos :=
begin
  split,
  { rintros h i1 i2 hi,
    have h' := h i1 i2 hi,
    simp [dot_product, mul_apply,*] at *, },
  { intros ha i j h,
    have h':= ha h,
    simp [mul_apply, *, dot_product] at *,
  }
end

lemma Kronecker_prod_is_diagonal_of_both_are_diagonal [mul_zero_class α]
{A : matrix I I α} {B : matrix J J α} (ga: A.is_diagonal) (gb: B.is_diagonal): 
(A ⊗ B).is_diagonal := 
begin
  rintros ⟨a, b⟩ ⟨c, d⟩ h,
  simp [Kronecker],
  by_cases ha: a = c,
  have hb: b ≠ d, {intros hb, rw [ha, hb] at h, apply h rfl},
  rw (gb _ _ hb), simp,
  rw (ga _ _ ha), simp,
end

lemma mul_tranpose_eq_diagonal_iff_has_orthogonal_rows
[has_mul α] [add_comm_monoid α] [decidable_eq I] (A : matrix I J α) :
(∃ d, A ⬝ Aᵀ = diagonal d) ↔ A.has_orthogonal_rows :=
by rw [←is_diagonal_iff_diagonal, mul_tranpose_is_diagonal_iff_has_orthogonal_rows]

lemma tranpose_mul_eq_diagonal_iff_has_orthogonal_cols
[has_mul α] [add_comm_monoid α] [decidable_eq J] (A : matrix I J α) :
(∃ d, Aᵀ ⬝ A = diagonal d) ↔ A.has_orthogonal_clos :=
by rw [←is_diagonal_iff_diagonal, tranpose_mul_is_diagonal_iff_has_orthogonal_cols]

end matrix_pre

/- ## Hadamard_matrix  -/
section Hadamard_matrix
open fintype finset matrix

class Hadamard_matrix (H : matrix I I ℚ) : Prop :=
(one_or_neg_one []: ∀ i j, (H i j) = 1 ∨ (H i j) = -1)
(orthogonal_rows []: H.has_orthogonal_rows)

-- alternative def
private abbreviation S := {x : ℚ// x = 1 ∨ x = -1}
instance fun_S_to_ℚ: has_coe (β → S) (β → ℚ) := ⟨λ f x, f x⟩
class Hadamard_matrix' (H : matrix I I S):=
(orthogonal_rows []: ∀ i₁ i₂, i₁ ≠ i₂ → dot_product ((H i₁) : (I → ℚ)) (H i₂) = 0)

@[reducible, simp]
def matched (H : matrix I I ℚ) (i₁ i₂ : I) : set I := 
{j : I | H i₁ j = H i₂ j}

@[reducible, simp]
def mismatched (H : matrix I I ℚ) (i₁ i₂ : I) : set I := 
{j : I | H i₁ j ≠ H i₂ j}

lemma matched_is_finite (H : matrix I I ℚ) (i₁ i₂ : I) : (matched H i₁ i₂).finite :=
set.finite.of_fintype (matched H i₁ i₂)

lemma mismatched_is_finite (H : matrix I I ℚ) (i₁ i₂ : I) : (mismatched H i₁ i₂).finite :=
set.finite.of_fintype (mismatched H i₁ i₂)

example (H : matrix I I ℚ) (i₁ i₂ : I) : fintype (matched H i₁ i₂) := subtype.fintype (λ (x : I), x ∈ matched H i₁ i₂)

@[reducible, simp]
def matcheded_finset (H : matrix I I ℚ) (i₁ i₂ : I) : finset I := 
set.to_finset (matched H i₁ i₂)

@[reducible, simp]
def mismatcheded_finset (H : matrix I I ℚ) (i₁ i₂ : I) : finset I := 
set.to_finset (mismatched H i₁ i₂)

section set

@[simp] lemma match_union_mismatch (H : matrix I I ℚ) (i₁ i₂ : I) :
matched H i₁ i₂ ∪ mismatched H i₁ i₂ = @set.univ I :=
set.union_compl' _ 

@[simp] lemma match_union_mismatch' (H : matrix I I ℚ) (i₁ i₂ : I) :
{j : I | H i₁ j = H i₂ j} ∪ {j : I | ¬H i₁ j = H i₂ j} = @set.univ I :=
begin
  have h := match_union_mismatch H i₁ i₂,
  simp* at *,
end

lemma match_union_mismatch_finset [decidable_eq I] (H : matrix I I ℚ) (i₁ i₂ : I) :
(matched H i₁ i₂).to_finset ∪ (mismatched H i₁ i₂).to_finset = @univ I _:=
begin
  simp only [←set.to_finset_union, univ_eq_set_univ_to_finset],
  congr, simp
end

@[simp] lemma disjoint_match_mismatch (H : matrix I I ℚ) (i₁ i₂ : I) :
disjoint (matched H i₁ i₂) (mismatched H i₁ i₂) :=
set.disjoint_of_compl' _

@[simp] lemma match_disjoint_mismatch_finset [decidable_eq I] (H : matrix I I ℚ) (i₁ i₂ : I) :
disjoint (matched H i₁ i₂).to_finset (mismatched H i₁ i₂).to_finset :=
by simp [set.to_finset_disjoint_iff]

--@[simp] lemma match_disjoint_mismatch_finset' (H : matrix I I ℚ) (i₁ i₂ : I) :
--disjoint {j : I | H i₁ j = H i₂ j}.to_finset {j : I | ¬H i₁ j = H i₂ j}.to_finset :=
--by simp [set.to_finset_disjoint_iff]

lemma card_match_add_card_mismatch [decidable_eq I] (H : matrix I I ℚ) (i₁ i₂ : I) :
set.card (@set.univ I) = set.card (matched H i₁ i₂) + set.card (mismatched H i₁ i₂) :=
set.card_disjoint_union' (disjoint_match_mismatch _ _ _) (match_union_mismatch _ _ _)

lemma dot_product_split [decidable_eq I] (H : matrix I I ℚ) (i₁ i₂ : I) : 
∑ j in (@set.univ I).to_finset, H i₁ j * H i₂ j = 
∑ j in (matched H i₁ i₂).to_finset, H i₁ j * H i₂ j + 
∑ j in (mismatched H i₁ i₂).to_finset, H i₁ j * H i₂ j := 
set.sum_union' (disjoint_match_mismatch H i₁ i₂) (match_union_mismatch H i₁ i₂)

end set

open matrix Hadamard_matrix

/- ## basic properties  -/

section properties
variables (H : matrix I I ℚ) [Hadamard_matrix H]
variables (H' : matrix (fin n) (fin n) ℚ) [Hadamard_matrix H']

attribute [simp] Hadamard_matrix.one_or_neg_one

@[simp] lemma Hadamard_matrix.neg_one_or_one (i j : I) : (H i j) = -1 ∨ (H i j) = 1 :=
(one_or_neg_one H i j).swap

@[simp] lemma Hadamard_matrix.entry_mul_self (i j : I) :
(H i j) * (H i j) = 1 :=
by rcases one_or_neg_one H i j; simp* at *

variables {H}
lemma Hadamard_matrix.entry_eq 
{i j k l : I} (h : H i j ≠ H k l) (h' : H i j = 1):
H i j = 1 → H k l = -1 :=
by rcases one_or_neg_one H k l; simp* at *

lemma Hadamard_matrix.entry_eq' 
{i j k l : I} (h : H i j ≠ H k l) (h' : H i j = -1):
H k l = 1 :=
by rcases one_or_neg_one H k l; simp* at *

variables (H)
@[simp] lemma Hadamard_matrix.entry_mul_mismatch {i j k l : I} (h : H i j ≠ H k l):
(H i j) * (H k l) = -1 :=
by {rcases one_or_neg_one H i j; 
    simp [*, Hadamard_matrix.entry_eq h, Hadamard_matrix.entry_eq' h] at *,}

@[simp] lemma Hadamard_matrix.row_dot_product_self (i : I) :
dot_product (H i) (H i) = card I := by simp [dot_product, finset.card_univ]

@[simp] lemma Hadamard_matrix.col_dot_product_self (j : I) :
dot_product (λ i, H i j) (λ i, H i j) = card I := by simp [dot_product, finset.card_univ]

@[simp] lemma Hadamard_matrix.row_dot_product_other {i₁ i₂ : I} (h : i₁ ≠ i₂) :
dot_product (H i₁) (H i₂) = 0 := orthogonal_rows H h
 
@[simp] lemma Hadamard_matrix.row_dot_product_other' {i₁ i₂ : I} (h : i₂ ≠ i₁) :
dot_product (H i₁) (H i₂)= 0 := by simp [ne.symm h]

@[simp] lemma Hadamard_matrix.row_dot_product'_other {i₁ i₂ : I} (h : i₁ ≠ i₂) :
∑ j, (H i₁ j) * (H i₂ j) = 0 := orthogonal_rows H h

lemma Hadamard_matrix.mul_tanspose [decidable_eq I] :
H ⬝ Hᵀ = (card I : ℚ) • 1 :=
begin
  ext, have : int.one = 1, {refl},
  simp [transpose, matrix.mul, diagonal],
  by_cases i = j; simp [*, mul_one] at *,
end

lemma Hadamard_matrix.det_sq [decidable_eq I] :
(det H)^2 = (card I)^(card I) :=
calc (det H)^2 = (det H) * (det H) : by ring
           ... = det (H ⬝ Hᵀ) : by simp
           ... = det ((card I : ℚ) • (1 : matrix I I ℚ)) : by rw Hadamard_matrix.mul_tanspose
           ... = (card I : ℚ)^(card I) : by simp

lemma Hadamard_matrix.mul_tanspose': H' ⬝ H'ᵀ = (n : ℚ) • 1 :=
by simp [Hadamard_matrix.mul_tanspose]

lemma Hadamard_matrix.right_invertible [decidable_eq I] : 
H ⬝ ((1 / (card I : ℚ)) • Hᵀ) = 1 :=
begin
  have h := Hadamard_matrix.mul_tanspose H,
  by_cases hI : card I = 0,
  {exact @eq_of_empty _ _ _ (card_eq_zero_iff.mp hI) _ _}, --trivial case 
  have h':= congr_arg (has_scalar.smul (1 / (card I : ℚ))) h,
  have hI': (card I : ℚ) ≠ 0, {exact nat.cast_ne_zero.mpr hI},
  have aux : (1 / (card I : ℚ)) • ↑(card I) = (1 : ℚ), {simp* at *},
  rwa [←smul_assoc, aux, ←mul_smul, one_smul] at h',
end

lemma Hadamard_matrix.invertible [decidable_eq I] : invertible H :=
invertible_of_right_inverse (Hadamard_matrix.right_invertible _)

lemma Hadamard_matrix.nonsing_inv_eq [decidable_eq I] : H⁻¹ = (1 / (card I : ℚ)) • Hᵀ :=
inv_eq_right_inv (Hadamard_matrix.right_invertible _)

lemma Hadamard_matrix.tanspose_mul [decidable_eq I] :
Hᵀ ⬝ H = ((card I) : ℚ) • 1 :=
begin
  rw [←nonsing_inv_right_left (Hadamard_matrix.right_invertible H), smul_mul, ←smul_assoc],
  by_cases hI : card I = 0,
  {exact @eq_of_empty _ _ _ (card_eq_zero_iff.mp hI) _ _}, --trivial case 
  simp* at *,
end

-- We are now able to prove:
@[simp] lemma Hadamard_matrix.col_dot_product_other [decidable_eq I] {j₁ j₂ : I} (h : j₁ ≠ j₂) :
dot_product (λ i, H i j₁) (λ i, H i j₂) = 0 :=
begin
  have h':= congr_fun (congr_fun (Hadamard_matrix.tanspose_mul H) j₁) j₂,
  simp [matrix.mul, transpose, has_one.one, diagonal, h] at h',
  assumption,
end

@[simp] lemma Hadamard_matrix.col_dot_product_other' [decidable_eq I] {j₁ j₂ : I} (h : j₂ ≠ j₁) :
dot_product (λ i, H i j₁) (λ i, H i j₂)= 0 := by simp [ne.symm h]

lemma Hadamard_matrix.card_match_eq {i₁ i₂ : I} (h: i₁ ≠ i₂): 
(set.card (matched H i₁ i₂) : ℚ) = ∑ j in (matched H i₁ i₂).to_finset, H i₁ j * H i₂ j :=
begin
  simp [matched],
  have h : ∑ (x : I) in {j : I | H i₁ j = H i₂ j}.to_finset, H i₁ x * H i₂ x 
         = ∑ (x : I) in {j : I | H i₁ j = H i₂ j}.to_finset, 1,
  { apply finset.sum_congr rfl, 
    rintros j hj, 
    have hj': H i₁ j = H i₂ j, {simp* at *},
    simp* at * },
  rw [h, ← finset.card_eq_sum_ones_ℚ],
  congr,
end

lemma Hadamard_matrix.neg_card_mismatch_eq {i₁ i₂ : I} (h: i₁ ≠ i₂): 
- (set.card (mismatched H i₁ i₂) : ℚ) = ∑ j in (mismatched H i₁ i₂).to_finset, H i₁ j * H i₂ j :=
begin
  simp [mismatched],
  have h : ∑ (x : I) in {j : I | H i₁ j ≠ H i₂ j}.to_finset, H i₁ x * H i₂ x 
         = ∑ (x : I) in {j : I | H i₁ j ≠ H i₂ j}.to_finset, -1,
  { apply finset.sum_congr rfl, 
    rintros j hj, 
    have hj': H i₁ j ≠ H i₂ j, {simp* at *},
    simp* at * },
  have h' : ∑ (x : I) in {j : I | H i₁ j ≠ H i₂ j}.to_finset, - (1 : ℚ)
          = - ∑ (x : I) in {j : I | H i₁ j ≠ H i₂ j}.to_finset, (1 : ℚ),
  { simp },
  rw [h, h', ← finset.card_eq_sum_ones_ℚ],
  congr,
end

lemma Hadamard_matrix.card_mismatch_eq {i₁ i₂ : I} (h: i₁ ≠ i₂): 
(set.card (mismatched H i₁ i₂) : ℚ) = - ∑ j in (mismatched H i₁ i₂).to_finset, H i₁ j * H i₂ j :=
by {rw [←Hadamard_matrix.neg_card_mismatch_eq]; simp* at *}

lemma Hadamard_matrix.card_match_eq_card_mismatch_ℚ [decidable_eq I] {i₁ i₂ : I} (h: i₁ ≠ i₂): 
(set.card (matched H i₁ i₂) : ℚ)= set.card (mismatched H i₁ i₂) :=
begin
  have eq := dot_product_split H i₁ i₂,
  rw [Hadamard_matrix.card_match_eq H h, Hadamard_matrix.card_mismatch_eq H h],
  simp only [set.to_finset_univ, Hadamard_matrix.row_dot_product'_other H h] at eq,
  linarith,
end

lemma Hadamard_matrix.card_match_eq_card_mismatch_ℕ [decidable_eq I] {i₁ i₂ : I} (h: i₁ ≠ i₂): 
set.card (matched H i₁ i₂) = set.card (mismatched H i₁ i₂) :=
begin
  have h := Hadamard_matrix.card_match_eq_card_mismatch_ℚ H h,
  simp * at *,
end

def reindex_square (f : I ≃ J) := @reindex _ _ _ _ _ _ _ _ α f f

lemma Hadamard_matrix.reindex (f : I ≃ J) : Hadamard_matrix (reindex_square f H) :=
begin
  simp [reindex_square],
  refine {..},
  { simp [minor_apply] },
  intros i₁ i₂ h,
  simp [dot_product, minor_apply],
  rw [fintype.sum_equiv (f.symm) _ (λ x, H (f.symm i₁) x * H (f.symm i₂) x) (λ x, rfl)],
  have h' : f.symm i₁ ≠ f.symm i₂, {simp [h]},
  simp [h']
end

end properties
/- ## end basic properties  -/

/- ## basic constructions-/
section basic_constr

def H_0 : matrix empty empty ℚ := 1

def H_1 : matrix unit unit ℚ := 1

def H_1' : matrix punit punit ℚ := λ i j, 1

def H_2 : matrix (unit ⊕unit) (unit ⊕unit) ℚ := 
(1 :matrix unit unit ℚ).from_blocks 1 1 (-1)

lemma Hadamard_matrix.H_0 : Hadamard_matrix H_0 :=
⟨by tidy, by tidy⟩

lemma Hadamard_matrix.H_1 : Hadamard_matrix H_1 := 
⟨by tidy, by tidy⟩

lemma Hadamard_matrix.H_1' : Hadamard_matrix H_1' := 
⟨by tidy, by tidy⟩

lemma Hadamard_matrix.H_2 : Hadamard_matrix H_2 := 
⟨ by tidy, 
  λ i₁ i₂ h, by { cases i₁, any_goals {cases i₂}, 
                  any_goals {simp[*, H_2, dot_product, fintype.sum_sum_type] at *} }
⟩

end basic_constr
/- ## end basic constructions-/

/- ## "normalize" constructions-/
section normalize

open matrix Hadamard_matrix

variables [decidable_eq I] (H : matrix I I ℚ) [Hadamard_matrix H] 

def neg_one_smul_row (i : I) := update_row H i (- H i)

def neg_one_smul_col (j : I) := update_column H j (-λ i, H i j)

instance Hadamard_matrix.neg_one_smul_row (i : I) : 
Hadamard_matrix (H.neg_one_smul_row i) := 
begin
  refine {..},
  { intros j k,
    simp [neg_one_smul_row,  update_row_apply],
    by_cases j = i;
    simp[*, one_or_neg_one H i j] at *,
  },
  { intros j k hjk,
    by_cases h1 : j = i, any_goals {by_cases h2 : k = i},
    any_goals {simp [*, neg_one_smul_row, update_row_apply]},
    have h':= (rfl.congr (eq.symm h2)).mp h1,
    contradiction
  }
end

instance Hadamard_matrix.neg_one_smul_col (i : I) : 
Hadamard_matrix (H.neg_one_smul_col i) := 
begin
  refine {..},
  { intros j k,
    simp [neg_one_smul_col,  update_column_apply],
    by_cases k = i;
    simp[*, one_or_neg_one H i j] at *,
  },
  { intros j k hjk,
    simp [*, neg_one_smul_col, dot_product, update_column_apply],
    simp [apply_ite has_neg.neg],
    rw ← dot_product,
    simp *,  
  }
end

end normalize
/- ## end "normalize" constructions -/


/- ## special cases -/
section special_cases

namespace Hadamard_matrix
variables (H : matrix I I ℚ) [Hadamard_matrix H] 

def is_normalized [inhabited I] : Prop :=
H (default I) = 1 ∧ (λ i, H i (default I)) = 1

def is_skew [decidable_eq I] : Prop :=
Hᵀ + H = 2

def is_regular : Prop :=
∀ i j, H.row_sum i = H.col_sum j

variable {H}

@[simp] lemma is_skew_apply_diag 
[decidable_eq I] (h : is_skew H) (i : I) :
H i i + H i i = 2 :=
by replace h:= congr_fun (congr_fun h i) i; simp * at *

@[simp] lemma is_skew_apply_non_diag 
[decidable_eq I] (h : is_skew H) {i j : I} (hij : i ≠ j) :
H j i + H i j = 0 :=
by replace h:= congr_fun (congr_fun h i) j; simp * at *

lemma is_skew_of_neg_one_smul_row_col_of_is_skew 
[decidable_eq I] (i : I) (h : Hadamard_matrix.is_skew H) : 
is_skew ((H.neg_one_smul_row i).neg_one_smul_col i) :=
begin
  simp [is_skew, neg_one_smul_row, neg_one_smul_col],
  ext j k,
  simp [dmatrix.add_apply, update_column_apply, update_row_apply, bit0],
  by_cases g₁ : j = i,
  any_goals {by_cases g₂ : k = i},
  any_goals {simp [*, one_apply]},
  { ring },
  { simp [ne.symm g₂], rw [← neg_add, is_skew_apply_non_diag h (ne.symm g₂)], ring },
  { rw [← neg_add, is_skew_apply_non_diag h g₁], ring },
  { by_cases g₃ : j = k, any_goals {simp*}, ring }
end

end Hadamard_matrix

end special_cases
/- ## end special cases -/


/- ## Sylvester construction  -/
section Sylvester_constr

def Sylvester_constr₀ (H : matrix I I ℚ) [Hadamard_matrix H] : matrix (I ⊕ I) (I ⊕ I) ℚ := 
H.from_blocks H H (-H)

def Sylvester_constr₀' (H : matrix I I ℚ) [Hadamard_matrix H] : 
matrix (I × (unit ⊕ unit)) (I × (unit ⊕ unit)) ℚ := 
H ⊗ H_2

@[instance]
theorem Hadamard_matrix.Sylvester_constr₀ (H : matrix I I ℚ) [Hadamard_matrix H] :
Hadamard_matrix (matrix.Sylvester_constr₀ H) := 
begin
  refine{..},
  { rintros (i | i)  (j | j);
    simp [matrix.Sylvester_constr₀] },
  rintros (i | i) (j | j) h,
  all_goals {simp [matrix.Sylvester_constr₀, dot_product_block', *]},
  any_goals {rw [← dot_product], have h' : i ≠ j; simp* at *}
end

local notation `redindex` := equiv.sum_self_equiv_prod_unit_sum_unit

lemma Sylvester_constr'_eq_reindex_Sylvester_constr 
(H : matrix I I ℚ) [Hadamard_matrix H] : 
H.Sylvester_constr₀' = (reindex_square redindex) H.Sylvester_constr₀ :=
begin
  ext ⟨i, a⟩ ⟨j, b⟩,
  simp [reindex_square, Sylvester_constr₀', Sylvester_constr₀, Kronecker, H_2, from_blocks],
  rcases a with (a | a),
  any_goals {rcases b with (b | b)},
  any_goals {simp [one_apply]},
end

@[instance]
theorem Hadamard_matrix.Sylvester_constr₀' (H : matrix I I ℚ) [Hadamard_matrix H] :
Hadamard_matrix (Sylvester_constr₀' H) := 
begin
  have inst := Hadamard_matrix.Sylvester_constr₀ H, resetI,
  convert Hadamard_matrix.reindex H.Sylvester_constr₀ redindex,
  exact H.Sylvester_constr'_eq_reindex_Sylvester_constr,
end

end Sylvester_constr
/- ## end Sylvester construction  -/

/- ## general Sylvester construction  -/
section general_Sylvester_constr

def Sylvester_constr 
(H₁ : matrix I I ℚ) [Hadamard_matrix H₁] (H₂ : matrix J J ℚ) [Hadamard_matrix H₂] : 
matrix (I × J) (I × J) ℚ := H₁ ⊗ H₂

@[instance]
theorem Hadamard_matrix.Sylvester_constr'
(H₁ : matrix I I ℚ) [Hadamard_matrix H₁] (H₂ : matrix J J ℚ) [Hadamard_matrix H₂] : 
Hadamard_matrix (H₁ ⊗ H₂) :=
begin
  refine {..},
  { rintros ⟨i₁, j₁⟩ ⟨i₂, j₂⟩,
    simp [Kronecker],
    obtain (h | h) := one_or_neg_one H₁ i₁ i₂;
    simp [h] },
  rintros ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h,
  simp [dot_product, ←finset.univ_product_univ, finset.sum_product, Kronecker],
  have : ∑ (x : I) (x_1 : J), H₁ i₁ x * H₂ j₁ x_1 * (H₁ i₂ x * H₂ j₂ x_1) 
       =  ∑ (x : I), (H₁ i₁ x * H₁ i₂ x) * ∑ (y : J), (H₂ j₁ y * H₂ j₂ y),
  { simp [finset.mul_sum], repeat {apply finset.sum_congr rfl, intros x hx}, ring },
  rw this, clear this,
  by_cases hj: j₁ = j₂, any_goals {simp*},
  rw [← finset.sum_mul],
  by_cases hi: i₁ = i₂, any_goals {simp* at *},
end

@[instance]
theorem Hadamard_matrix.Sylvester_constr
(H₁ : matrix I I ℚ) [Hadamard_matrix H₁] (H₂ : matrix J J ℚ) [Hadamard_matrix H₂] : 
Hadamard_matrix (Sylvester_constr H₁ H₂) :=
Hadamard_matrix.Sylvester_constr' H₁ H₂

end general_Sylvester_constr
/- ## end general Sylvester construction  -/

/-
/- ## Paley construction -/
section Paley_construction

variables {F : Type*} [field F] [fintype F] [decidable_eq F] {p : ℕ} [char_p F p]
local notation `q` := fintype.card F 

open finite_field

/- ## Jacobsthal_matrix -/
variable (F)
@[reducible] def Jacobsthal_matrix : matrix F F ℚ := λ a b, χ (a-b)

namespace Jacobsthal_matrix

variable {F}
@[simp] lemma diag_entry_eq_zero (i : F) : (Jacobsthal_matrix F) i i = 0 :=
by simp [Jacobsthal_matrix]

@[simp] lemma non_diag_entry_eq {i j : F} (h : i ≠ j): 
(Jacobsthal_matrix F) i j = 1 ∨ (Jacobsthal_matrix F) i j = -1 :=
by simp [*, Jacobsthal_matrix]

@[simp] lemma non_diag_entry_square_eq {i j : F} (h : i ≠ j): 
(Jacobsthal_matrix F) i j * (Jacobsthal_matrix F) i j = 1 :=
by obtain (h₁ | h₂) := Jacobsthal_matrix.non_diag_entry_eq h; simp*

@[simp] lemma entry_square_eq (i j : F) : 
(Jacobsthal_matrix F) i j * (Jacobsthal_matrix F) i j = ite (i=j) 0 1 :=
by by_cases i=j; simp * at *

-- JJᵀ = qI − one
lemma mul_transpose_self (hp : p ≠ 2) : 
(Jacobsthal_matrix F) ⬝ (Jacobsthal_matrix F)ᵀ = (q : ℚ) • 1 - all_one := 
begin
  ext,
  by_cases i = j,
  { rw ← h,
    simp [mul_apply, all_one],
    simp [sum_ite, filter_ne, fintype.card],
    rw @card_erase_of_mem' _ _ _ (@finset.univ F _) _, 
    any_goals {simp}},
  simp [*, mul_apply, Jacobsthal_matrix, all_one, quad_char_sum_mul h hp],
end

-- J ⬝ one = 0
@[simp] lemma mul_all_one (hp : p ≠ 2) : 
(Jacobsthal_matrix F) ⬝ (all_one : matrix F F ℚ) = 0 := 
begin
  ext,
  simp [all_one, Jacobsthal_matrix, mul_apply],
  exact quad_char.sum_in_univ_eq_zero_reindex_1 hp,
end

-- one ⬝ J = 0
@[simp] lemma all_one_mul (hp : p ≠ 2) : 
(all_one : matrix F F ℚ) ⬝ (Jacobsthal_matrix F) = 0 := 
begin
  ext,
  simp [all_one, Jacobsthal_matrix, mul_apply],
  exact quad_char.sum_in_univ_eq_zero_reindex_2 hp,
end

@[simp] lemma mul_col_one (hp : p ≠ 2) : 
Jacobsthal_matrix F ⬝ col 1 = 0 := 
begin
  ext,
  simp [Jacobsthal_matrix, mul_apply],
  exact quad_char.sum_in_univ_eq_zero_reindex_1 hp,
end

variables {F} 

lemma is_sym_of (h : card F ≡ 1 [MOD 4]) : 
(Jacobsthal_matrix F).is_sym := 
begin
  obtain ⟨p, inst⟩ := char_p.exists F,
  resetI,
  obtain hp := char_ne_two p (or.inl h),
  ext,
  simp [Jacobsthal_matrix],
  have := quad_char_eq_one_of (by simp) ((@neg_one_eq_sq_iff_card_eq_one_mod_four F _ _ _ inst hp).2 h),
  rw [← one_mul (χ (j - i)), ← this, ← quad_char_mul hp],
  congr, ring,
  assumption
end

lemma is_sym_of' (h : card F ≡ 1 [MOD 4]) : 
(Jacobsthal_matrix F)ᵀ = Jacobsthal_matrix F := is_sym_of h

lemma char_j_sub_i_eq_char_i_sub_j (h : q ≡ 1 [MOD 4]) (i j : F) :
χ (j - i) = χ (i - j) :=
begin
  have g := is_sym_of h,
  simp [matrix.is_sym, Jacobsthal_matrix] at g,
  have g' := congr_fun (congr_fun g i) j,
  simp [transpose_apply] at g',
  assumption
end

lemma is_skewsym_of (h : q ≡ 3 [MOD 4]) : 
(Jacobsthal_matrix F).is_skewsym := 
begin
  obtain ⟨p, inst⟩ := char_p.exists F,
  resetI,
  obtain ⟨hp, h'⟩ := char_ne_two' p h,
  ext,
  simp [Jacobsthal_matrix],
  have g: ¬ ∃ (a : F), -1 = a ^ 2, 
  { intro g, 
    rw @neg_one_eq_sq_iff_card_eq_one_mod_four _ _ _ _ inst hp at g, 
    exact absurd g h' },
  have := quad_char_eq_neg_one_of (by simp) g,
  rw [← neg_one_mul (χ (i - j)), ← this, ← quad_char_mul hp],
  congr, ring,
  assumption
end

lemma is_skesym_of' (h : q ≡ 3 [MOD 4]) : 
(Jacobsthal_matrix F)ᵀ = - (Jacobsthal_matrix F) := 
begin
  have := Jacobsthal_matrix.is_skewsym_of h,
  unfold matrix.is_skewsym at this,
  nth_rewrite 1 [← this],
  simp,
end

-- When q is a prime number, J is a circulant matrix. 

end Jacobsthal_matrix
/- ## end Jacobsthal_matrix -/

open Jacobsthal_matrix

/- ## Paley_constr_1 -/

variable (F)
def Paley_constr_1 : matrix (unit ⊕ F) (unit ⊕ F) ℚ :=
(1 : matrix unit unit ℚ).from_blocks (- row 1) (col 1) (1 + (Jacobsthal_matrix F))

@[simp] def Paley_constr_1'_aux : matrix (unit ⊕ F) (unit ⊕ F) ℚ :=
(0 : matrix unit unit ℚ).from_blocks (- row 1) (col 1) (Jacobsthal_matrix F)

def Paley_constr_1' := 1 + (Paley_constr_1'_aux F)

lemma Paley_constr_1'_eq_Paley_constr_1 : 
Paley_constr_1' F = Paley_constr_1 F :=
begin
  simp only [Paley_constr_1', Paley_constr_1'_aux, Paley_constr_1, ←from_blocks_one, from_blocks_add],
  simp,
end

variable {F}
theorem Hadamard_matrix.Paley_constr_1 (h : q ≡ 3 [MOD 4]): 
Hadamard_matrix (Paley_constr_1 F) := 
begin
  obtain ⟨p, inst⟩ := char_p.exists F,
  resetI,
  obtain ⟨hp, h'⟩ := char_ne_two' p h,
  refine {..},
  {
    rintros (i | i)  (j | j),
    all_goals {simp [Paley_constr_1, one_apply, Jacobsthal_matrix]},
    by_cases i = j,
    all_goals {simp*}
  },
  rw ←mul_tranpose_is_diagonal_iff_has_orthogonal_rows,
  simp only [Paley_constr_1, from_blocks_transpose, from_blocks_multiply],
  apply is_diagnoal_of_block_conditions,
  repeat {split},
  { exact is_diagonal_of_unit _ },
  { simp [col_one_mul_row_one, matrix.add_mul, matrix.mul_add],
    rw [mul_transpose_self hp, is_skesym_of' h, add_assoc, add_comm, add_assoc], 
    simp,
    assumption },
  { simp [matrix.mul_add], 
    rw [← transpose_col, ← transpose_mul, mul_col_one hp, transpose_zero],
    assumption },
  { simp [matrix.add_mul], rw [mul_col_one hp],
    assumption },
end

/- ## end Paley_constr_1 -/

/- ## Paley_constr_2 -/

/- # Paley_constr_2_helper -/
namespace Paley_constr_2

variable (F)

def pre_1 : matrix (unit ⊕ unit) (unit ⊕ unit) ℚ :=
(1 : matrix unit unit ℚ).from_blocks (-1) (-1) (-1)

lemma pre_1_is_sym : pre_1.is_sym :=
is_sym_of_block_conditions ⟨by simp, by simp, by simp⟩

lemma pre_1_is_sym' (a b : unit ⊕ unit) : pre_1 a b = pre_1 b a :=
begin
  have h:= congr_fun (congr_fun pre_1_is_sym b) a,
  simp [transpose_apply] at h,
  assumption
end

def pre_2 : matrix (unit ⊕ unit) (unit ⊕ unit) ℚ :=
(1 : matrix unit unit ℚ).from_blocks 1 1 (-1)

lemma pre_2_is_sym : pre_2.is_sym :=
is_sym_of_block_conditions ⟨by simp, by simp, by simp⟩

lemma pre_2_is_sym' (a b : unit ⊕ unit) : pre_2 a b = pre_2 b a :=
begin
  have h:= congr_fun (congr_fun pre_2_is_sym b) a,
  simp [transpose_apply] at h,
  assumption
end

def sq : matrix (unit ⊕ unit) (unit ⊕ unit) ℚ :=
(2 : matrix unit unit ℚ).from_blocks 0 0 2

@[simp] lemma sq_is_diagonal : sq.is_diagonal := 
is_diagnoal_of_block_conditions ⟨by simp, by simp, rfl, rfl⟩

@[simp] lemma sq_pre_1 : 
pre_1 ⬝ pre_1ᵀ = sq := 
begin
  simp [from_blocks_transpose, from_blocks_multiply, sq, pre_1],
  congr' 1,
end

@[simp] lemma sq_pre_2 : 
pre_2 ⬝ pre_2ᵀ = sq := 
begin
  simp [from_blocks_transpose, from_blocks_multiply, sq, pre_2],
  congr' 1,
end
 
def replace (A : matrix I J ℚ) : 
matrix (I × (unit ⊕ unit)) (J × (unit ⊕ unit)) ℚ :=
λ ⟨i, a⟩ ⟨j, b⟩, 
if (A i j = 0) then pre_1 a b 
               else (A i j) • pre_2 a b
 
lemma replace_transpose (A : matrix I J ℚ) :
(replace A)ᵀ = replace (Aᵀ) := 
begin
  ext ⟨i, a⟩ ⟨j, b⟩,
  simp [transpose_apply, replace],
  congr' 1,
  rw pre_1_is_sym' b a,
  rw pre_2_is_sym' b a,
end

lemma replace_zero :
replace (0 : matrix unit unit ℚ) = 1 ⊗ pre_1 :=
begin
  ext ⟨a, b⟩ ⟨c, d⟩,
  simp [replace, Kronecker, one_apply]
end

lemma replace_no_zero_entry_matrix
{A : matrix I J ℚ} (h : ∀ i j, A i j ≠ 0) : replace A = A ⊗ pre_2 := 
begin
  ext ⟨i, a⟩ ⟨j, b⟩,
  simp [replace, Kronecker],
  intro g,
  exact absurd g (h i j)
end

lemma replace_minus_row_one : 
replace (-row 1 : matrix unit F ℚ) = (-row 1) ⊗ pre_2 :=
replace_no_zero_entry_matrix (λ a i, by simp [row])

@[simp] lemma sq_replace_zero :
replace (0 : matrix unit unit ℚ) ⬝ (replace (0 : matrix unit unit ℚ))ᵀ = 1 ⊗ sq :=
by simp [replace_zero, K_transpose, K_mul]

@[simp] lemma sq_replace_no_zero_entry_matrix 
{A : matrix I J ℚ} (h : ∀ i j, A i j ≠ 0) :   
(replace A) ⬝ (replace A)ᵀ = (A ⬝ Aᵀ) ⊗ sq := 
by simp [replace_no_zero_entry_matrix h, K_transpose, K_mul]  

variable {F}

lemma sq_replace_Jacobsthal_matrix_aux (hF : card F ≡ 1 [MOD 4]) :   
replace (Jacobsthal_matrix F) ⬝ (replace (Jacobsthal_matrix F))ᵀ = 
((Jacobsthal_matrix F) ⬝ (Jacobsthal_matrix F)ᵀ + 1 ⬝ (1 : matrix F F ℚ)ᵀ) ⊗ sq := 
begin
  ext ⟨i, a⟩ ⟨j, b⟩,
  simp only [Kronecker, mul_apply, ←finset.univ_product_univ, finset.sum_product,
             dmatrix.add_apply, ←finset.sum_add_distrib, sum_mul],
  rw finset.sum_split _ (λ k, k = i ∨ k = j),
  rw finset.sum_split univ (λ k, k = i ∨ k = j),
  congr' 1, 
  { by_cases i = j,
    { simp [h, fintype.sum_sum_type, Jacobsthal_matrix, replace], 
      obtain (a | a) := a,
      any_goals { obtain (b | b) := b },
      any_goals { simp [pre_1, pre_2, sq, one_apply] },
      ring, ring },
    simp [h, (ne.symm h), fintype.sum_sum_type, Jacobsthal_matrix, replace],
    obtain (a | a) := a,
    any_goals { obtain (b | b) := b },
    any_goals { simp [pre_1, pre_2, sq, one_apply] },
    any_goals { rw [char_j_sub_i_eq_char_i_sub_j hF i j], ring },
  },
  any_goals {apply finset.sum_congr rfl, intros k hk, simp at hk, simp [fintype.sum_sum_type]},
  push_neg at hk,
  obtain ⟨h₁, h₂⟩ := hk,
  have g₁ : i - k ≠ 0, {intros h, apply h₁, exact (eq_of_sub_eq_zero h).symm},
  have g₂ : j - k ≠ 0, {intros h, apply h₂, exact (eq_of_sub_eq_zero h).symm},
  simp [Jacobsthal_matrix, replace, g₁, g₂, h₁.symm, h₂.symm],
  any_goals {obtain (a | a) := a}, 
  any_goals {obtain (b | b) := b},
  any_goals {simp [pre_1, pre_2, sq, one_apply]},
  ring, ring,
end

lemma sq_replace_Jacobsthal_matrix (hF : card F ≡ 1 [MOD 4]) :   
replace (Jacobsthal_matrix F) ⬝ (replace (Jacobsthal_matrix F))ᵀ = 
(((q : ℚ) + 1) • (1 : matrix F F ℚ) - all_one) ⊗ sq := 
begin
  obtain ⟨p, inst⟩ := char_p.exists F,
  obtain hp := @char_ne_two _ _ _ _ inst (or.inl hF),
  rw [sq_replace_Jacobsthal_matrix_aux hF],
  rw [Jacobsthal_matrix.mul_transpose_self hp],
  congr' 1,
  simp [add_smul, sub_add_eq_add_sub],
  assumption
end

end Paley_constr_2
/- # end Paley_constr_2_helper -/

open Paley_constr_2

variable (F)
def Paley_constr_2 :=
(replace (0 : matrix unit unit ℚ)).from_blocks 
(replace (- row 1)) 
(replace (- col 1))
(replace (Jacobsthal_matrix F))

lemma Paley_constr_2.one_or_neg_one : 
∀ (i j : unit × (unit ⊕ unit) ⊕ F × (unit ⊕ unit)), 
Paley_constr_2 F i j = 1 ∨ Paley_constr_2 F i j = -1 :=
begin
  rintros (⟨a, (u₁|u₂)⟩ | ⟨i, (u₁ | u₂)⟩) (⟨b, (u₃|u₄)⟩ | ⟨j, (u₃ | u₄)⟩),
  all_goals {simp [Paley_constr_2, one_apply, Jacobsthal_matrix, replace, pre_1, pre_2]},
  all_goals {by_cases i = j},
  any_goals {simp [h]},
end


variable {F}
theorem Hadamard_matrix.Paley_constr_2 (h : card F ≡ 1 [MOD 4]): 
Hadamard_matrix (Paley_constr_2 F) :=
begin
  obtain ⟨p, inst⟩ := char_p.exists F,
  resetI,
  obtain hp := char_ne_two p (or.inl h),
  refine {..},
  { exact Paley_constr_2.one_or_neg_one F },
  rw ←mul_tranpose_is_diagonal_iff_has_orthogonal_rows,
  have sym := mul_transpose_self_is_sym (Paley_constr_2 F),
  convert is_diagnoal_of_sym_block_conditions' sym _ ⟨_, _, _⟩,
  swap 5,
  { simp [Paley_constr_2, from_blocks_transpose, from_blocks_multiply] },
  { simp [row_one_mul_col_one, nat.smul_one_eq_coe, ← add_K],
    apply Kronecker_prod_is_diagonal_of_both_are_diagonal; simp },
  { simp only [col_one_mul_row_one, sq_replace_Jacobsthal_matrix h, ← add_K],
    refine Kronecker_prod_is_diagonal_of_both_are_diagonal _ sq_is_diagonal,
    simp },
  { simp [replace_zero, replace_transpose, is_sym_of' h, replace_minus_row_one, K_mul],
    ext ⟨i, a⟩ ⟨j, b⟩,
    simp [dmatrix.add_apply, mul_apply, ←finset.univ_product_univ, finset.sum_product],
    rw finset.sum_comm,
    simp [fintype.sum_sum_type, Kronecker, replace, Jacobsthal_matrix, finset.sum_ite],
    simp [finset.filter_eq', finset.filter_ne'],
    repeat {rw [finset.sum_erase _]},
    swap 2, {simp},
    swap 2, {simp},
    simp [pre_1, pre_2, from_blocks_multiply],
    rcases a with (a | a), 
    any_goals {rcases b with (b | b)},
    any_goals {simp [from_blocks, one_apply], ring},
    any_goals {rw [quad_char.sum_in_univ_eq_zero_reindex_2 hp], ring},
    any_goals {assumption} },
end

/- ## end Paley_constr_2 -/
end Paley_construction
/- ## end Paley construction -/
-/

/- ## order 92-/
section order_92

variables [comm_ring R]

def poly (n : ℕ) : polynomial (matrix (fin n) (fin n) R)  := sorry

-- aeval M (char_poly M)

def circulant' {α : Type*} {n : ℕ} (v : fin n → α) : matrix (fin n) (fin n) α :=
polynomial.aeval v (poly n)

@[reducible]
def circulant {α : Type*} {n : ℕ} (v : fin n → α) : matrix (fin n) (fin n) α
| i j := v (i - j)

namespace H_92

def a : fin 23 → ℚ := 
![ 1,  1, -1, -1, -1,  1, -1, -1, -1,  1, -1,  1,  1, -1,  1, -1, -1, -1,  1, -1, -1, -1,  1]
def b : fin 23 → ℚ := 
![ 1, -1,  1,  1, -1,  1,  1, -1, -1,  1,  1,  1,  1,  1,  1, -1, -1,  1,  1, -1,  1,  1, -1]
def c : fin 23 → ℚ := 
![ 1,  1,  1, -1, -1, -1,  1,  1, -1,  1, -1,  1,  1, -1,  1, -1,  1,  1, -1, -1, -1,  1,  1]
def d : fin 23 → ℚ := 
![ 1,  1,  1, -1,  1,  1,  1, -1,  1, -1, -1, -1, -1, -1, -1,  1, -1,  1,  1,  1, -1,  1,  1]

local notation `A` := circulant a
local notation `B` := circulant b
local notation `C` := circulant c
local notation `D` := circulant d

lemma eq : A^2 + B^2 + C^2 + D^2 = (92 : matrix (fin 23) (fin 23) ℚ) := 
begin
  sorry
end


end H_92


end order_92
/- ## end order 92-/

/- ## order -/
section order
open matrix Hadamard_matrix

example : 1 = 2 := by {sorry} -- do below
/-
theorem Hadamard_matrix.order_constraint [decidable_eq I] (H : matrix I I ℚ) [Hadamard_matrix H] 
: card I ≥ 3 →  4 ∣ card I := 
begin
  intros h, 
  obtain ⟨i₁, i₂, i₃, ⟨h₁₂, h₁₃, h₂₃⟩⟩:= pick_elements h,
  set J₁ := {j : I | H i₁ j = H i₂ j ∧ H i₂ j = H i₃ j},
  set J₂ := {j : I | H i₁ j = H i₂ j ∧ H i₂ j ≠ H i₃ j},
  set J₃ := {j : I | H i₁ j ≠ H i₂ j ∧ H i₁ j = H i₃ j},
  set J₄ := {j : I | H i₁ j ≠ H i₂ j ∧ H i₂ j = H i₃ j},
  have d₁₂: disjoint J₁ J₂, 
    {simp [set.disjoint_iff_inter_eq_empty], ext, simp, intros, sorry},
  have d₁₃: disjoint J₁ J₃, 
    {simp [set.disjoint_iff_inter_eq_empty], ext, simp, intros a b c d, exact c a},
  have d₁₄: disjoint J₁ J₄, 
    {simp [set.disjoint_iff_inter_eq_empty], ext, simp, intros a b c d, sorry},
  have d₂₃: disjoint J₂ J₃, 
    {simp [set.disjoint_iff_inter_eq_empty], ext, simp, intros a b c d, sorry},
  have d₂₄: disjoint J₂ J₄, 
    {simp [set.disjoint_iff_inter_eq_empty], ext, simp, intros a b c d, sorry},
  have d₃₄: disjoint J₃ J₄, 
    {simp [set.disjoint_iff_inter_eq_empty], ext, simp, intros a b c d, 
    have : H i₁ x = H i₂ x, {sorry}, sorry},
  have u₁₂: J₁.union J₂ = matched H i₁ i₂, {sorry},
  have u₁₃: J₁.union J₃ = matched H i₁ i₃, {sorry},
  have u₁₄: J₁.union J₄ = matched H i₂ i₃, {sorry},
  have u₂₃: J₂.union J₃ = mismatched H i₂ i₃, {sorry},
  have u₂₄: J₂.union J₄ = mismatched H i₁ i₃, {sorry},
  have u₃₄: J₃.union J₄ = mismatched H i₁ i₂, {sorry},
  have eq₁ := card_match_eq_card_mismatch_ℕ H h₁₂,
  have eq₂ := card_match_eq_card_mismatch_ℕ H h₁₃,
  have eq₃ := card_match_eq_card_mismatch_ℕ H h₂₃,
  have eq := card_match_add_card_mismatch H i₁ i₂,
  rw [set.card_disjoint_union' d₁₂ u₁₂, set.card_disjoint_union' d₃₄ u₃₄] at eq₁ eq,
  rw [set.card_disjoint_union' d₁₃ u₁₃, set.card_disjoint_union' d₂₄ u₂₄] at eq₂,
  rw [set.card_disjoint_union' d₁₄ u₁₄, set.card_disjoint_union' d₂₃ u₂₃] at eq₃,
  have g₂₁ : J₂.card = J₁.card, {linarith},
  have g₃₁ : J₃.card = J₁.card, {linarith},
  have g₄₁ : J₄.card = J₁.card, {linarith},
  rw [g₂₁, g₃₁, g₄₁, set.univ_card_eq_fintype_card] at eq,
  use J₁.card,
  simp [eq],
  noncomm_ring,
end
-/

theorem Hadamard_matrix.order_constructed_1: 
∀ n : ℕ, ∃ (I : Type*) (inst : fintype I) 
(H : @matrix I I inst inst ℚ) (h : @Hadamard_matrix I inst H), 
@fintype.card I inst = 2^n := 
begin
  intro n,
  induction n with n hn,
  { refine ⟨punit, (infer_instance), H_1', Hadamard_matrix.H_1', by simp⟩ },
  rcases hn with ⟨I, inst, H, h, hI⟩,
  resetI,
  refine ⟨ I ⊕ I, infer_instance, H.Sylvester_constr₀, infer_instance, _ ⟩,
  rw [fintype.card_sum, hI],
  ring_nf,
end

theorem Hadamard_matrix.Hadamard_conjecture: 
∀ k : ℕ, ∃ (I : Type*) (inst : fintype I) 
(H : @matrix I I inst inst ℚ) (h : @Hadamard_matrix I inst H), 
@fintype.card I inst = 4 * k := sorry

end order
/- ## end order -/

end Hadamard_matrix
/- ## end Hadamard_matrix  -/

end matrix

----------------------------------------------- end of file
