import tactic
import tactic.gptf
import data.fintype.card
import data.finset.basic
import algebra.big_operators
import linear_algebra.char_poly.basic

import finite_field
import circulant_matrix
import diagonal_matrix

--attribute [to_additive] fintype.prod_dite
--local attribute [-instance] set.has_coe_to_sort
local attribute [-instance] set.fintype_univ
local attribute [instance] set_fintype

open_locale big_operators

----------------------------------------------------------------------------
section pre 

variables {α β I J : Type*} (S T U : set α)
variables [fintype I] [fintype J] 

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

@[simp] private 
lemma push_nag [add_group α] (A : matrix I J α) {i : I} {j : J} {a : α}: 
- A i j = a ↔ A i j = -a :=
⟨λ h, eq_neg_of_eq_neg (eq.symm h), λ h, neg_eq_iff_neg_eq.mp (eq.symm h)⟩

lemma dot_product_split_over_subtypes {R} [semiring R] 
(v w : I → R) (p : I → Prop) [decidable_pred p] :
dot_product v w =
∑ j : {j : I // p j}, v j * w j + ∑ j : {j : I // ¬ (p j)}, v j * w j :=
by { simp [dot_product], rw fintype.sum_split p}

def reindex_square (f : I ≃ J) := @reindex _ _ _ _ _ _ _ _ α f f

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
namespace Hadamard_matrix

variables (H : matrix I I ℚ) [Hadamard_matrix H]
variables (H' : matrix (fin n) (fin n) ℚ) [Hadamard_matrix H']

attribute [simp] one_or_neg_one

@[simp] lemma neg_one_or_one (i j : I) : (H i j) = -1 ∨ (H i j) = 1 :=
(one_or_neg_one H i j).swap

@[simp] lemma entry_mul_self (i j : I) :
(H i j) * (H i j) = 1 :=
by rcases one_or_neg_one H i j; simp* at *

variables {H}

lemma entry_eq_one_of_ne_neg_one {i j : I} (h : H i j ≠ -1) :
H i j = 1 := by {have := one_or_neg_one H i j, tauto}

lemma entry_eq_neg_one_of_ne_one {i j : I} (h : H i j ≠ 1) :
H i j = -1 := by {have := one_or_neg_one H i j, tauto}

lemma entry_eq_neg_one_of {i j k l : I} (h : H i j ≠ H k l) (h' : H i j = 1):
H k l = -1 := by rcases one_or_neg_one H k l; simp* at *

lemma entry_eq_one_of {i j k l : I} (h : H i j ≠ H k l) (h' : H i j = -1):
H k l = 1 := by rcases one_or_neg_one H k l; simp* at *

lemma entry_eq_entry_of {a b c d e f : I} (h₁: H a b ≠ H c d) (h₂: H a b ≠ H e f) :
H c d = H e f := 
begin
  by_cases g : H a b = 1,
  { have g₁ := entry_eq_neg_one_of h₁ g,
    have g₂ := entry_eq_neg_one_of h₂ g,
    linarith },
  { replace g:= entry_eq_neg_one_of_ne_one g,
    have g₁ := entry_eq_one_of h₁ g,
    have g₂ := entry_eq_one_of h₂ g,
    linarith }
end

variables (H)
@[simp] lemma entry_mul_mismatch {i j k l : I} (h : H i j ≠ H k l):
(H i j) * (H k l) = -1 :=
by {rcases one_or_neg_one H i j; 
    simp [*, entry_eq_one_of h, entry_eq_neg_one_of h] at *,}

@[simp] lemma row_dot_product_self (i : I) :
dot_product (H i) (H i) = card I := by simp [dot_product, finset.card_univ]

@[simp] lemma col_dot_product_self (j : I) :
dot_product (λ i, H i j) (λ i, H i j) = card I := by simp [dot_product, finset.card_univ]

@[simp] lemma row_dot_product_other {i₁ i₂ : I} (h : i₁ ≠ i₂) :
dot_product (H i₁) (H i₂) = 0 := orthogonal_rows H h
 
@[simp] lemma row_dot_product_other' {i₁ i₂ : I} (h : i₂ ≠ i₁) :
dot_product (H i₁) (H i₂)= 0 := by simp [ne.symm h]

@[simp] lemma row_dot_product'_other {i₁ i₂ : I} (h : i₁ ≠ i₂) :
∑ j, (H i₁ j) * (H i₂ j) = 0 := orthogonal_rows H h

lemma mul_tanspose [decidable_eq I] :
H ⬝ Hᵀ = (card I : ℚ) • 1 :=
begin
  ext, have : int.one = 1, {refl},
  simp [transpose, matrix.mul, diagonal],
  by_cases i = j; simp [*, mul_one] at *,
end

lemma det_sq [decidable_eq I] :
(det H)^2 = (card I)^(card I) :=
calc (det H)^2 = (det H) * (det H) : by ring
           ... = det (H ⬝ Hᵀ) : by simp
           ... = det ((card I : ℚ) • (1 : matrix I I ℚ)) : by rw mul_tanspose
           ... = (card I : ℚ)^(card I) : by simp

lemma mul_tanspose': H' ⬝ H'ᵀ = (n : ℚ) • 1 :=
by simp [mul_tanspose]

lemma right_invertible [decidable_eq I] : 
H ⬝ ((1 / (card I : ℚ)) • Hᵀ) = 1 :=
begin
  have h := mul_tanspose H,
  by_cases hI : card I = 0,
  {exact @eq_of_empty _ _ _ (card_eq_zero_iff.mp hI) _ _}, --trivial case 
  have h':= congr_arg (has_scalar.smul (1 / (card I : ℚ))) h,
  have hI': (card I : ℚ) ≠ 0, {exact nat.cast_ne_zero.mpr hI},
  have aux : (1 / (card I : ℚ)) • ↑(card I) = (1 : ℚ), {simp* at *},
  rwa [←smul_assoc, aux, ←mul_smul, one_smul] at h',
end

lemma invertible [decidable_eq I] : invertible H :=
invertible_of_right_inverse (Hadamard_matrix.right_invertible _)

lemma nonsing_inv_eq [decidable_eq I] : H⁻¹ = (1 / (card I : ℚ)) • Hᵀ :=
inv_eq_right_inv (Hadamard_matrix.right_invertible _)

lemma tanspose_mul [decidable_eq I] :
Hᵀ ⬝ H = ((card I) : ℚ) • 1 :=
begin
  rw [←nonsing_inv_right_left (right_invertible H), smul_mul, ←smul_assoc],
  by_cases hI : card I = 0,
  {exact @eq_of_empty _ _ _ (card_eq_zero_iff.mp hI) _ _}, --trivial case 
  simp* at *,
end

-- We are now able to prove:
@[simp] lemma col_dot_product_other [decidable_eq I] {j₁ j₂ : I} (h : j₁ ≠ j₂) :
dot_product (λ i, H i j₁) (λ i, H i j₂) = 0 :=
begin
  have h':= congr_fun (congr_fun (tanspose_mul H) j₁) j₂,
  simp [matrix.mul, transpose, has_one.one, diagonal, h] at h',
  assumption,
end

@[simp] lemma col_dot_product_other' [decidable_eq I] {j₁ j₂ : I} (h : j₂ ≠ j₁) :
dot_product (λ i, H i j₁) (λ i, H i j₂)= 0 := by simp [ne.symm h]

lemma card_match_eq {i₁ i₂ : I} (h: i₁ ≠ i₂): 
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

lemma neg_card_mismatch_eq {i₁ i₂ : I} (h: i₁ ≠ i₂): 
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

lemma card_mismatch_eq {i₁ i₂ : I} (h: i₁ ≠ i₂): 
(set.card (mismatched H i₁ i₂) : ℚ) = - ∑ j in (mismatched H i₁ i₂).to_finset, H i₁ j * H i₂ j :=
by {rw [←neg_card_mismatch_eq]; simp* at *}

lemma card_match_eq_card_mismatch_ℚ [decidable_eq I] {i₁ i₂ : I} (h: i₁ ≠ i₂): 
(set.card (matched H i₁ i₂) : ℚ)= set.card (mismatched H i₁ i₂) :=
begin
  have eq := dot_product_split H i₁ i₂,
  rw [card_match_eq H h, card_mismatch_eq H h],
  simp only [set.to_finset_univ, row_dot_product'_other H h] at eq,
  linarith,
end

lemma card_match_eq_card_mismatch_ℕ [decidable_eq I] {i₁ i₂ : I} (h: i₁ ≠ i₂): 
set.card (matched H i₁ i₂) = set.card (mismatched H i₁ i₂) :=
begin
  have h := card_match_eq_card_mismatch_ℚ H h,
  simp * at *,
end

lemma reindex (f : I ≃ J) : Hadamard_matrix (reindex_square f H) :=
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

end Hadamard_matrix
end properties
/- ## end basic properties  -/

open Hadamard_matrix

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

lemma Sylvester_constr₀'_eq_reindex_Sylvester_constr₀ 
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
  exact H.Sylvester_constr₀'_eq_reindex_Sylvester_constr₀,
end

theorem Hadamard_matrix.order_conclusion_1: 
∀ (n : ℕ), ∃ {I : Type*} [inst : fintype I] 
{H : @matrix I I inst inst ℚ} (h : @Hadamard_matrix I inst H), 
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

theorem {u v} Hadamard_matrix.order_conclusion_2 {I : Type u} {J : Type v} [fintype I] [fintype J]
(H₁ : matrix I I ℚ) [Hadamard_matrix H₁] (H₂ : matrix J J ℚ) [Hadamard_matrix H₂] :
∃ {K : Type max u v} [inst : fintype K] (H : @matrix K K inst inst ℚ), 
@Hadamard_matrix K inst H ∧ @fintype.card K inst = card I * card J :=
⟨(I × J), _, Sylvester_constr H₁ H₂, ⟨infer_instance, card_prod I J⟩⟩

end general_Sylvester_constr
/- ## end general Sylvester construction  -/


/- ## Paley construction -/
section Paley_construction

variables {F : Type*} [field F] [fintype F] [decidable_eq F] {p : ℕ} [char_p F p]
local notation `q` := fintype.card F 

open finite_field

/- ## Jacobsthal_matrix -/
variable (F)
@[reducible] def Jacobsthal_matrix : matrix F F ℚ := λ a b, χ (a-b)

namespace Jacobsthal_matrix

lemma eq_cir : (Jacobsthal_matrix F) = cir χ := rfl

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

lemma is_sym_of (h : q ≡ 1 [MOD 4]) : 
(Jacobsthal_matrix F).is_sym := 
begin
  rw [eq_cir, cir_is_sym_ext_iff],
  exact quad_char_is_sym_of h
end

lemma is_sym_of' (h : card F ≡ 1 [MOD 4]) : 
(Jacobsthal_matrix F)ᵀ = Jacobsthal_matrix F := is_sym_of h

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

@[instance]
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
    any_goals { simp [quad_char_is_sym_of' hF i j], ring },
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

@[instance]
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
  { simp [replace_zero, replace_transpose, (is_sym_of h).eq, replace_minus_row_one, K_mul],
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


/- ## order 92-/
section order_92

namespace H_92

def a : fin 23 → ℚ := 
![ 1,  1, -1, -1, -1,  1, -1, -1, -1,  1, -1,  1,  1, -1,  1, -1, -1, -1,  1, -1, -1, -1,  1]
def b : fin 23 → ℚ := 
![ 1, -1,  1,  1, -1,  1,  1, -1, -1,  1,  1,  1,  1,  1,  1, -1, -1,  1,  1, -1,  1,  1, -1]
def c : fin 23 → ℚ := 
![ 1,  1,  1, -1, -1, -1,  1,  1, -1,  1, -1,  1,  1, -1,  1, -1,  1,  1, -1, -1, -1,  1,  1]
def d : fin 23 → ℚ := 
![ 1,  1,  1, -1,  1,  1,  1, -1,  1, -1, -1, -1, -1, -1, -1,  1, -1,  1,  1,  1, -1,  1,  1]

abbreviation A := cir a
abbreviation B := cir b
abbreviation C := cir c
abbreviation D := cir d

@[simp] lemma a.one_or_neg_one : ∀ i, a i ∈ ({1, -1} : set ℚ) := 
λ i, begin simp, dec_trivial! end
@[simp] lemma b.one_or_neg_one : ∀ i, b i ∈ ({1, -1} : set ℚ) := 
λ i, begin simp, dec_trivial! end
@[simp] lemma c.one_or_neg_one : ∀ i, c i ∈ ({1, -1} : set ℚ) := 
λ i, begin simp, dec_trivial! end
@[simp] lemma d.one_or_neg_one : ∀ i, d i ∈ ({1, -1} : set ℚ) := 
λ i, begin simp, dec_trivial! end

@[simp] lemma A.one_or_neg_one : ∀ i j, A i j = 1 ∨ A i j = -1 := 
by convert cir_entry_in_of_vec_entry_in a.one_or_neg_one
@[simp] lemma A.neg_one_or_one : ∀ i j, A i j = -1 ∨ A i j = 1 := 
λ i j, (A.one_or_neg_one i j).swap
@[simp] lemma B.one_or_neg_one : ∀ i j, B i j = 1 ∨ B i j = -1 := 
by convert cir_entry_in_of_vec_entry_in b.one_or_neg_one
@[simp] lemma B.neg_one_or_one : ∀ i j, B i j = -1 ∨ B i j = 1 := 
λ i j, (B.one_or_neg_one i j).swap
@[simp] lemma C.one_or_neg_one : ∀ i j, C i j = 1 ∨ C i j = -1 := 
by convert cir_entry_in_of_vec_entry_in c.one_or_neg_one
@[simp] lemma C.neg_one_or_one : ∀ i j, C i j = -1 ∨ C i j = 1 := 
λ i j, (C.one_or_neg_one i j).swap
@[simp] lemma D.one_or_neg_one : ∀ i j, D i j = 1 ∨ D i j = -1 := 
by convert cir_entry_in_of_vec_entry_in d.one_or_neg_one
@[simp] lemma D.neg_one_or_one : ∀ i j, D i j = -1 ∨ D i j = 1 := 
λ i j, (D.one_or_neg_one i j).swap

@[simp] lemma a_is_sym : ∀ (i : fin 23), a (-i) = a i := by dec_trivial

@[simp] lemma a_is_sym' : ∀ (i : fin 23), 
![(1 : ℚ), 1, -1, -1, -1,  1, -1, -1, -1,  1, -1,  1,  1, -1,  1, -1, -1, -1,  1, -1, -1, -1,  1] (-i) = 
![(1 : ℚ), 1, -1, -1, -1,  1, -1, -1, -1,  1, -1,  1,  1, -1,  1, -1, -1, -1,  1, -1, -1, -1,  1]   i := 
by convert a_is_sym

@[simp] lemma b_is_sym : ∀ (i : fin 23), b (-i) = b i := by dec_trivial

@[simp] lemma b_is_sym' : ∀ (i : fin 23), 
![(1 : ℚ), -1,  1,  1, -1,  1,  1, -1, -1,  1,  1,  1,  1,  1,  1, -1, -1,  1,  1, -1,  1,  1, -1] (-i) = 
![(1 : ℚ), -1,  1,  1, -1,  1,  1, -1, -1,  1,  1,  1,  1,  1,  1, -1, -1,  1,  1, -1,  1,  1, -1]   i := 
by convert b_is_sym

@[simp] lemma c_is_sym : ∀ (i : fin 23), c (-i) = c i := by dec_trivial

@[simp] lemma c_is_sym' : ∀ (i : fin 23), 
![ (1 : ℚ), 1,  1, -1, -1, -1,  1,  1, -1,  1, -1,  1,  1, -1,  1, -1,  1,  1, -1, -1, -1,  1,  1] (-i) = 
![ (1 : ℚ), 1,  1, -1, -1, -1,  1,  1, -1,  1, -1,  1,  1, -1,  1, -1,  1,  1, -1, -1, -1,  1,  1]   i := 
by convert c_is_sym

@[simp] lemma d_is_sym : ∀ (i : fin 23), d (-i) = d i := by dec_trivial

@[simp] lemma d_is_sym' : ∀ (i : fin 23), 
![ (1 : ℚ), 1,  1, -1,  1,  1,  1, -1,  1, -1, -1, -1, -1, -1, -1,  1, -1,  1,  1,  1, -1,  1,  1] (-i) = 
![ (1 : ℚ), 1,  1, -1,  1,  1,  1, -1,  1, -1, -1, -1, -1, -1, -1,  1, -1,  1,  1,  1, -1,  1,  1]   i := 
by convert d_is_sym

@[simp] lemma A_is_sym : Aᵀ = A :=  
by rw [←is_sym, cir_is_sym_ext_iff]; exact a_is_sym
@[simp] lemma B_is_sym : Bᵀ = B :=  
by rw [←is_sym, cir_is_sym_ext_iff]; exact b_is_sym
@[simp] lemma C_is_sym : Cᵀ = C :=  
by rw [←is_sym, cir_is_sym_ext_iff]; exact c_is_sym
@[simp] lemma D_is_sym : Dᵀ = D :=  
by rw [←is_sym, cir_is_sym_ext_iff]; exact d_is_sym

def i : matrix (fin 4) (fin 4) ℚ := 
![![0, 1, 0, 0],
  ![-1, 0, 0, 0],
  ![0, 0, 0, -1],
  ![0, 0, 1, 0]]

def j : matrix (fin 4) (fin 4) ℚ := 
![![0, 0, 1, 0],
  ![0, 0, 0, 1],
  ![-1, 0, 0, 0],
  ![0, -1, 0, 0]]

def k: matrix (fin 4) (fin 4) ℚ := 
![![0, 0, 0, 1], 
  ![0, 0, -1, 0], 
  ![0, 1, 0, 0], 
  ![-1, 0, 0, 0]]

@[simp] lemma i_is_skewsym : iᵀ = - i := by dec_trivial
@[simp] lemma j_is_skewsym : jᵀ = - j := by dec_trivial
@[simp] lemma k_is_skewsym : kᵀ = - k := by dec_trivial

@[simp] lemma i_mul_i : (i ⬝ i) = -1 := by simp [i]; dec_trivial
@[simp] lemma j_mul_j : (j ⬝ j) = -1 := by simp [j]; dec_trivial
@[simp] lemma k_mul_k : (k ⬝ k) = -1 := by simp [k]; dec_trivial
@[simp] lemma i_mul_j : (i ⬝ j) = k := by simp [i, j, k]; dec_trivial
@[simp] lemma i_mul_k : (i ⬝ k) = -j := by simp [i, j, k]; dec_trivial
@[simp] lemma j_mul_i : (j ⬝ i) = -k := by simp [i, j, k]; dec_trivial
@[simp] lemma k_mul_i : (k ⬝ i) = j := by simp [i, j, k]; dec_trivial
@[simp] lemma j_mul_k : (j ⬝ k) = i := by simp [i, j, k]; dec_trivial
@[simp] lemma k_mul_j : (k ⬝ j) = -i := by simp [i, j, k]; dec_trivial

lemma fin_23_shift (f : fin 23 → ℚ) (s : fin 23 → fin 23): 
(λ (j : fin 23), f (s j)) = 
![f (s 0), f (s 1), f (s 2), f (s 3), f (s 4), f (s 5), f (s 6), f (s 7), 
  f (s 8), f (s 9), f (s 10), f (s 11), f (s 12), f (s 13), f (s 14), f (s 15), 
  f (s 16), f (s 17), f (s 18), f (s 19), f (s 20), f (s 21), f (s 22)] :=
by {ext i, fin_cases i, any_goals {simp},}

@[simp] lemma eq_aux₁: 
dot_product (λ (j : fin 23), a (1 - j)) a + 
dot_product (λ (j : fin 23), b (1 - j)) b + 
dot_product (λ (j : fin 23), c (1 - j)) c + 
dot_product (λ (j : fin 23), d (1 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₂: 
dot_product (λ (j : fin 23), a (2 - j)) a + 
dot_product (λ (j : fin 23), b (2 - j)) b + 
dot_product (λ (j : fin 23), c (2 - j)) c + 
dot_product (λ (j : fin 23), d (2 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₃: 
dot_product (λ (j : fin 23), a (3 - j)) a + 
dot_product (λ (j : fin 23), b (3 - j)) b + 
dot_product (λ (j : fin 23), c (3 - j)) c + 
dot_product (λ (j : fin 23), d (3 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₄: 
dot_product (λ (j : fin 23), a (4 - j)) a + 
dot_product (λ (j : fin 23), b (4 - j)) b + 
dot_product (λ (j : fin 23), c (4 - j)) c + 
dot_product (λ (j : fin 23), d (4 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₅: 
dot_product (λ (j : fin 23), a (5 - j)) a + 
dot_product (λ (j : fin 23), b (5 - j)) b + 
dot_product (λ (j : fin 23), c (5 - j)) c + 
dot_product (λ (j : fin 23), d (5 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₆: 
dot_product (λ (j : fin 23), a (6 - j)) a + 
dot_product (λ (j : fin 23), b (6 - j)) b + 
dot_product (λ (j : fin 23), c (6 - j)) c + 
dot_product (λ (j : fin 23), d (6 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₇: 
dot_product (λ (j : fin 23), a (7 - j)) a + 
dot_product (λ (j : fin 23), b (7 - j)) b + 
dot_product (λ (j : fin 23), c (7 - j)) c + 
dot_product (λ (j : fin 23), d (7 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₈: 
dot_product (λ (j : fin 23), a (8 - j)) a + 
dot_product (λ (j : fin 23), b (8 - j)) b + 
dot_product (λ (j : fin 23), c (8 - j)) c + 
dot_product (λ (j : fin 23), d (8 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₉: 
dot_product (λ (j : fin 23), a (9 - j)) a + 
dot_product (λ (j : fin 23), b (9 - j)) b + 
dot_product (λ (j : fin 23), c (9 - j)) c + 
dot_product (λ (j : fin 23), d (9 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₁₀: 
dot_product (λ (j : fin 23), a (10 - j)) a + 
dot_product (λ (j : fin 23), b (10 - j)) b + 
dot_product (λ (j : fin 23), c (10 - j)) c + 
dot_product (λ (j : fin 23), d (10 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₁₁: 
dot_product (λ (j : fin 23), a (11 - j)) a + 
dot_product (λ (j : fin 23), b (11 - j)) b + 
dot_product (λ (j : fin 23), c (11 - j)) c + 
dot_product (λ (j : fin 23), d (11 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₁₂: 
dot_product (λ (j : fin 23), a (12 - j)) a + 
dot_product (λ (j : fin 23), b (12 - j)) b + 
dot_product (λ (j : fin 23), c (12 - j)) c + 
dot_product (λ (j : fin 23), d (12 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₁₃: 
dot_product (λ (j : fin 23), a (13 - j)) a + 
dot_product (λ (j : fin 23), b (13 - j)) b + 
dot_product (λ (j : fin 23), c (13 - j)) c + 
dot_product (λ (j : fin 23), d (13 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₁₄: 
dot_product (λ (j : fin 23), a (14 - j)) a + 
dot_product (λ (j : fin 23), b (14 - j)) b + 
dot_product (λ (j : fin 23), c (14 - j)) c + 
dot_product (λ (j : fin 23), d (14 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₁₅: 
dot_product (λ (j : fin 23), a (15 - j)) a + 
dot_product (λ (j : fin 23), b (15 - j)) b + 
dot_product (λ (j : fin 23), c (15 - j)) c + 
dot_product (λ (j : fin 23), d (15 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₁₆: 
dot_product (λ (j : fin 23), a (16 - j)) a + 
dot_product (λ (j : fin 23), b (16 - j)) b + 
dot_product (λ (j : fin 23), c (16 - j)) c + 
dot_product (λ (j : fin 23), d (16 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₁₇: 
dot_product (λ (j : fin 23), a (17 - j)) a + 
dot_product (λ (j : fin 23), b (17 - j)) b + 
dot_product (λ (j : fin 23), c (17 - j)) c + 
dot_product (λ (j : fin 23), d (17 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₁₈: 
dot_product (λ (j : fin 23), a (18 - j)) a + 
dot_product (λ (j : fin 23), b (18 - j)) b + 
dot_product (λ (j : fin 23), c (18 - j)) c + 
dot_product (λ (j : fin 23), d (18 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₁₉: 
dot_product (λ (j : fin 23), a (19 - j)) a + 
dot_product (λ (j : fin 23), b (19 - j)) b + 
dot_product (λ (j : fin 23), c (19 - j)) c + 
dot_product (λ (j : fin 23), d (19 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₂₀: 
dot_product (λ (j : fin 23), a (20 - j)) a + 
dot_product (λ (j : fin 23), b (20 - j)) b + 
dot_product (λ (j : fin 23), c (20 - j)) c + 
dot_product (λ (j : fin 23), d (20 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₂₁: 
dot_product (λ (j : fin 23), a (21 - j)) a + 
dot_product (λ (j : fin 23), b (21 - j)) b + 
dot_product (λ (j : fin 23), c (21 - j)) c + 
dot_product (λ (j : fin 23), d (21 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₂₂: 
dot_product (λ (j : fin 23), a (22 - j)) a + 
dot_product (λ (j : fin 23), b (22 - j)) b + 
dot_product (λ (j : fin 23), c (22 - j)) c + 
dot_product (λ (j : fin 23), d (22 - j)) d = 0 :=
by {simp only [fin_23_shift, a, b ,c ,d], norm_num}

@[simp] lemma eq_aux₀: 
dot_product (λ (j : fin 23), a (0 - j)) a + 
dot_product (λ (j : fin 23), b (0 - j)) b + 
dot_product (λ (j : fin 23), c (0 - j)) c + 
dot_product (λ (j : fin 23), d (0 - j)) d = 92 :=
by {unfold a b c d, norm_num}

lemma equality : 
A ⬝ A + B ⬝ B + C ⬝ C + D ⬝ D = (92 : ℚ) • (1 : matrix (fin 23) (fin 23) ℚ) := 
begin
  admit,
  simp [cir_mul, cir_add, one_eq_cir, smul_cir],
  congr' 1,
  ext i, 
  simp [mul_vec, cir],
  fin_cases i,
  exact eq_aux₀,
  exact eq_aux₁,
  exact eq_aux₂,
  exact eq_aux₃,
  exact eq_aux₄,
  exact eq_aux₅,
  exact eq_aux₆,
  exact eq_aux₇,
  exact eq_aux₈,
  exact eq_aux₉,
  exact eq_aux₁₀,
  exact eq_aux₁₁,
  exact eq_aux₁₂,
  exact eq_aux₁₃,
  exact eq_aux₁₄,
  exact eq_aux₁₅,
  exact eq_aux₁₆,
  exact eq_aux₁₇,
  exact eq_aux₁₈,
  exact eq_aux₁₉,
  exact eq_aux₂₀,
  exact eq_aux₂₁,
  exact eq_aux₂₂,
end
end H_92

open H_92

def H_92 := A ⊗ 1 + B ⊗ i + C ⊗ j + D ⊗ k

lemma H_92.one_or_neg_one : ∀ i j, (H_92 i j) = 1 ∨ (H_92 i j) = -1 := 
begin
  rintros ⟨c, a⟩ ⟨d, b⟩,
  simp [H_92, Kronecker],
  fin_cases a,
  any_goals {fin_cases b},
  any_goals {norm_num [one_apply, i, j, k]},
end

lemma H_92_mul_transpose_self_is_diagonal : (H_92 ⬝ H_92ᵀ).is_diagonal :=
begin
  simp [H_92, K_transpose, matrix.mul_add, matrix.add_mul, K_mul, 
  cir_mul_comm _ a, cir_mul_comm c b, cir_mul_comm d b, cir_mul_comm d c],
  have : 
  (cir a ⬝ cir a)⊗1 + -(cir a ⬝ cir b)⊗i + -(cir a ⬝ cir c)⊗j + -(cir a ⬝ cir d)⊗k + 
  ((cir a ⬝ cir b)⊗i + (cir b ⬝ cir b)⊗1 + -(cir b ⬝ cir c)⊗k + (cir b ⬝ cir d)⊗j) + 
  ((cir a ⬝ cir c)⊗j + (cir b ⬝ cir c)⊗k + (cir c ⬝ cir c)⊗1 + -(cir c ⬝ cir d)⊗i) + 
  ((cir a ⬝ cir d)⊗k + -(cir b ⬝ cir d)⊗j + (cir c ⬝ cir d)⊗i + (cir d ⬝ cir d)⊗1) = 
  (cir a ⬝ cir a)⊗1 + (cir b ⬝ cir b)⊗1 + (cir c ⬝ cir c)⊗1 + (cir d ⬝ cir d)⊗1 :=
  by abel,
  rw this, clear this,
  simp [←add_K, equality],
end

@[instance]
theorem Hadamard_matrix.H_92 : Hadamard_matrix H_92 :=
⟨H_92.one_or_neg_one, mul_tranpose_is_diagonal_iff_has_orthogonal_rows.1 H_92_mul_transpose_self_is_diagonal⟩

end order_92
/- ## end order 92-/

/- ## order -/
section order
open matrix Hadamard_matrix

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
    {simp [set.disjoint_iff_inter_eq_empty], ext, simp, intros, linarith},
  have d₁₃: disjoint J₁ J₃, 
    {simp [set.disjoint_iff_inter_eq_empty], ext, simp, intros a b c d, exact c a},
  have d₁₄: disjoint J₁ J₄, 
    {simp [set.disjoint_iff_inter_eq_empty], ext, simp, intros a b c d, exact c a},
  have d₂₃: disjoint J₂ J₃, 
    {simp [set.disjoint_iff_inter_eq_empty], ext, simp, intros a b c d, exact c a},
  have d₂₄: disjoint J₂ J₄, 
    {simp [set.disjoint_iff_inter_eq_empty], ext, simp, intros a b c d, exact c a},
  have d₃₄: disjoint J₃ J₄, 
    {simp [set.disjoint_iff_inter_eq_empty], ext, simp, intros a b c d, 
    have : H i₁ x = H i₂ x, {linarith}, exact c this},
  have u₁₂: J₁.union J₂ = matched H i₁ i₂, 
    {ext, simp [J₁, J₂, matched, set.union], tauto},
  have u₁₃: J₁.union J₃ = matched H i₁ i₃, 
    {ext, simp [J₁, J₃, matched, set.union], by_cases g : H i₁ x = H i₂ x; simp [g]},
  have u₁₄: J₁.union J₄ = matched H i₂ i₃, 
    {ext, simp [J₁, J₄, matched, set.union], tauto},
  have u₂₃: J₂.union J₃ = mismatched H i₂ i₃, 
    { ext, simp [J₂, J₃, mismatched, set.union], 
      by_cases g₁ : H i₂ x = H i₃ x; simp [g₁], 
      by_cases g₂ : H i₁ x = H i₂ x; simp [g₁, g₂],
      exact entry_eq_entry_of (ne.symm g₂) g₁ },
  have u₂₄: J₂.union J₄ = mismatched H i₁ i₃, 
    { ext, simp [J₂, J₄, mismatched, set.union], 
      by_cases g₁ : H i₁ x = H i₂ x; simp [g₁],
      split, {rintros g₂ g₃, exact g₁ (g₃.trans g₂.symm)},
      intros g₂, 
      exact entry_eq_entry_of g₁ g₂ },
  have u₃₄: J₃.union J₄ = mismatched H i₁ i₂,
    { ext, simp [J₃, J₄, matched, set.union],
      split; try {tauto},
      intros g₁, 
      by_cases g₂ : H i₁ x = H i₃ x,
      { left, exact ⟨g₁, g₂⟩ },
      { right, exact ⟨g₁, entry_eq_entry_of g₁ g₂⟩ } },
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
