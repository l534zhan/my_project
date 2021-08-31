/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Lu-Ming Zhang.
-/
import tactic.gptf
import finite_field
import circulant_matrix
import diagonal_matrix

/-!
# Hadamard matrices.

This file defines the Hadamard matrices `matrix.Hadamard_matrix` as a type class, 
and implements Sylvester's constructions and Payley's constructions of Hadamard matrices and a Hadamard matrix of order 92.
In particular, this files implements at least one Hadamard matrix of oder `n` for every possible `n ≤ 100`.

## References

*  <https://en.wikipedia.org/wiki/Hadamard_matrix>
*  <https://en.wikipedia.org/wiki/Paley_construction>
* [F.J. MacWilliams, *2 Nonlinear codes, Hadamard matrices, designs and the Golay code*][macwilliams1977]
* [L. D. Baumert, *Discovery of an Hadamard matrix of order 92*][baumert1962]
  

## Tags

Hadamard matrix, Hadamard
-/

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

-- The original proof is due to Eric Wieser, given in <https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/card>.
private lemma pick_elements (h : fintype.card I ≥ 3) : 
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

section set

/-- `matched H i₁ i₂ ∪ mismatched H i₁ i₂ = I` as sets -/
@[simp] lemma match_union_mismatch (H : matrix I I ℚ) (i₁ i₂ : I) :
matched H i₁ i₂ ∪ mismatched H i₁ i₂ = @set.univ I :=
set.union_compl' _ 

/-- a variant of `match_union_mismatch` -/
@[simp] lemma match_union_mismatch' (H : matrix I I ℚ) (i₁ i₂ : I) :
{j : I | H i₁ j = H i₂ j} ∪ {j : I | ¬H i₁ j = H i₂ j} = @set.univ I :=
begin
  have h := match_union_mismatch H i₁ i₂,
  simp* at *,
end

/-- `matched H i₁ i₂ ∪ mismatched H i₁ i₂ = I` as finsets -/
lemma match_union_mismatch_finset [decidable_eq I] (H : matrix I I ℚ) (i₁ i₂ : I) :
(matched H i₁ i₂).to_finset ∪ (mismatched H i₁ i₂).to_finset = @univ I _:=
begin
  simp only [←set.to_finset_union, univ_eq_set_univ_to_finset],
  congr, simp
end

/-- `matched H i₁ i₂` and `mismatched H i₁ i₂` are disjoint as sets -/
@[simp] lemma disjoint_match_mismatch (H : matrix I I ℚ) (i₁ i₂ : I) :
disjoint (matched H i₁ i₂) (mismatched H i₁ i₂) :=
set.disjoint_of_compl' _

/-- `matched H i₁ i₂` and `mismatched H i₁ i₂` are disjoint as finsets -/
@[simp] lemma match_disjoint_mismatch_finset [decidable_eq I] (H : matrix I I ℚ) (i₁ i₂ : I) :
disjoint (matched H i₁ i₂).to_finset (mismatched H i₁ i₂).to_finset :=
by simp [set.to_finset_disjoint_iff]

/-- `|I| = |H.matched i₁ i₂| + |H.mismatched i₁ i₂|`
    for any rows `i₁` `i₂` of a matrix `H` with index type `I`-/
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
@[simp] lemma entry_mul_of_ne {i j k l : I} (h : H i j ≠ H k l):
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
  ext,
  simp [transpose, matrix.mul],
  by_cases i = j; simp [*, mul_one] at *,
end

lemma det_sq [decidable_eq I] :
(det H)^2 = (card I)^(card I) :=
calc (det H)^2 = (det H) * (det H) : by ring
           ... = det (H ⬝ Hᵀ) : by simp
           ... = det ((card I : ℚ) • (1 : matrix I I ℚ)) : by rw mul_tanspose
           ... = (card I : ℚ)^(card I) : by simp

lemma right_invertible [decidable_eq I] : 
H ⬝ ((1 / (card I : ℚ)) • Hᵀ) = 1 :=
begin
  have h := mul_tanspose H,
  by_cases hI : card I = 0,
  {exact @eq_of_empty _ _ _ (card_eq_zero_iff.mp hI) _ _}, -- the trivial case 
  have hI': (card I : ℚ) ≠ 0, {simp [hI]},
  simp [h, hI'],
end

def invertible [decidable_eq I] : invertible H :=
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

/-- The dot product of a column with another column equals `0`. -/
@[simp] lemma col_dot_product_other [decidable_eq I] {j₁ j₂ : I} (h : j₁ ≠ j₂) :
dot_product (λ i, H i j₁) (λ i, H i j₂) = 0 :=
begin
  have h':= congr_fun (congr_fun (tanspose_mul H) j₁) j₂,
  simp [matrix.mul, transpose, has_one.one, diagonal, h] at h',
  assumption,
end

/-- The dot product of a column with another column equals `0`. -/
@[simp] lemma col_dot_product_other' [decidable_eq I] {j₁ j₂ : I} (h : j₂ ≠ j₁) :
dot_product (λ i, H i j₁) (λ i, H i j₂)= 0 := by simp [ne.symm h]

/-- Hadamard matrix `H` has orthogonal rows-/
@[simp] lemma has_orthogonal_cols [decidable_eq I] :
H.has_orthogonal_cols:=
by intros i j h; simp [h]

/-- `Hᵀ` is a Hadamard matrix suppose `H` is. -/
instance transpose [decidable_eq I] : Hadamard_matrix Hᵀ :=
begin
  refine{..}, {intros, simp[transpose]},
  simp [transpose_has_orthogonal_rows_iff_has_orthogonal_cols]
end

/-- `Hᵀ` is a Hadamard matrix implies `H` is a Hadamard matrix.-/
lemma of_Hadamard_matrix_transpose [decidable_eq I] 
{H : matrix I I ℚ} (h: Hadamard_matrix Hᵀ): 
Hadamard_matrix H :=
by convert Hadamard_matrix.transpose Hᵀ; simp

lemma card_match_eq {i₁ i₂ : I} (h: i₁ ≠ i₂): 
(set.card (matched H i₁ i₂) : ℚ) = ∑ j in (matched H i₁ i₂).to_finset, H i₁ j * H i₂ j :=
begin
  simp [matched],
  have h : ∑ (x : I) in {j : I | H i₁ j = H i₂ j}.to_finset, H i₁ x * H i₂ x 
         = ∑ (x : I) in {j : I | H i₁ j = H i₂ j}.to_finset, 1,
  { apply finset.sum_congr rfl, 
    rintros j hj, 
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
  { apply finset.sum_congr rfl, rintros j hj, simp* at * },
  have h' : ∑ (x : I) in {j : I | H i₁ j ≠ H i₂ j}.to_finset, - (1 : ℚ)
          = - ∑ (x : I) in {j : I | H i₁ j ≠ H i₂ j}.to_finset, (1 : ℚ),
  { simp },
  rw [h, h', ← finset.card_eq_sum_ones_ℚ],
  congr,
end

lemma card_mismatch_eq {i₁ i₂ : I} (h: i₁ ≠ i₂): 
(set.card (mismatched H i₁ i₂) : ℚ) = - ∑ j in (mismatched H i₁ i₂).to_finset, H i₁ j * H i₂ j :=
by {rw [←neg_card_mismatch_eq]; simp* at *}

/-- `|H.matched i₁ i₂| = |H.mismatched i₁ i₂|` as rational numbers if `H` is a Hadamard matrix.-/
lemma card_match_eq_card_mismatch_ℚ [decidable_eq I] {i₁ i₂ : I} (h: i₁ ≠ i₂): 
(set.card (matched H i₁ i₂) : ℚ)= set.card (mismatched H i₁ i₂) :=
begin
  have eq := dot_product_split H i₁ i₂,
  rw [card_match_eq H h, card_mismatch_eq H h],
  simp only [set.to_finset_univ, row_dot_product'_other H h] at eq,
  linarith,
end

/-- `|H.matched i₁ i₂| = |H.mismatched i₁ i₂|` if `H` is a Hadamard matrix.-/
lemma card_match_eq_card_mismatch [decidable_eq I] {i₁ i₂ : I} (h: i₁ ≠ i₂): 
set.card (matched H i₁ i₂) = set.card (mismatched H i₁ i₂) :=
by have h := card_match_eq_card_mismatch_ℚ H h; simp * at *

lemma reindex (f : I ≃ J) (g : I ≃ J): Hadamard_matrix (reindex f g H) :=
begin
  refine {..},
  { simp [minor_apply] },
  intros i₁ i₂ h,
  simp [dot_product, minor_apply],
  rw [fintype.sum_equiv (g.symm) _ (λ x, H (f.symm i₁) x * H (f.symm i₂) x) (λ x, rfl)],
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

def H_2 : matrix (unit ⊕ unit) (unit ⊕ unit) ℚ := 
(1 :matrix unit unit ℚ).from_blocks 1 1 (-1)

instance Hadamard_matrix.H_0 : Hadamard_matrix H_0 :=
⟨by tidy, by tidy⟩

instance Hadamard_matrix.H_1 : Hadamard_matrix H_1 := 
⟨by tidy, by tidy⟩

instance Hadamard_matrix.H_1' : Hadamard_matrix H_1' := 
⟨by tidy, by tidy⟩

instance Hadamard_matrix.H_2 : Hadamard_matrix H_2 := 
⟨ by tidy, 
  λ i₁ i₂ h, by { cases i₁, any_goals {cases i₂}, 
                  any_goals {simp[*, H_2, dot_product, fintype.sum_sum_type] at *} }
⟩

end basic_constr
/- ## end basic constructions-/

/- ## "normalize" constructions-/
section normalize

open matrix Hadamard_matrix

/-- negate row `i` of matrix `A`; `[decidable_eq I]` is required for `update_row` -/
def neg_row [has_neg α] [decidable_eq I] (A : matrix I J α) (i : I) := 
update_row A i (- A i)

/-- negate column `j` of matrix `A`; `[decidable_eq J]` is required for `update_column` -/
def neg_col [has_neg α] [decidable_eq J] (A : matrix I J α) (j : J) := 
update_column A j (-λ i, A i j)

section neg

/-- Negating row `i` and then column `j` equals negating column `j` first and then row `i`. -/
lemma neg_row_neg_col_comm [has_neg α] [decidable_eq I] [decidable_eq J]
(A : matrix I J α) (i : I) (j : J) :
(A.neg_row i).neg_col j = (A.neg_col j).neg_row i :=
begin
  ext a b,
  simp [neg_row, neg_col, update_column_apply, update_row_apply],
  by_cases a = i,
  any_goals {by_cases b = j},
  any_goals {simp* at *},
end

lemma transpose_neg_row [has_neg α] [decidable_eq I] (A : matrix I J α) (i : I) :
(A.neg_row i)ᵀ = Aᵀ.neg_col i :=
by simp [← update_column_transpose, neg_row, neg_col]

lemma transpose_neg_col [has_neg α] [decidable_eq J] (A : matrix I J α) (j : J) :
(A.neg_col j)ᵀ = Aᵀ.neg_row j :=
by {simp [← update_row_transpose, neg_row, neg_col, trans_row_eq_col]}

lemma neg_row_add [add_comm_group α] [decidable_eq I] 
(A B : matrix I J α) (i : I) :
(A.neg_row i) + (B.neg_row i) = (A + B).neg_row i :=
begin
  ext a b,
  simp [neg_row, neg_col, update_column_apply, update_row_apply],
  by_cases a = i,
  any_goals {simp* at *},
  abel
end

lemma neg_col_add [add_comm_group α] [decidable_eq J] 
(A B : matrix I J α) (j : J) :
(A.neg_col j) + (B.neg_col j) = (A + B).neg_col j :=
begin
  ext a b,
  simp [neg_row, neg_col, update_column_apply, update_row_apply],
  by_cases b = j,
  any_goals {simp* at *},
  abel
end

/-- Negating the same row and column of diagonal matrix `A` equals `A` itself. -/
lemma neg_row_neg_col_eq_self_of_is_diag [add_group α] [decidable_eq I]
{A : matrix I I α} (h : A.is_diagonal) (i : I) :
(A.neg_row i).neg_col i = A :=
begin
  ext a b,
  simp [neg_row, neg_col, update_column_apply, update_row_apply],
  by_cases h₁ : a = i,
  any_goals {by_cases h₂ : b = i},
  any_goals {simp* at *},
  { simp [h.apply_ne' h₂] },
  { simp [h.apply_ne h₁] },
end 

end neg

variables [decidable_eq I] (H : matrix I I ℚ) [Hadamard_matrix H] 

/-- Negating any row `i` of a Hadamard matrix `H` produces another Hadamard matrix. -/
instance Hadamard_matrix.neg_row (i : I) : 
Hadamard_matrix (H.neg_row i) := 
begin
  -- first goal
  refine {..},
  { intros j k,
    simp [neg_row,  update_row_apply],
    by_cases j = i; simp* at * },
  -- second goal
  { intros j k hjk,
    by_cases h1 : j = i, any_goals {by_cases h2 : k = i},
    any_goals {simp [*, neg_row, update_row_apply]},
    tidy }
end

/-- Negating any column `j` of a Hadamard matrix `H` produces another Hadamard matrix. -/
instance Hadamard_matrix.neg_col (j : I) : 
Hadamard_matrix (H.neg_col j) := 
begin
  apply of_Hadamard_matrix_transpose, --changes the goal to `(H.neg_col j)ᵀ.Hadamard_matrix`
  simp [transpose_neg_col, Hadamard_matrix.neg_row] 
  -- `(H.neg_col j)ᵀ = Hᵀ.neg_row j`, in which the RHS has been proved to be a Hadamard matrix.
end

end normalize
/- ## end "normalize" constructions -/


/- ## special cases -/
section special_cases

namespace Hadamard_matrix
variables (H : matrix I I ℚ) [Hadamard_matrix H] 

/-- normalized Hadamard matrix -/
def is_normalized [inhabited I] : Prop :=
H (default I) = 1 ∧ (λ i, H i (default I)) = 1

/-- skew Hadamard matrix -/
def is_skew [decidable_eq I] : Prop :=
Hᵀ + H = 2

/-- regular Hadamard matrix -/
def is_regular : Prop :=
∀ i j, ∑ b, H i b = ∑ a, H a j

variable {H}

lemma is_skew.eq [decidable_eq I] (h : is_skew H) :
Hᵀ + H = 2 := h

@[simp] lemma is_skew.apply_eq 
[decidable_eq I] (h : is_skew H) (i : I) :
H i i + H i i = 2 :=
by replace h:= congr_fun (congr_fun h i) i; simp * at *

@[simp] lemma is_skew.apply_ne 
[decidable_eq I] (h : is_skew H) {i j : I} (hij : i ≠ j) :
H j i + H i j = 0 :=
by replace h:= congr_fun (congr_fun h i) j; simp * at *

lemma is_skew.of_neg_col_row_of_is_skew 
[decidable_eq I] (i : I) (h : Hadamard_matrix.is_skew H) : 
is_skew ((H.neg_row i).neg_col i) :=
begin
  simp [is_skew],
  -- to show ((H.neg_row i).neg_col i)ᵀ + (H.neg_row i).neg_col i = 2
  nth_rewrite 0 [neg_row_neg_col_comm],
  simp [transpose_neg_row, transpose_neg_col, neg_row_add, neg_col_add],
  rw [h.eq],
  convert neg_row_neg_col_eq_self_of_is_diag _ _,
  apply is_diagonal_add; by simp
end


end Hadamard_matrix

end special_cases
/- ## end special cases -/

/- ## Sylvester construction  -/
section Sylvester_constr

def Sylvester_constr₀ (H : matrix I I ℚ) [Hadamard_matrix H] : matrix (I ⊕ I) (I ⊕ I) ℚ := 
H.from_blocks H H (-H)

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

def Sylvester_constr₀' (H : matrix I I ℚ) [Hadamard_matrix H]: 
matrix (I × (unit ⊕ unit)) (I × (unit ⊕ unit)) ℚ := 
H ⊗ H_2

local notation `reindex_map` := equiv.sum_self_equiv_prod_unit_sum_unit

lemma Sylvester_constr₀'_eq_reindex_Sylvester_constr₀ 
(H : matrix I I ℚ) [Hadamard_matrix H] : 
H.Sylvester_constr₀' = reindex reindex_map reindex_map H.Sylvester_constr₀:=
begin
  ext ⟨i, a⟩ ⟨j, b⟩,
  simp [Sylvester_constr₀', Sylvester_constr₀, Kronecker, H_2, from_blocks],
  rcases a with (a | a),
  any_goals {rcases b with (b | b)},
  any_goals {simp [one_apply]},
end

@[instance]
theorem Hadamard_matrix.Sylvester_constr₀' (H : matrix I I ℚ) [Hadamard_matrix H] :
Hadamard_matrix (Sylvester_constr₀' H) := 
begin
  convert Hadamard_matrix.reindex H.Sylvester_constr₀ reindex_map reindex_map,
  exact H.Sylvester_constr₀'_eq_reindex_Sylvester_constr₀,
end

theorem Hadamard_matrix.order_conclusion_1: 
∀ (n : ℕ),  ∃ {I : Type*} [inst : fintype I]
(H : @matrix I I inst inst ℚ) [@Hadamard_matrix I inst H], 
@fintype.card I inst = 2^n := 
begin
  intro n,
  induction n with n ih,
  -- the case 0
  {exact ⟨punit, infer_instance, H_1', infer_instance, by simp⟩},
  -- the case n.succ
  rcases ih with ⟨I, inst, H, h, hI⟩, resetI, -- unfold the IH
  refine ⟨I ⊕ I, infer_instance, H.Sylvester_constr₀, infer_instance, _⟩,
  rw [fintype.card_sum, hI], ring_nf, -- this line proves `card (I ⊕ I) = 2 ^ n.succ`
end

end Sylvester_constr
/- ## end Sylvester construction  -/

/- ## general Sylvester construction  -/
section general_Sylvester_constr

def Sylvester_constr 
(H₁ : matrix I I ℚ) [Hadamard_matrix H₁] (H₂ : matrix J J ℚ) [Hadamard_matrix H₂] : 
matrix (I × J) (I × J) ℚ := H₁ ⊗ H₂

@[instance] theorem Hadamard_matrix.Sylvester_constr'
(H₁ : matrix I I ℚ) [Hadamard_matrix H₁] (H₂ : matrix J J ℚ) [Hadamard_matrix H₂] : 
Hadamard_matrix (H₁ ⊗ H₂) :=
begin
  refine {..},
  -- first goal
  { rintros ⟨i₁, j₁⟩ ⟨i₂, j₂⟩,
    simp [Kronecker], 
    -- the current goal : H₁ i₁ i₂ * H₂ j₁ j₂ = 1 ∨ H₁ i₁ i₂ * H₂ j₁ j₂ = -1
    obtain (h | h) := one_or_neg_one H₁ i₁ i₂; -- prove by cases : H₁ i₁ i₂ = 1 or -1
    simp [h] },
  -- second goal
  rintros ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h,
  simp [dot_product_Kronecker_row_split],
  -- by cases j₁ = j₂; simp* closes the case j₁ ≠ j₂
  by_cases hi: i₁ = i₂, any_goals {simp*},
  -- the left case: i₁ = i₂
  by_cases hi: j₁ = j₂, any_goals {simp* at *},
end

/-- wraps `Hadamard_matrix.Sylvester_constr'`-/
@[instance] theorem Hadamard_matrix.Sylvester_constr
(H₁ : matrix I I ℚ) [Hadamard_matrix H₁] (H₂ : matrix J J ℚ) [Hadamard_matrix H₂] : 
Hadamard_matrix (Sylvester_constr H₁ H₂) :=
Hadamard_matrix.Sylvester_constr' H₁ H₂

theorem {u v} Hadamard_matrix.order_conclusion_2 {I : Type u} {J : Type v} [fintype I] [fintype J]
(H₁ : matrix I I ℚ) [Hadamard_matrix H₁] (H₂ : matrix J J ℚ) [Hadamard_matrix H₂] :
∃ {K : Type max u v} [inst : fintype K] (H : @matrix K K inst inst ℚ),
by exactI Hadamard_matrix H ∧ card K = card I * card J :=
⟨(I × J), _, Sylvester_constr H₁ H₂, ⟨infer_instance, card_prod I J⟩⟩

end general_Sylvester_constr
/- ## end general Sylvester construction  -/


/- ## Paley construction -/
section Paley_construction

variables {F : Type*} [field F] [fintype F] [decidable_eq F] {p : ℕ} [char_p F p]
local notation `q` := fintype.card F 

open finite_field

/- ## Jacobsthal_matrix -/

variable (F) -- `F` is an explicit variable to `Jacobsthal_matrix`.

@[reducible] def Jacobsthal_matrix : matrix F F ℚ := λ a b, χ (a-b)
-- We will use `J` to denote `Jacobsthal_matrix F` in annotations.

namespace Jacobsthal_matrix

/-- `J` is the circulant matrix `cir χ`. -/
lemma eq_cir : (Jacobsthal_matrix F) = cir χ := rfl

variable {F} -- this line makes `F` an implicit variable to the following lemmas/defs

@[simp] lemma diag_entry_eq_zero (i : F) : (Jacobsthal_matrix F) i i = 0 :=
by simp [Jacobsthal_matrix]

@[simp] lemma non_diag_entry_eq {i j : F} (h : i ≠ j): 
(Jacobsthal_matrix F) i j = 1 ∨ (Jacobsthal_matrix F) i j = -1 :=
by simp [*, Jacobsthal_matrix]

@[simp] lemma non_diag_entry_Euare_eq {i j : F} (h : i ≠ j): 
(Jacobsthal_matrix F) i j * (Jacobsthal_matrix F) i j = 1 :=
by obtain (h₁ | h₂) := Jacobsthal_matrix.non_diag_entry_eq h; simp*

@[simp] lemma entry_Euare_eq (i j : F) : 
(Jacobsthal_matrix F) i j * (Jacobsthal_matrix F) i j = ite (i=j) 0 1 :=
by by_cases i=j; simp * at *

-- JJᵀ = qI − 𝟙
lemma mul_transpose_self (hp : p ≠ 2) : 
(Jacobsthal_matrix F) ⬝ (Jacobsthal_matrix F)ᵀ = (q : ℚ) • 1 - 𝟙 := 
begin
  ext i j,
  simp [mul_apply, all_one, Jacobsthal_matrix, one_apply],
  -- the current goal is 
  -- ∑ (x : F), χ (i - x) * χ (j - x) = ite (i = j) q 0 - 1
  by_cases i = j, 
  -- when i = j
  { simp[h, sum_ite, filter_ne, fintype.card],
    rw [@card_erase_of_mem' _ _ j (@finset.univ F _) _];
    simp },
  -- when i ≠ j
  simp [quad_char.sum_mul h hp, h],
end

-- J ⬝ 𝟙 = 0
@[simp] lemma mul_all_one (hp : p ≠ 2) : 
(Jacobsthal_matrix F) ⬝ (𝟙 : matrix F F ℚ) = 0 := 
begin
  ext i j,
  simp [all_one, Jacobsthal_matrix, mul_apply],
  -- the current goal: ∑ (x : F), χ (i - x) = 0
  exact quad_char.sum_eq_zero_reindex_1 hp,
end

-- 𝟙 ⬝ J = 0
@[simp] lemma all_one_mul (hp : p ≠ 2) : 
(𝟙 : matrix F F ℚ) ⬝ (Jacobsthal_matrix F) = 0 := 
begin
  ext i j,
  simp [all_one, Jacobsthal_matrix, mul_apply],
  exact quad_char.sum_eq_zero_reindex_2 hp,
end

-- J ⬝ col 1 = 0
@[simp] lemma mul_col_one (hp : p ≠ 2) : 
Jacobsthal_matrix F ⬝ col 1 = 0 := 
begin
  ext,
  simp [Jacobsthal_matrix, mul_apply],
  -- the current goal: ∑ (x : F), χ (i - x) = 0
  exact quad_char.sum_eq_zero_reindex_1 hp,
end

-- row 1 ⬝ Jᵀ = 0
@[simp] lemma row_one_mul_transpose (hp : p ≠ 2) : 
row 1 ⬝ (Jacobsthal_matrix F)ᵀ = 0 := 
begin
  apply eq_of_transpose_eq,
  simp,
  exact mul_col_one hp
end

variables {F} 

lemma is_sym_of (h : q ≡ 1 [MOD 4]) : 
(Jacobsthal_matrix F).is_sym := 
by ext; simp [Jacobsthal_matrix, quad_char_is_sym_of' h i j]

lemma is_skewsym_of (h : q ≡ 3 [MOD 4]) : 
(Jacobsthal_matrix F).is_skewsym := 
by ext; simp [Jacobsthal_matrix, quad_char_is_skewsym_of' h i j]

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

/-- if `q ≡ 3 [MOD 4]`, `Paley_constr_1 F` is a Hadamard matrix. -/
@[instance]
theorem Hadamard_matrix.Paley_constr_1 (h : q ≡ 3 [MOD 4]): 
Hadamard_matrix (Paley_constr_1 F) := 
begin
  obtain ⟨p, inst⟩ := char_p.exists F, -- derive the char p of F
  resetI, -- resets the instance cache
  obtain ⟨hp, h'⟩ := char_ne_two_of' p h, -- prove p ≠ 2
  refine {..},
  -- first goal
  {
    rintros (i | i)  (j | j),
    all_goals {simp [Paley_constr_1, one_apply, Jacobsthal_matrix]},
    {by_cases i = j; simp*}
  },
  -- second goal
  rw ←mul_tranpose_is_diagonal_iff_has_orthogonal_rows,   -- changes the goal to prove J ⬝ Jᵀ is diagonal
  simp [Paley_constr_1, from_blocks_transpose, from_blocks_multiply, 
        matrix.add_mul, matrix.mul_add, col_one_mul_row_one],
  rw [mul_col_one hp, row_one_mul_transpose hp, mul_transpose_self hp], 
  simp,
  convert is_diagnoal_of_block_conditions ⟨is_diagonal_of_unit _, _, rfl, rfl⟩,
  -- to show the lower right corner block is diagonal
  {rw [is_skesym_of' h, add_assoc, add_comm, add_assoc], simp},
  any_goals {assumption},
end

open Hadamard_matrix

/-- if `q ≡ 3 [MOD 4]`, `Paley_constr_1 F` is a skew Hadamard matrix. -/
theorem Hadamard_matrix.Paley_constr_1_is_skew (h : q ≡ 3 [MOD 4]): 
@is_skew _ _ (Paley_constr_1 F) (Hadamard_matrix.Paley_constr_1 h) _ := 
begin
  simp [is_skew, Paley_constr_1, from_blocks_transpose, 
        from_blocks_add, is_skesym_of' h],
  have : 1 + -Jacobsthal_matrix F + (1 + Jacobsthal_matrix F) = 1 + 1, 
  {noncomm_ring},
  rw [this], clear this,
  ext (a | i) (b | j),
  swap 3, rintro (b | j),
  any_goals {simp [one_apply, from_blocks, bit0]},
end

/- ## end Paley_constr_1 -/

/- ## Paley_constr_2 -/

/- # Paley_constr_2_helper -/
namespace Paley_constr_2

variable (F)

def C : matrix (unit ⊕ unit) (unit ⊕ unit) ℚ :=
(1 : matrix unit unit ℚ).from_blocks (-1) (-1) (-1)

/-- C is symmetric. -/
@[simp] lemma C_is_sym : C.is_sym :=
is_sym_of_block_conditions ⟨by simp, by simp, by simp⟩

def D : matrix (unit ⊕ unit) (unit ⊕ unit) ℚ :=
(1 : matrix unit unit ℚ).from_blocks 1 1 (-1)

/-- D is symmetric. -/
@[simp] lemma D_is_sym : D.is_sym :=
is_sym_of_block_conditions ⟨by simp, by simp, by simp⟩

/-- C ⬝ D = - D ⬝ C -/
lemma C_mul_D_anticomm : C ⬝ D = - D ⬝ C :=
begin
  ext (i | i) (j | j),
  swap 3, rintros (j | j),
  any_goals {simp [from_blocks_multiply, C, D]}
end

def E : matrix (unit ⊕ unit) (unit ⊕ unit) ℚ :=
(2 : matrix unit unit ℚ).from_blocks 0 0 2

/-- E is diagonal. -/
@[simp] lemma E_is_diagonal : E.is_diagonal := 
is_diagnoal_of_block_conditions ⟨by simp, by simp, rfl, rfl⟩

/-- C ⬝ C = E -/
@[simp] lemma C_mul_self : C ⬝ C = E := 
by simp [from_blocks_transpose, from_blocks_multiply, E, C]; congr' 1

/-- C ⬝ Cᵀ = E -/
@[simp] lemma C_mul_transpose_self : C ⬝ Cᵀ = E := 
by simp [C_is_sym.eq]

/-- D ⬝ D = E -/ 
@[simp] lemma D_mul_self : D ⬝ D = E := 
by simp [from_blocks_transpose, from_blocks_multiply, E, D]; congr' 1

/-- D ⬝ Dᵀ = E -/
@[simp] lemma D_mul_transpose_self : D ⬝ Dᵀ = E := 
by simp [D_is_sym.eq]

def replace (A : matrix I J ℚ) : 
matrix (I × (unit ⊕ unit)) (J × (unit ⊕ unit)) ℚ :=
λ ⟨i, a⟩ ⟨j, b⟩, 
if (A i j = 0)
then C a b 
else (A i j) • D a b

variable (F)

/-- `(replace A)ᵀ = replace (Aᵀ)` -/
lemma transpose_replace (A : matrix I J ℚ) :
(replace A)ᵀ = replace (Aᵀ) := 
begin
  ext ⟨i, a⟩ ⟨j, b⟩,
  simp [transpose_apply, replace],
  congr' 1,
  {rw [C_is_sym.apply']},
  {rw [D_is_sym.apply']},
end

variable (F)

/-- `replace A` is a symmetric matrix if `A` is. -/
lemma replace_is_sym_of {A : matrix I I ℚ} (h : A.is_sym) : 
(replace A).is_sym:= 
begin
  ext ⟨i, a⟩ ⟨j, b⟩,
  simp [transpose_replace, replace, h.apply', C_is_sym.apply', D_is_sym.apply']
end

/-- `replace 0 = I ⊗ C` -/
lemma replace_zero :
replace (0 : matrix unit unit ℚ) = 1 ⊗ C :=
begin
  ext ⟨a, b⟩ ⟨c, d⟩,
  simp [replace, Kronecker, one_apply]
end

/-- `replace A = A ⊗ D` for a matrix `A` with no `0` entries. -/
lemma replace_matrix_of_no_zero_entry
{A : matrix I J ℚ} (h : ∀ i j, A i j ≠ 0) : replace A = A ⊗ D := 
begin
  ext ⟨i, a⟩ ⟨j, b⟩,
  simp [replace, Kronecker],
  intro g,
  exact absurd g (h i j)
end

/-- In particular, we can apply `replace_matrix_of_no_zero_entry` to `- row 1`. -/
lemma replace_neg_row_one : 
replace (-row 1 : matrix unit F ℚ) = (-row 1) ⊗ D :=
replace_matrix_of_no_zero_entry (λ a i, by simp [row])

/-- `replace J = J ⊗ D + I ⊗ C` -/
lemma replace_Jacobsthal : 
replace (Jacobsthal_matrix F) = 
(Jacobsthal_matrix F) ⊗ D + 1 ⊗ C:= 
begin
  ext ⟨i, a⟩ ⟨j, b⟩,
  by_cases i = j, --inspect the diagonal and non-diagonal entries respectively 
  any_goals {simp [h, Jacobsthal_matrix, replace, Kronecker]},
end

/-- `(replace 0) ⬝ (replace 0)ᵀ= I ⊗ E` -/
@[simp] lemma replace_zero_mul_transpose_self :
replace (0 : matrix unit unit ℚ) ⬝ (replace (0 : matrix unit unit ℚ))ᵀ = 1 ⊗ E :=
by simp [replace_zero, transpose_K, K_mul]

/-- `(replace A) ⬝ (replace A)ᵀ = (A ⬝ Aᵀ) ⊗ E` -/
@[simp] lemma replace_matrix_of_no_zero_entry_mul_transpose_self 
{A : matrix I J ℚ} (h : ∀ i j, A i j ≠ 0) :   
(replace A) ⬝ (replace A)ᵀ = (A ⬝ Aᵀ) ⊗ E := 
by simp [replace_matrix_of_no_zero_entry h, transpose_K, K_mul]  

variable {F}

lemma replace_Jacobsthal_mul_transpose_self' (h : q ≡ 1 [MOD 4]) : 
replace (Jacobsthal_matrix F) ⬝ (replace (Jacobsthal_matrix F))ᵀ = 
((Jacobsthal_matrix F) ⬝ (Jacobsthal_matrix F)ᵀ + 1) ⊗ E :=
begin
  simp [transpose_replace, (is_sym_of h).eq],
  simp [replace_Jacobsthal, matrix.add_mul, matrix.mul_add,
        K_mul, C_mul_D_anticomm, add_K],
  noncomm_ring
end

/-- enclose `replace_Jacobsthal_mul_transpose_self'` by replacing `J ⬝ Jᵀ` with `qI − 𝟙` -/
@[simp]lemma replace_Jacobsthal_mul_transpose_self (h : q ≡ 1 [MOD 4]) :   
replace (Jacobsthal_matrix F) ⬝ (replace (Jacobsthal_matrix F))ᵀ = 
(((q : ℚ) + 1) • (1 : matrix F F ℚ) - 𝟙) ⊗ E := 
begin
  obtain ⟨p, inst⟩ := char_p.exists F, -- obtains the character p of F
  resetI, -- resets the instance cache
  obtain hp := char_ne_two_of p (or.inl h),  -- hp: p ≠ 2
  simp [replace_Jacobsthal_mul_transpose_self' h, add_smul],
  rw [mul_transpose_self hp],
  congr' 1, noncomm_ring,
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

variable {F}
/-- `Paley_constr_2 F` is a symmetric matrix when `card F ≡ 1 [MOD 4]`. -/
@[simp] 
lemma Paley_constr_2_is_sym (h : q ≡ 1 [MOD 4]) : 
(Paley_constr_2 F).is_sym :=
begin
  convert is_sym_of_block_conditions ⟨_, _, _⟩,
  { simp [replace_zero] }, -- `0` is symmetric
  { apply replace_is_sym_of (is_sym_of h) }, -- `J` is symmetric
  { simp [transpose_replace] } -- `(replace (-row 1))ᵀ = replace (-col 1)`
end

variable (F)
/-- Every entry of `Paley_constr_2 F` equals `1` or `-1`. -/
lemma Paley_constr_2.one_or_neg_one : 
∀ (i j : unit × (unit ⊕ unit) ⊕ F × (unit ⊕ unit)), 
Paley_constr_2 F i j = 1 ∨ Paley_constr_2 F i j = -1 :=
begin
  rintros (⟨a, (u₁|u₂)⟩ | ⟨i, (u₁ | u₂)⟩) (⟨b, (u₃|u₄)⟩ | ⟨j, (u₃ | u₄)⟩),
  all_goals {simp [Paley_constr_2, one_apply, Jacobsthal_matrix, replace, C, D]},
  all_goals {by_cases i = j},
  any_goals {simp [h]},
end

variable {F}

@[instance]
theorem Hadamard_matrix.Paley_constr_2 (h : q ≡ 1 [MOD 4]): 
Hadamard_matrix (Paley_constr_2 F) :=
begin
  refine {..},
  -- the first goal
  { exact Paley_constr_2.one_or_neg_one F },
  -- the second goal
  -- turns the goal to `Paley_constr_2 F ⬝ (Paley_constr_2 F)ᵀ` is diagonal
  rw ←mul_tranpose_is_diagonal_iff_has_orthogonal_rows,
  -- sym : `Paley_constr_2 F ⬝ (Paley_constr_2 F)ᵀ` is symmetric
  have sym := mul_transpose_self_is_sym (Paley_constr_2 F),
  -- The next `simp` turns `Paley_constr_2 F ⬝ (Paley_constr_2 F)ᵀ` into a block form. 
  simp [Paley_constr_2, from_blocks_transpose, from_blocks_multiply] at *,
  convert is_diagnoal_of_sym_block_conditions sym ⟨_, _, _⟩, -- splits into the three goals
  any_goals {clear sym},
  -- to prove the upper left corner block is diagonal.
  { simp [row_one_mul_col_one, ← add_K], 
    apply K_is_diagonal_of; simp },
  -- to prove the lower right corner block is diagonal.
  { simp [h, col_one_mul_row_one, ← add_K], 
    apply smul_is_diagonal_of,
    apply K_is_diagonal_of; simp },
  -- to prove the upper right corner block is `0`.
  { obtain ⟨p, inst⟩ := char_p.exists F, -- obtains the character p of F
    resetI, -- resets the instance cache
    obtain hp := char_ne_two_of p (or.inl h), -- hp: p ≠ 2
    simp [transpose_replace, (is_sym_of h).eq],
    simp [replace_zero, replace_neg_row_one, replace_Jacobsthal,
          matrix.mul_add, K_mul, C_mul_D_anticomm],
    rw [←(is_sym_of h).eq, row_one_mul_transpose hp],
    simp, assumption }
end

/- ## end Paley_constr_2 -/
end Paley_construction
/- ## end Paley construction -/


/- ## order 92-/
section order_92
/-
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
λ i, begin simp, dec_trivial! end -- `dec_trivial!` inspects every entry 
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

/-- `fin_23_shift` normalizes `λ (j : fin 23), f (s j)` in `![]` form,
    where `s : fin 23 → fin 23` is a function shifting indices. -/
lemma fin_23_shift (f : fin 23 → ℚ) (s : fin 23 → fin 23) :
(λ (j : fin 23), f (s j)) = 
![f (s 0), f (s 1), f (s 2), f (s 3), f (s 4), f (s 5), f (s 6), f (s 7), 
  f (s 8), f (s 9), f (s 10), f (s 11), f (s 12), f (s 13), f (s 14), f (s 15), 
  f (s 16), f (s 17), f (s 18), f (s 19), f (s 20), f (s 21), f (s 22)] :=
by {ext i, fin_cases i, any_goals {simp},}


@[simp] lemma eq_aux₀: 
dot_product (λ (j : fin 23), a (0 - j)) a + 
dot_product (λ (j : fin 23), b (0 - j)) b + 
dot_product (λ (j : fin 23), c (0 - j)) c + 
dot_product (λ (j : fin 23), d (0 - j)) d = 92 :=
by {unfold a b c d, norm_num}

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

lemma equality : 
A ⬝ A + B ⬝ B + C ⬝ C + D ⬝ D = (92 : ℚ) • (1 : matrix (fin 23) (fin 23) ℚ) := 
begin
  -- the first `simp` transfers the equation to the form `cir .. = cir ..`
  simp [cir_mul, cir_add, one_eq_cir, smul_cir], 
  -- we then show the two `cir`s consume equal arguments
  congr' 1, 
  -- to show the two vectors are equal
  ext i, 
  simp [mul_vec, cir],
  -- ask lean to inspect the 23 pairs entries one by one
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

/-- Poves every entry of `H_92` is `1` or `-1`. -/
lemma H_92.one_or_neg_one : ∀ i j, (H_92 i j) = 1 ∨ (H_92 i j) = -1 := 
begin
  rintros ⟨c, a⟩ ⟨d, b⟩,
  simp [H_92, Kronecker],
  fin_cases a,
  any_goals {fin_cases b},
  any_goals {norm_num [one_apply, i, j, k]},
end

/-- Proves `H_92 ⬝ H_92ᵀ` is a diagonal matrix. -/
lemma H_92_mul_transpose_self_is_diagonal : (H_92 ⬝ H_92ᵀ).is_diagonal :=
begin
  simp [H_92, transpose_K, matrix.mul_add, matrix.add_mul, K_mul, 
  cir_mul_comm _ a, cir_mul_comm c b, cir_mul_comm d b, cir_mul_comm d c],
  have : 
  (cir a ⬝ cir a)⊗1 + -(cir a ⬝ cir b)⊗i + -(cir a ⬝ cir c)⊗j + -(cir a ⬝ cir d)⊗k + 
  ((cir a ⬝ cir b)⊗i + (cir b ⬝ cir b)⊗1 + -(cir b ⬝ cir c)⊗k + (cir b ⬝ cir d)⊗j) + 
  ((cir a ⬝ cir c)⊗j + (cir b ⬝ cir c)⊗k + (cir c ⬝ cir c)⊗1 + -(cir c ⬝ cir d)⊗i) + 
  ((cir a ⬝ cir d)⊗k + -(cir b ⬝ cir d)⊗j + (cir c ⬝ cir d)⊗i + (cir d ⬝ cir d)⊗1) = 
  (cir a ⬝ cir a)⊗1 + (cir b ⬝ cir b)⊗1 + (cir c ⬝ cir c)⊗1 + (cir d ⬝ cir d)⊗1 :=
  by abel,
  rw this, clear this,
  simp [←add_K, equality], -- uses `equality`
end

@[instance]
theorem Hadamard_matrix.H_92 : Hadamard_matrix H_92 :=
⟨H_92.one_or_neg_one, mul_tranpose_is_diagonal_iff_has_orthogonal_rows.1 H_92_mul_transpose_self_is_diagonal⟩
-/
end order_92
/- ## end order 92-/

/- ## order -/
section order
open matrix Hadamard_matrix

theorem Hadamard_matrix.order_constraint 
[decidable_eq I] (H : matrix I I ℚ) [Hadamard_matrix H] 
: card I ≥ 3 →  4 ∣ card I := 
begin
  intros h, -- h: card I ≥ 3
  -- pick three distinct rows i₁, i₂, i₃
  obtain ⟨i₁, i₂, i₃, ⟨h₁₂, h₁₃, h₂₃⟩⟩:= pick_elements h,
  -- the cardinalities of J₁, J₂, J₃, J₄ are denoted as i, j, k, l in the proof in words
  set J₁ := {j : I | H i₁ j = H i₂ j ∧ H i₂ j = H i₃ j},
  set J₂ := {j : I | H i₁ j = H i₂ j ∧ H i₂ j ≠ H i₃ j},
  set J₃ := {j : I | H i₁ j ≠ H i₂ j ∧ H i₁ j = H i₃ j},
  set J₄ := {j : I | H i₁ j ≠ H i₂ j ∧ H i₂ j = H i₃ j},
  -- dₘₙ proves Jₘ Jₙ are disjoint
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
  -- u₁₂ proves J₁ ∪ J₂ = matched H i₁ i₂
  have u₁₂: J₁.union J₂ = matched H i₁ i₂, 
  {ext, simp [J₁, J₂, matched, set.union], tauto},
  -- u₁₃ proves J₁ ∪ J₃ = matched H i₁ i₃
  have u₁₃: J₁.union J₃ = matched H i₁ i₃, 
  {ext, simp [J₁, J₃, matched, set.union], by_cases g : H i₁ x = H i₂ x; simp [g]},
  -- u₁₄ proves J₁ ∪ J₄ = matched H i₂ i₃
  have u₁₄: J₁.union J₄ = matched H i₂ i₃, 
  {ext, simp [J₁, J₄, matched, set.union], tauto},
  -- u₂₃ proves J₂ ∪ J₃ = mismatched H i₂ i₃
  have u₂₃: J₂.union J₃ = mismatched H i₂ i₃, 
  { ext, simp [J₂, J₃, mismatched, set.union], 
    by_cases g₁ : H i₂ x = H i₃ x; simp [g₁], 
    by_cases g₂ : H i₁ x = H i₂ x; simp [g₁, g₂],
    exact entry_eq_entry_of (ne.symm g₂) g₁ },
  -- u₂₄ proves J₂ ∪ J₄ = mismatched H i₂ i₄
  have u₂₄: J₂.union J₄ = mismatched H i₁ i₃, 
  { ext, simp [J₂, J₄, mismatched, set.union], 
    by_cases g₁ : H i₁ x = H i₂ x; simp [g₁],
    split, {rintros g₂ g₃, exact g₁ (g₃.trans g₂.symm)},
    intros g₂, 
    exact entry_eq_entry_of g₁ g₂ },
 -- u₃₄ proves J₃ ∪ J₄ = mismatched H i₁ i₂
  have u₃₄: J₃.union J₄ = mismatched H i₁ i₂,
  { ext, simp [J₃, J₄, matched, set.union],
    split; try {tauto},
    intros g₁, 
    by_cases g₂ : H i₁ x = H i₃ x,
    { left, exact ⟨g₁, g₂⟩ },
    { right, exact ⟨g₁, entry_eq_entry_of g₁ g₂⟩ } },
  -- eq₁: |H.matched i₁ i₂| = |H.mismatched i₁ i₂|
  have eq₁ := card_match_eq_card_mismatch H h₁₂,
  -- eq₂: |H.matched i₁ i₃| = |H.mismatched i₁ i₃|
  have eq₂ := card_match_eq_card_mismatch H h₁₃,
  -- eq₃: |H.matched i₂ i₃| = |H.mismatched i₂ i₃|
  have eq₃ := card_match_eq_card_mismatch H h₂₃,
  -- eq : |I| = |H.matched i₁ i₂| + |H.mismatched i₁ i₂|
  have eq := card_match_add_card_mismatch H i₁ i₂,
  -- rewrite eq to |I| = |J₁| + |J₂| + |J₃| + |J₄|, and
  -- rewrite eq₁ to |J₁| + |J₂| = |J₃| + |J₄|
  rw [set.card_disjoint_union' d₁₂ u₁₂, set.card_disjoint_union' d₃₄ u₃₄] at eq₁ eq,
  -- rewrite eq₂ to |J₁| + |J₃| = |J₂| + |J₄|
  rw [set.card_disjoint_union' d₁₃ u₁₃, set.card_disjoint_union' d₂₄ u₂₄] at eq₂,
  -- rewrite eq₃ to |J₁| + |J₄| = |J₂| + |J₄|
  rw [set.card_disjoint_union' d₁₄ u₁₄, set.card_disjoint_union' d₂₃ u₂₃] at eq₃,
  -- g₂₁, g₃₁, g₄₁ prove that |J₁| = |J₂| = |J₃| = |J₄|
  have g₂₁ : J₂.card = J₁.card, {linarith},
  have g₃₁ : J₃.card = J₁.card, {linarith},
  have g₄₁ : J₄.card = J₁.card, {linarith},
  -- rewrite eq to |I| = |J₁| + |J₁| + |J₁| + |J₁|
  rw [g₂₁, g₃₁, g₄₁, set.univ_card_eq_fintype_card] at eq,
  use J₁.card,
  simp [eq], noncomm_ring,
end

theorem Hadamard_matrix.Hadamard_conjecture: 
∀ k : ℕ, ∃ (I : Type*) [fintype I], 
by exactI ∃ (H : matrix I I ℚ) [Hadamard_matrix H], 
card I = 4 * k := 
sorry -- Here, `sorry` means if you ask me to prove this conjecture, 
      -- then I have to apologize.

end order
/- ## end order -/

end Hadamard_matrix
/- ## end Hadamard_matrix  -/


end matrix
----------------------------------------------- end of file
