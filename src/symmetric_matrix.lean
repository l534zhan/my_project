/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Lu-Ming Zhang.
-/
import set_finset_fintype
import matrix_basic

/-!
# Symmetric matrices

This file contains basic results about symmetric matrices.
See `matrix_basic.lean` for the definition of symmetric matrices. 

## Tags

sym, symmetric, matrix
-/

namespace matrix

open_locale matrix 

variables {α I J R : Type*} [fintype I] [fintype J] 

lemma is_sym.eq {A : matrix I I α} (h : A.is_sym) : Aᵀ = A := h

lemma is_sym.ext_iff {A : matrix I I α} : A.is_sym ↔ ∀ i j, Aᵀ i j = A i j :=
by rw [is_sym, matrix.ext_iff]

lemma is_sym.ext_iff' {A : matrix I I α} : A.is_sym ↔ ∀ i j, A j i = A i j :=
is_sym.ext_iff

lemma is_sym.apply {A : matrix I I α} (h : A.is_sym) (i j : I) : Aᵀ i j = A i j := 
is_sym.ext_iff.1 h i j

lemma is_sym.apply' {A : matrix I I α} (h : A.is_sym) (i j : I) : A j i = A i j := 
is_sym.apply h i j

lemma is_sym.ext {A : matrix I I α} : (∀ i j, Aᵀ i j = A i j) → A.is_sym := 
is_sym.ext_iff.2

lemma is_sym.ext' {A : matrix I I α} : (∀ i j, Aᵀ i j = A i j) → A.is_sym := 
is_sym.ext

/-- A block matrix `A.from_blocks B C D` is symmetric, if `A` and `D` are symmetric and `Bᵀ = C`. -/
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

/-- `A ⬝ Aᵀ` is symmertric. -/
lemma mul_transpose_self_is_sym [comm_semiring α] (A : matrix I I α) : 
(A ⬝ Aᵀ).is_sym :=
by simp [matrix.is_sym, transpose_mul]

/-- The identity matrix is symmetric. -/
@[simp] lemma is_sym_of_one [decidable_eq I] [has_zero α] [has_one α] : 
(1 : matrix I I α).is_sym := by {ext, simp}

/-- The negtive identity matrix is symmetric. -/
@[simp] lemma is_sym_of_neg_one [decidable_eq I] [has_zero α] [has_one α] [has_neg α] : 
(-1 : matrix I I α).is_sym := by {ext, simp}

/-- The identity matrix multiplied by any scalar `k` is symmetric. -/
@[simp] lemma is_sym_of_smul_one
[decidable_eq I] [monoid R] [add_monoid α] [has_one α] [distrib_mul_action R α] (k : R) : 
(k • (1 : matrix I I α)).is_sym := 
by { ext, simp [is_sym_of_one.apply'] }

/-- If a block matrix `A.from_blocks B C D` is symmetric,-/
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

end matrix