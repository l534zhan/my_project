import set_finset_fintype
import matrix_basic

namespace matrix

variables {α I J R : Type*}
variables [fintype I] [fintype J] 
open_locale matrix 

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

@[simp] lemma is_sym_of_one [decidable_eq I] [has_zero α] [has_one α] : 
(1 : matrix I I α).is_sym := by {ext, simp}

lemma is_sym_of_one' [decidable_eq I] [has_zero α] [has_one α] (i j : I): 
(1 : matrix I I α) i j = (1 : matrix I I α) j i :=
by { have h := congr_fun (congr_fun (@is_sym_of_one α _ _ _ _ _) i) j, 
     rw [transpose_apply] at h,
     exact h.symm }

@[simp] lemma is_sym_of_neg_one [decidable_eq I] [has_zero α] [has_one α] [has_neg α] : 
(-1 : matrix I I α).is_sym := by {ext, simp}

@[simp] lemma is_sym_of_smul_one
[decidable_eq I] [monoid R] [add_monoid α] [has_one α] [distrib_mul_action R α] (k : R) : 
(k • (1 : matrix I I α)).is_sym := 
by { ext, simp, rw [is_sym_of_one' j i] }

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