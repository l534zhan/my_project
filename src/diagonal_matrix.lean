import symmetric_matrix
import main1

namespace matrix

variables {α R I J : Type*}
variables [fintype I] [fintype J]
open_locale matrix

def has_orthogonal_rows [has_mul α] [add_comm_monoid α] (A : matrix I J α) : Prop := 
∀ ⦃i₁ i₂⦄, i₁ ≠ i₂ → dot_product (A i₁) (A i₂) = 0

def has_orthogonal_clos [has_mul α] [add_comm_monoid α] (A : matrix I J α) : Prop := 
∀ ⦃i₁ i₂⦄, i₁ ≠ i₂ → dot_product (λ j, A  j i₁) (λ j, A j i₂) = 0

def is_diagonal [has_zero α] (A : matrix I I α) : Prop := ∀ i j, i ≠ j → A i j = 0

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

@[simp] lemma is_diagonal_of_smul_one
[decidable_eq I] [monoid R] [add_monoid α] [has_one α] [distrib_mul_action R α] (k : R) : 
(k • (1 : matrix I I α)).is_diagonal := by {intros i j h, simp *}

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

lemma is_diagnoal_of_sym_block_conditions [has_zero α] 
{A : matrix I I α} {B : matrix I J α} {C : matrix J I α} {D : matrix J J α}
(sym : (A.from_blocks B C D).is_sym) :
(A.is_diagonal) ∧ (D.is_diagonal) ∧ (B = 0) → (A.from_blocks B C D).is_diagonal:=
begin
  rintros h,
  apply is_diagnoal_of_block_conditions,
  refine ⟨h.1, h.2.1, h.2.2, _⟩,
  obtain ⟨g1, g2, g3, g4⟩ := block_conditions_of_is_sym sym,
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
[has_mul α] [add_comm_monoid α] {A : matrix I J α} :
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
[has_mul α] [add_comm_monoid α] {A : matrix I J α} :
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

end matrix