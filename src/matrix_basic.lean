import linear_algebra.matrix.trace
import linear_algebra.matrix.to_lin
import linear_algebra.matrix.nonsingular_inverse
import data.complex.basic

variables {α β γ I J K L M N: Type*}
variables {R : Type*}
variables [fintype I] [fintype J] [fintype K] [fintype L] [fintype M] [fintype N]

/- ## reindex and coercion -/
instance prod_assoc : has_coe ((α × β) × γ) (α × β × γ) := ⟨λ ⟨⟨a,b⟩,c⟩, ⟨a,b,c⟩⟩
instance matrix.prod_assoc : has_coe (matrix (I × J × K) (L × M × N) α) (matrix ((I × J) × K) ((L × M) × N) α):=
⟨λ M ⟨⟨a,b⟩,c⟩ ⟨⟨d,e⟩,f⟩, M ⟨a,b,c⟩ ⟨d,e,f⟩⟩
def matrix.reindex_prod_assoc : matrix ((I × J) × K) ((L × M) × N) α ≃ matrix (I × J × K) (L × M × N) α :=
matrix.reindex (equiv.prod_assoc _ _ _) (equiv.prod_assoc _ _ _)
def matrix.reindex_prod_comm_fst : matrix I (J × K) α ≃ matrix I (K × J) α :=
matrix.reindex (equiv.refl _) (equiv.prod_comm _ _)
def matrix.reindex_prod_comm_snd : matrix (I × J) K α ≃ matrix (J × I) K α :=
matrix.reindex (equiv.prod_comm _ _) (equiv.refl _)
def matrix.reindex_prod_comm : matrix (I × J) (K × L) α ≃ matrix (J × I) (L × K) α :=
matrix.reindex (equiv.prod_comm _ _) (equiv.prod_comm _ _)
/- ## end reindex and coercion -/

/- ## perm matrix -/
def equiv.perm.to_matrix [decidable_eq I] (α) [has_zero α] [has_one α] (σ : equiv.perm I) : matrix I I α
| i j := if σ i = j then 1 else 0

lemma equiv.perm.to_matrix_eq_to_prequiv_to_matrix [decidable_eq I] [has_zero α] [has_one α] (σ : equiv.perm I) :
(σ.to_pequiv.to_matrix : matrix I I α)= σ.to_matrix α:=
by ext i j; simp [pequiv.to_matrix, equiv.perm.to_matrix,equiv.to_pequiv]
/- ## end perm matrix -/
----------------------------------------------------------------------------------

namespace matrix
open_locale matrix big_operators
open complex

/- ## one -/
section one
variables [mul_one_class α] [add_comm_monoid α] [non_assoc_semiring β]

open_locale big_operators

def vec_one [has_one α] : I → α := λ x, 1

@[simp] lemma dot_product_one (v : I → α) : dot_product v vec_one = ∑ i, v i :=
by simp [dot_product, vec_one]

@[simp] lemma dot_product_one' (v : I → α) : dot_product v (λ i, 1) = ∑ i, v i :=
by simp [dot_product]

@[simp] lemma one_dot_product (v : I → α) : dot_product vec_one v = ∑ i, v i :=
by simp [dot_product, vec_one]

@[simp] lemma one_dot_product' (v : I → α) : dot_product (λ i, 1 : I → α) v = ∑ i, v i :=
by simp [dot_product]

lemma one_dot_one_eq_card : dot_product (vec_one : I → α) vec_one = fintype.card I :=
by simp [dot_product, vec_one, fintype.card]

lemma one_dot_one_eq_card' : dot_product (λ i, 1 : I → α) (λ i, 1) = fintype.card I :=
by simp [dot_product, fintype.card]

@[simp] lemma mul_vector_one (A : matrix I J β) :
mul_vec A vec_one = λ i, ∑ j, A i j :=
by ext; simp [mul_vec, vec_one, dot_product]

@[simp] lemma mul_vector_one' (A : matrix I J β) :
mul_vec A (λ i, 1) = λ i, ∑ j, A i j :=
by ext; simp [mul_vec, dot_product]

@[simp] lemma vector_one_mul (A : matrix I J β) :
vec_mul vec_one A = λ j, ∑ i, A i j :=
by ext; simp [vec_mul, vec_one, dot_product]

@[simp] lemma vector_one_mul' (A : matrix I J β) :
vec_mul (λ j, 1 : I → β) A = λ j, ∑ i, A i j :=
by ext; simp [vec_mul, dot_product]

end one

section all_one_matrix

def all_one [has_one α]: matrix I J α := λ i, 1

def row_sum [add_comm_monoid α] (A : matrix I J α) (i : I) := ∑ j, A i j

def col_sum [add_comm_monoid α] (A : matrix I J α) (j : J) := ∑ i, A i j

lemma col_one_mul_row_one [non_assoc_semiring α] : 
col (1 : I → α) ⬝ row (1 : I → α) = all_one :=
by ext; simp [matrix.mul, all_one]

lemma row_one_mul_col_one [non_assoc_semiring α] : 
row (1 : I → α) ⬝ col (1 : I → α) = fintype.card I • 1 :=
by {ext, simp [mul_apply, one_apply], congr,}

end all_one_matrix

/- ## end one -/

/- ## trace section -/
section trace
def tr [add_comm_monoid α] (A : matrix I I α) : α := ∑ i : I, A i i
lemma trace_eq_tr [semiring β] [add_comm_monoid α] [module β α] (A : matrix I I α)
: trace I β α A = tr A := rfl
end trace
/- ## end trace -/

/- ## conjugate transpose and symmetric -/
section conjugate_transpose

@[simp] lemma star_vec [has_star α] (v : I → α) (i : I) : star v i = star (v i) := rfl

/-
def conj_transpose [has_star α] (M : matrix I J α) : matrix J I α
| x y := star (M y x)

localized "postfix `ᴴ`:1500 := matrix.conj_transpose" in matrix

lemma conj_transpose_eq_star_of_square_matrix [decidable_eq I] [semiring α] [star_ring α] (M : matrix I I α) :
Mᴴ = star M := rfl

lemma trans_col_eq_row (A : matrix I J α) (i : I) : (λ j, Aᵀ j i) = A i :=
by simp [transpose]

lemma trans_row_eq_col (A : matrix I J α) (j : J) : Aᵀ j = (λ i, A i j):=
by ext; simp [transpose]
-/

def is_sym (A : matrix I I α) : Prop := Aᵀ = A

lemma is_sym.eq {A : matrix I I α} (h : A.is_sym) : Aᵀ = A := h

lemma is_sym.ext_iff {A : matrix I I α} : A.is_sym ↔ ∀ i j, Aᵀ i j = A i j :=
by rw [is_sym, matrix.ext_iff]

lemma is_sym.apply {A : matrix I I α} (h : A.is_sym) (i j : I) : 
Aᵀ i j = A i j := is_sym.ext_iff.1 h i j

lemma is_sym.ext {A : matrix I I α} : 
(∀ i j, Aᵀ i j = A i j) → A.is_sym := is_sym.ext_iff.2

def is_skewsym [has_neg α] (A : matrix I I α) : Prop := -Aᵀ = A

def is_Hermitian [has_star α] (A : matrix I I α) : Prop := Aᴴ = A

end conjugate_transpose
/- ## end conjugate transpose and symmetric-/

/- ## definite section -/
section definite
open_locale complex_order
protected def is_pos_def (M : matrix I I ℂ):=
M.is_Hermitian ∧ ∀ v : I → ℂ, v ≠ 0 → 0 < dot_product v (M.mul_vec v)
protected def is_pos_semidef (M : matrix I I ℂ):=
M.is_Hermitian∧ ∀ v : I → ℂ, 0 ≤ dot_product v (M.mul_vec v)
protected def is_neg_def (M : matrix I I ℂ):=
M.is_Hermitian ∧ ∀ v : I → ℂ, v ≠ 0 → dot_product v (M.mul_vec v) < 0
protected def is_neg_semidef (M : matrix I I ℂ):=
M.is_Hermitian ∧ ∀ v : I → ℂ, dot_product v (M.mul_vec v) ≤ 0
end definite
/- ## end definite -/

/- ## matrix rank section  -/
section rank
variables [decidable_eq J] [field α]
protected noncomputable
def rank (A : matrix I J α) := rank A.to_lin'
end rank
/- ## end matrix rank -/

/- ## orthogonal section  -/
section orthogonal
variable [decidable_eq I]
open_locale matrix
protected def is_ortho (A : matrix I I ℝ) : Prop := Aᵀ ⬝ A = 1
protected def is_uni (A : matrix I I ℂ) : Prop := Aᴴ ⬝ A = 1
lemma is_ortho_left_right (A : matrix I I ℝ) : A.is_ortho ↔ A ⬝ Aᵀ = 1 :=
⟨nonsing_inv_right_left, nonsing_inv_left_right⟩
lemma is_uni_left_right (A : matrix I I ℂ) : A.is_uni ↔ A ⬝ Aᴴ = 1 :=
⟨nonsing_inv_right_left, nonsing_inv_left_right⟩
lemma is_ortho_iff_orthonormal_cols (A : matrix I I ℝ) :
matrix.is_ortho A ↔ ∀ j₁ j₂, dot_product (λ i, A i j₁) (λ i, A i j₂) = ite (j₁ = j₂) 1 0 :=
begin
  simp [matrix.is_ortho,matrix.mul,has_one.one, diagonal],
  split,
  { intros h j₁ j₂,
    exact congr_fun (congr_fun h j₁) j₂,
  },
  { intros h, ext, apply h _ _},
end
lemma is_ortho_iff_orthonormal_row (A : matrix I I ℝ) :
matrix.is_ortho A ↔ ∀ i₁ i₂, dot_product (A i₁) (A i₂) = ite (i₁ = i₂) 1 0 :=
begin
  rw is_ortho_left_right,
  simp [matrix.is_ortho,matrix.mul,has_one.one, diagonal],
  split,
  { intros h i₁ i₂,
    exact congr_fun (congr_fun h i₁) i₂,
  },
  { intros h, ext, apply h _ _},
end
end orthogonal
/- ## end orthogonal -/

/- ## permutation matrix -/
section perm
open equiv
section defns
variables [decidable_eq I] [has_zero α] [has_one α]

protected def is_perm (P : matrix I I α) : Prop :=
∃ σ : equiv.perm I, P = perm.to_matrix α σ
protected def is_perfect_shuffle (P : matrix I I α) : Prop :=
∃ σ : equiv.perm I, (P = perm.to_matrix α σ ∧ ∀ i : I, σ i ≠ i)
protected def is_perm' (P : matrix I I α) : Prop :=
(∀ i, ∃! j, ∀ j', ite (j' = j) (P i j' = 1) (P i j' = 0)) ∧
(∀ j, ∃! i, ∀ i', ite (i' = i) (P i' j = 1) (P i' j = 0))

lemma is_perm_of_is_perfect_shuffle (P : matrix I I α) : P.is_perfect_shuffle → P.is_perm :=
by {intro h, rcases h with ⟨σ, rfl, h2⟩, use σ}

--lemma is_perm_of_is_perm' {P : matrix I I α} (h : P.is_perm'): P.is_perm :=
--sorry

--lemma is_perm'_of_is_perm {P : matrix I I α} (h : P.is_perm): P.is_perm' :=
--sorry

--lemma is_perm_iff_is_perm' (P : matrix I I α) : P.is_perm ↔ P.is_perm' :=
--⟨is_perm'_of_is_perm, is_perm_of_is_perm'⟩

def std := {v : I → α| ∃! (i : I), ∀ j : I, ite (j = i) (v j = 1) (v j = 0)}

end defns

/-
lemma bij_on_std_of_is_perm [non_assoc_semiring α] [decidable_eq I] (P : matrix I I α) (h : P.is_perm) :
set.bij_on (λ v, P.mul_vec v) std std :=
begin
  rcases h with ⟨σ, rfl⟩,
  split,
  {
    intros v hv,
    simp [std, perm.to_matrix, mul_vec, dot_product] at *,
    rcases hv with ⟨i, ⟨h1, h2⟩⟩,
    use σ.inv_fun i,
    sorry
  },
  sorry
end
-/

end perm
/- ## end permutation -/



/- ## matrix similarity section  -/
section similarity
variables [comm_ring α] [decidable_eq I]

def similar_to (A B : matrix I I α) := ∃ (P : matrix I I α), is_unit P.det ∧ B = P⁻¹ ⬝ A ⬝ P

def similar_to' (A B : matrix I I α) := ∃ (P : matrix I I α), is_unit P ∧ B = P⁻¹ ⬝ A ⬝ P

def perm_similar_to (A B : matrix I I α) := ∃ (P : matrix I I α), P.is_perm ∧ B = P⁻¹ ⬝ A ⬝ P

localized "notation `∼`:50 := similar_to" in matrix
localized "notation `∼ₚ`:50 := perm_similar_to" in matrix

lemma similar_to_iff_similar_to' (A B : matrix I I α) : similar_to A B ↔ similar_to' A B :=
⟨ by {rintros ⟨P ,h1, h2⟩, rw ←is_unit_iff_is_unit_det at h1, use⟨P ,h1, h2⟩},
  by {rintros ⟨P ,h1, h2⟩, rw is_unit_iff_is_unit_det at h1, use⟨P ,h1, h2⟩} ⟩

end similarity
/- ## end matrix similarity -/

/- ## others -/
lemma eq_of_empty [c: is_empty I] (M N: matrix I I α) : M = N := 
by {ext, exfalso, apply is_empty_iff.mp c i}

lemma dot_product_block' [has_mul α] [add_comm_monoid α] (v w : I ⊕ J → α) : 
dot_product v w = ∑ i, v (sum.inl i) * w (sum.inl i) + ∑ j, v (sum.inr j) * w (sum.inr j) :=
begin
  rw [dot_product, ←fintype.sum_sum_elim],
  congr, 
  ext (i | j); simp 
end

lemma dot_product_block [has_mul α] [add_comm_monoid α] (v w : I ⊕ J → α) : 
dot_product v w = dot_product (λ i, v (sum.inl i))  (λ i, w (sum.inl i)) + dot_product (λ j, v (sum.inr j))  (λ j, w (sum.inr j)) :=
by simp [dot_product, dot_product_block']
/- ## end others -/

end matrix