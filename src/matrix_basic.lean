/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Lu-Ming Zhang.
-/
import linear_algebra.matrix.trace
import linear_algebra.matrix.to_lin
import linear_algebra.matrix.nonsingular_inverse
import data.complex.basic

/-!
This file supplements things about `matrix`, that are current missing in mathlib, 
in particular those that will be used for the implementation of the Kronecker product and the constructions of Hadamard matrices.

## Main definitions

Here only lists main definitions that are used for the implementation of the Kronecker product and Hadamard matrices.
- `matrix.all_one`: the matrix whose entries are all `1`s.
- `matrix.is_sym`: a Proposition. Matrix `A` is symmetric `A.is_sym` means `Aᵀ = A`.
-/

variables {α β γ I J K L M N: Type*}
variables {R : Type*}
variables [fintype I] [fintype J] [fintype K] [fintype L] [fintype M] [fintype N]

/- ## reindex and coercion -/
instance prod_assoc : has_coe ((α × β) × γ) (α × β × γ) := ⟨λ ⟨⟨a,b⟩,c⟩, ⟨a,b,c⟩⟩
instance matrix.prod_assoc : has_coe (matrix (I × J × K) (L × M × N) α) (matrix ((I × J) × K) ((L × M) × N) α):=
⟨λ M ⟨⟨a,b⟩,c⟩ ⟨⟨d,e⟩,f⟩, M ⟨a,b,c⟩ ⟨d,e,f⟩⟩
/-- `matrix.reindex_prod_assoc` constructs a natural equivalence between `matrix ((I × J) × K) ((L × M) × N) α` and `matrix (I × J × K) (L × M × N) α`. -/
def matrix.reindex_prod_assoc : matrix ((I × J) × K) ((L × M) × N) α ≃ matrix (I × J × K) (L × M × N) α :=
matrix.reindex (equiv.prod_assoc _ _ _) (equiv.prod_assoc _ _ _)
/-- `matrix.reindex_prod_comm_fst` constructs a natural equivalence between `matrix I (J × K) α` and `matrix I (K × J) α`. -/
def matrix.reindex_prod_comm_fst : matrix I (J × K) α ≃ matrix I (K × J) α :=
matrix.reindex (equiv.refl _) (equiv.prod_comm _ _)
/-- `matrix.reindex_prod_comm_snd` constructs a natural equivalence between `matrix (I × J) K α` and `matrix (J × I) K α`. -/
def matrix.reindex_prod_comm_snd : matrix (I × J) K α ≃ matrix (J × I) K α :=
matrix.reindex (equiv.prod_comm _ _) (equiv.refl _)
/-- `matrix.reindex_prod_comm` constructs a natural equivalence between `matrix (I × J) (K × L) α` and `matrix (J × I) (L × K) α`. -/
def matrix.reindex_prod_comm : matrix (I × J) (K × L) α ≃ matrix (J × I) (L × K) α :=
matrix.reindex (equiv.prod_comm _ _) (equiv.prod_comm _ _)
/- ## end reindex and coercion -/

/- ## perm matrix -/
/-- `equiv.perm.to_matrix σ` is the permutation matrix given by a permutation `σ : equiv.perm I` on the index tpye `I`. -/
def equiv.perm.to_matrix [decidable_eq I] (α) [has_zero α] [has_one α] (σ : equiv.perm I) : matrix I I α
| i j := if σ i = j then 1 else 0

/-- Proves `(σ.to_pequiv.to_matrix : matrix I I α)= σ.to_matrix α`. -/
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

@[simp] lemma dot_product_one (v : I → α) : dot_product v 1 = ∑ i, v i :=
by simp [dot_product]

@[simp] lemma dot_product_one' (v : I → α) : dot_product v (λ i, 1) = ∑ i, v i :=
by simp [dot_product]

@[simp] lemma one_dot_product (v : I → α) : dot_product 1 v = ∑ i, v i :=
by simp [dot_product]

@[simp] lemma one_dot_product' (v : I → α) : dot_product (λ i, 1 : I → α) v = ∑ i, v i :=
by simp [dot_product]

lemma one_dot_one_eq_card : dot_product (1 : I → α) 1 = fintype.card I :=
by simp [dot_product, fintype.card]

lemma one_dot_one_eq_card' : dot_product (λ i, 1 : I → α) (λ i, 1) = fintype.card I :=
by simp [dot_product, fintype.card]

@[simp] lemma mul_vector_one (A : matrix I J β) :
mul_vec A 1 = λ i, ∑ j, A i j :=
by ext; simp [mul_vec, dot_product]

@[simp] lemma mul_vector_one' (A : matrix I J β) :
mul_vec A (λ i, 1) = λ i, ∑ j, A i j :=
by ext; simp [mul_vec, dot_product]

@[simp] lemma vector_one_mul (A : matrix I J β) :
vec_mul 1 A = λ j, ∑ i, A i j :=
by ext; simp [vec_mul, dot_product]

@[simp] lemma vector_one_mul' (A : matrix I J β) :
vec_mul (λ j, 1 : I → β) A = λ j, ∑ i, A i j :=
by ext; simp [vec_mul, dot_product]

end one

section all_one_matrix

/-- `matrix.all_one` is the matrix whose entries are all `1`s. -/
def all_one [has_one α]: matrix I J α := λ i, 1

/-- `matrix.row sum A i` is the sum of entries of the row indexed by `i` of matrix `A`. -/
def row_sum [add_comm_monoid α] (A : matrix I J α) (i : I) := ∑ j, A i j

/-- `matrix.col_sum A j` is the sum of entries of the column indexed by `j` of matrix `A`. -/
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
/-- The "trace" of a matrix.
    A different version of "trace" is defined in `trace.lean` as `matrix.trace`.
    One advantage of `matrix.tr` is that this definition is more elementary,
    which only requires α to be a `add_comm_monoid`; whilst `matrix.trace` requires
    `[semiring β] [add_comm_monoid α] [module β α]`.
    The equivalence can be easily established when `α` is indeed a `β-module`.
    Another advantage is that `matrix.tr` is more convenient for users to explore lemmas/theorems
    involving "trace" from a combinatorial aspect.-/
def tr [add_comm_monoid α] (A : matrix I I α) : α := ∑ i : I, A i i

/-- Establishes that `matrix.trace` is equivalent to `matrix.tr`. -/
lemma trace_eq_tr [semiring β] [add_comm_monoid α] [module β α] (A : matrix I I α)
: trace I β α A = tr A := rfl
end trace
/- ## end trace -/

/- ## conjugate transpose and symmetric -/
section conjugate_transpose

@[simp] lemma star_vec [has_star α] (v : I → α) (i : I) : star v i = star (v i) := rfl

lemma trans_col_eq_row (A : matrix I J α) (i : I) : (λ j, Aᵀ j i) = A i :=
by simp [transpose]

lemma trans_row_eq_col (A : matrix I J α) (j : J) : Aᵀ j = (λ i, A i j):=
by ext; simp [transpose]

lemma eq_of_transpose_eq {A B : matrix I J α} : Aᵀ = Bᵀ → A = B :=
begin
  intros h, ext i j,
  have h':= congr_fun (congr_fun h j) i,
  simp [transpose] at h',
  assumption
end

/-

/-- The conjugate transpose of a matrix defined in term of `star`. -/
def conj_transpose [has_star α] (M : matrix I J α) : matrix J I α
| x y := star (M y x)

localized "postfix `ᴴ`:1500 := matrix.conj_transpose" in matrix

@[simp] lemma conj_transpose_apply [has_star α] (M : matrix m n α) (i j) :
  M.conj_transpose j i = star (M i j) := rfl

@[simp] lemma conj_transpose_conj_transpose [has_involutive_star α] (M : matrix m n α) :
  Mᴴᴴ = M :=
by ext; simp

@[simp] lemma conj_transpose_zero [semiring α] [star_ring α] : (0 : matrix m n α)ᴴ = 0 :=
by ext i j; simp

@[simp] lemma conj_transpose_one [decidable_eq n] [semiring α] [star_ring α]:
  (1 : matrix n n α)ᴴ = 1 :=
by simp [conj_transpose]

@[simp] lemma conj_transpose_add
[semiring α] [star_ring α] (M : matrix m n α) (N : matrix m n α) :
  (M + N)ᴴ = Mᴴ + Nᴴ  := by ext i j; simp

@[simp] lemma conj_transpose_sub [ring α] [star_ring α] (M : matrix m n α) (N : matrix m n α) :
  (M - N)ᴴ = Mᴴ - Nᴴ  := by ext i j; simp

@[simp] lemma conj_transpose_smul [comm_monoid α] [star_monoid α] (c : α) (M : matrix m n α) :
  (c • M)ᴴ = (star c) • Mᴴ :=
by ext i j; simp [mul_comm]

@[simp] lemma conj_transpose_mul [semiring α] [star_ring α] (M : matrix m n α) (N : matrix n l α) :
  (M ⬝ N)ᴴ = Nᴴ ⬝ Mᴴ  := by ext i j; simp [mul_apply]

@[simp] lemma conj_transpose_neg [ring α] [star_ring α] (M : matrix m n α) :
  (- M)ᴴ = - Mᴴ  := by ext i j; simp

section star

/-- When `α` has a star operation, square matrices `matrix n n α` have a star
operation equal to `matrix.conj_transpose`. -/
instance [has_star α] : has_star (matrix n n α) := {star := conj_transpose}

lemma star_eq_conj_transpose [has_star α] (M : matrix m m α) : star M = Mᴴ := rfl

@[simp] lemma star_apply [has_star α] (M : matrix n n α) (i j) :
  (star M) i j = star (M j i) := rfl

instance [has_involutive_star α] : has_involutive_star (matrix n n α) :=
{ star_involutive := conj_transpose_conj_transpose }

/-- When `α` is a `*`-(semi)ring, `matrix.has_star` is also a `*`-(semi)ring. -/
instance [decidable_eq n] [semiring α] [star_ring α] : star_ring (matrix n n α) :=
{ star_add := conj_transpose_add,
  star_mul := conj_transpose_mul, }

/-- A version of `star_mul` for `⬝` instead of `*`. -/
lemma star_mul [semiring α] [star_ring α] (M N : matrix n n α) :
  star (M ⬝ N) = star N ⬝ star M := conj_transpose_mul _ _

end star

@[simp] lemma conj_transpose_minor
  [has_star α] (A : matrix m n α) (r_reindex : l → m) (c_reindex : o → n) :
  (A.minor r_reindex c_reindex)ᴴ = Aᴴ.minor c_reindex r_reindex :=
ext $ λ _ _, rfl

lemma conj_transpose_reindex [has_star α] (eₘ : m ≃ l) (eₙ : n ≃ o) (M : matrix m n α) :
  (reindex eₘ eₙ M)ᴴ = (reindex eₙ eₘ Mᴴ) :=
rfl

-/

/-- Proposition `matrix.is_sym`. `A.is_sym` means `Aᵀ = A`. -/
def is_sym (A : matrix I I α) : Prop := Aᵀ = A

/-- Proposition `matrix.is_skewsym`. `A.is_skewsym` means `-Aᵀ = A` if `[has_neg α]`. -/
def is_skewsym [has_neg α] (A : matrix I I α) : Prop := -Aᵀ = A

/-- Proposition `matrix.is_Hermitian`. `A.is_Hermitian` means `Aᴴ = A` if `[has_star α]`. -/
def is_Hermitian [has_star α] (A : matrix I I α) : Prop := Aᴴ = A

end conjugate_transpose
/- ## end conjugate transpose and symmetric-/

/- ## definite section -/
section definite
open_locale complex_order

/-- Proposition `matrix.is_pos_def`. -/
def is_pos_def (M : matrix I I ℂ):= M.is_Hermitian ∧ ∀ v : I → ℂ, v ≠ 0 → 0 < dot_product v (M.mul_vec v)

/-- Proposition `matrix.is_pos_semidef`. -/
def is_pos_semidef (M : matrix I I ℂ):= M.is_Hermitian∧ ∀ v : I → ℂ, 0 ≤ dot_product v (M.mul_vec v)

/-- Proposition `matrix.is_neg_def`. -/
def is_neg_def (M : matrix I I ℂ):= M.is_Hermitian ∧ ∀ v : I → ℂ, v ≠ 0 → dot_product v (M.mul_vec v) < 0

/-- Proposition `matrix.is_neg_semidef`. -/
def is_neg_semidef (M : matrix I I ℂ):= M.is_Hermitian ∧ ∀ v : I → ℂ, dot_product v (M.mul_vec v) ≤ 0

end definite
/- ## end definite -/

/- ## matrix rank section  -/
section rank
variables [decidable_eq J] [field α]
/-- `rank A` is the rank of matrix `A`, defined as the rank of `A.to_lin'`. -/
noncomputable def rank (A : matrix I J α) := rank A.to_lin'
end rank
/- ## end matrix rank -/

/- ## orthogonal section  -/
section orthogonal
variable [decidable_eq I]

/-- Proposition `matrix.is_ortho`. 
    `A` is orthogonal `A.is_ortho` means `Aᵀ ⬝ A = 1`, where `A : matrix I I ℝ`. -/
def is_ortho (A : matrix I I ℝ) : Prop := Aᵀ ⬝ A = 1

/-- Proposition `matrix.is_uni`. 
    `A` is unitray `A.is_uni` means `Aᴴ ⬝ A = 1`, where `A : matrix I I ℂ`. -/
def is_uni (A : matrix I I ℂ) : Prop := Aᴴ ⬝ A = 1

lemma is_ortho_left_right (A : matrix I I ℝ) : A.is_ortho ↔ A ⬝ Aᵀ = 1 := ⟨nonsing_inv_right_left, nonsing_inv_left_right⟩

lemma is_uni_left_right (A : matrix I I ℂ) : A.is_uni ↔ A ⬝ Aᴴ = 1 := ⟨nonsing_inv_right_left, nonsing_inv_left_right⟩

/-- A matrix `A` is orthogonal iff `A` has orthonormal columns. -/
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

/-- A matrix `A` is orthogonal iff `A` has orthonormal rows. -/
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

variables [decidable_eq I] [has_zero α] [has_one α]

/-- `P.is_perm` if matrix `P` is induced by some permutation `σ`. -/
def is_perm (P : matrix I I α) : Prop :=
∃ σ : equiv.perm I, P = perm.to_matrix α σ

/-- `P.is_perfect_shuffle` if matrix `P` is induced by some permutation `σ`, and `∀ i : I, σ i ≠ i`. -/
def is_perfect_shuffle (P : matrix I I α) : Prop :=
∃ σ : equiv.perm I, (P = perm.to_matrix α σ ∧ ∀ i : I, σ i ≠ i)

/-- A permutation matrix is a perfect shuffle. -/
lemma is_perm_of_is_perfect_shuffle (P : matrix I I α) : P.is_perfect_shuffle → P.is_perm :=
by {intro h, rcases h with ⟨σ, rfl, h2⟩, use σ}

/-
def is_perm' (P : matrix I I α) : Prop :=
(∀ i, ∃! j, ∀ j', ite (j' = j) (P i j' = 1) (P i j' = 0)) ∧
(∀ j, ∃! i, ∀ i', ite (i' = i) (P i' j = 1) (P i' j = 0))
lemma is_perm_of_is_perm' {P : matrix I I α} (h : P.is_perm'): P.is_perm := sorry
lemma is_perm'_of_is_perm {P : matrix I I α} (h : P.is_perm): P.is_perm' := sorry
lemma is_perm_iff_is_perm' (P : matrix I I α) : P.is_perm ↔ P.is_perm' := ⟨is_perm'_of_is_perm, is_perm_of_is_perm'⟩

def std := {v : I → α| ∃! (i : I), ∀ j : I, ite (j = i) (v j = 1) (v j = 0)}

lemma bij_on_std_of_is_perm {α} [non_assoc_semiring α] [decidable_eq I] (P : matrix I I α) (h : P.is_perm) :
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

/-- `matrix.similar_to` defines the proposition that matrix `A` is similar to `B`, denoted as `A ∼ B`. -/
def similar_to (A B : matrix I I α) := ∃ (P : matrix I I α), is_unit P.det ∧ B = P⁻¹ ⬝ A ⬝ P
localized "notation `∼`:50 := similar_to" in matrix

/-- An equivalent definition of matrix similarity `similar_to`. -/
def similar_to' (A B : matrix I I α) := ∃ (P : matrix I I α), is_unit P ∧ B = P⁻¹ ⬝ A ⬝ P

/-- `matrix.perm_similar_to` defines the proposition that matrix `A` is permutation-similar to `B`, denoted as `A ∼ₚ B`.-/
def perm_similar_to (A B : matrix I I α) := ∃ (P : matrix I I α), P.is_perm ∧ B = P⁻¹ ⬝ A ⬝ P
localized "notation `∼ₚ`:50 := perm_similar_to" in matrix

/-- Proves the equivalence of `matrix.similar_to` and `matrix.similar_to'`. -/
lemma similar_to_iff_similar_to' (A B : matrix I I α) : similar_to A B ↔ similar_to' A B :=
⟨ by {rintros ⟨P ,h1, h2⟩, rw ←is_unit_iff_is_unit_det at h1, use⟨P ,h1, h2⟩},
  by {rintros ⟨P ,h1, h2⟩, rw is_unit_iff_is_unit_det at h1, use⟨P ,h1, h2⟩} ⟩

end similarity
/- ## end matrix similarity -/

/- ## others -/
/-- Two empties matrices are equal. -/
lemma eq_of_empty [c: is_empty I] (M N: matrix I I α) : M = N := 
by {ext, exfalso, apply is_empty_iff.mp c i}

/-- `matrix.dot_product_block'` splits the `dot_product` of two block vectors into a sum of two `Σ` sums. -/
lemma dot_product_block' [has_mul α] [add_comm_monoid α] (v w : I ⊕ J → α) : 
dot_product v w = ∑ i, v (sum.inl i) * w (sum.inl i) + ∑ j, v (sum.inr j) * w (sum.inr j) :=
begin
  rw [dot_product, ←fintype.sum_sum_elim],
  congr, 
  ext (i | j); simp 
end

/-- `matrix.dot_product_block` splits the `dot_product` of two block vectors into a sum of two `dot_product` . -/
lemma dot_product_block [has_mul α] [add_comm_monoid α] (v w : I ⊕ J → α) : 
dot_product v w = dot_product (λ i, v (sum.inl i))  (λ i, w (sum.inl i)) + dot_product (λ j, v (sum.inr j))  (λ j, w (sum.inr j)) :=
by simp [dot_product, dot_product_block']
/- ## end others -/

end matrix