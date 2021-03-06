/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Lu-Ming Zhang.
-/
import data.matrix.notation
import symmetric_matrix

/-!
# Hadamard product and Kronecker product.

This file defines the Hadamard product `matrix.Hadamard` and the Kronecker product `matrix.Kronecker` and
contains basic properties about them.

## Main definitions

- `matrix.Hadamard`: defines the Hadamard product, which is the pointwise product of two matrices of the same size.
- `matrix.Kronecker`: defines the Kronecker product, denoted by `⊗`. 
  For `A : matrix I J α` and `B : matrix K L α`, `A ⊗ B ⟨a, b⟩ ⟨c, d⟩` is defined to be ` (A a c) * (B b d)`.
- `matrix.fin_Kronecker`: the `fin` version of `matrix.Kronecker`, denoted by `⊗ₖ`.
  For `A : matrix (fin m) (fin n) α` and `B : matrix (fin p) (fin q) α`, `A ⊗ₖ B` is of type `matrix (fin (m * p)) (fin (n * q))`.
  The difference from `A ⊗ B` is that each of the index types `fin (m * p)` and `fin (n * q)` of the resulting matrix has a natural order.

## Notation

* `⊙`: the Hadamard product `matrix.Hadamard`;
* `⊗`: the Kronecker product `matrix.Kronecker`;
* `⊗ₖ`: the Kronecker product `fin_Kronecker` of matrices with index types `fin _`.

## References

*  <https://en.wikipedia.org/wiki/Hadamard_product_(matrices)>
*  <https://en.wikipedia.org/wiki/Kronecker_product>

## Tags

Hadamard product, Kronecker product, Hadamard, Kronecker
-/

variables {α β γ I J K L M N: Type*}
variables {R : Type*}
variables {m n p q r s t: ℕ}
variables [fintype I] [fintype J] [fintype K] [fintype L] [fintype M] [fintype N]

namespace matrix
open_locale matrix big_operators
open complex

/- ## Hadamard product  -/
section Hadamard_product

def Hadamard [has_mul α] (A : matrix I J α) (B : matrix I J α) :
matrix I J α :=
λ i j, (A i j) * (B i j)
localized "infix `⊙`:100 := matrix.Hadamard" in matrix -- declares the notation

section basic_properties
variables (A : matrix I J α) (B : matrix I J α) (C : matrix I J α)

/- commutativity -/
lemma Had_comm [comm_semigroup α] : A ⊙ B = B ⊙ A := 
by ext; simp [Hadamard, mul_comm]

/- associativity -/
lemma Had_assoc [semigroup α] : A ⊙ B ⊙ C = A ⊙ (B ⊙ C) :=
by ext; simp [Hadamard, mul_assoc]

/- distributivity -/
section distrib
variables [distrib α]
lemma Had_add : A ⊙ (B + C) = A ⊙ B + A ⊙ C :=
by ext; simp [Hadamard, left_distrib]
lemma add_Had : (B + C) ⊙ A = B ⊙ A + C ⊙ A :=
by ext; simp [Hadamard, right_distrib]
end distrib

/- scalar multiplication -/
section scalar
@[simp] lemma smul_Had 
[has_mul α] [has_scalar R α] [is_scalar_tower R α α] (k : R) : 
(k • A) ⊙ B = k • A ⊙ B :=
by {ext, simp [Hadamard], exact smul_assoc _ (A i j) _}
@[simp] lemma Had_smul 
[has_mul α] [has_scalar R α] [smul_comm_class R α α] (k : R): 
A ⊙ (k • B) = k • A ⊙ B :=
by {ext, simp [Hadamard], exact (smul_comm k (A i j) (B i j)).symm}
end scalar

section zero
variables [mul_zero_class α]
@[simp] lemma Had_zero : A ⊙ (0 : matrix I J α) = 0 :=
by ext; simp [Hadamard]
@[simp] lemma zero_Had : (0 : matrix I J α) ⊙ A = 0 :=
by ext; simp [Hadamard]
end zero

section trace
variables [comm_semiring α] [decidable_eq I] [decidable_eq J]

/--`vᵀ (M₁ ⊙ M₂) w = tr ((diagonal v)ᵀ ⬝ M₁ ⬝ (diagonal w) ⬝ M₂ᵀ)` -/
lemma tr_identity (v : I → α) (w : J → α) (M₁ : matrix I J α) (M₂ : matrix I J α):
dot_product (vec_mul  v  (M₁ ⊙ M₂)) w =
tr ((diagonal v)ᵀ ⬝ M₁ ⬝ (diagonal w) ⬝ M₂ᵀ) :=
begin
  simp [dot_product, vec_mul, Hadamard, finset.sum_mul],
  rw finset.sum_comm,
  apply finset.sum_congr, refl, intros i hi,
  simp [diagonal, transpose, matrix.mul, dot_product],
  apply finset.sum_congr, refl, intros j hj,
  ring,
end

/-- `trace` version of `tr_identity` -/
lemma trace_identity (v : I → α) (w : J → α) (M₁ : matrix I J α) (M₂ : matrix I J α):
dot_product (vec_mul  v  (M₁ ⊙ M₂)) w =
trace I α α ((diagonal v)ᵀ ⬝ M₁ ⬝ (diagonal w) ⬝ M₂ᵀ) :=
by rw [trace_eq_tr, tr_identity]

/-- `∑ (i : I) (j : J), (M₁ ⊙ M₂) i j = tr (M₁ ⬝ M₂ᵀ)` -/
lemma sum_Had_eq_tr_mul (M₁ : matrix I J α) (M₂ : matrix I J α) :
∑ (i : I) (j : J), (M₁ ⊙ M₂) i j = tr (M₁ ⬝ M₂ᵀ) :=
begin
  have h:= tr_identity (λ i, 1 : I → α) (λ i, 1 : J → α) M₁ M₂,
  simp at h,
  rw finset.sum_comm at h,
  assumption,
end

/-- `vᴴ (M₁ ⊙ M₂) w = tr ((diagonal v)ᴴ ⬝ M₁ ⬝ (diagonal w) ⬝ M₂ᵀ)` over `ℂ` -/
lemma tr_identity_over_ℂ 
(v : I → ℂ) (w : J → ℂ) (M₁ : matrix I J ℂ) (M₂ : matrix I J ℂ):
dot_product (vec_mul (star v)  (M₁ ⊙ M₂)) w =
tr ((diagonal v)ᴴ ⬝ M₁ ⬝ (diagonal w) ⬝ M₂ᵀ) :=
begin
  simp [dot_product, vec_mul, Hadamard, finset.sum_mul],
  rw finset.sum_comm,
  apply finset.sum_congr, refl, intros i hi,
  simp [diagonal, transpose, conj_transpose, matrix.mul, dot_product, star, has_star.star],
  apply finset.sum_congr, refl, intros j hj,
  ring_nf,
end

/-- `trace` version of `tr_identity_over_ℂ` -/
lemma trace_identity_over_ℂ 
(v : I → ℂ) (w : J → ℂ) (M₁ : matrix I J ℂ) (M₂ : matrix I J ℂ):
dot_product (vec_mul (star v)  (M₁ ⊙ M₂)) w =
trace I ℂ ℂ ((diagonal v)ᴴ ⬝ M₁ ⬝ (diagonal w) ⬝ M₂ᵀ) :=
by rw [trace_eq_tr, tr_identity_over_ℂ]

end trace

/-
section rank
variables [decidable_eq J] [field α]
theorem rank_Had_le_rank_mul :
matrix.rank (A ⊙ B) ≤ A.rank  * B.rank := sorry
end rank
-/

end basic_properties

/-
section psd
open_locale complex_order
variables {A B : matrix I I ℂ}
variables (ha : A.is_pos_semidef) (hb : B.is_pos_semidef)
--Schur_product_theorem
theorem Hadamard.is_pos_semidef_of_is_pos_semidef : (A ⊙ B).is_pos_semidef :=
sorry
--#check det
variable [decidable_eq I]
theorem det_Had_ge_det_mul_of_psd : ((A ⊙ B).det) ≥ (A.det) * (B.det) :=
sorry
end psd
-/

end Hadamard_product
/- ## end Hadamard product  -/
----------------------------------------------------------------------------------

/- ## Kronecker product  -/
section Kronecker_product
open_locale matrix

@[elab_as_eliminator]
def Kronecker [has_mul α] (A : matrix I J α) (B : matrix K L α) :
matrix (I × K) (J × L) α :=
λ ⟨i, k⟩ ⟨j, l⟩, (A i j) * (B k l)

/- an infix notation for the Kronecker product -/
localized "infix `⊗`:100 := matrix.Kronecker" in matrix

/- The advantage of the following def is that one can directly #eval the Kronecker product of specific matrices-/
/- ## fin_Kronecker_prodcut  -/

@[elab_as_eliminator]
def fin_Kronecker [has_mul α]
(A : matrix (fin m) (fin n) α) (B : matrix (fin p) (fin q) α)
: matrix (fin (m * p)) (fin (n * q)) α :=
λ i j,
A ⟨(i / p), by {have h:= i.2, simp [mul_comm m] at *, apply nat.div_lt_of_lt_mul h}⟩ 
  ⟨(j / q), by {have h:= j.2, simp [mul_comm n] at *, apply nat.div_lt_of_lt_mul h}⟩ 
*
B ⟨(i % p), by {cases p, linarith [i.2], apply nat.mod_lt _ (nat.succ_pos _)}⟩
  ⟨(j % q), by {cases q, linarith [j.2], apply nat.mod_lt _ (nat.succ_pos _)}⟩ 

localized "infix `⊗ₖ`:100 := matrix.fin_Kronecker" in matrix

section notations
def matrix_empty : matrix (fin 0) (fin 0) α := λ x, ![]
localized "notation `!![]` := matrix.matrix_empty" in matrix
example : (!![]: matrix (fin 0) (fin 0) α) = ![] := by {ext, have h:= x.2, simp* at *}
end notations

section examples
open_locale matrix

def ex1:= ![![1, 2], ![3, 4]]
def ex2:= ![![0, 5], ![6, 7]]
def ex3:= ![![(1:ℤ), -4, 7], ![-2, 3, 3]]
def ex4:= ![![(8:ℤ), -9, -6, 5], ![1, -3, -4, 7], ![2, 8, -8, -3], ![1, 2, -5, -1]]

#eval (!![]: matrix (fin 0) (fin 0) ℕ) 
#eval ex3 ⊗ₖ ex4 
#eval ex1 ⊗ₖ ex2 
#eval 2 • (ex1 ⊗ₖ ex2) 
#eval ex2 ⊗ₖ ![![]]
#eval ![![]] ⊗ₖ ex2 
#eval ex2 ⊗ₖ !![] 
#eval !![] ⊗ₖ ex2 
#eval ![![]] ⊗ₖ (![![]] :matrix (fin 1) (fin 0) ℕ)

end examples
/- ## end fin_Kronecker_prodcut  -/

lemma Kronecker_apply [has_mul α] 
(A : matrix I J α) (B : matrix K L α) (a : I × K) (b : J × L) :
(A ⊗ B) a b = (A a.1 b.1) * (B a.2 b.2) := 
begin
  have ha : a = ⟨a.1, a.2⟩ := by {ext; simp},
  have hb : b = ⟨b.1, b.2⟩ := by {ext; simp},
  rw [ha, hb], dsimp [Kronecker], refl
end

/- distributivity -/
section distrib
variables [distrib α] -- variables are restricted to this section
variables (A : matrix I J α) (B : matrix K L α) (B' : matrix K L α)
lemma K_add :A ⊗ (B + B') = A ⊗ B + A ⊗ B' :=
by {ext ⟨a,b⟩ ⟨c,d⟩, simp [Kronecker, left_distrib]}
lemma add_K :(B + B') ⊗ A = B ⊗ A + B' ⊗ A :=
by {ext ⟨a,b⟩ ⟨c,d⟩, simp [Kronecker, right_distrib]}
end distrib

/- distributivity over substraction -/
section distrib_sub
variables [ring α] 
variables (A : matrix I J α) (B : matrix K L α) (B' : matrix K L α)
lemma K_sub :A ⊗ (B - B') = A ⊗ B - A ⊗ B' :=
by {ext ⟨a,b⟩ ⟨c,d⟩, simp [Kronecker, mul_sub]}
lemma sub_K :(B - B') ⊗ A = B ⊗ A - B' ⊗ A :=
by {ext ⟨a,b⟩ ⟨c,d⟩, simp [Kronecker, sub_mul]}
end distrib_sub

/-
section non_comm
variables [decidable_eq I] [decidable_eq K] [decidable_eq J] [decidable_eq L] [mul_one_class α] [add_comm_monoid α]
variables (A : matrix I J α) (B : matrix K L α)
lemma non_comm : ∃ P Q,  B ⊗ A = reindex_prod_comm (P ⬝ (A ⊗ B) ⬝ Q) ∧ P.is_perfect_shuffle ∧ Q.is_perfect_shuffle :=
sorry
end non_comm
-/

/-- associativity -/
lemma K_assoc 
[semigroup α] (A : matrix I J α) (B : matrix K L α) (C : matrix M N α) : 
A ⊗ B ⊗ C = A ⊗ (B ⊗ C) :=
by {ext ⟨⟨a1, b1⟩, c1⟩ ⟨⟨a2, b2⟩, c2⟩, simp[Kronecker, mul_assoc], refl}

section zero
variables [mul_zero_class α] (A : matrix I J α)
@[simp] lemma K_zero : A ⊗ (0 : matrix K L α) = 0 :=
by {ext ⟨a,b⟩ ⟨c,d⟩, simp [Kronecker]}
@[simp] lemma K_zero' : A ⊗ ((λ _ _, 0):matrix K L α) = 0 :=
K_zero A
@[simp] lemma zero_K : (0 : matrix K L α) ⊗ A = 0 :=
by {ext ⟨a,b⟩ ⟨c,d⟩, simp [Kronecker]}
@[simp] lemma zero_K' : ((λ _ _, 0):matrix K L α) ⊗ A = 0 :=
zero_K A
end zero

/-- `1 ⊗ 1 = 1`. 
    The Kronecker product of two identity matrices is an identity matrix. -/
@[simp] lemma one_K_one 
[mul_zero_one_class α] [decidable_eq I] [decidable_eq J] : 
(1 :matrix I I α) ⊗ (1 :matrix J J α) = 1 :=
begin
  ext ⟨a,b⟩ ⟨c,d⟩,
  by_cases h: a = c,
  any_goals {by_cases g: b = d},
  any_goals {simp[*, Kronecker] at *},
end

section neg
variables [ring α] 
variables (A : matrix I J α) (B : matrix K L α)
@[simp] lemma neg_K: (-A) ⊗ B = - A ⊗ B := by {ext ⟨a,b⟩ ⟨c,d⟩, simp [Kronecker]}
@[simp] lemma K_neg: A ⊗ (-B) = - A ⊗ B := by {ext ⟨a,b⟩ ⟨c,d⟩, simp [Kronecker]}
end neg

/- scalar multiplication -/
section scalar
@[simp] lemma smul_K 
[has_mul α] [has_scalar R α] [is_scalar_tower R α α]
(k : R) (A : matrix I J α) (B : matrix K L α) : 
(k • A) ⊗ B = k • A ⊗ B :=
by {ext ⟨a,b⟩ ⟨c,d⟩, simp [Kronecker], exact smul_assoc _ (A a c) _}
@[simp] lemma K_smul 
[has_mul α] [has_scalar R α] [smul_comm_class R α α]
(k : R) (A : matrix I J α) (B : matrix K L α) : 
A ⊗ (k • B) = k • A ⊗ B :=
by {ext ⟨a,b⟩ ⟨c,d⟩, simp [Kronecker], exact (smul_comm k (A a c) _).symm}
end scalar

/- Kronecker product mixes matrix multiplication -/
section Kronecker_mul
variables [comm_ring α]
variables
(A : matrix I J α) (C : matrix J K α)
(B : matrix L M α) (D : matrix M N α)
lemma K_mul: (A ⊗ B) ⬝ (C ⊗ D) = (A ⬝ C) ⊗ (B ⬝ D) :=
begin
  ext ⟨a,b⟩ ⟨c,d⟩,
  simp [matrix.mul,dot_product,Kronecker,finset.sum_mul,finset.mul_sum],
  rw [←finset.univ_product_univ,finset.sum_product],
  simp [Kronecker._match_1,Kronecker._match_2],
  rw finset.sum_comm,
  repeat {congr, ext},
  ring,
end
variables [decidable_eq I] [decidable_eq M] [decidable_eq L] [decidable_eq J]
@[simp] lemma one_K_mul: (1 ⊗ B) ⬝ (A ⊗ 1) = A ⊗ B := by simp [K_mul]
@[simp] lemma K_one_mul: (A ⊗ 1) ⬝ (1 ⊗ B) = A ⊗ B := by simp [K_mul]
end Kronecker_mul

/- Kronecker product mixes Hadamard product -/
section Kronecker_Hadamard
variables [comm_semigroup α]
(A : matrix I J α) (C : matrix I J α)
(B : matrix K L α) (D : matrix K L α)
lemma Kronecker_Hadamard : (A ⊗ B) ⊙ (C ⊗ D) = (A ⊙ C) ⊗ (B ⊙ D) :=
begin
  ext ⟨a, b⟩ ⟨c, d⟩,
  simp [Hadamard, Kronecker],
  rw ← mul_assoc,
  rw mul_assoc _ (B b d),
  rw mul_comm (B b d),
  simp [mul_assoc]
end
end Kronecker_Hadamard

lemma transpose_K 
[has_mul α] (A : matrix I J α) (B : matrix K L α): 
(A ⊗ B)ᵀ = Aᵀ ⊗ Bᵀ :=
by ext ⟨a,b⟩ ⟨c,d⟩; simp [transpose, Kronecker]

lemma conj_transpose_K
[comm_monoid α] [star_monoid α] (M₁ : matrix I J α) (M₂ : matrix K L α) : 
(M₁ ⊗ M₂)ᴴ = M₁ᴴ ⊗ M₂ᴴ:=
by ext ⟨a,b⟩ ⟨c,d⟩; simp [conj_transpose,Kronecker, mul_comm]

section trace
variables [semiring β] [non_unital_non_assoc_semiring α] [module β α]
variables (A : matrix I I α) (B : matrix J J α)
lemma trace_K: trace (I × J) β α (A ⊗ B) = (trace I β α A) * (trace J β α B) :=
begin
  simp[Kronecker, trace, ←finset.univ_product_univ, finset.sum_product, 
       Kronecker._match_2,finset.sum_mul,finset.mul_sum],
  rw finset.sum_comm,
end
end trace

section inverse

variables [decidable_eq I] [decidable_eq J] [comm_ring α]
variables (A : matrix I I α) (B : matrix J J α) (C : matrix I I α)

lemma K_inverse [invertible A] [invertible B] :(A ⊗ B)⁻¹ = A⁻¹ ⊗ B⁻¹ :=
begin
  suffices : (A⁻¹ ⊗ B⁻¹) ⬝ (A ⊗ B) = 1,
  apply inv_eq_left_inv this,
  simp [K_mul],
end

@[simp] noncomputable
def Kronecker.invertible_of_invertible [invertible A] [invertible B] : invertible (A ⊗ B) :=
⟨A⁻¹ ⊗ B⁻¹, by simp [K_mul], by simp [K_mul]⟩


@[simp] lemma Kronecker.unit_of_unit (ha : is_unit A) (hb : is_unit B) : is_unit (A ⊗ B) :=
@is_unit_of_invertible _ _ (A ⊗ B) (@Kronecker.invertible_of_invertible _ _ _ _ _ _ _ _ A B (is_unit.invertible ha) (is_unit.invertible hb))

end inverse

section symmetric
variables [has_mul α]
@[simp] lemma Kronecker.is_sym_of_is_sym {A : matrix I I α} {B : matrix J J α} (ha: A.is_sym) (hb: B.is_sym) :
(A ⊗ B).is_sym := by simp [matrix.is_sym, transpose_K, *] at *
@[simp] lemma Kronecker.is_Hermitian_of_is_Hermitian {A : matrix I I ℂ} {B : matrix J J ℂ} (ha: A.is_Hermitian) (hb: B.is_Hermitian) :
(A ⊗ B).is_Hermitian := by simp [matrix.is_Hermitian, conj_transpose_K, *] at *
end symmetric

/-
section pos_def
@[simp]
lemma Kronecker.is_pos_def_of_is_pos_def {A : matrix I I ℂ} {B : matrix J J ℂ} (ha : A.is_pos_def) (hb : B.is_pos_def) :
(A ⊗ B).is_pos_def :=
begin
  /-
  simp [matrix.is_pos_def, *] at *,
  simp [dot_product, mul_vec] at *,
  intros v hv,
  simp [←finset.univ_product_univ, finset.sum_product],
  simp [Kronecker,finset.mul_sum] at *,
  have h1 := ha.2,
  have h2 := hb.2,
  -/
  sorry -- I suspect there are more missing lemmas to get this
end
end pos_def
-/

section ortho
variables  [decidable_eq I] [decidable_eq J]
@[simp] lemma Kronecker.is_ortho_of_is_ortho {A : matrix I I ℝ} {B : matrix J J ℝ} (ha : A.is_ortho) (hb : B.is_ortho) :
(A ⊗ B).is_ortho := by simp [matrix.is_ortho,  transpose_K, K_mul, ha, hb, *] at *
end ortho

section perm
open equiv

variables [decidable_eq I] [decidable_eq J] [mul_zero_one_class α]
variables {A : matrix I I α} {B : matrix J J α}
@[simp] lemma Kronecker.is_perm_of_is_perm (ha : A.is_perm) (hb : B.is_perm) :
(A ⊗ B).is_perm :=
begin
  rcases ha with ⟨σ₁, rfl⟩,
  rcases hb with ⟨σ₂, rfl⟩,
  use prod_congr σ₁ σ₂,
  ext ⟨a,b⟩ ⟨c,d⟩,
  by_cases h1: σ₁ a = c,
  all_goals {simp [*, perm.to_matrix, Kronecker]},
end
end perm

/-
section det
variables [comm_ring α] [decidable_eq I] [decidable_eq J]
variables
#check det
lemma K_det (A : matrix I I α) (B : matrix J J α) :
(A ⊗ B).det = (A.det)^(fintype.card J) * (B.det)^(fintype.card I) :=
sorry
lemma K_det' (A : matrix (fin n) (fin n) α) (B : matrix (fin m) (fin m) α) :
(A ⊗ B).det = (A.det)^m * (B.det)^n := by simp [K_det, fintype.card_fin]
end det
-/

end Kronecker_product

open_locale matrix

section dot_product

lemma dot_product_Kronecker_row [has_mul α] [add_comm_monoid α]
(A : matrix I K α) (B : matrix J L α) (a b : I × J):
dot_product ((A ⊗ B) a) ((A ⊗ B) b) = 
∑ (k : K) (l : L), (A a.1 k * B a.2 l) * (A b.1 k * B b.2 l) := 
by simp [dot_product, ←finset.univ_product_univ, finset.sum_product, Kronecker_apply]

lemma dot_product_Kronecker_row' [comm_semiring α] 
(A : matrix I K α) (B : matrix J L α) (a b : I × J):
dot_product ((A ⊗ B) a) ((A ⊗ B) b) = 
(∑ (k : K), (A a.1 k * A b.1 k)) * ∑ (l : L), (B a.2 l * B b.2 l) :=
begin
simp [dot_product_Kronecker_row, finset.mul_sum, finset.sum_mul],
repeat {apply finset.sum_congr rfl, intros _ _},
ring
end

lemma dot_product_Kronecker_row_split [comm_semiring α] 
(A : matrix I K α) (B : matrix J L α) (a b : I × J):
dot_product ((A ⊗ B) a) ((A ⊗ B) b) = 
(dot_product (A a.1)  (A b.1)) * (dot_product (B a.2) (B b.2)) :=
by rw [dot_product_Kronecker_row', dot_product, dot_product]

end dot_product


section sym

/-- `A ⊗ B` is symmetric if `A` and `B` are symmetric. -/
lemma is_sym_K_of [has_mul α] {A : matrix I I α} {B : matrix J J α} 
(ha : A.is_sym) (hb : B.is_sym) : (A ⊗ B).is_sym :=
begin
  ext ⟨a, b⟩ ⟨c, d⟩,
  simp [transpose_K, Kronecker, ha.apply', hb.apply'],
end

end sym
/- ## end Kronecker product  -/

end matrix
----------------------------------------------- end of file