import tactic
import tactic.gptf
import data.complex.basic
import algebra.field
import data.matrix.notation
import algebra.big_operators.ring
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.trace
import linear_algebra.matrix.to_lin
import combinatorics.simple_graph.basic
--import analysis.normed_space.inner_product
--import algebra.big_operators.basic
--import linear_algebra.tensor_product
--import data.matrix.basic
--#check tensor_product
set_option pp.beta true

section one
variables {m n α β: Type*} [fintype n] [fintype m]
variables [mul_one_class α] [add_comm_monoid α] [non_assoc_semiring β]
namespace matrix
open_locale big_operators

def vec_one [has_one α] : n → α := λ x, 1

@[simp] lemma dot_product_one (v : n → α) : dot_product v vec_one = ∑ i, v i :=
by simp [dot_product, vec_one]

@[simp] lemma dot_product_one' (v : n → α) : dot_product v (λ i, 1) = ∑ i, v i :=
by simp [dot_product]

@[simp] lemma one_dot_product (v : n → α) : dot_product vec_one v = ∑ i, v i :=
by simp [dot_product, vec_one]

@[simp] lemma one_dot_product' (v : n → α) : dot_product (λ i, 1 : n → α) v = ∑ i, v i :=
by simp [dot_product]

lemma one_dot_one_eq_card : dot_product (vec_one : n → α) vec_one = fintype.card n :=
by simp [dot_product, vec_one, fintype.card]

lemma one_dot_one_eq_card' : dot_product (λ i, 1 : n → α) (λ i, 1) = fintype.card n :=
by simp [dot_product, fintype.card]

@[simp] lemma mul_vector_one (A : matrix m n β) :
mul_vec A vec_one = λ i, ∑ j, A i j :=
by ext; simp [mul_vec, vec_one, dot_product]

@[simp] lemma mul_vector_one' (A : matrix m n β) :
mul_vec A (λ i, 1) = λ i, ∑ j, A i j :=
by ext; simp [mul_vec, dot_product]

@[simp] lemma vector_one_mul (A : matrix m n β) :
vec_mul vec_one A = λ j, ∑ i, A i j :=
by ext; simp [vec_mul, vec_one, dot_product]

@[simp] lemma vector_one_mul' (A : matrix m n β) :
vec_mul (λ j, 1 : m → β) A = λ j, ∑ i, A i j :=
by ext; simp [vec_mul, dot_product]

#check finset.univ

end matrix
end one

----------------------------------------------------------------------------

variables {α β γ I J K L M N: Type*}
variables {𝔽 : Type*} [field 𝔽]
variables {R : Type*}
variables {m n p q r s t: ℕ}
variables [fintype I] [fintype J] [fintype K] [fintype L] [fintype M] [fintype N]

----------------------------------------------------------------------------
/-
-- a missing lemma
lemma inv_of_eq_left_inv [monoid α] {a b : α} [invertible a] (hac : b * a = 1) :
⅟a = b := (left_inv_eq_right_inv  hac (mul_inv_of_self _)).symm
-/
----------------------------------------------------------------------------
example :(α × (β × γ)) = (α × β × γ) := rfl
--#check nat.add_assoc
instance prod_assoc : has_coe ((α × β) × γ) (α × β × γ) := ⟨λ ⟨⟨a,b⟩,c⟩, ⟨a,b,c⟩⟩
instance matrix.prod_assoc : has_coe (matrix (I × J × K) (L × M × N) α) (matrix ((I × J) × K) ((L × M) × N) α):=
⟨λ M ⟨⟨a,b⟩,c⟩ ⟨⟨d,e⟩,f⟩, M ⟨a,b,c⟩ ⟨d,e,f⟩⟩


/- ## reindex and coercion -/
def reindex_prod_assoc : matrix ((I × J) × K) ((L × M) × N) α ≃ matrix (I × J × K) (L × M × N) α :=
matrix.reindex (equiv.prod_assoc _ _ _) (equiv.prod_assoc _ _ _)
def reindex_prod_comm_fst : matrix I (J × K) α ≃ matrix I (K × J) α :=
matrix.reindex (equiv.refl _) (equiv.prod_comm _ _)
def reindex_prod_comm_snd : matrix (I × J) K α ≃ matrix (J × I) K α :=
matrix.reindex (equiv.prod_comm _ _) (equiv.refl _)
def reindex_prod_comm : matrix (I × J) (K × L) α ≃ matrix (J × I) (L × K) α :=
matrix.reindex (equiv.prod_comm _ _) (equiv.prod_comm _ _)
/- ## end reindex and coercion -/

def equiv.perm.to_matrix [decidable_eq I] [has_zero α] [has_one α] (σ : equiv.perm I) : matrix I I α
| i j := if σ i = j then 1 else 0

lemma equiv.perm.to_matrix_eq_to_prequiv_to_matrix [decidable_eq I] [has_zero α] [has_one α] (σ : equiv.perm I) :
(σ.to_pequiv.to_matrix : matrix I I α)= σ.to_matrix :=
by ext i j; simp [pequiv.to_matrix, equiv.perm.to_matrix,equiv.to_pequiv]

#check matrix.det_permutation

namespace matrix
open_locale matrix big_operators
open complex

/-
/- ## inverse section -/
section inverse
variables [decidable_eq I] [comm_ring α]
variables (A B: matrix I I α)

lemma is_unit_det_of_invertible [invertible A] : is_unit A.det :=
by apply is_unit_det_of_left_inverse A (invertible.inv_of A) (inv_of_mul_self A)
#check is_unit_det_of_invertible

@[simp,norm]
lemma inv_eq_nonsing_inv_of_invertible [invertible A] : ⅟ A = A⁻¹ :=
begin
  have ha:= is_unit_det_of_invertible A,
  have ha':= (is_unit_iff_is_unit_det A).2 ha,
  have h:= inv_of_mul_self A,
  have h':= nonsing_inv_mul A ha,
  rw ←h' at h,
  apply (is_unit.mul_left_inj ha').1 h,
end
#check inv_eq_nonsing_inv_of_invertible

variables {A} {B}

noncomputable
def invertible_of_is_unit_det  (h: is_unit A.det) : invertible A :=
⟨A⁻¹, nonsing_inv_mul A h, mul_nonsing_inv A h⟩
#check invertible_of_is_unit_det

lemma inv_eq_right_inv (h : A ⬝ B = 1) : A⁻¹ = B :=
begin
  have h1 :=  (is_unit_det_of_right_inverse A B h),
  have h2 := invertible_of_is_unit_det h1,
  have := @inv_of_eq_right_inv (matrix I I α) (infer_instance) A B h2 h,
  simp* at *,
end
#check inv_eq_right_inv

lemma inv_eq_left_inv (h : B ⬝ A = 1) : A⁻¹ = B :=
begin
  have h1 :=  (is_unit_det_of_left_inverse A B h),
  have h2 := invertible_of_is_unit_det h1,
  have := @inv_of_eq_left_inv (matrix I I α) (infer_instance) A B h2 h,
  simp* at *,
end

variables {C: matrix I I α}

lemma left_inv_eq_left_inv (h: B ⬝ A = 1) (g: C ⬝ A = 1) : B = C :=
by rw [←(inv_eq_left_inv h), ←(inv_eq_left_inv g)]

lemma right_inv_eq_right_inv (h: A ⬝ B = 1) (g: A ⬝ C = 1) : B = C :=
by rw [←(inv_eq_right_inv h), ←(inv_eq_right_inv g)]

lemma right_inv_eq_left_inv (h: A ⬝ B = 1) (g: C ⬝ A = 1) : B = C :=
by rw [←(inv_eq_right_inv h), ←(inv_eq_left_inv g)]

/-- We can construct an instance of invertible A if A has a left inverse. -/
def invertible_of_left_inverse (h: B ⬝ A = 1) : invertible A :=
⟨B, h, nonsing_inv_right_left h⟩

/-- We can construct an instance of invertible A if A has a right inverse. -/
def invertible_of_right_inverse (h: A ⬝ B = 1) : invertible A :=
⟨B, nonsing_inv_left_right h, h⟩

variable (A)

#check mul_nonsing_inv
@[simp] lemma mul_inv_of_invertible [invertible A] : A ⬝ A⁻¹ = 1 :=
mul_nonsing_inv A (is_unit_det_of_invertible A)

@[simp] lemma inv_mul_of_invertible [invertible A] : A⁻¹ ⬝ A = 1 :=
nonsing_inv_mul A (is_unit_det_of_invertible A)

end inverse
/- ## end inverse -/
-/

/- ## trace section -/
section trace
def tr [add_comm_monoid α] (A : matrix I I α) : α := ∑ i : I, A i i
lemma trace_eq_tr [semiring β] [add_comm_monoid α] [module β α] (A : matrix I I α)
: trace I β α A = tr A := rfl
end trace
/- ## end trace -/

/- ## conjugate transpose and symmetric -/
section conjugate_transpose

instance vec_has_star [has_star α]: has_star (I → α) := ⟨λ v i, star (v i)⟩

@[simp] lemma vec_star_ext [has_star α] (v : I → α) (i : I) : star v i = star (v i) := rfl

def conj_transpose [has_star α] (M : matrix I J α) : matrix J I α
| x y := star (M y x)

localized "postfix `ᴴ`:1500 := matrix.conj_transpose" in matrix

lemma conj_transpose_eq_star_of_square_matrix [decidable_eq I] [semiring α] [star_ring α] (M : matrix I I α) :
Mᴴ = star M := rfl

lemma trans_col_eq_row (A : matrix I J α) (i : I) : (λ j, Aᵀ j i) = A i :=
by simp [transpose]

lemma trans_row_eq_col (A : matrix I J α) (j : J) : Aᵀ j = (λ i, A i j):=
by ext; simp [transpose]

protected def is_sym (A : matrix I I α) : Prop := Aᵀ = A
protected def is_skewsym [has_neg α] (A : matrix I I α) : Prop := -Aᵀ = A
protected def is_Hermitian [has_star α] (A : matrix I I α) : Prop := Aᴴ = A

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
∃ σ : equiv.perm I, P = perm.to_matrix σ
protected def is_perfect_shuffle (P : matrix I I α) : Prop :=
∃ σ : equiv.perm I, (P = perm.to_matrix σ ∧ ∀ i : I, σ i ≠ i)
protected def is_perm' (P : matrix I I α) : Prop :=
(∀ i, ∃! j, ∀ j', ite (j' = j) (P i j' = 1) (P i j' = 0)) ∧
(∀ j, ∃! i, ∀ i', ite (i' = i) (P i' j = 1) (P i' j = 0))

lemma is_perm_of_is_perfect_shuffle (P : matrix I I α) : P.is_perfect_shuffle → P.is_perm :=
by {intro h, rcases h with ⟨σ, rfl, h2⟩, use σ}
lemma is_perm_of_is_perm' {P : matrix I I α} (h : P.is_perm'): P.is_perm :=
sorry
lemma is_perm'_of_is_perm {P : matrix I I α} (h : P.is_perm): P.is_perm' :=
sorry
lemma is_perm_iff_is_perm' (P : matrix I I α) : P.is_perm ↔ P.is_perm' :=
⟨is_perm'_of_is_perm, is_perm_of_is_perm'⟩

def std := {v : I → α| ∃! (i : I), ∀ j : I, ite (j = i) (v j = 1) (v j = 0)}

end defns

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

#check set.bijective_iff_bij_on_univ
--#check subtype.inj_on
#check set.inj_on
def pp : ℕ → Prop := λ x, x=1 ∨ x=2
#check pp
#check subtype pp
#check subtype.val
#check fin
#check semigroup
end perm
/- ## end permutation -/



/- ## matrix similarity section  -/
section similarity
variables [comm_ring α] [decidable_eq I]
#check nonsing_inv
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

/- ## Hadamard product  -/
section Hadamard_product

def Hadamard [has_mul α] (A : matrix I J α) (B : matrix I J α) :
matrix I J α :=
λ i j, (A i j) * (B i j)

localized "infix `⊙`:100 := matrix.Hadamard" in matrix.Hadamard_product

/- The advantage of the following def is that one can directly #eval the Kronecker product of specific matrices-/
/- ## fin_Kronecker_prodcut  -/
@[elab_as_eliminator]
def fin_Kronecker_prodcut [has_mul α]
(A : matrix (fin m) (fin n) α) (B : matrix (fin p) (fin q) α)
: matrix (fin (m * p)) (fin (n * q)) α :=
λ i j,
A ⟨(i / p), by {have h:= i.2, simp [mul_comm m] at *, apply nat.div_lt_of_lt_mul h}⟩ 
  ⟨(j / q), by {have h:= j.2, simp [mul_comm n] at *, apply nat.div_lt_of_lt_mul h}⟩ 
*
B ⟨(i % p), by {cases p, linarith [i.2], apply nat.mod_lt _ (nat.succ_pos _)}⟩
  ⟨(j % q), by {cases q, linarith [j.2], apply nat.mod_lt _ (nat.succ_pos _)}⟩ 
localized "infix `⊗ₖ'`:100 := matrix.fin_Kronecker_prodcut" in matrix
section notations
def matrix_empty : matrix (fin 0) (fin 0) α := λ x, ![]
localized "notation `!![]` := matrix.matrix_empty" in matrix
example : (!![]: matrix (fin 0) (fin 0) α) = ![] :=
  by {ext, have h:= x.2, simp* at *}
end notations
section examples
open_locale matrix
def ex1:= ![![1, 2], ![3, 4]]
def ex2:= ![![0, 5], ![6, 7]]
def ex3:= ![![(1:ℤ), -4, 7], ![-2, 3, 3]]
def ex4:= ![![(8:ℤ), -9, -6, 5], ![1, -3, -4, 7], ![2, 8, -8, -3], ![1, 2, -5, -1]]
#eval (!![]: matrix (fin 0) (fin 0) ℕ) #eval ex3 ⊗ₖ' ex4 
#eval ex1 ⊗ₖ' ex2 #eval 2 • (ex1 ⊗ₖ' ex2) #eval ex2 ⊗ₖ' ![![]]
#eval ![![]] ⊗ₖ' ex2 #eval ex2 ⊗ₖ' !![] #eval !![] ⊗ₖ' ex2 
#eval ![![]] ⊗ₖ' (![![]] :matrix (fin 1) (fin 0) ℕ)
end examples
/- ## end fin_Kronecker_prodcut  -/

section basic_properties
variables (A : matrix I J α) (B : matrix I J α) (C : matrix I J α)

section comm
variables [comm_semigroup α]
lemma Had_comm : A ⊙ B = B ⊙ A := by ext; simp [Hadamard, mul_comm]
end comm

section assoc
variables [semigroup α]
lemma Had_assoc : A ⊙ B ⊙ C = A ⊙ (B ⊙ C) :=
by ext; simp [Hadamard, mul_assoc]
end assoc

section distrib
variables [distrib α]
lemma Had_add : A ⊙ (B + C) = A ⊙ B + A ⊙ C :=
by ext; simp [Hadamard, left_distrib]
lemma add_Had : (B + C) ⊙ A = B ⊙ A + C ⊙ A :=
by ext; simp [Hadamard, right_distrib]
end distrib

section scalar
variables [has_mul α] [has_scalar R α] [is_scalar_tower R α α] [smul_comm_class R α α]
variables (k : R)
private lemma aux_smul_mul_assoc (x y : α) :
(k • x) * y = k • (x * y) := smul_assoc k x y
private lemma aux_mul_smul_comm (x y : α) :
x * (k • y) = k • (x * y) := (smul_comm k x y).symm
@[simp] lemma smul_Had : (k • A) ⊙ B = k • A ⊙ B :=
  by ext; simp [Hadamard, aux_smul_mul_assoc]
@[simp] lemma Had_smul : A ⊙ (k • B) = k • A ⊙ B :=
  by ext; simp [Hadamard, aux_mul_smul_comm]
end scalar

section zero
variables [mul_zero_class α]
@[simp] lemma Had_zero : A ⊙ (0 : matrix I J α) = 0 :=
by ext; simp [Hadamard]
@[simp] lemma Had_zero' : A ⊙ ((λ _ _, 0):matrix I J α) = 0 :=
Had_zero A
@[simp] lemma zero_Had : (0 : matrix I J α) ⊙ A = 0 :=
by ext; simp [Hadamard]
@[simp] lemma zero_Had' : ((λ _ _, 0):matrix I J α) ⊙ A = 0 :=
zero_Had A
end zero

section trace
open_locale matrix
variables [comm_semiring α] [decidable_eq I] [decidable_eq J]

@[simp] private lemma conj_ite {p : Prop} {z₁ z₂ : ℂ} [decidable p] :
conj (ite p z₁ z₂) = ite p (conj z₁) (conj z₂) :=
apply_ite ⇑conj p z₁ z₂

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

lemma trace_identity (v : I → α) (w : J → α) (M₁ : matrix I J α) (M₂ : matrix I J α):
dot_product (vec_mul  v  (M₁ ⊙ M₂)) w =
trace I α α ((diagonal v)ᵀ ⬝ M₁ ⬝ (diagonal w) ⬝ M₂ᵀ) :=
by rw [trace_eq_tr, tr_identity]

lemma sum_Had_eq_tr_mul (M₁ : matrix I J α) (M₂ : matrix I J α) :
∑ (i : I) (j : J), (M₁ ⊙ M₂) i j = tr (M₁ ⬝ M₂ᵀ) :=
begin
  have h:= tr_identity (λ i, 1 : I → α) (λ i, 1 : J → α) M₁ M₂,
  simp at h,
  rw finset.sum_comm at h,
  assumption,
end

lemma tr_identity_over_ℂ (v : I → ℂ) (w : J → ℂ) (M₁ : matrix I J ℂ) (M₂ : matrix I J ℂ):
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

lemma trace_identity_over_ℂ (v : I → ℂ) (w : J → ℂ) (M₁ : matrix I J ℂ) (M₂ : matrix I J ℂ):
dot_product (vec_mul (star v)  (M₁ ⊙ M₂)) w =
trace I ℂ ℂ ((diagonal v)ᴴ ⬝ M₁ ⬝ (diagonal w) ⬝ M₂ᵀ) :=
by rw [trace_eq_tr, tr_identity_over_ℂ]

end trace

section rank
variables [decidable_eq J] [field α]
theorem rank_Had_le_rank_mul :
matrix.rank (A ⊙ B) ≤ A.rank  * B.rank := sorry
end rank

end basic_properties

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

end Hadamard_product
/- ## end Hadamard product  -/
----------------------------------------------------------------------

/- ## Kronecker product  -/
section Kronecker_product

open_locale matrix.Hadamard_product

@[elab_as_eliminator]
def Kronecker [has_mul α] (A : matrix I J α) (B : matrix K L α) :
matrix (I × K)  (J × L) α :=
λ ⟨i, k⟩ ⟨j, l⟩, (A i j) * (B k l)

localized "infix `⊗`:100 := matrix.Kronecker" in matrix
--def emppty_matrix : matrix empty empty α := λ x, empty.rec (λ (n : empty), α)
--localized "notation `!![]` := matrix.emppty_matrix" in matrix

section one_K_one
variables [monoid_with_zero α] [decidable_eq I] [decidable_eq J]
@[simp] lemma one_K_one : (1 :matrix I I α) ⊗ (1 :matrix J J α) = 1 :=
begin
  ext ⟨a,b⟩ ⟨c,d⟩,
  simp [Kronecker],
  by_cases h: a = c,
  {by_cases g: b = d; simp* at *},
  simp* at *,
end
end one_K_one

section transpose
variables [has_mul α]
(A : matrix I J α) (B : matrix K L α)
lemma K_transpose: (A ⊗ B)ᵀ = Aᵀ ⊗ Bᵀ :=
by ext ⟨a,b⟩ ⟨c,d⟩; simp [transpose,Kronecker]
end transpose

section conj_transpose
open_locale matrix
variables [comm_monoid α] [star_monoid α] (M₁ : matrix I J α) (M₂ : matrix K L α)
lemma K_conj_transpose: (M₁ ⊗ M₂)ᴴ = M₁ᴴ ⊗ M₂ᴴ:=
by ext ⟨a,b⟩ ⟨c,d⟩; simp [conj_transpose,Kronecker, mul_comm]
#check matrix.trace_apply
end conj_transpose

section distrib
variables [distrib α]
variables
(A : matrix I J α)
(B : matrix K L α)
(B' : matrix K L α)
lemma K_add :A ⊗ (B + B') = A ⊗ B + A ⊗ B' :=
  by {ext ⟨a,b⟩ ⟨c,d⟩, simp [Kronecker, left_distrib]}
lemma add_K :(B + B') ⊗ A = B ⊗ A + B' ⊗ A :=
  by {ext ⟨a,b⟩ ⟨c,d⟩, simp [Kronecker, right_distrib]}
end distrib

section non_comm
#check matrix.is_perfect_shuffle
#check matrix.mul
variables [decidable_eq I] [decidable_eq K] [decidable_eq J] [decidable_eq L] [mul_one_class α] [add_comm_monoid α]
variables (A : matrix I J α) (B : matrix K L α)
lemma non_comm : ∃ P Q,  B ⊗ A = reindex_prod_comm (P ⬝ (A ⊗ B) ⬝ Q) ∧ P.is_perfect_shuffle ∧ Q.is_perfect_shuffle :=
sorry
-- #check eq.rec_on

#check equiv.prod_comm
#check equiv.refl
end non_comm

section associativity
variables [semigroup α]
variables (A : matrix I J α) (B : matrix K L α) (C : matrix M N α)
lemma K_assoc : A ⊗ B ⊗ C = A ⊗ (B ⊗ C) :=
by {ext ⟨⟨a1, b1⟩, c1⟩ ⟨⟨a2, b2⟩, c2⟩, simp[Kronecker, mul_assoc], refl}
end associativity

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
@[simp] lemma id_K_mul: (1 ⊗ B) ⬝ (A ⊗ 1) = A ⊗ B := by simp [K_mul]
@[simp] lemma K_id_mul: (A ⊗ 1) ⬝ (1 ⊗ B) = A ⊗ B := by simp [K_mul]
end Kronecker_mul

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

section scalar
variables [has_mul α] [has_scalar R α] [is_scalar_tower R α α] [smul_comm_class R α α]
variables (k : R) (A : matrix I J α) (B : matrix K L α)
private lemma aux_smul_mul_assoc' (x y : α) :
(k • x) * y = k • (x * y) := smul_assoc k x y
private  lemma aux_mul_smul_comm' (x y : α) :
x * (k • y) = k • (x * y) := (smul_comm k x y).symm
@[simp] lemma smul_K : (k • A) ⊗ B = k • A ⊗ B :=
  by ext ⟨a,b⟩ ⟨c,d⟩; simp [Kronecker, aux_smul_mul_assoc']
@[simp] lemma K_smul : A ⊗ (k • B) = k • A ⊗ B :=
  by ext ⟨a,b⟩ ⟨c,d⟩; simp [Kronecker, aux_mul_smul_comm']
end scalar

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
--#check matrix.nonsing_inv
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
(A ⊗ B).is_sym := by simp [matrix.is_sym, K_transpose, *] at *
@[simp] lemma Kronecker.is_Hermitian_of_is_Hermitian {A : matrix I I ℂ} {B : matrix J J ℂ} (ha: A.is_Hermitian) (hb: B.is_Hermitian) :
(A ⊗ B).is_Hermitian := by simp [matrix.is_Hermitian, K_conj_transpose, *] at *
end symmetric

section pos_def
#check matrix.is_pos_def
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

section ortho
variables  [decidable_eq I] [decidable_eq J]
@[simp] lemma Kronecker.is_ortho_of_is_ortho {A : matrix I I ℝ} {B : matrix J J ℝ} (ha : A.is_ortho) (hb : B.is_ortho) :
(A ⊗ B).is_ortho := by simp [matrix.is_ortho,  K_transpose, K_mul, ha, hb, *] at *
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

--Block matrices
--abstract properties

end Kronecker_product
/- ## end Kronecker product  -/

end matrix


----------------------------------------------- end of file
/- 
--#check
instance silly [ring α] : has_scalar α α := ⟨ring.mul⟩



variables [has_zero α] [has_one α] [decidable_eq M]
--instance : has_one (matrix M M α) :=sorry
#check matrix.has_one
#check (1 :matrix M M α)

def ex1:= ![![(1:ℂ), 2], ![3, 4]]

#check star (1: ℂ)

--#print has_star ℂ




#check simple_graph

namespace test
private abbreviation S :set ℤ := {-1, 1, 0}

def f : S → ℕ := sorry

#reduce ↥S
#check ↥S
#check subtype
#check monoid
#check {x : ℤ// x = -1 ∨ x = 1 ∨ x =  0}
#check has_coe_to_sort S
example: f =f := by obviously
#check simple_graph
end test

def complete_graph' (V : Type) : simple_graph V :=
⟨ ne, by obviously, by tidy ⟩ 
-/