import symmetric_matrix
import tactic.gptf

variables {α I R : Type*} [fintype I] {n : ℕ}

namespace matrix
open_locale matrix big_operators

def cir [has_sub I] (v : I → α) : matrix I I α
| i j := v (i - j)

lemma cir_is_sym_ext_iff' [has_sub I] {v : I → α} : 
(cir v).is_sym ↔ ∀ i j, v (j - i) = v (i - j) :=
by simp [is_sym.ext_iff, cir]

lemma cir_is_sym_ext_iff [add_group I] {v : I → α} : 
(cir v).is_sym ↔ ∀ i, v (- i) = v i :=
begin
  rw [cir_is_sym_ext_iff'],
  split,
  { intros h i, convert h i 0; simp },
  { intros h i j, convert h (i - j), simp }
end

lemma fin.cir_is_sym_ext_iff {v : fin n → α} : 
(cir v).is_sym ↔ ∀ i, v (- i) = v i :=
begin
  induction n with n ih, 
  { rw [cir_is_sym_ext_iff'], 
    split; 
    {intros h i, have :=i.2, simp* at *} },
  convert cir_is_sym_ext_iff,
end

lemma cir_is_sym_apply [add_group I] {v : I → α} (h : (cir v).is_sym) (i : I) : 
v (-i) = v i := cir_is_sym_ext_iff.1 h i

lemma fin.cir_is_sym_apply {v : fin n → α} (h : (cir v).is_sym) (i : fin n) : 
v (-i) = v i := fin.cir_is_sym_ext_iff.1 h i

lemma cir_add [has_add α] [has_sub I] (v w : I → α) :
cir v + cir w = cir (v + w) := 
by ext; simp [cir]

lemma cir_mul [comm_semiring α] [add_comm_group I] (v w : I → α) :
cir v ⬝ cir w = cir (mul_vec (cir w) v) := 
begin
  ext i j,
  simp [mul_apply, mul_vec, cir, dot_product],
  refine fintype.sum_equiv ((equiv.add_left (-i)).trans (equiv.neg _)) _ _ _,
  simp [mul_comm],
  intro x,
  congr' 2; abel
end

lemma fin.cir_mul [comm_semiring α] (v w : fin n → α) :
cir v ⬝ cir w = cir (mul_vec (cir w) v) := 
begin
  induction n with n ih, {refl},
  exact cir_mul v w,
end

lemma cir_mul_comm
[comm_semigroup α] [add_comm_monoid α] [add_comm_group I] (v w : I → α) : 
cir v ⬝ cir w = cir w ⬝ cir v := 
begin
  ext i j,
  simp [mul_apply, cir, mul_comm],
  refine fintype.sum_equiv (((equiv.add_right (-i)).trans (equiv.neg _)).trans (equiv.add_right j)) _ _ _,
  simp,
  intro x,
  congr' 2; abel
end

lemma fin.cir_mul_comm
[comm_semigroup α] [add_comm_monoid α] (v w : fin n → α) : 
cir v ⬝ cir w = cir w ⬝ cir v := 
begin
  induction n with n ih, {refl},
  exact cir_mul_comm v w,
end

lemma cir_ext_iff [add_group I] {v w : I → α} :
cir v = cir w ↔ v = w :=
begin
  split,
  { intro h, ext, 
    simp [←matrix.ext_iff, cir] at h,
    convert h x 0; simp },
  { rintro rfl, refl }
end

lemma fin.cir_ext_iff {v w : fin n → α} :
cir v = cir w ↔ v = w :=
begin
  induction n with n ih,
  {tidy},
  exact cir_ext_iff
end

lemma smul_cir [has_sub I] [has_scalar R α] {k : R} {v : I → α} : 
k • cir v = cir (k • v) := by {ext, simp [cir]}

lemma one_eq_cir [has_zero α] [has_one α] [decidable_eq I] [add_group I]:
(1 : matrix I I α) = cir (λ i, ite (i = 0) 1 0) :=
begin
  ext,
  simp [cir, one_apply],
  congr' 1,
  apply propext,
  exact sub_eq_zero.symm
end

lemma one_eq_cir' [has_zero α] [has_one α] [decidable_eq I] [add_group I]:
(1 : matrix I I α) = cir (λ i, (1 : matrix I I α) i 0) := one_eq_cir

lemma fin.one_eq_cir [has_zero α] [has_one α] :
(1 : matrix (fin n) (fin n) α) = cir (λ i, ite (i.1 = 0) 1 0) :=
begin
  induction n with n, {dec_trivial},
  convert one_eq_cir,
  ext, congr' 1,
  apply propext, 
  exact (fin.ext_iff x 0).symm
end

lemma pred_cir_entry_of_pred_vec_entry [has_sub I] {p : α → Prop} {v : I → α} :
(∀ k, p (v k)) → ∀ i j, p ((cir v) i j) :=
begin
  intros h i j,
  simp [cir],
  exact h (i - j),
end

lemma cir_entry_in_of_vec_entry_in [has_sub I] {S : set α} {v : I → α} :
(∀ k, v k ∈ S) → ∀ i j, (cir v) i j ∈ S :=
@pred_cir_entry_of_pred_vec_entry α I _ _ S v

noncomputable
def cir_poly [semiring α] (v : fin n → α) : polynomial α := 
∑ i : fin n, polynomial.monomial i (v i)

def cir_perm : Π n, equiv.perm (fin n) := λ n, equiv.symm (fin_rotate n) 

def cir_P (α) [has_zero α] [has_one α] (n : ℕ) :
matrix (fin n) (fin n) α := 
equiv.perm.to_matrix α (cir_perm n)

end matrix