/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Lu-Ming Zhang.
-/

/-
import linear_algebra.matrix.nonsingular_inverse

/-!
This file supplements things about matrix inverse, that were missing in mathlib.
-/

namespace matrix
universes u v
variables {n : Type u} [decidable_eq n] [fintype n] {α : Type v} [comm_ring α]
open_locale matrix big_operators
open equiv equiv.perm finset

variables (A : matrix n n α) (B : matrix n n α)

/- `is_unit_of_invertible A`
   converts the "stronger" condition `invertible A` to proposition `is_unit A`. -/

/-- `matrix.is_unit_det_of_invertible` converts `invertible A` to `is_unit A.det`. -/
lemma is_unit_det_of_invertible [invertible A] : is_unit A.det :=
@is_unit_of_invertible _ _ _(det_invertible_of_invertible A)

@[simp]
lemma inv_eq_nonsing_inv_of_invertible [invertible A] : ⅟ A = A⁻¹ :=
begin
  suffices : is_unit A,
  { rw [←this.mul_left_inj, inv_of_mul_self, matrix.mul_eq_mul, nonsing_inv_mul],
    rwa ←is_unit_iff_is_unit_det },
  exact is_unit_of_invertible _
end

variables {A} {B}

/- `is_unit.invertible` lifts the proposition `is_unit A` to a constructive inverse of `A`. -/

/-- "Lift" the proposition `is_unit A.det` to a constructive inverse of `A`. -/
noncomputable def invertible_of_is_unit_det  (h : is_unit A.det) : invertible A :=
⟨A⁻¹, nonsing_inv_mul A h, mul_nonsing_inv A h⟩

/-- If matrix A is left invertible, then its inverse equals its left inverse. -/
lemma inv_eq_left_inv (h : B ⬝ A = 1) : A⁻¹ = B :=
begin
  have h1 :=  (is_unit_det_of_left_inverse h),
  have h2 := matrix.invertible_of_is_unit_det h1,
  have := @inv_of_eq_left_inv (matrix n n α) (infer_instance) A B h2 h,
  simp* at *,
end

/-- If matrix A is right invertible, then its inverse equals its right inverse. -/
lemma inv_eq_right_inv (h : A ⬝ B = 1) : A⁻¹ = B :=
begin
  have h1 :=  (is_unit_det_of_right_inverse h),
  have h2 := matrix.invertible_of_is_unit_det h1,
  have := @inv_of_eq_right_inv (matrix n n α) (infer_instance) A B h2 h,
  simp* at *,
end

/-- We can construct an instance of invertible A if A has a left inverse. -/
def invertible_of_left_inverse (h: B ⬝ A = 1) : invertible A :=
⟨B, h, nonsing_inv_right_left h⟩

/-- We can construct an instance of invertible A if A has a right inverse. -/
def invertible_of_right_inverse (h: A ⬝ B = 1) : invertible A :=
⟨B, nonsing_inv_left_right h, h⟩

variables {C: matrix n n α}

/-- The left inverse of matrix A is unique when existing. -/
lemma left_inv_eq_left_inv (h: B ⬝ A = 1) (g: C ⬝ A = 1) : B = C :=
by rw [←(inv_eq_left_inv h), ←(inv_eq_left_inv g)]

/-- The right inverse of matrix A is unique when existing. -/
lemma right_inv_eq_right_inv (h: A ⬝ B = 1) (g: A ⬝ C = 1) : B = C :=
by rw [←(inv_eq_right_inv h), ←(inv_eq_right_inv g)]

/-- The right inverse of matrix A equals the left inverse of A when they exist. -/
lemma right_inv_eq_left_inv (h: A ⬝ B = 1) (g: C ⬝ A = 1) : B = C :=
by rw [←(inv_eq_right_inv h), ←(inv_eq_left_inv g)]

variable (A)

@[simp] lemma mul_inv_of_invertible [invertible A] : A ⬝ A⁻¹ = 1 :=
mul_nonsing_inv A (is_unit_det_of_invertible A)

@[simp] lemma inv_mul_of_invertible [invertible A] : A⁻¹ ⬝ A = 1 :=
nonsing_inv_mul A (is_unit_det_of_invertible A)

end matrix
-/
