/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Lu-Ming Zhang.
-/
import field_theory.finite.basic
import group_theory.quotient_group
import monoid_hom
import set_finset_fintype

import tactic.gptf

/-!
# Finite fields

This file supplements basic results about finite field that are missing in mathlib.
As well, this files defines quadratic residues and the quadratic character, 
and contains basic results about them.
Throughout most of this file, `F` denotes a finite field, 
and `q` is notation for the cardinality of `F`, and `p` is the character of `F`.

## Main results
1. `finite_field.is_quad_residue`: a proposition predicating whether a given `a : F` is a quadratic residue in `F`. 
   `finite_field.is_quad_residue a` is defined to be `a ≠ 0 ∧ ∃ b, a = b^2`.
2. `finite_field.is_non_residue`: a proposition predicating whether a given `a : F` is a quadratic non-residue in `F`.
   `finite_field.is_non_residue a` is defined to be `a ≠ 0 ∧ ¬ ∃ b, a = b^2`.

3. `finite_field.quad_residues`: the subtype of `F` containing quadratic residues.
4. `finite_field.quad_residues_set`: the set containing quadratic residues of `F`.
5. `finite_field.non_residues`: the subtype of `F` containing quadratic non-residues.
6. `finite_field.non_residues_set`: the set containing quadratic non-residues of `F`.

7. `finite_field.sq`: the square function from `units F` to `units F`, defined as a group homomorphism.

8. `finite_filed.non_residue_mul`: is the map `_ * b` given a non-residue `b` defined on `{a : F // is_quad_residue a}`.

9. `finite_field.quad_char`: defines the quadratic character of `a` in a finite field `F`. 
   - `χ a = 0 ` if `a = 0`
   - `χ a = 1` if `a ≠ 0` and  `a` is a square
   - `χ a = -1` otherwise

## Notation

Throughout most of this file, `F` denotes a finite field, 
and `q` is notation for the cardinality of `F`, and `p` is the character of `F`.
`χ a` denotes the quadratic character of `a : F`.

-/

--local attribute [instance] set_fintype
--local attribute [-instance] set.fintype_univ

set_option pp.beta true

open_locale big_operators
open finset fintype monoid_hom nat.modeq function

namespace finite_field

variables {F : Type*} [field F] [fintype F] {p : ℕ} [char_p F p] 
local notation `q` := fintype.card F -- declares `q` as a notation

/- ## basic -/
section basic

/-- `|F| = |units F| + 1`. The `+` version of `finite_field.card_units`. -/
lemma card_units' : 
fintype.card F = fintype.card (units F) + 1 :=
begin
  simp [card_units],
  have h : 0 < fintype.card F := fintype.card_pos_iff.2 ⟨0⟩,
  rw [nat.sub_add_cancel h]
end

variables (p)
/-- If `n` is a prime number and `↑n = 0` in `F`, then `p = n`. -/
lemma char_eq_of_prime_eq_zero 
{n : ℕ} (h₁ : nat.prime n) (h₂ : ↑n = (0 : F)) : p = n :=
begin
  have g₁ : nat.prime p, {obtain ⟨n, h1, h2⟩:= finite_field.card F p, assumption},
  have g₂ := (char_p.cast_eq_zero_iff F p n).1 h₂,
  exact (nat.prime_dvd_prime_iff_eq g₁ h₁).1 g₂,
end

lemma char_ne_two_of :
q ≡ 1 [MOD 4] ∨ q ≡ 3 [MOD 4] → p ≠ 2 :=
begin
  obtain ⟨n, p_prime, g⟩:= finite_field.card F p,
  rw g,
  rintro (h | h),
  any_goals 
  { rw nat.modeq_iff_dvd at h, 
    rintro hp, rw hp at h, 
    rcases h with ⟨k, h⟩, 
    simp at h,
    have : 2 ∣ 4 * k + 2 ^ ↑n,
    { use (2 * k + (2 : ℤ) ^ n.1.pred), 
      simp [mul_add], congr' 1, 
      ring, 
      have : (2 : ℤ) * 2 ^ (n : ℕ).pred = 2 ^ ((n : ℕ).pred + 1), {refl}, 
      convert this.symm, 
      clear this,
      convert (nat.succ_pred_eq_of_pos _).symm, 
      exact n.2 },
  },
  { have g := eq_add_of_sub_eq h, rw ← g at this, revert this, dec_trivial },
  { have g := eq_add_of_sub_eq h, rw ← g at this, revert this, dec_trivial }, 
end

lemma char_ne_two_of' : 
q ≡ 3 [MOD 4] → p ≠ 2 ∧ ¬ q ≡ 1 [MOD 4] :=
begin
  intros h,
  refine ⟨char_ne_two_of p (or.inr h), _⟩,
  intro h',
  have g := h'.symm.trans  h,
  simp [nat.modeq_iff_dvd] at g,
  rcases g with ⟨k, g⟩,
  norm_num at g, 
  have : 2 / 4 = (4 * k) / 4, {rw ← g},
  norm_num at this,
  simp [← this] at g,
  assumption  
end

/-- For non-zero `a : F`, `to_unit` converts `a` to an instance of `units F`. -/
@[simp] def to_unit {a : F} (h : a ≠ 0): units F :=
by refine {val := a, inv := a⁻¹, ..}; simp* at *

/-- The order of `a : units F` equals the order of `a` coerced in `F`. -/
lemma order_of_unit_eq (a : units F) : order_of a = order_of (a : F) :=
begin
  convert (@order_of_injective (units F) _ F _ (units.coe_hom F) _ a).symm,
  intros i j h,
  simp[*, units.ext_iff] at *,
end

variables (F) {p} 

@[simp] 
lemma two_eq_zero (hp : p = 2) : (2 : F) = 0 :=
by convert (char_p.cast_eq_zero_iff F p 2).2 _; simp [hp]

@[simp]
lemma neg_one_eq_one_of (hp : p = 2) : (-1 : F) = 1 :=
calc (-1 : F) = (-1 : F) + 0 : by simp
          ... = (-1 : F) + (1 + 1)  : by {congr, norm_num [two_eq_zero F hp]}
          ... = 1 : by simp

@[simp]
lemma neg_one_eq_one_of' (hp: p = 2) : (-1 : units F) = 1 := 
by simp [units.ext_iff, neg_one_eq_one_of F hp]
                  

/-- If the character of `F` is not `2`, `-1` is not equal to `1` in `F`. -/
lemma neg_one_ne_one_of (hp: p ≠ 2) : (-1 : F) ≠ 1 :=
begin
  intros h,
  have h' := calc ↑(2 : ℕ) = (2 : F)     : by simp
                      ... = (1 : F) + 1  : by ring
                      ... = (-1 : F) + 1 : by nth_rewrite 0 ←h
                      ... = 0            : by ring,
  have hp' := char_eq_of_prime_eq_zero p nat.prime_two h',
  contradiction
end

/-- If the character of `F` is not `2`, `-1` is not equal to `1` in `units F`. -/
lemma neg_one_ne_one_of' (hp: p ≠ 2) : (-1 : units F) ≠ 1 := 
by simp [units.ext_iff, neg_one_ne_one_of F hp]

variable {F}

/-- For `x : F`, `x^2 = 1 ↔ x = 1 ∨ x = -1`. -/
lemma sq_eq_one_iff_eq_one_or_eq_neg_one (x : F) :
x^2 = 1 ↔ x = 1 ∨ x = -1 :=
begin
  rw [sub_eq_zero.symm],
  have h: x ^ 2 - 1 = (x - 1) * (x + 1), {ring},
  rw [h, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]
end

/-- For `x : units F`, `x^2 = 1 ↔ x = 1 ∨ x = -1`. -/
lemma sq_eq_one_iff_eq_one_or_eq_neg_one' (x : units F) :
x^2 = 1 ↔ x = 1 ∨ x = -1 :=
begin
  simp only [units.ext_iff],
  convert sq_eq_one_iff_eq_one_or_eq_neg_one (x : F),
  simp,
end

/-- If the character of `F` is not `2`, `-1` is the only order 2 element in `F`. -/
lemma order_of_eq_two_iff (hp: p ≠ 2) (x : F) : order_of x = 2 ↔ x = -1 := 
begin
  have g := pow_order_of_eq_one x, -- g: x ^ order_of x = 1
  split, -- splits into `order_of x = 2 → x = -1` and `x = -1 → order_of x = 2`
  any_goals {intros h},
  { rw [h, sq_eq_one_iff_eq_one_or_eq_neg_one] at g, -- g : x = 1 ∨ x = -1
    have : x ≠ 1, { intro hx, rw ←order_of_eq_one_iff at hx, linarith },
    exact or_iff_not_imp_left.1 g this },
  { have hx : x^2 = 1, {rw h, ring},
    have inst : fact (nat.prime 2), 
    {exact ⟨nat.prime_two⟩}, 
    resetI, -- resets the instance cache.
    convert order_of_eq_prime hx _,
    rw [h],
    exact neg_one_ne_one_of F hp }
end

/-- The "units" version of `order_of_eq_two_iff`. -/
lemma order_of_eq_two_iff' (hp: p ≠ 2) (x : units F) : order_of x = 2 ↔ x = -1 := 
by simp [units.ext_iff]; rw [← order_of_eq_two_iff hp (x : F), order_of_unit_eq x]

lemma card_eq_one_mod_n_iff_n_divide_card_units (n : ℕ):
q ≡ 1 [MOD n] ↔ n ∣ fintype.card (units F) := 
begin
  rw [finite_field.card_units, nat.modeq.comm],
  convert nat.modeq_iff_dvd' (card_pos_iff.mpr ⟨(0 : F)⟩),
end

/-- `-1` is a square in `units F` iff the cardinal `q ≡ 1 [MOD 4]`. -/
theorem neg_one_eq_sq_iff' (hp: p ≠ 2) : 
(∃ a : units F, -1 = a^2) ↔ q ≡ 1 [MOD 4] :=
begin
  -- rewrites the RHS to `4 ∣ fintype.card (units F)`
  rw card_eq_one_mod_n_iff_n_divide_card_units,
  split, -- splits the goal into two directions
  -- the `→` direction
  { rintros ⟨a, h'⟩,
    -- h: a ^ 4 = 1
    have h := calc a^4 = a^2 * a^2 : by group
                 ... = 1: by simp [← h'],
    -- h₀: order_of a ∣ 4
    have h₀ := order_of_dvd_of_pow_eq_one h,
    -- au: order_of a ≤ 4
    have au := nat.le_of_dvd dec_trivial h₀,
    -- g₁ : a ≠ 1
    have g₁ : a ≠ 1, 
    { rintro rfl, simp at h',
      exact absurd h' (neg_one_ne_one_of' F hp) },
    -- h₁ : order_of a ≠ 1
    have h₁ := mt order_of_eq_one_iff.1 g₁, 
    -- g₂ : a ≠ -1
    have g₂ : a ≠ -1, 
    { rintro rfl, simp [pow_two] at h', 
      exact absurd h' (neg_one_ne_one_of' F hp) },
    -- h₂ : order_of a ≠ 2 
    have h₂ := mt (order_of_eq_two_iff' hp a).1 g₂,
    -- ha : order_of a = 4
    have ha : order_of a = 4, 
    { revert h₀ h₁ h₂, 
      interval_cases (order_of a), 
      any_goals {rw h_1, norm_num} }, 
    simp [← ha, order_of_dvd_card_univ] },
  -- the `←` direction
  { rintro ⟨k, hF⟩, -- hF : |units F| = 4 * k
    -- `hg'` is a proof that `g` generates `units F`
    obtain ⟨g, hg'⟩ := is_cyclic.exists_generator (units F),
    -- hg : g ^ |units F| = 1
    have hg := @pow_card_eq_one (units F) g _ _,
    have eq : 4 * k = k * 2 * 2, {ring},
    -- rewrite `hg` to `hg : g ^ (k * 2) = 1 ∨ g ^ (k * 2) = -1`
    rw [hF, eq, pow_mul, sq_eq_one_iff_eq_one_or_eq_neg_one'] at hg,
    rcases hg with (hg | hg), -- splits into two cases
    -- case `g ^ (k * 2) = 1`
    { have hk₁ := card_pos_iff.mpr ⟨(1 : units F)⟩, 
      have o₁ := order_of_eq_card_of_forall_mem_gpowers hg',
      have o₂ := order_of_dvd_of_pow_eq_one hg,
      have le := nat.le_of_dvd (by linarith) o₂,
      rw [o₁, hF] at *,
      exfalso, linarith },
    -- case `g ^ (k * 2) = -1`
    { use g ^ k, simp [← hg, pow_mul] } },
end

/-- `-1` is a square in `F` iff the cardinal `q ≡ 1 [MOD 4]`. -/
lemma neg_one_eq_sq_iff (hp: p ≠ 2) : 
(∃ a : F, -1 = a^2) ↔ fintype.card F ≡ 1 [MOD 4] :=
begin
  rw [←neg_one_eq_sq_iff' hp],
  -- the current goal is
  -- `(∃ (a : F), -1 = a ^ 2) ↔ ∃ (a : units F), -1 = a ^ 2`
  split, -- splits into two directions
  any_goals {rintros ⟨a, ha⟩},
  -- the `→` direction
  { have ha' : a ≠ 0,  
    {rintros rfl, simp* at *}, 
    use (to_unit ha'), 
    simpa [units.ext_iff] },
  -- the `←` direction
  { use a, simp [units.ext_iff] at ha, assumption },
  assumption
end

variables (F)

lemma disjoint_units_zero : disjoint {a : F | a ≠ 0} {0} :=
by simp 

lemma units_union_zero : {a : F | a ≠ 0} ∪ {0} = @set.univ F :=
by {tidy, tauto}

end basic
/- ## end basic -/

/- ## quad_residues -/
section quad_residues

variables {F p}

/-- A proposition predicating whether a given `a : F` is a quadratic residue in `F`. 
    `finite_field.is_quad_residue a` is defined to be `a ≠ 0 ∧ ∃ b, a = b^2`. -/
--@[derive decidable] 
def is_quad_residue (a : F) : Prop := a ≠ 0 ∧ ∃ b, a = b^2

/-- A proposition predicating whether a given `a : F` is a quadratic non-residue in `F`.
    `finite_field.is_non_residue a` is defined to be `a ≠ 0 ∧ ¬ ∃ b, a = b^2`. -/
--@[derive decidable] 
def is_non_residue (a : F) : Prop := a ≠ 0 ∧ ¬ ∃ b, a = b^2

instance [decidable_eq F] (a : F) : decidable (is_quad_residue a) := 
by {unfold is_quad_residue, apply_instance}

instance [decidable_eq F] (a : F) : decidable (is_non_residue a) := 
by {unfold is_non_residue, apply_instance}

variables {F p}

lemma not_residue_iff_is_non_residue 
{a : F} (h : a ≠ 0) : 
¬ is_quad_residue a ↔ is_non_residue a :=
by simp [is_quad_residue, is_non_residue, *] at *

lemma is_non_residue_of_not_residue 
{a : F} (h : a ≠ 0) (g : ¬ is_quad_residue a) : 
is_non_residue a :=
(not_residue_iff_is_non_residue h).1 g

lemma not_non_residue_iff_is_residue 
{a : F} (h : a ≠ 0) : 
¬ is_non_residue a ↔ is_quad_residue a :=
by simp [is_quad_residue, is_non_residue, *] at *

lemma is_residue_of_not_non_residue 
{a : F} (h : a ≠ 0) (g : ¬ is_non_residue a) : 
is_quad_residue a :=
(not_non_residue_iff_is_residue h).1 g

lemma residue_or_non_residue 
{a : F} (h : a ≠ 0) :
is_quad_residue a ∨  is_non_residue a :=
begin
  by_cases g: is_quad_residue a,
  exact or.inl g,
  exact or.inr (is_non_residue_of_not_residue h g),
end

/-- `-1` is a residue if `q ≡ 1 [MOD 4]`. -/
lemma neg_one_is_residue_of (hF : q ≡ 1 [MOD 4]) :
is_quad_residue (-1 : F) := 
begin
  obtain ⟨p, inst⟩ := char_p.exists F, -- derive the char p of F
  resetI, -- resets the instance cache
  have hp := char_ne_two_of p (or.inl hF), -- hp: p ≠ 2
  have h := (neg_one_eq_sq_iff hp).2 hF, -- h : -1 is a square
  refine ⟨by tidy, h⟩
end

/-- `-1` is a non-residue if `q ≡ 3 [MOD 4]`. -/
lemma neg_one_is_non_residue_of (hF : q ≡ 3 [MOD 4]) :
is_non_residue (-1 : F) := 
begin
  obtain ⟨p, inst⟩ := char_p.exists F, -- derive the char p of F
  resetI, -- resets the instance cache
  -- hp: p ≠ 2, hF': ¬fintype.card F ≡ 1 [MOD 4]
  obtain ⟨hp, hF'⟩ := char_ne_two_of' p hF,
  -- h: ¬∃ (a : F), -1 = a ^ 2
  have h := mt (neg_one_eq_sq_iff hp).1 hF',
  refine ⟨by tidy, h⟩
end

variable (F)

@[simp] lemma eq_residues : 
{j // ¬j = 0 ∧ ∃ (b : F), j = b ^ 2} = 
{a : F // is_quad_residue a} := rfl

@[simp] lemma eq_non_residues : 
{j // ¬j = 0 ∧ ¬∃ (x : F), j = x ^ 2} = 
{a : F // is_non_residue a} := rfl

@[simp] lemma eq_non_residues' : 
{j // ¬j = 0 ∧ ∀ (x : F), ¬j = x ^ 2} = 
{a : F // is_non_residue a} := by simp [is_non_residue]

/-- `|F| = 1 + |{a : F // is_quad_residue a}| + |{a : F // is_non_residue a}|` -/
lemma eq_one_add_card_residues_add_card_non_residues 
[decidable_eq F]:
q = 1 + fintype.card {a : F // is_quad_residue a} + 
        fintype.card {a : F // is_non_residue a} :=
begin
  rw [fintype.card_split (λ a : F, a = 0),
      fintype.card_split' (λ a : F, a ≠ 0) (λ a, ∃ b, a = b^2)],
  simp [add_assoc],
end

/- ### sq_function -/
section sq_function

open quotient_group

variables (F) -- re-declares `F` as an explicit variable

/-- `sq` is the square function from `units F` to `units F`, 
    defined as a group homomorphism. -/
def sq : (units F) →* (units F) := 
⟨λ a, a * a, by simp, (λ x y, by simp [units.ext_iff]; ring)⟩

/-- `|units F| = |(sq F).range| * |(sq F).ker|` -/
theorem sq.iso [decidable_eq F] : 
fintype.card (units F) = fintype.card (sq F).range * fintype.card (sq F).ker :=
begin
  have iso := quotient_ker_equiv_range (sq F),
  have eq := fintype.card_congr (mul_equiv.to_equiv iso),
  rw [subgroup.card_eq_card_quotient_mul_card_subgroup (sq F).ker, eq]
end

/-- `sq.range_equiv` constructs the natural equivalence between 
    the `(sq F).range` and `{a : F // is_quad_residue a}`. -/
def sq.range_equiv : (sq F).range ≃ {a : F // is_quad_residue a} := 
⟨ 
 λ a, ⟨a, by {have h := a.2, simp [sq] at h, rcases h with ⟨b, h⟩, 
              simp [is_quad_residue, ← h], use b, ring }⟩, 
 λ a, ⟨to_unit (a.2).1, by {obtain ⟨h, ⟨b, hab⟩⟩:= a.2, 
                            have hb : b ≠ 0, {rintros rfl, simp* at *},
                            use to_unit hb, simp [units.ext_iff, sq, ← pow_two, ← hab] }⟩, 
 λ a, by simp [units.ext_iff],
 λ a, by simp
⟩

/-- `|(sq F).range| = |{a : F // is_quad_residue a}|` -/
theorem sq.card_range_eq [decidable_eq F] : 
fintype.card (sq F).range = fintype.card {a : F // is_quad_residue a} :=
by apply fintype.card_congr (sq.range_equiv F)

--lemma test : ↥(sq F).ker = {a : units F // a = 1 ∨ a = -1} := sorry

lemma sq.ker_carrier_eq : 
(sq F).ker.carrier = {1, -1} :=
begin
  ext, 
  simp [sq, mem_ker, ←pow_two, sq_eq_one_iff_eq_one_or_eq_neg_one' x],
end

lemma sq.ker_carrier_eq_of_char_eq_two (hp: p = 2): 
(sq F).ker.carrier = {1} :=
by simp [sq.ker_carrier_eq, neg_one_eq_one_of' F hp]

lemma sq.card_ker_carrier_eq_of_char_ne_two [decidable_eq F] (hp: p ≠ 2) : 
fintype.card (sq F).ker.carrier = 2 :=
begin
  simp [sq.ker_carrier_eq F],
  convert @set.card_insert _ (1 : units F) {-1} _ _ _; simp,
  exact ne.symm (neg_one_ne_one_of' F hp),
end

/-- `|(sq F).ker| = 2` if `p ≠ 2` -/
theorem sq.card_ker_eq_of_char_ne_two [decidable_eq F] (hp: p ≠ 2) : 
fintype.card (sq F).ker = 2 :=
by rw [←sq.card_ker_carrier_eq_of_char_ne_two F hp]; refl

lemma sq.card_ker_carrier_eq_of_char_eq_two [decidable_eq F] (hp: p = 2) : 
fintype.card (sq F).ker.carrier = 1 :=
by simp [sq.ker_carrier_eq_of_char_eq_two F hp]

/-- `|(sq F).ker| = 1` if `p = 2` -/
theorem sq.card_ker_eq_of_char_eq_two [decidable_eq F] (hp: p = 2) : 
fintype.card (sq F).ker = 1 :=
by rw [←sq.card_ker_carrier_eq_of_char_eq_two F hp]; refl

end sq_function
/- ### end sq_function -/

variable (F)

/-- `|units F| = |{a : F // is_quad_residue a}| * 2` if `p ≠ 2` -/
theorem card_units_eq_card_residues_mul_two [decidable_eq F] (hp: p ≠ 2) :
fintype.card (units F) = fintype.card {a : F // is_quad_residue a} * 2 :=
by rwa [sq.iso, sq.card_range_eq, sq.card_ker_eq_of_char_ne_two F hp]

/-- `|units F| = |{a : F // is_quad_residue a}|` if `p = 2` -/
theorem card_units_eq_card_residues [decidable_eq F] (hp: p = 2) :
fintype.card (units F) = fintype.card {a : F // is_quad_residue a}:=
by simp [sq.iso, sq.card_range_eq, sq.card_ker_eq_of_char_eq_two F hp]

/-- `|{a : F // is_quad_residue a}| = |{a : F // is_non_residue a}|`-/
theorem card_residues_eq_card_non_residues
[decidable_eq F] (hp : p ≠ 2):
fintype.card {a : F // is_quad_residue a} = 
fintype.card {a : F // is_non_residue a} :=
begin
  have eq := eq_one_add_card_residues_add_card_non_residues F,
  simp [card_units', card_units_eq_card_residues_mul_two F hp] at eq,
  linarith
end

/-- unfolded version of `card_residues_eq_card_non_residues` -/
theorem card_residues_eq_card_non_residues'
[decidable_eq F] (hp : p ≠ 2):
(@univ {a : F // is_quad_residue a} _).card = 
(@univ {a : F // is_non_residue a} _).card :=
by convert card_residues_eq_card_non_residues F hp


variable {F} -- re-declares `F` as an implicit variable

lemma false_of_char_eq_two_of_is_non_residue  
(hp : p = 2) {a : F} (ha: is_non_residue a) : false :=
begin
  classical,
  have h := eq_one_add_card_residues_add_card_non_residues F,
  rw [card_units', card_units_eq_card_residues F hp, add_comm _ 1, add_assoc] at h,
  have g : fintype.card {a // is_non_residue a} = 0 := 
           add_right_eq_self.mp (congr_fun (congr_arg (+) ((add_right_inj 1).mp h).symm) _),
  clear h,
  rw [card_eq_zero_iff] at g,
  apply g.false,
  exact ⟨a, ha⟩,
end

lemma is_quad_residue_of_char_eq_two (hp : p = 2) {a : F} (ha : a ≠ 0) : 
  is_quad_residue a :=
begin
  by_contra,
  exact false_of_char_eq_two_of_is_non_residue hp (is_non_residue_of_not_residue ha h),
end

example : (0 : F)⁻¹ = 0 := by simp

/-- `a⁻¹` is a residue if and only if `a` is. -/
theorem inv_is_residue_iff {a : F} : 
is_quad_residue a⁻¹ ↔ is_quad_residue a := 
begin
  split, -- splits into two directions
  any_goals {rintro ⟨h, b, g⟩, refine ⟨by tidy, b⁻¹, by simp [←g]⟩},
end

/-- `a⁻¹` is a non residue if and only if `a` is. -/
theorem inv_is_non_residue_iff {a : F} : 
is_non_residue a⁻¹ ↔ is_non_residue a := 
begin
  by_cases h : a = 0,
  {simp* at *}, -- when `a = 0`
  have h' : a⁻¹ ≠ 0 := by simp [h],
  simp [←not_residue_iff_is_non_residue, *, inv_is_residue_iff]
end

theorem residue_mul_residue_is_residue
{a b : F} (ha : is_quad_residue a) (hb : is_quad_residue b) : 
is_quad_residue (a * b) :=
begin
  obtain ⟨ha, c, rfl⟩ := ha,
  obtain ⟨hb, d, rfl⟩ := hb,
  refine ⟨mul_ne_zero ha hb, c*d, _⟩,
  ring
end

theorem non_residue_mul_residue_is_non_residue
{a b : F} (ha : is_non_residue a) (hb : is_quad_residue b) : 
is_non_residue (a * b) :=
begin
  obtain ⟨hb, c, rfl⟩ := hb,
  refine ⟨mul_ne_zero ha.1 hb, _⟩,
  rintro ⟨d, h⟩,
  convert ha.2 ⟨(d * c⁻¹), _⟩,
  field_simp [← h],
end

theorem residue_mul_non_residue_is_non_residue
{a b : F} (ha : is_quad_residue a) (hb : is_non_residue b): 
is_non_residue (a * b) :=
by simp [mul_comm a, non_residue_mul_residue_is_non_residue hb ha]

/-- `finite_filed.non_residue_mul` is the map `a * _` given a non-residue `a` 
    defined on `{b : F // is_quad_residue b}`. -/
def non_residue_mul {a: F} (ha : is_non_residue a) : 
{b : F // is_quad_residue b} → {b : F // is_non_residue b} :=
λ b, ⟨a * b, non_residue_mul_residue_is_non_residue ha b.2⟩

open function

/-- proves that `a * _` is injective from residues for a non-residue `a` -/
lemma is_non_residue.mul_is_injective 
{a: F} (ha : is_non_residue a) : 
injective (non_residue_mul ha):=
begin
  intros b₁ b₂ h,
  simp [non_residue_mul] at h,
  ext,
  convert or.resolve_right h ha.1,
end

/-- proves that `a * _` is surjective onto non-residues for a non-residue `a` -/
lemma is_non_residue.mul_is_surjective 
[decidable_eq F] (hp : p ≠ 2) {a: F} (ha : is_non_residue a) : 
surjective (non_residue_mul ha):=
begin
  by_contra, -- prove by contradtiction
  have lt := card_lt_of_injective_not_surjective 
    (non_residue_mul ha) (ha.mul_is_injective) h,
  have eq := card_residues_eq_card_non_residues F hp,
  linarith
end

theorem non_residue_mul_non_residue_is_residue 
[decidable_eq F] {a b : F} (ha : is_non_residue a) (hb : is_non_residue b): 
is_quad_residue (a * b) :=
begin
  obtain ⟨p, inst⟩ := char_p.exists F, -- derive the char p of F
  resetI, -- resets the instance cache
  by_cases hp : p = 2,
  {apply is_quad_residue_of_char_eq_two hp, simp [ha.1, hb.1], assumption},
  by_contra h, -- prove by contradtiction
  -- rw `h` to `is_non_residue (a * b)`
  rw [not_residue_iff_is_non_residue (mul_ne_zero ha.1 hb.1)] at h,
  -- surj : `a * _` is surjective onto non-residues from residues
  have surj := ha.mul_is_surjective hp,
  simp [function.surjective] at surj,
  -- in particular, non-residue `a * b` is in the range of `a * _`
  specialize surj (a * b) h,
  -- say `a * b' = a * b` and `hb' : is_quad_residue b'`
  rcases surj with ⟨b', hb', eq⟩,
  simp [non_residue_mul, ha.1] at eq, -- `eq: b' = b`
  rw [eq] at hb',
  exact absurd hb'.2 hb.2,
end

end quad_residues

/- ## end quad_residues -/

/- ## quad_char -/

section quad_char

variables {F} [decidable_eq F]

/-- `finite_field.quad_char` defines the quadratic character of `a` in a finite field `F`. -/
def quad_char (a : F) : ℚ :=
if a = 0            then 0 else 
if ∃ b : F, a = b^2 then 1 else
                        -1.

notation `χ` := quad_char  -- declare the notation for `quad_char`

@[simp] lemma quad_char_zero_eq_zero : χ (0 : F) = 0 := by simp [quad_char]

@[simp] lemma quad_char_one_eq_one : χ (1 : F) = 1 := 
by {simp [quad_char], intros h, specialize h 1, simp* at *}

@[simp] lemma quad_char_ne_zero_of_ne_zero {a : F} (h : a ≠ 0) : 
χ a ≠ 0 := 
by by_cases (∃ (b : F), a = b ^ 2); simp [quad_char, *] at *

@[simp] lemma quad_char_eq_zero_iff_eq_zero (a : F) :
χ a = 0 ↔ a = 0 :=
begin
  split,
  {contrapose, exact quad_char_ne_zero_of_ne_zero},
  {rintro rfl, exact quad_char_zero_eq_zero}
end

@[simp] lemma quad_char_i_sub_j_eq_zero_iff_i_eq_j (i j : F) : 
χ (i - j) = 0 ↔ i = j := 
by simp [sub_eq_zero]

@[simp] lemma quad_char_eq_one_or_neg_one_of_char_ne_zero {a : F} (h : χ a ≠ 0) : 
(χ a = 1) ∨ (χ a = -1) := 
by by_cases (∃ (b : F), a = b ^ 2); simp [quad_char, *] at *

@[simp] lemma quad_char_eq_neg_one_or_one_of_ne_zero' {a : F} (h : χ a ≠ 0) : 
(χ a = -1) ∨ (χ a = 1) := 
or.swap (quad_char_eq_one_or_neg_one_of_char_ne_zero h)

@[simp] lemma quad_char_eq_one_or_neg_one_of_ne_zero {a : F} (h : a ≠ 0) : 
(χ a = 1) ∨ (χ a = -1) := 
quad_char_eq_one_or_neg_one_of_char_ne_zero (quad_char_ne_zero_of_ne_zero h)

@[simp] lemma quad_char_suqare_eq_one_of_ne_zero {a : F} (h : a ≠ 0) : 
χ a * χ a = 1 := 
by by_cases (∃ (b : F), a = b ^ 2); simp [quad_char, *] at *

@[simp] lemma quad_char_eq_one_of {a : F} (h : a ≠ 0) (h' : ∃ (b : F), a = b ^ 2) : 
χ a = 1 := 
by simp [quad_char, *] at *

@[simp] lemma quad_char_eq_neg_one_of {a : F} (h : a ≠ 0) (h' : ¬ ∃ (b : F), a = b ^ 2) : 
χ a = -1 := 
by simp [quad_char, *] at *

@[simp] lemma quad_char_eq_one_of_quad_residue {a : F} (h : is_quad_residue a) : 
χ a = 1 := quad_char_eq_one_of h.1 h.2

@[simp] lemma quad_char_eq_neg_one_of_non_residue {a : F} (h : is_non_residue a) : 
χ a = -1 := quad_char_eq_neg_one_of h.1 h.2

@[simp] lemma nonzero_quad_char_eq_one_or_neg_one' {a b : F} (h : a ≠ b) : 
(χ (a - b) = 1) ∨ (χ (a - b) = -1) := 
by {have h':= sub_ne_zero.mpr h, simp* at *}

variables {F p}

theorem quad_char_inv (a : F) : χ a⁻¹ = χ a := 
begin
  by_cases ha: a = 0,
  {simp [ha]}, -- case `a=0`
  -- splits into cases if `a` is a residue
  obtain (ga | ga) := residue_or_non_residue ha,
  -- case 1: `a` is a residue
  {have g':= inv_is_residue_iff.2 ga, simp*},
  -- case 2: `a` is a non-residue
  {have g':= inv_is_non_residue_iff.2 ga, simp*},
end

theorem quad_char_mul (a b : F) : χ (a * b) = χ a * χ b :=
begin
  by_cases ha: a = 0,
  any_goals {by_cases hb : b = 0},
  any_goals {simp*}, -- closes cases when `a = 0` or `b =0`
  -- splits into cases if `a` is a residue
  obtain (ga | ga) := residue_or_non_residue ha,
  -- splits into cases if `b` is a residue
  any_goals {obtain (gb | gb) := residue_or_non_residue hb},
  -- case 1 : `a` is, `b` is
  { have g:= residue_mul_residue_is_residue ga gb, simp* },
  -- case 2 : `a` is, `b` is not
  { have g:= residue_mul_non_residue_is_non_residue ga gb, simp* },
  -- case 1 : `a` is not, `b` is
  { have g:= non_residue_mul_residue_is_non_residue ga gb, simp* },
  -- case 4 : `a` is not, `b` is not
  { have g:= non_residue_mul_non_residue_is_residue ga gb, simp* },
end

/-- `χ (-1) = 1` if `q ≡ 1 [MOD 4]`. -/
@[simp] theorem char_neg_one_eq_one_of (hF : q ≡ 1 [MOD 4]) :
χ (-1 : F) = 1 :=
by simp [neg_one_is_residue_of hF]

/-- `χ (-1) = -1` if `q ≡ 3 [MOD 4]`. -/
@[simp] theorem char_neg_one_eq_neg_one_of (hF : q ≡ 3 [MOD 4]) :
χ (-1 : F) = -1 :=
by simp [neg_one_is_non_residue_of hF]

/-- `χ (-i) = χ i` if `q ≡ 1 [MOD 4]`. -/
theorem quad_char_is_sym_of (hF : q ≡ 1 [MOD 4]) (i : F) :
χ (-i) = χ i :=
begin
  have h := char_neg_one_eq_one_of hF, -- h: χ (-1) = 1
  -- χ (-i) = 1 * χ (-i) = χ (-1) * χ (-i) = χ ((-1) * (-i))
  rw [← one_mul (χ (-i)), ← h, ← quad_char_mul], 
  simp,
end 

/-- another form of `quad_char_is_sym_of` -/
theorem quad_char_is_sym_of' (hF : q ≡ 1 [MOD 4]) (i j : F) :
χ (j - i) = χ (i - j) :=
by convert quad_char_is_sym_of hF (i - j); ring

/-- `χ (-i) = - χ i` if `q ≡ 3 [MOD 4]`. -/
theorem quad_char_is_skewsym_of (hF : q ≡ 3 [MOD 4]) (i : F) :
χ (-i) = - χ i :=
begin
  have h := char_neg_one_eq_neg_one_of hF, -- h: χ (-1) = 1
  rw [← neg_one_mul (χ i), ← h, ← quad_char_mul],
  simp, 
end

/-- another form of `quad_char_is_skewsym_of` -/
theorem quad_char_is_skewsym_of' (hF : q ≡ 3 [MOD 4]) (i j : F) :
χ (j - i) = - χ (i - j) :=
by convert quad_char_is_skewsym_of hF (i - j); ring

variable (F) -- use `F` as an explicit parameter

/-- `∑ a : {a : F // a ≠ 0}, χ (a : F) = 0` if `p ≠ 2`. -/
lemma quad_char.sum_in_non_zeros_eq_zero (hp : p ≠ 2):
∑ a : {a : F // a ≠ 0}, χ (a : F) = 0 :=
begin
  simp [fintype.sum_split' (λ a : F, a ≠ 0) (λ a : F, ∃ b, a = b^2)],
  suffices h : 
  ∑ (j : {j // j ≠ 0 ∧ ∃ (b : F), j = b ^ 2}), χ (j : F) =
  ∑ a : {a : F // is_quad_residue a} , 1,
  suffices g :
  ∑ (j : {j // j ≠ 0 ∧ ¬∃ (b : F), j = b ^ 2}), χ (j : F) =
  ∑ a : {a : F // is_non_residue a} , -1,
  simp [h, g, sum_neg_distrib, 
        card_residues_eq_card_non_residues' F hp],
  any_goals
  {apply fintype.sum_congr, intros a, have := a.2, simp* at *},
end

/-- `∑ (a : F), χ a = 0` if `p ≠ 2`. -/
theorem quad_char.sum_eq_zero (hp : p ≠ 2):
∑ (a : F), χ a = 0 :=
by simp [fintype.sum_split (λ b, b = (0 : F)), 
         quad_char.sum_in_non_zeros_eq_zero F hp, default]

variable {F} -- use `F` as an implicit parameter

/-- another form of `quad_char.sum_eq_zero` -/
@[simp] lemma quad_char.sum_eq_zero_reindex_1 (hp : p ≠ 2) {a : F}: 
∑ (b : F), χ (a - b) = 0 :=
begin
  rw ← quad_char.sum_eq_zero F hp,
  refine fintype.sum_equiv ((equiv.sub_right a).trans (equiv.neg _)) _ _ (by simp),
end

/-- another form of `quad_char.sum_eq_zero` -/
@[simp] lemma quad_char.sum_eq_zero_reindex_2 (hp : p ≠ 2) {b : F}:
∑ (a : F), χ (a - b) = 0 :=
begin
  rw ← quad_char.sum_eq_zero F hp,
  refine fintype.sum_equiv (equiv.sub_right b) _ _ (by simp),
end

variable {F} -- use `F` as an implicit parameter

/-- helper of `quad_char.sum_mul'`: reindex the terms in the summation -/
lemma quad_char.sum_mul'_aux {b : F} (hb : b ≠ 0) :
∑ (a : F) in filter (λ (a : F), ¬a = 0) univ, χ (1 + a⁻¹ * b) =
∑ (c : F) in filter (λ (c : F), ¬c = 1) univ, χ (c) :=
begin
  refine finset.sum_bij (λ a ha, 1 + a⁻¹ * b) (λ a ha, _) 
    (λ a ha, rfl) (λ a₁ a₂ h1 h2 h, _) (λ c hc, _),
  { simp at ha, simp* },
  { simp at h1 h2, field_simp at h, rw (mul_right_inj' hb).1 h.symm },
  { simp at hc, use b * (c - 1)⁻¹, 
    simp [*, mul_inv_rev', sub_ne_zero.2 hc] }
end

/-- If `b ≠ 0` and `p ≠ 2`, `∑ a : F, χ (a) * χ (a + b) = -1`. -/
theorem quad_char.sum_mul' {b : F} (hb : b ≠ 0) (hp : p ≠ 2): 
∑ a : F, χ (a) * χ (a + b) = -1 := 
begin
  rw [finset.sum_split _ (λ a, a = (0 : F))],
  simp,
  have h : ∑ (a : F) in filter (λ (a : F), ¬a = 0) univ, χ a * χ (a + b) =
           ∑ (a : F) in filter (λ (a : F), ¬a = 0) univ, χ (1 + a⁻¹ * b),
  { apply finset.sum_congr rfl,
    intros a ha, simp at ha,
    simp [←quad_char_inv a, ←quad_char_mul a⁻¹],
    field_simp },
  rw [h, quad_char.sum_mul'_aux hb],
  have g:= @finset.sum_split _ _ _ (@finset.univ F _) (χ) (λ a : F, a = 1) _,
  simp [quad_char.sum_eq_zero F hp] at g,
  linarith
end

/-- another form of `quad_char.sum_mul'` -/
theorem quad_char.sum_mul {b c : F} (hbc : b ≠ c) (hp : p ≠ 2): 
∑ a : F, χ (b - a) * χ (c - a) = -1 := 
begin
  rw ← quad_char.sum_mul' (sub_ne_zero.2 (ne.symm hbc)) hp,
  refine fintype.sum_equiv ((equiv.sub_right b).trans (equiv.neg _)) _ _ (by simp),
end

end quad_char
/- ## end quad_char -/

end finite_field