/-
/-- `|{a : F // is_quad_residue a}| * 2 = |F| - 1` -/
theorem card_residues_mul_two_eq [decidable_eq F] (hp: p ≠ 2) :
fintype.card {a : F // is_quad_residue a} * 2 = q - 1 :=
by rwa [← card_units, card_units_eq_card_residues_mul_two F hp]
-/

/-
lemma residues_setcard_eq_fintype_card [decidable_eq F] :
set.card {a : F | is_quad_residue a} = fintype.card {a : F // is_quad_residue a} :=
set.to_finset_card {a : F | is_quad_residue a}

lemma non_residues_setcard_eq_fintype_card [decidable_eq F] :
set.card {a : F | is_non_residue a} = fintype.card {a : F // is_non_residue a} :=
set.to_finset_card {a : F | is_non_residue a}

lemma disjoint_residues_non_residues [decidable_eq F] : 
disjoint {a : F | is_quad_residue a} {a : F | is_non_residue a} :=
begin 
  simp [set.disjoint_iff_inter_eq_empty, is_non_residue, is_quad_residue], 
  ext, simp,
  rintros h b rfl _,
  use b,
end

lemma residues_union_non_residues [decidable_eq F] : 
{a : F | is_quad_residue a} ∪ {a : F | is_non_residue a} = {a : F | a ≠ 0} :=
begin
  ext,
  simp [is_non_residue, is_quad_residue, ←and_or_distrib_left],
  intros,
  convert or_not,
  simp,
end 

lemma univ_setcard_split [decidable_eq F] : 
(@set.univ F).card = {a : F | a ≠ 0}.card + ({0} : set F).card :=
set.card_disjoint_union' (disjoint_units_zero F) (units_union_zero F)

lemma zero_setcard_eq_one [decidable_eq F] : ({0} : set F).card = 1 := 
by simp [set.card]

lemma univ_setcard_eq_units_setcard_add_one [decidable_eq F] : 
(@set.univ F).card = {a : F | a ≠ 0}.card + 1 :=
by rw [univ_setcard_split,zero_setcard_eq_one]

lemma units_setcard_split [decidable_eq F] : 
{a : F | a ≠ 0}.card = {a : F | is_quad_residue a}.card + {a : F | is_non_residue a}.card  :=
set.card_disjoint_union' (disjoint_residues_non_residues F) (residues_union_non_residues F)

@[simp] lemma in_residues_sum_one_eq [decidable_eq F] : 
∑ i in {a : F | is_quad_residue a}.to_finset, (1 : ℚ) = {a : F | is_quad_residue a}.card :=
by simp only [set.card, finset.card_eq_sum_ones_ℚ]

@[simp] lemma in_non_residues_sum_neg_one_eq [decidable_eq F] : 
∑ i in {a : F | is_non_residue a}.to_finset, (-1 : ℚ) = - {a : F | is_non_residue a}.card :=
by simp only [set.card, finset.card_eq_sum_ones_ℚ, sum_neg_distrib]
-/

/-
variable {F}

/-- The cardinality of quadratic residues equals that of non-residues. -/
lemma card_residues_eq_card_non_residues_set [decidable_eq F] (hp : p ≠ 2):
{a : F | is_quad_residue a}.card = {a : F | is_non_residue a}.card :=
begin
  have h:= card_residues_mul_two_eq F hp,
  rw [card_eq_set_card_of_univ F, ←residues_setcard_eq_fintype_card, 
      univ_setcard_eq_units_setcard_add_one,  units_setcard_split] at h,
  simp [mul_two, *] at *,
end

/-- `fintype` version of `finite_field.card_residues_eq_card_non_residues_set` . -/
lemma card_residues_eq_card_non_residues_subtpye [decidable_eq F] (hp : p ≠ 2):
fintype.card {a : F // is_quad_residue a} = fintype.card {a : F // is_non_residue a} :=
by rwa [←residues_setcard_eq_fintype_card, ←non_residues_setcard_eq_fintype_card, 
        card_residues_eq_card_non_residues_set hp]

-/

/-
lemma quad_char.sum_in_units_eq_zero (hp : p ≠ 2):
∑ (b : F) in univ.filter (λ b, b ≠ (0 : F)), χ b = 0 :=
begin
  rw [finset.sum_split _ (λ b : F, is_quad_residue b)],
  have h1 : ∑ (j : F) in filter (λ (b : F), is_quad_residue b) (filter (λ (b : F), b ≠ 0) univ), χ j =
            ∑ (j : F) in {a : F | is_quad_residue a}.to_finset, 1,
  { apply finset.sum_congr,
    {ext, split, all_goals {intro h, simp* at *}, use h.1},
    intros x hx,
    simp* at * },
  have h2 : ∑ (j : F) in filter (λ (x : F), ¬is_quad_residue x) (filter (λ (b : F), b ≠ 0) univ), χ j =
            ∑ (j : F) in {a : F | is_non_residue a}.to_finset, -1,
  { apply finset.sum_congr,
    {ext, split, all_goals {intro h, simp [*, is_non_residue, is_quad_residue] at *}},
    intros x hx,
    simp* at * },
  simp at h1 h2,
  simp [h1, h2],      
end

-/