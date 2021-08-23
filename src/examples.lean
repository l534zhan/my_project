import tactic.gptf
import data.matrix.basic
import data.complex.basic
import field_theory.finite.basic

section sec1

lemma irrelevant (P : Prop) (pf1 pf2 : P) : pf1 = pf2 := by simp

universe u
variable a : Type u 
#check a  -- prints `a : Type u`

#check unit
#check punit --universe polymorphic version H i₁ i₂ α β γ  Prop, ℕ, ℤ, ℚ, ℝ, ℕ → ℕ, ...

#check ℕ → ℕ

#check 2 -- prints `2 : ℕ` as Lean view `2` as a natural number by default
#check (2 : ℚ) -- prints `2 : ℚ` if we claim the given `2` is a rational number
#check 2 + 3  -- prints `2 + 3 : ℕ`

def f (x : ℕ) := 2 * x  -- this defines a function
#check f  -- prints `f : ℕ → ℕ`

#check (4, 5) -- prints `(4, 5) : ℕ × ℕ`, 
              -- where `×` is the notation of the operation `prod`

#check ℕ -- prints `ℕ : Type`
#check ℕ × ℚ -- prints `ℕ × ℚ : Type`
#check bool -- prints `bool : Type`

def p := 2 + 3 = 5 -- defines `p` to be the statement `2 + 3 = 5`
#check p  -- prints `p : Prop`

lemma pf : p := by simp [p] -- this constructs `pf1` as a proof of `p`
#check pf  -- prints `pf : p`

#check Type -- Type : Type 1
#check Type 1 -- Type 1 : Type 2
-- ...

variables α : Type* -- declares variables `α`
variable β : Type 2 -- declares variables `b`

#check α -- prints `α : Type u_1`
#check β -- prints `β : Type 2`

#check list  -- prints `list : Type u_1 → Type u_1`, 
             -- where `u_1` is a variable ranging over type levels
#check list ℕ  -- prints `list ℕ : Type`
#check list α -- prints `list α : Type u_1`

#check prod -- prints `prod : Type u_3 → Type u_4 → Type (max u_3 u_4)`
#check ℕ × ℕ -- prints `ℕ × ℕ : Type`
#check ℕ × β -- prints `ℕ × β : Type 2`
#check α × β -- prints `α × β : Type (max u_1 2)`


namespace foo -- declares we are working in the namespace `foo`

-- Now, we are working in the namespace `foo`

def b : ℕ := 10
def f (x : ℕ) : ℕ := x + 5
def fb : ℕ := f b

namespace bar -- declares we are working in the namespace `bar`

-- Now, we are working in the namespace `foo.bar`

def ffb : ℕ := f (f b)

#check fb
#check ffb

end bar

-- Now, we back to the namespace `foo`

#check fb
-- `#check ffb` will reports error: unknown identifier 'ffb'.
#check bar.ffb

end foo

#check foo.fb
#check foo.bar.ffb

namespace foo -- We can redo `namespace foo`.
def g (x : ℕ) : ℕ := b + 5
#check g
end foo

-- #check g -- error
#check foo.g

open foo -- `open foo` allows us to use the shorter name `name` 
         -- for any identifier in form `foo.name`,
         -- but if we declare an identifier `g` after `open foo`,
         -- `g`'s full name is `g`, not `foo.g`.

#check g
#check bar.ffb

-- a term-style proof
lemma pf1 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
and.intro hp (and.intro hq hp)

#check and.intro -- prints `and.intro : ?M_1 → ?M_2 → ?M_1 ∧ ?M_2`,
                 -- where `?M_1` and `?M_2` denotes indeterminate variables

-- a tactic-style proof
lemma pf2 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin -- the `begin ... end` block allows us to write a list of tactics
  split, -- splits the goal `p ∧ q ∧ p` into two goals `p` and `q ∧ p`
  -- the first goal is `p` 
  -- I.e. Lean expects us to provide an expression of type `p`
  exact hp, -- provides an exact proof term `hp`
            -- this closes the first goal as `hp` has type `p`
  split, -- splits `q ∧ p` into `q` and `p`
  exact hq, -- provides an exact proof term `hq`
  exact hp, -- provides an exact proof term `hp`
end

-- mix
lemma pf3 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
  split,
  exact hp, -- `hp` is a proof term
  exact and.intro hq hp -- `and.intro hq hp` is a proof term
end

#check int.of_nat

#check rat.of_int --ℤ

variables m n : ℕ
variables i : ℤ
variables j : ℚ
#check i + m -- i + ↑m : ℤ
#check i + m + n -- i + ↑m + ↑n : Z
#check j + i + m -- j + ↑i + ↑m : ℚ

-- #check m + i -- error
#check ↑m + i -- ↑m + i : ℤ
#check ↑(m + n) + i -- ↑(m + n) + i : ℤ
#check ↑m + ↑n + i -- ↑m + ↑n + i : ℤ
#check ↑i + ↑m + j -- ↑i + ↑m + j : ℚ  β

instance my_coe : has_coe ℝ ℂ := ⟨λ r, ⟨r, 0⟩⟩
variables (r : ℝ) (c : ℂ)
#check c + r -- c + ↑r : ℂ

end sec1

section str
-- the following is the definition of `prod` in mathlib
--structure prod (α : Type u) (β : Type v) := -- round brackets mark parameters explicitly supplied by the user
--(fst : α) (snd : β)
#check prod -- prod : Type u_1 → Type u_2 → Type (max u_1 u_2)

variables α β : Type*
#check prod α β -- α × β : Type (max u_1 u_2)
                -- α × β is a new type and itself has type Type (max u_1 u_2)

variables (a : α) (b : β)

#check prod.mk a b -- (a, b) : α × β
#check (⟨a, b⟩ : prod α β) -- (a, b) : α × β
#check (a, b) -- (a, b) : α × β

#check prod.fst -- prod.fst : ?M_1 × ?M_2 → ?M_1
#reduce prod.fst (10, 20) -- 10
#reduce (10, 20).1 -- 10

#check prod.snd -- prod.snd : ?M_1 × ?M_2 → ?M_2
#reduce prod.snd (10, 20) -- 20
#reduce (10, 20).2 -- 20

structure my_str := -- a new structure with thtree fields
(f1 : ℕ) (f2 : ℕ) (f3 : ℕ)

variables n : ℕ 
-- defines `triple n` to be `⟨n, n + n, n + n + n⟩`
def triple : my_str := ⟨n, n + n, n + n + n⟩ 

#check triple n -- triple n : my_str
#reduce (triple n).1 -- n
#reduce (triple n).2 -- n.add n
#reduce (triple n).3 -- (n.add n).add n
#reduce my_str.f3 (triple 5) -- 15
#reduce (triple 5).3 -- 15

end str

#check has_add 

-- class has_add (α : Type u) := (add : α → α → α)

#check nat.has_add -- nat.has_add : has_add ℕ

-- We construt an element `my_inst` of `has_add ℕ`.
def my_inst : has_add ℕ := ⟨nat.add⟩ -- `nat.add` is a function defined in mathlib
-- Next, we declare `my_inst` to be an instance of `has_add ℕ`.
attribute [instance] my_inst

-- @[instance] def my_inst : has_add ℕ := ⟨nat.add⟩ 
-- instance my_inst : has_add ℕ := ⟨nat.add⟩ 

instance my_inst' : has_add (ℕ × ℕ):= ⟨λ ⟨a, b⟩ ⟨c, d⟩, ⟨a + c, b + c⟩⟩

--variables α : Type*
--instance my_inst'' : has_add (α × α):= ⟨λ ⟨a, b⟩ ⟨c, d⟩, ⟨a + c, b + c⟩⟩ 

/-
/-- `finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements.
  `finset.nodup` is the poof that `finset.val` has no duplicate elements. -/
structure finset (α : Type*) :=
(val : multiset α)
(nodup : nodup val)

/-- `fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof `complete` that everything of type `α` is in the list. -/
class fintype (α : Type*) :=
(elems [] : finset α)
(complete : ∀ x : α, x ∈ elems)
-/

open matrix

--variables (I α : Type*) [fintype I] [has_one α]
--#check (1 : I → α)

#check diagonal

variables (I α : Type*) [fintype I]
variables [decidable_eq I] [has_zero α] [has_one α]
#check matrix.has_one
#check (1 : matrix I I α)

#check semigroup

/-
class has_one      (α : Type u) := (one : α)

class has_mul      (α : Type u) := (mul : α → α → α)

class semigroup (G : Type u) extends has_mul G :=
(mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))

class mul_one_class (M : Type u) extends has_one M, has_mul M :=
(one_mul : ∀ (a : M), 1 * a = a)
(mul_one : ∀ (a : M), a * 1 = a)

class monoid (M : Type u) extends semigroup M, mul_one_class M :=
(npow : ℕ → M → M := npow_rec)
(npow_zero' : ∀ x, npow 0 x = 1 . try_refl_tac)
(npow_succ' : ∀ (n : ℕ) x, npow n.succ x = x * npow n x . try_refl_tac)
-/

/-
lemma simple {a : ℕ} (h : a ∣ 4) : a = 1 ∨ a = 2 ∨ a = 4 :=
begin
  dec_trivial
end
-/

example (a : ℕ) (h : a > 0) : a = a - 1 + 1 := by rw nat.sub_add_cancel h

-- rw fintype.card_eq,
example {F : Type*} [fintype F] [has_zero F] [decidable_eq F] : 
fintype.card {a : F // a = 0} = 1 := 
begin
  simp [fintype.card_eq_one_iff],
  /-
  have h: fintype.card {a : F // a = 0} = fintype.card ({0} : set F),
  { rw fintype.card_eq,
    have eq : {a:F // a = 0} ≃ ({0} : set F), 
    { refine {..},
      exact λ a : {a:F // a = 0}, by tidy,
      exact λ a : ({0} : set F), by tidy,
      tidy,
      
    },
    exact ⟨eq⟩,},
  simp [h],
  -/
end


