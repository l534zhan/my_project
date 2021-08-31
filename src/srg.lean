import main2
import combinatorics.simple_graph.adj_matrix
import combinatorics.simple_graph.strongly_regular

/-!
# Strong regular graphs

This file attempts to construct strong regular graphs from
regular symmetric Hadamard matrices with constant diagonal (RSHCD).

-/

set_option pp.beta true

variables {α I R V : Type*} 
variables [fintype V] [fintype I] -- [semiring R]

open matrix simple_graph fintype finset

open_locale big_operators matrix

local notation `n` := (fintype.card V : ℚ)

namespace matrix

class adj_matrix 
[mul_zero_one_class α] [nontrivial α]
(A : matrix I I α) : Prop :=
(zero_or_one [] : ∀ i j, (A i j) = 0 ∨ (A i j) = 1 . obviously)
(sym [] : A.is_sym . obviously)
(loopless [] : ∀ i, A i i = 0 . obviously)

lemma is_sym_of_adj_matrix 
[semiring R] (G : simple_graph I) [decidable_rel G.adj] : 
(G.adj_matrix R).is_sym := transpose_adj_matrix G 

instance is_adj_matrix_of_adj_matrix
[semiring R] [nontrivial R] (G : simple_graph I) [decidable_rel G.adj] : 
adj_matrix (G.adj_matrix R) := 
{ zero_or_one := λ i j, by by_cases G.adj i j; simp*,
  sym := is_sym_of_adj_matrix G,
  loopless := λ i, by simp }

#check compl_adj

def compl 
[mul_zero_one_class α] [nontrivial α] [decidable_eq α] [decidable_eq V] 
(A : matrix V V α) [adj_matrix A] : matrix V V α :=
λ i j, ite (i = i) 0 (ite (A i j = 0) 1 0)

@[simp]
lemma diag_ne_one_of_adj_matrix 
[mul_zero_one_class α] [nontrivial α]
(A : matrix V V α) [c : adj_matrix A] (i : V) :
A i i ≠ 1 := 
by simp [c.loopless]

def to_graph 
[mul_zero_one_class α] [nontrivial α] [decidable_eq α]
(A : matrix V V α) [c : adj_matrix A]:
simple_graph V :=
{ adj := λ i j, ite (A i j = 1) true false,
  sym := λ i j h, by simp only [c.sym.apply' i j]; convert h,
  loopless := λ i, by simp }

instance 
[mul_zero_one_class α] [nontrivial α] [decidable_eq α]
(A : matrix V V α) [c : adj_matrix A] : 
decidable_rel A.to_graph.adj := 
by {simp [to_graph], apply_instance}

#check is_regular_of_degree

lemma to_graph_is_SRG_of
[non_assoc_semiring α] [nontrivial α] [decidable_eq α] [decidable_eq V]
(A : matrix V V α) [adj_matrix A] {k l m : ℕ}
(eq₁ : A ⬝ (𝟙 : matrix V V α) = k • 𝟙)
(eq₂ : A ⬝ A = k • 1 + l • A + m • A.compl): 
is_SRG_of A.to_graph (card I) k l m := sorry

-------------------------------------------------------------------------------

class RSHCD (H : matrix I I ℚ) extends Hadamard_matrix H : Prop := 
(regular [] : ∀ i j, ∑ b, H i b = ∑ a, H a j)
(sym [] : H.is_sym)
(const_diag [] : ∀ i j, H i i = H i j)

namespace RSHCD

def diag [inhabited I] (H : matrix I I ℚ) [RSHCD H] : ℚ :=
H (default I) (default I)

lemma regular_row 
(H : matrix I I ℚ) [RSHCD H] (a b : I) :
∑ j : I, H a j = ∑ j : I, H b j  := 
by rw [regular H a a, regular H b a]

def row_sum [inhabited I] (H : matrix I I ℚ) [RSHCD H] : ℚ :=
∑ j : I, H (default I) j 

@[simp] lemma eq_row_sum 
[inhabited I] (H : matrix I I ℚ) [RSHCD H] (i : I) : 
∑ j : I, H i j = ∑ j : I, H (default I) j  :=
regular_row  H i (default I)

def to_adj [inhabited V] (H : matrix V V ℚ) [RSHCD H] : 
matrix V V ℚ :=
((1 : ℚ) / 2) • (𝟙 - (diag H) • H)

def to_adj_eq₁
[inhabited V] (H : matrix V V ℚ) [RSHCD H] : 
(to_adj H) ⬝ (𝟙 : matrix V V ℚ) = 
((n - (diag H) * (row_sum H)) / 2) • 𝟙 := 
begin
  have : (n - (diag H) * (row_sum H)) / 2 = 
         ((1 : ℚ) / 2) * (n - (diag H) * (row_sum H)) := by field_simp,
  rw[this], ext i j,
  simp [matrix.mul, all_one, to_adj, row_sum, ←finset.mul_sum],
  congr,
end

end RSHCD

open RSHCD

instance [inhabited V] (H : matrix V V ℚ) [RSHCD H] : 
adj_matrix (to_adj H) := {..}

def to_graph_of_RSHD [inhabited V] (H : matrix V V ℚ) [RSHCD H] : 
simple_graph V := (to_adj H).to_graph

instance adj.decidable_rel'
[inhabited V] (H : matrix V V ℚ) [RSHCD H] : 
decidable_rel H.to_graph_of_RSHD.adj :=
by simp [to_graph_of_RSHD]; apply_instance

lemma to_graph_is_SRG_of_RSHD
[inhabited V] [decidable_eq V] (H : matrix V V ℚ) [RSHCD H] : 
is_SRG_of H.to_graph_of_RSHD sorry sorry sorry sorry := sorry

end matrix


#check transpose_adj_matrix
#check simple_graph
#check adj_matrix
#check from_rel
#check is_SRG_of
#check is_regular_of_degree
