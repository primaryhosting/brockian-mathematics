import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the `import` line: Lean 4 requires `import`
commands to come first in a file.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

open Matrix

/-! ## Permanents as counting problems -/

/-- The permanent, written as a sum over permutations of the products `∏ i, M i (σ i)`
(Mathlib's definition uses `∏ i, M (σ i) i`; the two agree). -/

theorem permanent_eq_card_witnesses {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℕ)
    (h : ∀ i j, M i j ≤ 1) :
    M.permanent = Nat.card {σ : Equiv.Perm V // ∀ i, M i (σ i) = 1} := by
  classical
  rw [permanent_eq_sum M, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  by_cases hs : ∀ i, M i (σ i) = 1
  · simp [hs]
  · simp only [hs, if_false]
    push_neg at hs
    obtain ⟨i, hi⟩ := hs
    have hzero : M i (σ i) = 0 := by have := h i (σ i); omega
    exact Finset.prod_eq_zero (Finset.mem_univ i) hzero

/-! ## Simulating nonnegative integer weights by 0/1 entries

Reading a square matrix `W` over `ℕ` as a weighted digraph, `W.permanent` is the total weight of
its cycle covers.  Replacing an edge `i → j` of weight `W i j` by `W i j` parallel two-step paths
through fresh vertices, each fresh vertex carrying a self-loop, produces a *0/1* matrix with the
same permanent.
-/

section Simulation

variable {n : ℕ}

/-- Internal vertices of the gadget: for each pair `(i,j)` we add `W i j` parallel intermediate
vertices. -/
abbrev Idx (W : Matrix (Fin n) (Fin n) ℕ) : Type := Σ p : Fin n × Fin n, Fin (W p.1 p.2)

/-- Vertices of the simulating 0/1 matrix. -/
abbrev Vtx (W : Matrix (Fin n) (Fin n) ℕ) : Type := Fin n ⊕ Idx W

/-- The 0/1 matrix simulating the nonnegative integer matrix `W`. -/
