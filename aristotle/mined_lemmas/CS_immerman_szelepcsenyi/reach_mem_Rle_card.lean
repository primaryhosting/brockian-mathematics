import RequestProject.Machine

/-!
# The inductive counting construction

Given a nondeterministic branching program we build, by Immerman and Szelepcsényi's
inductive counting method, a nondeterministic branching program of polynomially larger
size accepting exactly the complementary language.
-/

namespace CS

namespace Compl

variable {n : ℕ} (P : Setup n)

/-! ### The invariant -/

variable (x : Fin n → Bool)

/-- The set of configurations of the original machine reachable in at most `i` steps. -/

theorem reach_mem_Rle_card [Fintype V] {y : V} (h : Relation.ReflTransGen E st y) :
    y ∈ Rle E st (Fintype.card V - 1) := by
  classical
  set N := Fintype.card V with hN
  have hNpos : 1 ≤ N := Fintype.card_pos_iff.mpr ⟨st⟩
  have hstab : ∃ i, i ≤ N - 1 ∧ Rle E st (i + 1) = Rle E st i := by
    by_contra hcon
    push_neg at hcon
    have hne : ∀ k, k < N - 1 → Rle E st k ≠ Rle E st (k + 1) := by
      intro k hk hEq
      exact hcon k (le_of_lt hk) hEq.symm
    have hcard : (N - 1) + 1 ≤ (Rle E st (N - 1)).ncard := Rle_ncard_ge E st hne
    have huniv : Rle E st (N - 1) = Set.univ := by
      have hu : (Set.univ : Set V).ncard = N := by
        simp [Set.ncard_univ, Nat.card_eq_fintype_card, ← hN]
      have hle : (Set.univ : Set V).ncard ≤ (Rle E st (N - 1)).ncard := by omega
      exact Set.eq_of_subset_of_ncard_le (Set.subset_univ _) hle (Set.toFinite _)
    have hfix : Rle E st (N - 1 + 1) = Rle E st (N - 1) := by
      refine Set.Subset.antisymm ?_ (Rle_subset_succ E st _)
      rw [huniv]; exact Set.subset_univ _
    exact hcon (N - 1) le_rfl hfix
  obtain ⟨i, hi, hstab⟩ := hstab
  obtain ⟨m, hm⟩ := exists_mem_Rle E st h
  have h1 : Rle E st (max m i) = Rle E st i := Rle_stable E st hstab _ (le_max_right _ _)
  have h2 : y ∈ Rle E st i := h1 ▸ (Rle_mono E st (le_max_left m i) hm)
  exact Rle_mono E st hi h2

end

end CS

import Mathlib
import RequestProject.Basic
import RequestProject.Reach
import RequestProject.Complement

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above has to follow the `import` lines: Lean 4 requires `import`
commands to come first in a module.)

`NL` is formalized as the class of languages decided by polynomial-size families of
nondeterministic branching programs — the configuration graphs of nondeterministic
machines using logarithmic work space, where a single step inspects one bit of the
input.  `coNL` is the class of complements of languages in `NL`.  The theorem
`CS.immerman_szelepcsenyi` states `NL = coNL`.

The mathematical content is the explicit inductive counting construction
`CS.NBP.exists_complement`: from any nondeterministic branching program `B` one builds a
nondeterministic branching program of size at most `10 * (B.size + 1) ^ 8` accepting
exactly the inputs rejected by `B`.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- A polynomial bound on the size of the complementing machine. -/
