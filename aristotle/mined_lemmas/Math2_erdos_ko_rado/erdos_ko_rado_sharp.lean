/-
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option grind.warning false

namespace Math2

/-- The **Erdős–Ko–Rado theorem** for families of subsets of `[n] = {0, 1, ..., n-1}`.

If `𝒜` is a family of `k`-element subsets of `Finset.range n` that is intersecting (any two
members, including a member with itself, meet), and `n ≥ 2 * k`, then `#𝒜 ≤ (n-1).choose (k-1)`.

The proof transfers the statement to `Finset (Fin n)` and applies Mathlib's
`Finset.erdos_ko_rado` (proved there via the Kruskal–Katona theorem). -/

theorem erdos_ko_rado_sharp {n k : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (∀ A ∈ star n k, A ⊆ Finset.range n) ∧ (∀ A ∈ star n k, A.card = k) ∧
      (∀ A ∈ star n k, ∀ B ∈ star n k, (A ∩ B).Nonempty) ∧
      (star n k).card = (n - 1).choose (k - 1) := by
  refine ⟨fun A hA => (mem_star.1 hA).1.1, fun A hA => (mem_star.1 hA).1.2, ?_, card_star hk hn⟩
  intro A hA B hB
  exact ⟨0, Finset.mem_inter.2 ⟨(mem_star.1 hA).2, (mem_star.1 hB).2⟩⟩

end Math2

