import Mathlib
/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option grind.warning false

namespace CS

/-! ## Polynomial bounds -/

/-- `PolyBd f` says that `f : ℕ → ℕ` is bounded by a polynomial. -/

theorem size_eqC_le (r : Fin V.rlen → Bool) (i : Fin V.qnum)
    (r' : Fin V.rlen → Bool) (i' : Fin V.qnum) :
    (V.eqC r i r' i').size ≤ V.plen * (8 * V.size + 6) + 1 := by
  have hb : ∀ c ∈ (List.finRange V.plen).map
      (fun j => Circuit.iff (V.posC r i j) (V.posC r' i' j)), c.size ≤ 8 * V.size + 5 := by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨j, _, rfl⟩ := hc
    rw [Circuit.size_iff]
    have h1 := size_posC_le V r i j
    have h2 := size_posC_le V r' i' j
    omega
  have := Circuit.size_bigAnd_le _ _ hb
  simpa [eqC] using this

