/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` to come first in a file, so the header above the import is a plain
block comment and this is the module docstring with the same content.)

Mathlib does not contain Ramsey numbers, so the whole development is built here:
the recursion `R(3,t+1) ≤ t + R(3,t)`, the parity refinement giving `R(3,4) ≤ 9`,
hence `R(3,5) ≤ 14`, and the circulant graph `C₁₃(1,5)` witnessing `R(3,5) > 13`.
-/

set_option maxHeartbeats 2000000

namespace Math

open Finset

/-! ## The Ramsey property -/

/-- `RamseyProp n s t` says that every simple graph on `n` vertices contains either a clique
of size `s` or an independent set of size `t` (equivalently, a clique of size `t` in the
complement).  `R(s,t)` is the least `n` with this property. -/

theorem card_nonNbrIn_lt {A : Finset V} {v : V} {t k : ℕ} (hk : RamseyRel k t) (hv : v ∈ A)
    (htri : ¬ HasTriangleIn G A) (hind : ¬ HasIndepIn G A (t + 1)) :
    (nonNbrIn G A v).card < k := by
  by_contra hle
  push_neg at hle
  have hMA : nonNbrIn G A v ⊆ A := Finset.sdiff_subset
  rcases hk V G (nonNbrIn G A v) hle with h | h
  · exact htri (h.mono hMA)
  · obtain ⟨S, hS, hcard, hindep⟩ := h
    have hvS : v ∉ S := by
      intro hvS
      have := hS hvS
      simp [nonNbrIn] at this
    have hnadj : ∀ x ∈ S, ¬ G.Adj v x := by
      intro x hx
      have := hS hx
      simp only [nonNbrIn, nbrIn, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_filter] at this
      tauto
    refine hind ⟨insert v S, Finset.insert_subset hv (hS.trans hMA), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hvS, hcard]
    · intro x hx y hy hxy
      simp only [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact absurd rfl hxy
        · exact hnadj y hy
      · rcases hy with rfl | hy
        · exact fun h => hnadj x hx h.symm
        · exact hindep x hx y hy hxy

end Neighborhood

/-- The basic Ramsey recursion `R(3,t+1) ≤ t + R(3,t)`. -/
