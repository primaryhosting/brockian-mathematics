/-
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- An instance of the 0/1 permanent problem: a size `n` together with an `n × n`
matrix of bits, viewed equivalently as the adjacency data of a bipartite graph. -/
structure Inst where
  size : ℕ
  edge : Fin size → Fin size → Bool

/-- The 0/1 matrix (over `ℕ`) attached to an instance. -/

theorem parsimoniousReduction_trans {f g h : Inst → ℕ} (hfg : ParsimoniousReduction f g)
    (hgh : ParsimoniousReduction g h) : ParsimoniousReduction f h := by
  obtain ⟨r, ⟨c, hc⟩, hrc⟩ := hfg
  obtain ⟨s, ⟨d, hd⟩, hsd⟩ := hgh
  refine ⟨s ∘ r, ⟨d * c + d, fun I => ?_⟩, fun I => (hrc I).trans (hsd (r I))⟩
  have h1 := hd (r I)
  have h2 := hc I
  calc (s (r I)).size ≤ d * (r I).size + d := h1
    _ ≤ d * (c * I.size + c) + d := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left d h2) d
    _ ≤ (d * c + d) * I.size + (d * c + d) := by ring_nf; omega

/-- The hypotheses used below to speak about a counting class are satisfiable, so the
completeness statement is not vacuous: the class of problems parsimoniously reducible to
counting bipartite perfect matchings is such a class. -/
