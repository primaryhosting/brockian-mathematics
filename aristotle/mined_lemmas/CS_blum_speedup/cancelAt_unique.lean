/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Nat.Partrec Nat.Partrec.Code

namespace CS

deriving instance DecidableEq for Nat.Partrec.Code

/-! ## Blum complexity measures -/

/-- A *Blum complexity measure* for the standard numbering `Nat.Partrec.Code.eval` of the
partial computable functions.  `cost c x` is the amount of resource used by the program `c`
on input `x`.  Blum's two axioms are:

* `dom_eq`: `cost c x` is defined exactly when the program `c` halts on `x`;
* the graph of `cost` is decidable, witnessed here by a computable `Bool`-valued `graph`. -/
structure BlumMeasure where
  cost : Code → ℕ →. ℕ
  graph : Code → ℕ → ℕ → Bool
  graph_computable : Computable fun p : (Code × ℕ) × ℕ => graph p.1.1 p.1.2 p.2
  graph_spec : ∀ c x m, graph c x m = true ↔ m ∈ cost c x
  dom_eq : ∀ c x, (cost c x).Dom ↔ (c.eval x).Dom

/-! ## The step-counting measure -/


theorem cancelAt_unique (hr : Computable r) {i x x' : ℕ}
    (h : true ∈ cancelAt M r (selfCode M hr) i x)
    (h' : true ∈ cancelAt M r (selfCode M hr) i x') : x = x' := by
  obtain ⟨hix, hex, hnx⟩ := cancelAt_mem_true_iff.mp h
  obtain ⟨hix', hex', hnx'⟩ := cancelAt_mem_true_iff.mp h'
  rcases Nat.lt_trichotomy x x' with hlt | heq | hgt
  · exact absurd (Part.mem_unique hex (noElig_spec hnx' x hix hlt)) (by simp)
  · exact heq
  · exact absurd (Part.mem_unique hex' (noElig_spec hnx x' hix' hgt)) (by simp)

/-- Each level agrees with level `0` from some point on. -/
