/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- comment and is repeated as the module docstring below.)

import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
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

namespace QI

open scoped ComplexConjugate

variable {m n : ℕ}

/-- The amplitude matrix of a bipartite pure state, i.e. its coordinates in the product basis. -/

lemma finrank_eigsp {r : ℕ} {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {lam : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (hd : IsSchmidt ψ lam e f) {s : ℝ} (hs : 0 < s) :
    Module.finrank ℂ (eigsp ψ s) = (Finset.univ.filter fun i => lam i = s).card := by
  have he := (orthonormal_iff_coord e).mp hd.2.1
  have hli : LinearIndependent ℂ (fun i : {i : Fin r // lam i = s} =>
      ((e i : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ)) := by
    refine linearIndependent_of_coordOrtho _ fun i j => ?_
    rw [he i j]
    by_cases h : i = j
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun hc => h (Subtype.ext hc))]
  rw [eigsp_eq_span hd hs, finrank_span_eq_card hli, Fintype.card_subtype]

/-! ### Existence -/

/-- An orthonormal eigenbasis of the reduced density matrix of `ψ`. -/
