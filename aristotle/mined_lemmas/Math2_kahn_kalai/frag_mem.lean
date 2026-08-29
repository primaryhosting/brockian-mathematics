import Mathlib
import RequestProject.KahnKalai.Iteration

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Expectation and threshold are within a log factor: a formalisation of the Park–Pham proof
of the Kahn–Kalai conjecture.
-/

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `p`-biased measure of a family of subsets. -/

lemma frag_mem {W S : Finset α} (hS : S ∈ H) : frag H W S ∈ cand H W S := by
  have h := cand_nonempty H (W := W) hS
  rw [frag, dif_pos h]
  exact (Finset.exists_min_image (cand H W S) Finset.card h).choose_spec.1

