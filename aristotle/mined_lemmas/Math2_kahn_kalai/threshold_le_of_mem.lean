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

lemma threshold_le_of_mem {F : Finset (Finset α)} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h : 1 / 2 ≤ mu p F) : threshold F ≤ p := by
  refine csInf_le ⟨0, ?_⟩ ⟨hp0, hp1, h⟩
  rintro x ⟨hx, -, -⟩
  exact hx

