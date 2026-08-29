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

lemma residual_covers_Hfam {h : ℕ} {W : Finset α} :
    Covers (H.image (fun S => S \ W)) (Hfam H h W) := by
  intro T hT
  obtain ⟨S, hS, _, heq⟩ := mem_Hfam_iff.1 hT
  obtain ⟨S', hS', _, heq'⟩ := frag_spec H (W := W) hS
  exact ⟨S' \ W, Finset.mem_image.2 ⟨S', hS', rfl⟩, by rw [← heq', heq]⟩

variable (H)

/-- A choice of an edge of `H` inside `Z`, depending only on `Z`. -/
