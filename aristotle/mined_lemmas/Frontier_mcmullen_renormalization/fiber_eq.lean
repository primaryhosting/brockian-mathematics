/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
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

namespace Frontier

/-! ## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard; the basic object of McMullen's work on
renormalization) is a holomorphic proper degree-two branched cover `f : U → V`
between open subsets of `ℂ` with `U` compactly contained in `V`.  The
degree-two condition is encoded concretely below: there is one critical value,
whose fiber is a single point, and every other value has exactly two
preimages. -/

/-- The quadratic family `z ↦ z ^ 2 + c`. -/

lemma fiber_eq {w s : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) R) (hs : s ^ 2 = w - c) :
    {z ∈ qmap c ⁻¹' Metric.ball (0 : ℂ) R | qmap c z = w} = ({s, -s} : Set ℂ) := by
  have hmem : ∀ z : ℂ, qmap c z = w → z ∈ qmap c ⁻¹' Metric.ball (0 : ℂ) R := by
    intro z hz; simpa [Set.mem_preimage, hz] using hw
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, hz⟩
    have h2 : (z - s) * (z + s) = 0 := by
      simp only [qmap] at hz; linear_combination hz - hs
    rcases mul_eq_zero.1 h2 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  · have hval : qmap c s = w := by simp only [qmap]; linear_combination hs
    have hval' : qmap c (-s) = w := by simp only [qmap]; linear_combination hs
    rintro (rfl | rfl)
    · exact ⟨hmem _ hval, hval⟩
    · exact ⟨hmem _ hval', hval'⟩

/-- The quadratic map `z ↦ z ^ 2 + c` is quadratic-like from
`qmap c ⁻¹' ball 0 R` onto `ball 0 R`, whenever `2 ≤ R` and `‖c‖ < R`. -/
