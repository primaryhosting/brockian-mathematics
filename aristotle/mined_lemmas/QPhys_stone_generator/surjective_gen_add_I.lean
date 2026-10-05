import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set Filter Topology Complex
open scoped LinearPMap

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space `H`:
a family `U : ℝ → (H →L[ℂ] H)` with `U 0 = 1`, `U (s + t) = U s ∘ U t`, each `U t` norm
preserving (hence unitary, since the group law provides the inverse `U (-t)`), and such that
`t ↦ U t x` is continuous for every `x` (strong continuity). -/
structure IsUnitaryGroup (U : ℝ → H →L[ℂ] H) : Prop where
  map_zero : U 0 = 1
  map_add : ∀ s t, U (s + t) = (U s).comp (U t)
  norm_map : ∀ t x, ‖U t x‖ = ‖x‖
  continuous_apply : ∀ x, Continuous fun t => U t x

omit [CompleteSpace H] in
/-- Sanity check that the hypotheses are satisfiable: the constant family `U t = 1` is a
strongly continuous one-parameter unitary group. -/

theorem surjective_gen_add_I {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) (y : H) :
    ∃ x : genDomain U, gen U x + I • (x : H) = y := by
  obtain ⟨x, hx⟩ := stone_resolvent hU y
  obtain ⟨hxd, hgen⟩ := mem_genDomain_of_hasDerivAt hx
  refine ⟨(-I) • ⟨x, hxd⟩, ?_⟩
  rw [LinearPMap.map_smul, hgen]
  have hc : ((((-I) • (⟨x, hxd⟩ : genDomain U)) : genDomain U) : H) = (-I) • x := rfl
  rw [hc, smul_smul, smul_smul, smul_sub]
  rw [show (-I) * (-I) = -1 by simp [Complex.I_mul_I],
    show I * -I = 1 by simp [Complex.I_mul_I]]
  module

