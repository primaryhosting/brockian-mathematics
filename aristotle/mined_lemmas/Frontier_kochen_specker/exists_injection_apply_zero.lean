import Mathlib

/-!
# The rays of a three dimensional Kochen–Specker configuration

The 33 rays of a Kochen–Specker configuration in `ℝ³` (coordinates in `{0, ±1, ±√2}`),
together with the auxiliary vectors completing each orthogonal pair to a frame, and the
boolean bookkeeping lemmas used in the case analysis.
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Frontier
namespace KS3

/-- The three dimensional real Hilbert space. -/
abbrev V3 := EuclideanSpace ℝ (Fin 3)


theorem exists_injection_apply_zero {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (k : Fin n) :
    ∃ σ : Fin m → Fin n, Function.Injective σ ∧ σ ⟨0, hm⟩ = k := by
  refine ⟨fun i => Equiv.swap k (Fin.castLE hmn ⟨0, hm⟩) (Fin.castLE hmn i), ?_, by simp⟩
  intro a b hab
  simpa using (Fin.castLE_injective hmn)
    ((Equiv.swap k (Fin.castLE hmn ⟨0, hm⟩)).injective hab)

end KS

/--
Reduction of the Kochen–Specker property from dimension `n` to a smaller dimension `m`.

If a valuation of the forbidden kind exists in dimension `n`, then one exists in every
dimension `m ≤ n` (with `0 < m`): in the standard orthogonal frame of `ℝⁿ` exactly one vector
`e k` is assigned `1`, and any `m`-dimensional coordinate subspace containing `e k` inherits
such a valuation.
-/
