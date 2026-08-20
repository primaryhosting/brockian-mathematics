/-
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` before any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- **Kramers degeneracy.**

Setting: a finite-dimensional complex Hilbert space `H` (the state space), a Hamiltonian
`Ham : H →ₗ[ℂ] H` which is self-adjoint, and a time-reversal operator `T : H → H` which is
*antiunitary* (additive, conjugate-homogeneous, and `⟪T x, T y⟫ = ⟪y, x⟫`) and satisfies
`T ∘ T = -id`.  The condition `T² = -1` is exactly the half-integer-spin case
(for integer spin one has `T² = +1`).  Time-reversal invariance of the dynamics is the
commutation `T ∘ Ham = Ham ∘ T`.

Conclusion: for every eigenvector `v ≠ 0` with eigenvalue `μ`, the Kramers partner `T v` is an
eigenvector for the *same* eigenvalue and is orthogonal to `v`; consequently every eigenvalue of
`Ham` has an eigenspace of dimension at least `2`, i.e. all levels are (at least) doubly
degenerate. -/
theorem kramers_degeneracy
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (T : H → H) (Ham : H →ₗ[ℂ] H)
    (hTadd : ∀ x y, T (x + y) = T x + T y)
    (hTsmul : ∀ (c : ℂ) (x : H), T (c • x) = (starRingEnd ℂ) c • T x)
    (hTinner : ∀ x y, inner ℂ (T x) (T y) = inner ℂ y x)
    (hTsq : ∀ x, T (T x) = -x)
    (hHsa : ∀ x y, inner ℂ (Ham x) y = inner ℂ x (Ham y))
    (hcomm : ∀ x, T (Ham x) = Ham (T x))
    (μ : ℂ) (v : H) (hv : v ≠ 0) (hEv : Ham v = μ • v) :
    Ham (T v) = μ • T v ∧ inner ℂ v (T v) = 0 ∧
      2 ≤ Module.finrank ℂ (Module.End.eigenspace Ham μ) := by
  -- `T` sends `0` to `0`.
  have hT0 : T 0 = 0 := by
    have := hTadd 0 0
    simpa using this.symm
  -- The Kramers partner is nonzero.
  have hTv : T v ≠ 0 := by
    intro h
    apply hv
    have : T (T v) = 0 := by rw [h, hT0]
    rw [hTsq v] at this
    simpa using this
  -- Orthogonality of `v` and `T v`, forced by `T² = -1`.
  have horth : inner ℂ (T v) v = (0 : ℂ) := by
    have h1 : inner ℂ (T v) (T (T v)) = inner ℂ (T v) v := hTinner v (T v)
    rw [hTsq v, inner_neg_right] at h1
    linear_combination (-1/2 : ℂ) * h1
  have horth' : inner ℂ v (T v) = (0 : ℂ) := by
    have := congrArg (starRingEnd ℂ) horth
    rwa [inner_conj_symm, map_zero] at this
  -- The eigenvalue is real (self-adjointness).
  have hμ : (starRingEnd ℂ) μ = μ := by
    have h1 : inner ℂ (Ham v) v = inner ℂ v (Ham v) := hHsa v v
    rw [hEv, inner_smul_left, inner_smul_right] at h1
    have hvv : inner ℂ v v ≠ (0 : ℂ) := by
      simpa [inner_self_eq_zero] using hv
    exact mul_right_cancel₀ hvv h1
  -- `T v` is an eigenvector with the same eigenvalue.
  have hpartner : Ham (T v) = μ • T v := by
    have := hcomm v
    rw [hEv, hTsmul, hμ] at this
    exact this.symm
  refine ⟨hpartner, horth', ?_⟩
  -- `v` and `T v` are linearly independent, and both lie in the eigenspace.
  have hli : LinearIndependent ℂ ![v, T v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : inner ℂ v (s • v + t • T v) = (0 : ℂ) := by rw [hst, inner_zero_right]
    have h2 : inner ℂ (T v) (s • v + t • T v) = (0 : ℂ) := by rw [hst, inner_zero_right]
    rw [inner_add_right, inner_smul_right, inner_smul_right, horth'] at h1
    rw [inner_add_right, inner_smul_right, inner_smul_right, horth] at h2
    have hvv : inner ℂ v v ≠ (0 : ℂ) := by simpa [inner_self_eq_zero] using hv
    have hTvTv : inner ℂ (T v) (T v) ≠ (0 : ℂ) := by simpa [inner_self_eq_zero] using hTv
    constructor
    · have : s * inner ℂ v v = 0 := by linear_combination h1
      exact (mul_eq_zero.mp this).resolve_right hvv
    · have : t * inner ℂ (T v) (T v) = 0 := by linear_combination h2
      exact (mul_eq_zero.mp this).resolve_right hTvTv
  have hspan : Submodule.span ℂ (Set.range ![v, T v]) ≤ Module.End.eigenspace Ham μ := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact Module.End.mem_eigenspace_iff.mpr hEv
    · exact Module.End.mem_eigenspace_iff.mpr hpartner
  have hcard : Module.finrank ℂ (Submodule.span ℂ (Set.range ![v, T v])) = 2 := by
    simpa using finrank_span_eq_card hli
  calc (2 : ℕ) = Module.finrank ℂ (Submodule.span ℂ (Set.range ![v, T v])) := hcard.symm
    _ ≤ Module.finrank ℂ (Module.End.eigenspace Ham μ) := Submodule.finrank_mono hspan

end Phys

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

