/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean does not allow a module docstring before the `import` line, so the header above is a
plain block comment; the same header is repeated as a module docstring below.)
-/
import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Stone's theorem: the infinitesimal generator of a strongly continuous one-parameter
unitary group on a complex Hilbert space is self-adjoint (as an unbounded, i.e. partially
defined, operator).
-/

namespace QPhys

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The domain of the infinitesimal generator of a one-parameter group `U`:
the set of vectors `x` for which the orbit map `t ↦ U t x` is differentiable at `0`. -/

lemma hasDerivAt_inner_orbit {y : H} (hy : y ∈ (generator U).adjoint.domain)
    {x : H} (hx : x ∈ generatorDomain U) (t : ℝ) :
    HasDerivAt (fun t : ℝ => inner ℂ (U t x) y)
      (Complex.I * inner ℂ (U t x) ((generator U).adjoint ⟨y, hy⟩)) t := by
  set z : H := (generator U).adjoint ⟨y, hy⟩ with hzdef
  have h1 : HasDerivAt (fun t : ℝ => U t x) (U t (orbitDeriv U x)) t :=
    hasDerivAt_orbit U hUadd hx t
  have h2 := h1.inner ℂ (hasDerivAt_const t y)
  have hUtx : U t x ∈ generatorDomain U := (orbit_mem_domain U hUadd hx t).1
  have hgen : generator U ⟨U t x, hUtx⟩ = U t (Complex.I • orbitDeriv U x) := by
    show Complex.I • orbitDeriv U (U t x) = _
    rw [(orbit_mem_domain U hUadd hx t).2, map_smul]
  have hkey := inner_generator_adjoint U hU0 hUadd hUcont hy ⟨U t x, hUtx⟩
  rw [hgen, map_smul, inner_smul_left, Complex.conj_I] at hkey
  have hI : (Complex.I : ℂ) * Complex.I = -1 := Complex.I_mul_I
  have h3 : inner ℂ (U t (orbitDeriv U x)) y = Complex.I * inner ℂ (U t x) z := by
    linear_combination Complex.I * hkey + (inner ℂ (U t (orbitDeriv U x)) y : ℂ) * hI
  simpa [h3] using h2

include hU0 hUadd hUnorm hUcont in
/-- Integrated form of the differential identity. -/
