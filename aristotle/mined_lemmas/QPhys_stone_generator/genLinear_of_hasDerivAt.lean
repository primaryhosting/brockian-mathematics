/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Stone's theorem: the generator of a strongly continuous one-parameter unitary group

Let `H` be a complex Hilbert space and let `U : ℝ → H →L[ℂ] H` be a strongly continuous
one-parameter unitary group, i.e. `U 0 = 1`, `U (s + t) = U s * U t`, every `U t` is unitary,
and `t ↦ U t x` is continuous for every `x`.

The *generator* of `U` is the (in general unbounded) operator `A` whose domain consists of the
vectors `x` for which `t ↦ U t x` is differentiable at `0`, and which is given there by
`A x = -I • (d/dt)|_{t = 0} (U t x)`, so that formally `U t = exp (I * t * A)`.

The main result, `QPhys.stone_generator`, is that `A` is self-adjoint as a partially defined
operator (`LinearPMap`).

The proof follows the classical argument:

* `A` is symmetric, by differentiating `t ↦ ⟪U t x, U t y⟫`;
* `A ± I` are surjective, using the resolvent `x ↦ ∫ t in Ioi 0, exp (-t) • U t x`;
* consequently the domain of `A` is dense, and every symmetric operator with `A ± I` surjective
  is self-adjoint.
-/

open MeasureTheory Set

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The domain of the (infinitesimal) generator of a one-parameter family `U : ℝ → H →L[ℂ] H`:
the set of vectors `x` for which `t ↦ U t x` is differentiable at `0`. -/

theorem genLinear_of_hasDerivAt {U : ℝ → H →L[ℂ] H} {x : H} (hx : x ∈ genDomain U) {d : H}
    (h : HasDerivAt (fun t : ℝ => U t x) d 0) :
    genLinear U ⟨x, hx⟩ = -Complex.I • d := by
  show -Complex.I • genDeriv U ⟨x, hx⟩ = _
  rw [genDeriv_eq ⟨x, hx⟩ h]

/-- The generator of a strongly continuous one-parameter unitary group, as an unbounded
(partially defined) operator. -/
