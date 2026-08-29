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

theorem inner_deriv_add_deriv_inner (hU : IsUnitaryGroup U) {x y dx dy : H}
    (hx : HasDerivAt (fun t : ℝ => U t x) dx 0) (hy : HasDerivAt (fun t : ℝ => U t y) dy 0) :
    inner ℂ x dy + inner ℂ dx y = (0 : ℂ) := by
  have hd := hx.inner ℂ hy
  have hconst : (fun t : ℝ => (inner ℂ (U t x) (U t y) : ℂ)) = fun _ => (inner ℂ x y : ℂ) :=
    funext fun t => hU.inner_map_map t x y
  rw [hconst] at hd
  have := (hasDerivAt_const (0 : ℝ) (inner ℂ x y : ℂ)).unique hd
  simpa [hU.map_zero] using this.symm

/-- The generator is a symmetric (formally self-adjoint) operator. -/
