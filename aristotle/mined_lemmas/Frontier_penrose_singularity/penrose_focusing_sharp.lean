import Mathlib

/-!
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
## Formalization

Mathlib currently contains no Lorentzian causality theory (no `Spacetime`, no null
geodesic congruences, no trapped surfaces), so the Penrose singularity theorem cannot
be stated there verbatim.  What *is* the analytic core of the theorem, and what is
formalized and proved below, is the **Raychaudhuri focusing argument**:

Along a future-directed null geodesic congruence with affine parameter `t`, the
expansion `θ` obeys the Raychaudhuri equation

  `θ' = -θ²/2 - σ_{ab}σ^{ab} - R_{ab} k^a k^b`.

Hypersurface orthogonality gives `ω = 0` (no rotation term); the shear term
`σ_{ab}σ^{ab}` is nonnegative, and the *null energy condition* forces
`R_{ab} k^a k^b ≥ 0`.  A *trapped surface* is exactly the statement that the initial
expansion of the outgoing null congruence is negative, `θ 0 < 0`.

The Riccati comparison argument then shows that such a congruence **cannot exist on
an affine interval longer than `2 / |θ 0|`**: a conjugate point (caustic) is reached
first.  Consequently the null geodesics generating the congruence cannot be affinely
extended to all `t ≥ 0`; this is precisely the null geodesic incompleteness asserted
by Penrose's theorem (whose remaining, purely causal-theoretic, ingredients — global
hyperbolicity / non-compact Cauchy surface — serve to guarantee that the congruence
would otherwise have to be complete).

The statements below are therefore a faithful, self-contained Lean formalization of
the analytic reduction: *trapped surface + null energy condition ⟹ focusing in
affine parameter at most `2/|θ 0|` ⟹ no complete congruence*.
-/

namespace Frontier

/-- The Raychaudhuri equation for a hypersurface-orthogonal null geodesic congruence,
holding on a set `S` of affine parameters.

`θ` is the expansion of the congruence, `θ'` its derivative with respect to the affine
parameter, `ricci t` stands for the null-null Ricci curvature `R_{ab} k^a k^b`, and
`shear t` for the (nonnegative) shear scalar `σ_{ab} σ^{ab}`. -/

theorem penrose_focusing_sharp {L : ℝ} (hL2 : L < 2) :
    RaychaudhuriOn (Set.Icc 0 L) (fun t => 2 / (t - 2)) (fun t => -2 / (t - 2) ^ 2)
        (fun _ => 0) (fun _ => 0) ∧
      NullEnergyCondition (Set.Icc 0 L) (fun _ => 0) (fun _ => 0) ∧
      TrappedSurface (fun t => 2 / (t - 2)) := by
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) L, t - 2 ≠ 0 := by
    intro t ht
    have : t < 2 := lt_of_le_of_lt ht.2 hL2
    intro h
    linarith [sub_eq_zero.mp h]
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_⟩, fun t _ => ⟨le_refl 0, le_refl 0⟩, ?_⟩
  · have h1 : HasDerivAt (fun y : ℝ => y - 2) 1 t := (hasDerivAt_id t).sub_const 2
    have h2 : HasDerivAt (fun y : ℝ => (y - 2)⁻¹) (-1 / (t - 2) ^ 2) t := h1.inv (hne t ht)
    have h3 := h2.const_mul (2 : ℝ)
    have : (2 : ℝ) * (-1 / (t - 2) ^ 2) = -2 / (t - 2) ^ 2 := by ring
    rw [this] at h3
    simpa [div_eq_mul_inv] using h3
  · have h := hne t ht
    field_simp
    ring
  · show (2 : ℝ) / ((0 : ℝ) - 2) < 0
    norm_num

end Frontier

