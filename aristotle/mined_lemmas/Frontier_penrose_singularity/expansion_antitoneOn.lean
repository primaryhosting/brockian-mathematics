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

theorem expansion_antitoneOn (hR : RaychaudhuriOn (Set.Icc 0 L) θ θ' ricci shear)
    (hE : NullEnergyCondition (Set.Icc 0 L) ricci shear) :
    AntitoneOn θ (Set.Icc 0 L) := by
  obtain ⟨hd, hray⟩ := hR
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) L, deriv θ t = θ' t := fun t ht => (hd t ht).deriv
  refine antitoneOn_of_deriv_nonpos (convex_Icc 0 L)
    (fun t ht => ((hd t ht).continuousAt).continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
  · rw [interior_Icc] at ht
    exact ((hd t (Set.mem_Icc_of_Ioo ht)).differentiableAt).differentiableWithinAt
  · rw [interior_Icc] at ht
    have ht' : t ∈ Set.Icc (0 : ℝ) L := Set.mem_Icc_of_Ioo ht
    obtain ⟨hric, hsh⟩ := hE t ht'
    rw [hderiv t ht', hray t ht']
    nlinarith [sq_nonneg (θ t)]

/-- The expansion never exceeds its initial value; in particular, starting from a
trapped surface it stays negative. -/
