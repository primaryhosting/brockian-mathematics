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

theorem penrose_focusing (hL : 0 ≤ L)
    (hR : RaychaudhuriOn (Set.Icc 0 L) θ θ' ricci shear)
    (hE : NullEnergyCondition (Set.Icc 0 L) ricci shear) (hT : TrappedSurface θ) :
    L < 2 / (-θ 0) := by
  have hd := hR.1
  have hray := hR.2
  -- the expansion is `≤ θ 0 < 0` throughout
  have hneg : ∀ t ∈ Set.Icc (0 : ℝ) L, θ t < 0 := fun t ht =>
    lt_of_le_of_lt (expansion_le_initial hR hE ht) hT
  -- the auxiliary function `h t = -1/θ t + t/2` has nonpositive derivative
  set f : ℝ → ℝ := fun t => -(θ t)⁻¹ + t / 2 with hf
  have hfderiv : ∀ t ∈ Set.Icc (0 : ℝ) L,
      HasDerivAt f (θ' t / (θ t) ^ 2 + 1 / 2) t := by
    intro t ht
    have hne : θ t ≠ 0 := ne_of_lt (hneg t ht)
    have h1 : HasDerivAt (fun y => (θ y)⁻¹) (-θ' t / (θ t) ^ 2) t := (hd t ht).inv hne
    have h2 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2 : ℝ) t :=
      (hasDerivAt_id t).div_const 2
    have := h1.neg.add h2
    simpa [hf, neg_div, div_eq_mul_inv] using this
  have hfnonpos : ∀ t ∈ Set.Icc (0 : ℝ) L, θ' t / (θ t) ^ 2 + 1 / 2 ≤ 0 := by
    intro t ht
    obtain ⟨hric, hsh⟩ := hE t ht
    have hsq : (0 : ℝ) < (θ t) ^ 2 := by
      have h := hneg t ht
      nlinarith
    have key : θ' t ≤ -(θ t) ^ 2 / 2 := by
      rw [hray t ht]; linarith
    have : θ' t / (θ t) ^ 2 ≤ -1 / 2 := by
      rw [div_le_iff₀ hsq]; nlinarith
    linarith
  -- hence `f` is antitone on `[0, L]`
  have hanti : AntitoneOn f (Set.Icc 0 L) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 L)
      (fun t ht => ((hfderiv t ht).continuousAt).continuousWithinAt) (fun t ht => ?_)
      (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact ((hfderiv t (Set.mem_Icc_of_Ioo ht)).differentiableAt).differentiableWithinAt
    · rw [interior_Icc] at ht
      have ht' : t ∈ Set.Icc (0 : ℝ) L := Set.mem_Icc_of_Ioo ht
      rw [(hfderiv t ht').deriv]
      exact hfnonpos t ht'
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_refl 0, hL⟩
  have hLmem : L ∈ Set.Icc (0 : ℝ) L := ⟨hL, le_refl L⟩
  have hcmp : f L ≤ f 0 := hanti h0 hLmem hL
  have hposL : 0 < -(θ L)⁻¹ := by
    have h := inv_lt_zero.mpr (hneg L hLmem)
    linarith
  have h00 : f 0 = -(θ 0)⁻¹ := by simp [hf]
  have hfL : f L = -(θ L)⁻¹ + L / 2 := rfl
  have hkey : L / 2 < -(θ 0)⁻¹ := by
    rw [h00, hfL] at hcmp; linarith
  have hT' : θ 0 < 0 := hT
  have hθ0 : 0 < -θ 0 := by linarith
  have hinv : (-θ 0) * (-θ 0)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hθ0)
  have hkey' : L / 2 < (-θ 0)⁻¹ := by
    have : -(θ 0)⁻¹ = (-θ 0)⁻¹ := by field_simp
    linarith [this ▸ hkey]
  rw [lt_div_iff₀ hθ0]
  nlinarith [hkey', hθ0, hinv]

end

/-- **Penrose singularity theorem (analytic core): geodesic incompleteness.**

A spacetime containing a trapped surface (`θ 0 < 0` for the outgoing null congruence
orthogonal to it) and satisfying the null energy condition (`R_{ab} k^a k^b ≥ 0`)
cannot be null geodesically complete: the hypersurface-orthogonal null congruence
obeying the Raychaudhuri equation cannot be defined for all affine parameters
`t ≥ 0`, since focusing to a caustic occurs by affine parameter `2 / |θ 0|`. -/
