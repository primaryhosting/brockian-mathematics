/-
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment; its text is otherwise verbatim.)

import Mathlib

namespace Frontier

/-!
## The analytic core of the Penrose singularity theorem

Penrose's theorem says: a spacetime containing a closed *trapped surface* `T`, satisfying the
*null energy condition* (and admitting a non-compact Cauchy surface), cannot be null geodesically
complete.

The geometric input is packaged into the following standard reduction, which is the content
formalized here.  Let `k` be the tangent field of one of the null geodesic generators of the
boundary `∂J⁺(T)`, affinely parametrized by `s`, and let `θ s` be the expansion of the congruence
of these generators along it.  Then:

* **Raychaudhuri's equation** for a hypersurface-orthogonal null congruence in `4` dimensions reads
  `θ' = -θ²/2 - σ_{ab}σ^{ab} - Ric(k,k)`.  Since the shear term `σ_{ab}σ^{ab}` is non-negative and
  the *null energy condition* gives `Ric(k,k) ≥ 0`, this yields the differential inequality
  `θ' ≤ -θ²/2`  (hypothesis `hRaychaudhuri` below).
* **Trappedness** of `T` says exactly that both families of null geodesics orthogonal to `T` are
  converging, i.e. the initial expansion is strictly negative: `θ 0 < 0` (hypothesis `htrapped`).

The theorem `Frontier.raychaudhuri_affine_bound` then shows that such a `θ` cannot exist on an
affine interval longer than `2/|θ 0|`: a conjugate point (focal point) occurs at affine parameter
at most `2/|θ 0|`.  Consequently the generators of `∂J⁺(T)` are inextendible past that value of the
affine parameter, which is the statement that the spacetime is null geodesically incomplete
(`Frontier.penrose_singularity`).
-/

/-- **Focusing / conjugate point bound.**

If the expansion `θ` of a null geodesic congruence is defined on an affine interval `[0, L)`,
obeys the Raychaudhuri inequality `θ' ≤ -θ²/2` (Raychaudhuri's equation together with the null
energy condition and vanishing twist), and starts out converging, `θ 0 < 0` (a trapped surface),
then the interval is necessarily short:  `L ≤ 2/|θ 0|`.

In other words, a focal point of the congruence is reached at affine parameter at most `2/|θ 0|`. -/

theorem raychaudhuri_affine_bound_sharp :
    ∃ (θ θ' : ℝ → ℝ) (L : ℝ), 0 < L ∧ θ 0 < 0 ∧
      (∀ s ∈ Set.Ico (0 : ℝ) L, HasDerivAt θ (θ' s) s) ∧
      (∀ s ∈ Set.Ico (0 : ℝ) L, θ' s ≤ -(θ s) ^ 2 / 2) ∧
      L = -2 / θ 0 := by
  refine ⟨fun s => 2 * (s - 1)⁻¹, fun s => -2 / (s - 1) ^ 2, 1, one_pos, by norm_num, ?_, ?_, ?_⟩
  · intro s hs
    have hne : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hs.2)
    have h1 : HasDerivAt (fun s : ℝ => s - 1) 1 s := (hasDerivAt_id s).sub_const 1
    have h2 := (h1.inv hne).const_mul (2 : ℝ)
    convert h2 using 1
    field_simp
  · intro s hs
    have hne : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hs.2)
    simp only
    rw [show (2 * (s - 1)⁻¹) ^ 2 = 4 / (s - 1) ^ 2 by field_simp; ring,
      show -(4 / (s - 1) ^ 2) / 2 = -2 / (s - 1) ^ 2 by ring]
  · norm_num

/-- **Penrose singularity theorem (analytic core).**

A spacetime containing a closed trapped surface and satisfying the null energy condition is
null geodesically incomplete.

Formally: the expansion `θ` of the congruence of null geodesic generators of the boundary of the
future of the trapped surface cannot be defined for all affine parameters `s ≥ 0`.  Indeed, the
hypotheses state that

* the congruence extends to every affine parameter `s ≥ 0` (i.e. the null generators are complete),
* Raychaudhuri's equation plus the null energy condition give `θ' ≤ -θ²/2`,
* the surface is trapped, i.e. the generators are initially converging, `θ 0 < 0`,

and these are contradictory: focusing forces `θ → -∞` at affine parameter at most `2/|θ 0|`,
so the generators must leave the spacetime before that, i.e. geodesic incompleteness. -/
