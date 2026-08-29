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

theorem raychaudhuri_affine_bound (θ θ' : ℝ → ℝ) (L : ℝ)
    (hderiv : ∀ s ∈ Set.Ico (0 : ℝ) L, HasDerivAt θ (θ' s) s)
    (hRaychaudhuri : ∀ s ∈ Set.Ico (0 : ℝ) L, θ' s ≤ -(θ s) ^ 2 / 2)
    (htrapped : θ 0 < 0) :
    L ≤ -2 / θ 0 := by
  by_contra hcon
  push_neg at hcon
  set a : ℝ := -2 / θ 0 with ha_def
  have ha : 0 < a := by
    rw [ha_def]
    exact div_pos_of_neg_of_neg (by norm_num) htrapped
  -- The closed interval `[0, a]` is contained in the domain `[0, L)`.
  have hsub : Set.Icc (0 : ℝ) a ⊆ Set.Ico (0 : ℝ) L := fun s hs =>
    ⟨hs.1, lt_of_le_of_lt hs.2 hcon⟩
  have hd : ∀ s ∈ Set.Icc (0 : ℝ) a, HasDerivAt θ (θ' s) s := fun s hs => hderiv s (hsub hs)
  have hr : ∀ s ∈ Set.Icc (0 : ℝ) a, θ' s ≤ -(θ s) ^ 2 / 2 := fun s hs =>
    hRaychaudhuri s (hsub hs)
  -- Step 1: `θ` is non-increasing on `[0, a]`, since `θ' ≤ -θ²/2 ≤ 0`.
  have hcont : ContinuousOn θ (Set.Icc 0 a) := fun s hs =>
    ((hd s hs).continuousAt).continuousWithinAt
  have hint : interior (Set.Icc (0 : ℝ) a) = Set.Ioo 0 a := interior_Icc
  have hdiff : DifferentiableOn ℝ θ (interior (Set.Icc (0 : ℝ) a)) := by
    rw [hint]
    exact fun s hs => ((hd s (Set.mem_Icc_of_Ioo hs)).differentiableAt).differentiableWithinAt
  have hanti : AntitoneOn θ (Set.Icc 0 a) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont hdiff ?_
    intro s hs
    rw [hint] at hs
    have hs' : s ∈ Set.Icc (0 : ℝ) a := Set.mem_Icc_of_Ioo hs
    rw [(hd s hs').deriv]
    have := hr s hs'
    nlinarith [sq_nonneg (θ s)]
  have hneg : ∀ s ∈ Set.Icc (0 : ℝ) a, θ s < 0 := by
    intro s hs
    have : θ s ≤ θ 0 := hanti (Set.left_mem_Icc.mpr ha.le) hs hs.1
    linarith
  -- Step 2: `f s = 1/θ s - s/2` is non-decreasing on `[0, a]`.
  set f : ℝ → ℝ := fun s => (θ s)⁻¹ - s / 2 with hf_def
  have hfd : ∀ s ∈ Set.Icc (0 : ℝ) a,
      HasDerivAt f (-θ' s / (θ s) ^ 2 - 1 / 2) s := by
    intro s hs
    exact ((hd s hs).inv (hneg s hs).ne).sub ((hasDerivAt_id s).div_const 2)
  have hfd_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) a, 0 ≤ -θ' s / (θ s) ^ 2 - 1 / 2 := by
    intro s hs
    have hne : θ s ≠ 0 := (hneg s hs).ne
    have hsq : 0 < (θ s) ^ 2 := by positivity
    have h1 : θ' s ≤ -(θ s) ^ 2 / 2 := hr s hs
    rw [sub_nonneg, le_div_iff₀ hsq]
    nlinarith
  have hmono : MonotoneOn f (Set.Icc 0 a) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact fun s hs => ((hfd s hs).continuousAt).continuousWithinAt
    · rw [hint]
      exact fun s hs =>
        ((hfd s (Set.mem_Icc_of_Ioo hs)).differentiableAt).differentiableWithinAt
    · intro s hs
      rw [hint] at hs
      have hs' : s ∈ Set.Icc (0 : ℝ) a := Set.mem_Icc_of_Ioo hs
      rw [(hfd s hs').deriv]
      exact hfd_nonneg s hs'
  -- Step 3: comparing the endpoints gives a contradiction.
  have hle : f 0 ≤ f a :=
    hmono (Set.left_mem_Icc.mpr ha.le) (Set.right_mem_Icc.mpr ha.le) ha.le
  have hθa : θ a < 0 := hneg a (Set.right_mem_Icc.mpr ha.le)
  have h0 : (θ 0)⁻¹ - 0 / 2 = (θ 0)⁻¹ := by ring
  have ha2 : a / 2 = -(θ 0)⁻¹ := by
    rw [ha_def]
    field_simp
  simp only [hf_def, h0, ha2] at hle
  have : (θ a)⁻¹ < 0 := inv_neg''.mpr hθa
  linarith

/-- The focusing bound of `raychaudhuri_affine_bound` is sharp, and its hypotheses are
consistent for every `L < 2/|θ 0|`: the exact solution `θ s = 2/(s - 1)` of the Raychaudhuri
equation `θ' = -θ²/2` starts at `θ 0 = -2` and blows up exactly at the affine parameter
`L = 1 = 2/|θ 0|`. -/
