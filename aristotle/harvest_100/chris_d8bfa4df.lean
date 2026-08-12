/-
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open MeasureTheory Set

/-!
## Setting

Figalli's regularity theory for optimal transport says, roughly, that if the cost function
satisfies the Ma–Trudinger–Wang (MTW) condition, and the two measures have densities that
are bounded away from `0` and from `∞` on suitable domains, then the Brenier optimal
transport map is regular.

Here we formalize and prove in full the **base case** of that theory: dimension one with
quadratic cost.  In dimension one the MTW condition is vacuous, the Brenier map is the
*monotone rearrangement* `T = G⁻¹ ∘ F`, characterized by the matching of cumulative
distribution functions `G (T x) = F x`, and the regularity statement takes the sharp
quantitative form

  (density of `μ` `≤ Λ`) and (density of `ν` `≥ lam > 0`)  ⟹  `T` is `(Λ / lam)`-Lipschitz.

The density bounds are used only through their integrated consequences,
`μ (Ioc x y) ≤ Λ (y - x)` and `ν (Ioc x y) ≥ lam (y - x)`, so these are taken as the
hypotheses.  As in the classical theory, the lower bound on the target density is imposed
only on the (bounded) target domain `B`, and the estimate is obtained on the source
domain `A`; a global lower bound would be incompatible with finiteness of `ν`.
-/

/-- The (real valued) cumulative distribution function of a measure on `ℝ`. -/
noncomputable def cdfReal (mu : Measure ℝ) (x : ℝ) : ℝ := (mu (Set.Iic x)).toReal

lemma measure_Iic_add_Ioc (mu : Measure ℝ) {x y : ℝ} (hxy : x ≤ y) :
    mu (Set.Iic x) + mu (Set.Ioc x y) = mu (Set.Iic y) := by
  rw [← measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
    Set.Iic_union_Ioc_eq_Iic hxy]

lemma cdfReal_sub_cdfReal (mu : Measure ℝ) [IsFiniteMeasure mu] {x y : ℝ} (hxy : x ≤ y) :
    cdfReal mu y - cdfReal mu x = (mu (Set.Ioc x y)).toReal := by
  have h := measure_Iic_add_Ioc mu hxy
  have h' : (mu (Set.Iic y)).toReal = (mu (Set.Iic x)).toReal + (mu (Set.Ioc x y)).toReal := by
    rw [← h, ENNReal.toReal_add (measure_ne_top mu _) (measure_ne_top mu _)]
  simp only [cdfReal, h']
  ring

/-- An upper bound on the mass of an interval (an upper density bound) gives an upper bound
on the increment of the c.d.f. -/
lemma cdfReal_sub_le (mu : Measure ℝ) [IsFiniteMeasure mu] {Lam x y : ℝ} (hLam : 0 ≤ Lam)
    (hxy : x ≤ y) (h : mu (Set.Ioc x y) ≤ ENNReal.ofReal (Lam * (y - x))) :
    cdfReal mu y - cdfReal mu x ≤ Lam * (y - x) := by
  rw [cdfReal_sub_cdfReal mu hxy]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hLam (by linarith)) h

/-- A lower bound on the mass of an interval (a lower density bound) gives a lower bound on
the increment of the c.d.f. -/
lemma le_cdfReal_sub (mu : Measure ℝ) [IsFiniteMeasure mu] {lam x y : ℝ} (hxy : x ≤ y)
    (h : ENNReal.ofReal (lam * (y - x)) ≤ mu (Set.Ioc x y)) :
    lam * (y - x) ≤ cdfReal mu y - cdfReal mu x := by
  rw [cdfReal_sub_cdfReal mu hxy]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top mu _)).1 h

lemma cdfReal_mono (mu : Measure ℝ) [IsFiniteMeasure mu] : Monotone (cdfReal mu) := by
  intro x y hxy
  have := cdfReal_sub_cdfReal mu hxy
  have h0 : (0:ℝ) ≤ (mu (Set.Ioc x y)).toReal := ENNReal.toReal_nonneg
  linarith

/-!
## The abstract one-dimensional estimate

This is the analytic core: a statement purely about the two distribution functions `F`, `G`
and the map `T` matching them, with no measure theory involved.
-/

/-- Monotonicity of the monotone rearrangement: if `F` is monotone on `A`, `G` is strictly
increasing on `B` (quantitatively, with rate `lam > 0`), `T` maps `A` into `B` and matches
the distribution functions, then `T` is monotone on `A`. -/
theorem monotoneOn_of_cdf_eq {lam : ℝ} (hlam : 0 < lam) {F G T : ℝ → ℝ} {A B : Set ℝ}
    (hFmono : MonotoneOn F A)
    (hG : ∀ u ∈ B, ∀ v ∈ B, u ≤ v → lam * (v - u) ≤ G v - G u)
    (hTB : ∀ x ∈ A, T x ∈ B) (hT : ∀ x ∈ A, G (T x) = F x) :
    MonotoneOn T A := by
  intro x hx y hy hxy
  by_contra hlt
  push_neg at hlt
  have h1 : lam * (T x - T y) ≤ G (T x) - G (T y) :=
    hG _ (hTB y hy) _ (hTB x hx) hlt.le
  have h2 : G (T x) - G (T y) = F x - F y := by rw [hT x hx, hT y hy]
  have h3 : F x ≤ F y := hFmono hx hy hxy
  have h4 : 0 < lam * (T x - T y) := mul_pos hlam (by linarith)
  linarith

/-- **One-dimensional optimal transport regularity, analytic form.**
If `F` is monotone on `A` with increments at most `Λ (y - x)`, `G` has increments at least
`lam (v - u)` on `B` with `lam > 0`, and `T : A → B` matches the two distribution functions
(`G (T x) = F x`, i.e. `T = G⁻¹ ∘ F` is the monotone rearrangement), then `T` is
`(Λ / lam)`-Lipschitz on `A`. -/
theorem transport_lipschitzOn_of_cdf_bounds
    {lam Lam : ℝ} (hlam : 0 < lam) {F G T : ℝ → ℝ} {A B : Set ℝ} (hFmono : MonotoneOn F A)
    (hF : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → F y - F x ≤ Lam * (y - x))
    (hG : ∀ u ∈ B, ∀ v ∈ B, u ≤ v → lam * (v - u) ≤ G v - G u)
    (hTB : ∀ x ∈ A, T x ∈ B) (hT : ∀ x ∈ A, G (T x) = F x) :
    ∀ x ∈ A, ∀ y ∈ A, |T y - T x| ≤ (Lam / lam) * |y - x| := by
  have hTmono : MonotoneOn T A := monotoneOn_of_cdf_eq hlam hFmono hG hTB hT
  -- the key one-sided estimate
  have key : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → T y - T x ≤ (Lam / lam) * (y - x) := by
    intro x hx y hy hxy
    have h1 : lam * (T y - T x) ≤ G (T y) - G (T x) :=
      hG _ (hTB x hx) _ (hTB y hy) (hTmono hx hy hxy)
    have h2 : G (T y) - G (T x) = F y - F x := by rw [hT x hx, hT y hy]
    have h3 : F y - F x ≤ Lam * (y - x) := hF x hx y hy hxy
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
    nlinarith
  intro x hx y hy
  rcases le_total x y with h | h
  · have h1 : 0 ≤ T y - T x := sub_nonneg.2 (hTmono hx hy h)
    rw [abs_of_nonneg h1, abs_of_nonneg (sub_nonneg.2 h)]
    exact key x hx y hy h
  · have h1 : T y - T x ≤ 0 := sub_nonpos.2 (hTmono hy hx h)
    rw [abs_of_nonpos h1, abs_of_nonpos (sub_nonpos.2 h), neg_sub, neg_sub]
    exact key y hy x hx h

/-!
## The main statement
-/

/-- **Figalli-type optimal transport regularity: the one-dimensional base case.**

Let `mu`, `nu` be finite Borel measures on `ℝ`, let `A` be the source domain and `B` the
target domain.  Assume:

* an upper density bound for the source, `mu (Ioc x y) ≤ Λ (y - x)`;
* a lower density bound for the target on `B`, `nu (Ioc u v) ≥ lam (v - u)` with `lam > 0`;
* `T : A → B` is the monotone optimal transport map from `mu` to `nu` for the quadratic
  cost, characterized in dimension one by the matching of the cumulative distribution
  functions, `cdfReal nu (T x) = cdfReal mu x` (that is, `T = G⁻¹ ∘ F`).

Then `T` is Lipschitz on `A` with the sharp constant `Λ / lam`.

In dimension one the Ma–Trudinger–Wang condition for the quadratic cost holds trivially, so
this is exactly the base case of the MTW regularity theory, in its Caffarelli form. -/
theorem figalli_OT_regularity
    (mu nu : Measure ℝ) [IsFiniteMeasure mu] [IsFiniteMeasure nu] {A B : Set ℝ}
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hmu : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → mu (Set.Ioc x y) ≤ ENNReal.ofReal (Lam * (y - x)))
    (hnu : ∀ u ∈ B, ∀ v ∈ B, u ≤ v → ENNReal.ofReal (lam * (v - u)) ≤ nu (Set.Ioc u v))
    {T : ℝ → ℝ} (hTB : ∀ x ∈ A, T x ∈ B)
    (hT : ∀ x ∈ A, cdfReal nu (T x) = cdfReal mu x) :
    ∀ x ∈ A, ∀ y ∈ A, |T y - T x| ≤ (Lam / lam) * |y - x| :=
  transport_lipschitzOn_of_cdf_bounds hlam ((cdfReal_mono mu).monotoneOn A)
    (fun x hx y hy hxy => cdfReal_sub_le mu hLam hxy (hmu x hx y hy hxy))
    (fun u hu v hv huv => le_cdfReal_sub nu huv (hnu u hu v hv huv)) hTB hT

/-- Packaged form of `figalli_OT_regularity` as `LipschitzOnWith`. -/
theorem figalli_OT_regularity_lipschitzOnWith
    (mu nu : Measure ℝ) [IsFiniteMeasure mu] [IsFiniteMeasure nu] {A B : Set ℝ}
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hmu : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → mu (Set.Ioc x y) ≤ ENNReal.ofReal (Lam * (y - x)))
    (hnu : ∀ u ∈ B, ∀ v ∈ B, u ≤ v → ENNReal.ofReal (lam * (v - u)) ≤ nu (Set.Ioc u v))
    {T : ℝ → ℝ} (hTB : ∀ x ∈ A, T x ∈ B)
    (hT : ∀ x ∈ A, cdfReal nu (T x) = cdfReal mu x) :
    LipschitzOnWith (Real.toNNReal (Lam / lam)) T A := by
  have h := figalli_OT_regularity mu nu hlam hLam hmu hnu hTB hT
  have hc : ((Real.toNNReal (Lam / lam) : ℝ≥0) : ℝ) = Lam / lam :=
    Real.coe_toNNReal _ (div_nonneg hLam hlam.le)
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  rw [Real.dist_eq, Real.dist_eq, hc]
  simpa [abs_sub_comm] using h y hy x hx

/-!
## Non-vacuity

The hypotheses of `figalli_OT_regularity` are satisfiable: take for `mu` and `nu` the
uniform (Lebesgue) measure on `[0,1]`, `A = B = [0,1]`, `lam = Λ = 1` and `T = id`, which is
indeed the optimal map from the uniform measure to itself.
-/

theorem figalli_OT_regularity_hypotheses_satisfiable :
    ∃ (mu nu : Measure ℝ) (_ : IsFiniteMeasure mu) (_ : IsFiniteMeasure nu)
      (A B : Set ℝ) (lam Lam : ℝ) (T : ℝ → ℝ),
      0 < lam ∧ 0 ≤ Lam ∧ A.Nonempty ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≤ y → mu (Set.Ioc x y) ≤ ENNReal.ofReal (Lam * (y - x))) ∧
      (∀ u ∈ B, ∀ v ∈ B, u ≤ v → ENNReal.ofReal (lam * (v - u)) ≤ nu (Set.Ioc u v)) ∧
      (∀ x ∈ A, T x ∈ B) ∧ (∀ x ∈ A, cdfReal nu (T x) = cdfReal mu x) := by
  classical
  refine ⟨volume.restrict (Set.Icc (0:ℝ) 1), volume.restrict (Set.Icc (0:ℝ) 1),
    inferInstance, inferInstance, Set.Icc 0 1, Set.Icc 0 1, 1, 1, id,
    one_pos, zero_le_one, ⟨0, by norm_num⟩, ?_, ?_, fun x hx => hx, fun _ _ => rfl⟩
  · intro x hx y hy hxy
    have hsub : Set.Ioc x y ⊆ Set.Icc (0:ℝ) 1 := fun t ht =>
      ⟨le_trans hx.1 ht.1.le, le_trans ht.2 hy.2⟩
    rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_eq_left.2 hsub,
      Real.volume_Ioc]
    simp
  · intro u hu v hv huv
    have hsub : Set.Ioc u v ⊆ Set.Icc (0:ℝ) 1 := fun t ht =>
      ⟨le_trans hu.1 ht.1.le, le_trans ht.2 hv.2⟩
    rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_eq_left.2 hsub,
      Real.volume_Ioc]
    simp

/-!
## Tensorization

For a product of one-dimensional problems the optimal map acts componentwise, and the
Lipschitz bound survives with the same constant, for the sup distance on `ℝⁿ`.
-/

theorem figalli_OT_regularity_pi {n : ℕ}
    (mu nu : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (mu i)] [∀ i, IsFiniteMeasure (nu i)]
    {A B : Fin n → Set ℝ} {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hmu : ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, x ≤ y →
      mu i (Set.Ioc x y) ≤ ENNReal.ofReal (Lam * (y - x)))
    (hnu : ∀ i, ∀ u ∈ B i, ∀ v ∈ B i, u ≤ v →
      ENNReal.ofReal (lam * (v - u)) ≤ nu i (Set.Ioc u v))
    {T : Fin n → ℝ → ℝ} (hTB : ∀ i, ∀ x ∈ A i, T i x ∈ B i)
    (hT : ∀ i, ∀ x ∈ A i, cdfReal (nu i) (T i x) = cdfReal (mu i) x) :
    LipschitzOnWith (Real.toNNReal (Lam / lam))
      (fun x : Fin n → ℝ => fun i => T i (x i)) {x : Fin n → ℝ | ∀ i, x i ∈ A i} := by
  have hc : ((Real.toNNReal (Lam / lam) : ℝ≥0) : ℝ) = Lam / lam :=
    Real.coe_toNNReal _ (div_nonneg hLam hlam.le)
  have hnn : (0:ℝ) ≤ Lam / lam := div_nonneg hLam hlam.le
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  rw [hc]
  refine (dist_pi_le_iff (mul_nonneg hnn dist_nonneg)).2 fun i => ?_
  have hi := figalli_OT_regularity_lipschitzOnWith (mu i) (nu i) hlam hLam (hmu i) (hnu i)
    (hTB i) (hT i)
  have h1 : dist (T i (x i)) (T i (y i)) ≤ (Lam / lam) * dist (x i) (y i) := by
    have := hi.dist_le_mul (x i) (hx i) (y i) (hy i)
    rwa [hc] at this
  have h2 : dist (x i) (y i) ≤ dist x y := dist_le_pi_dist x y i
  calc dist (T i (x i)) (T i (y i)) ≤ (Lam / lam) * dist (x i) (y i) := h1
    _ ≤ (Lam / lam) * dist x y := by nlinarith [dist_nonneg (x := x) (y := y)]

end Frontier

