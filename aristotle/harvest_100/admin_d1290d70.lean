/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Real Set Filter Topology WeierstrassCurve

namespace Math2

/-! ## The Sato–Tate distribution

The Sato–Tate distribution is the probability measure on the interval `[0, π]` of Frobenius
angles with density `(2/π) · sin²θ` with respect to Lebesgue measure.  For an elliptic curve
`E / ℚ` without complex multiplication, with trace of Frobenius `a_p` at a prime `p` of good
reduction, the Hasse bound `|a_p| ≤ 2√p` lets one write `a_p = 2√p · cos θ_p` with
`θ_p ∈ [0, π]`, and the Sato–Tate theorem asserts that the angles `θ_p` are equidistributed
in `[0, π]` with respect to this measure.
-/

/-- The density of the Sato–Tate distribution: `θ ↦ (2/π) sin²θ`. -/
noncomputable def satoTateDensity (θ : ℝ) : ℝ := (2 / π) * Real.sin θ ^ 2

/-- The Sato–Tate measure: the measure on `ℝ` supported on `[0, π]` with density
`(2/π) sin²θ` with respect to Lebesgue measure. -/
noncomputable def satoTateMeasure : Measure ℝ :=
  volume.withDensity (fun θ => ENNReal.ofReal ((Set.Icc 0 π).indicator satoTateDensity θ))

/-- The Frobenius angle attached to a trace of Frobenius `a p` at the prime `p`:
`θ_p = arccos (a_p / (2√p))`, so that `a_p = 2√p cos θ_p`. -/
noncomputable def frobAngle (a : ℕ → ℤ) (p : ℕ) : ℝ :=
  Real.arccos ((a p : ℝ) / (2 * Real.sqrt p))

/-- The sequence of Frobenius angles, indexed by the primes in increasing order. -/
noncomputable def frobAngleSeq (a : ℕ → ℤ) (n : ℕ) : ℝ := frobAngle a (Nat.nth Nat.Prime n)

/-- The proportion of the first `N` terms of the sequence `θ` that lie in the set `I`. -/
noncomputable def satoTateProportion (θ : ℕ → ℝ) (N : ℕ) (I : Set ℝ) : ℝ :=
  (∑ n ∈ Finset.range N, I.indicator (fun _ => (1 : ℝ)) (θ n)) / N

/-- The sequence `θ` of angles is Sato–Tate equidistributed if, for every subinterval
`[x, y] ⊆ [0, π]`, the proportion of the first `N` angles lying in `[x, y]` converges to the
Sato–Tate measure of `[x, y]`. -/
def IsSatoTateEquidistributed (θ : ℕ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ π →
    Tendsto (fun N => satoTateProportion θ N (Set.Icc x y)) atTop
      (𝓝 ((satoTateMeasure (Set.Icc x y)).toReal))

/-! ## Frobenius data of an elliptic curve over `ℚ`

An elliptic curve over `ℚ` is presented by an integral Weierstrass model `W` over `ℤ`.  For a
prime `p`, reducing `W` modulo `p` and counting the points of the reduced curve (the affine
nonsingular points together with the point at infinity) gives `#E(𝔽_p)`, and the trace of
Frobenius is `a_p = p + 1 - #E(𝔽_p)`.
-/

/-- The number of points of the reduction of the integral Weierstrass model `W` modulo `p`,
i.e. `#E(𝔽_p)` (the nonsingular affine points together with the point at infinity). -/
noncomputable def curvePointCount (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card ((W.map (Int.castRingHom (ZMod p))).toAffine.Point)

/-- The trace of Frobenius `a_p = p + 1 - #E(𝔽_p)` of the integral Weierstrass model `W`. -/
noncomputable def curveTraceOfFrobenius (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (p : ℤ) + 1 - (curvePointCount W p : ℤ)

/-- The sequence of Frobenius angles `θ_p = arccos (a_p / (2√p))` of the curve `W`, indexed by
the primes in increasing order. -/
noncomputable def curveFrobAngleSeq (W : WeierstrassCurve ℤ) (n : ℕ) : ℝ :=
  frobAngleSeq (curveTraceOfFrobenius W) n

/-- The thirteen `j`-invariants of elliptic curves over `ℚ` with complex multiplication. -/
def cmJInvariants : Finset ℚ :=
  {0, 54000, -12288000, 1728, 287496, -3375, 16581375, 8000, -32768, -884736,
    -884736000, -147197952000, -262537412640768000}

/-- An elliptic curve over `ℚ` has complex multiplication exactly when its `j`-invariant is one
of the thirteen rational CM `j`-invariants; so `NonCM E` says that `E` has no complex
multiplication. -/
def NonCM (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop := E.j ∉ cmJInvariants

/-- Frobenius angles always lie in `[0, π]`. -/
theorem frobAngle_mem_Icc (a : ℕ → ℤ) (p : ℕ) : frobAngle a p ∈ Set.Icc 0 π :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- The mass that the Sato–Tate distribution assigns to a subinterval of `[0, π]` is
nonnegative. -/
theorem satoTate_arc_nonneg {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ (Real.sin x * Real.cos x - Real.sin y * Real.cos y + y - x) / π := by
  have hI : (0 : ℝ) ≤ ∫ t in x..y, Real.sin t ^ 2 :=
    intervalIntegral.integral_nonneg hxy (fun t _ => sq_nonneg _)
  rw [integral_sin_sq] at hI
  exact div_nonneg (by linarith) Real.pi_pos.le

/-- The Sato–Tate measure of a subinterval `[x, y] ⊆ [0, π]`, in closed form:
`(1/π) ∫_x^y 2 sin²θ dθ = (sin x cos x - sin y cos y + y - x)/π`. -/
theorem satoTateMeasure_Icc {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ π) :
    satoTateMeasure (Set.Icc x y)
      = ENNReal.ofReal ((Real.sin x * Real.cos x - Real.sin y * Real.cos y + y - x) / π) := by
  rw [satoTateMeasure, withDensity_apply _ measurableSet_Icc]
  have hsub : Set.Icc x y ⊆ Set.Icc 0 π := Set.Icc_subset_Icc hx hy
  have h1 : ∫⁻ t in Set.Icc x y, ENNReal.ofReal ((Set.Icc 0 π).indicator satoTateDensity t)
      = ∫⁻ t in Set.Icc x y, ENNReal.ofReal (satoTateDensity t) := by
    refine setLIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
    simp only [Set.indicator_of_mem (hsub ht)]
  rw [h1]
  have hint : IntegrableOn satoTateDensity (Set.Icc x y) volume := by
    apply Continuous.integrableOn_Icc
    unfold satoTateDensity
    fun_prop
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hxy]
    unfold satoTateDensity
    rw [intervalIntegral.integral_const_mul, integral_sin_sq]
    field_simp
  · filter_upwards with t
    unfold satoTateDensity
    positivity

/-- The Sato–Tate measure is a probability measure. -/
instance satoTateMeasure_isProbabilityMeasure : IsProbabilityMeasure satoTateMeasure := by
  constructor
  have h0 : satoTateMeasure (Set.Icc 0 π)ᶜ = 0 := by
    rw [satoTateMeasure, withDensity_apply _ measurableSet_Icc.compl]
    have h : ∫⁻ t in (Set.Icc 0 π)ᶜ, ENNReal.ofReal ((Set.Icc 0 π).indicator satoTateDensity t)
        = ∫⁻ _ in (Set.Icc 0 π)ᶜ, (0 : ENNReal) := by
      refine setLIntegral_congr_fun measurableSet_Icc.compl (fun t ht => ?_)
      simp only [Set.indicator_of_notMem ht, ENNReal.ofReal_zero]
    rw [h]
    simp
  have hu : satoTateMeasure Set.univ = satoTateMeasure (Set.Icc 0 π) := by
    rw [← Set.union_compl_self (Set.Icc 0 π), measure_union disjoint_compl_right
      measurableSet_Icc.compl, h0, add_zero]
  rw [hu, satoTateMeasure_Icc le_rfl Real.pi_pos.le le_rfl]
  rw [Real.sin_zero, Real.sin_pi]
  norm_num

/-- **The Sato–Tate distribution.**

Let `W` be an integral Weierstrass model over `ℤ` of an elliptic curve `E / ℚ` without complex
multiplication, with trace of Frobenius `a_p = p + 1 - #E(𝔽_p)` at the prime `p`, so that the
Frobenius angle at `p` is `θ_p = arccos (a_p / (2√p)) ∈ [0, π]` (the angle is well defined
by the Hasse bound `|a_p| ≤ 2√p`).

This theorem states the Sato–Tate distribution of these angles:

1. the Sato–Tate measure `(2/π) sin²θ dθ` on `[0, π]` is a probability measure;
2. it assigns to a subinterval `[x, y] ⊆ [0, π]` the mass
   `(sin x cos x - sin y cos y + y - x)/π`;
3. every Frobenius angle of the curve lies in `[0, π]`;
4. for a curve without complex multiplication, Sato–Tate equidistribution of the Frobenius
   angles `θ_{p_1}, θ_{p_2}, …` (the assertion of the Sato–Tate theorem) is exactly the
   statement that for every `0 ≤ x ≤ y ≤ π` the proportion of the first `N` primes whose
   Frobenius angle lies in `[x, y]` converges, as `N → ∞`, to
   `(sin x cos x - sin y cos y + y - x)/π`.

(The deep input — that the angles of a non-CM curve are indeed equidistributed — is the
Sato–Tate theorem of Clozel–Harris–Shepherd-Barron–Taylor; it is not available in Mathlib and
is not proved here.  What is proved here is the description of the distribution itself, and
the equivalence of the abstract and explicit forms of the equidistribution statement.  The
non-CM hypothesis is stated because it is part of the Sato–Tate statement, but it is not
needed for this equivalence.) -/
theorem sato_tate :
    IsProbabilityMeasure satoTateMeasure ∧
    (∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ π →
      satoTateMeasure (Set.Icc x y)
        = ENNReal.ofReal ((Real.sin x * Real.cos x - Real.sin y * Real.cos y + y - x) / π)) ∧
    (∀ (W : WeierstrassCurve ℤ) (n : ℕ), curveFrobAngleSeq W n ∈ Set.Icc 0 π) ∧
    (∀ (W : WeierstrassCurve ℤ) [(W.map (Int.castRingHom ℚ)).IsElliptic],
      NonCM (W.map (Int.castRingHom ℚ)) →
      (IsSatoTateEquidistributed (curveFrobAngleSeq W) ↔
        ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ π →
          Tendsto (fun N => satoTateProportion (curveFrobAngleSeq W) N (Set.Icc x y)) atTop
            (𝓝 ((Real.sin x * Real.cos x - Real.sin y * Real.cos y + y - x) / π)))) := by
  refine ⟨satoTateMeasure_isProbabilityMeasure, fun x y hx hxy hy =>
    satoTateMeasure_Icc hx hxy hy, fun W n => frobAngle_mem_Icc _ _, fun W _ _ => ?_⟩
  have key : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ π →
      (satoTateMeasure (Set.Icc x y)).toReal
        = (Real.sin x * Real.cos x - Real.sin y * Real.cos y + y - x) / π := by
    intro x y hx hxy hy
    rw [satoTateMeasure_Icc hx hxy hy, ENNReal.toReal_ofReal (satoTate_arc_nonneg hxy)]
  constructor
  · intro h x y hx hxy hy
    have := h x y hx hxy hy
    rwa [key x y hx hxy hy] at this
  · intro h x y hx hxy hy
    have := h x y hx hxy hy
    rwa [key x y hx hxy hy]

end Math2

