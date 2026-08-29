/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Metric Filter Topology

/-- A parameterization `K : Θ → P` of a torus is *invariant* for the dynamics `F : P → P`
with internal (rigid rotation) dynamics `R : Θ → Θ` if it conjugates `R` to `F`:
`F (K θ) = K (R θ)` for all `θ`.  This is the standard "parameterization method"
formulation of an invariant torus carrying quasi-periodic motion with rotation `R`. -/
def IsInvariantTorus {Θ P : Type*} (F : P → P) (R : Θ → Θ) (K : Θ → P) : Prop :=
  ∀ θ, F (K θ) = K (R θ)

/-- **KAM (persistence of invariant tori), functional-analytic form.**

Data: a family of dynamical systems `F ε : P → P` on phase space `P`, a rigid rotation
`R : Θ → Θ` of the model torus `Θ`, a complete metric space `X` of torus parameterizations
with `emb : X → (Θ → P)` realizing each element as a map `Θ → P`, and an *invariance operator*
`T ε : X → X` whose fixed points parameterize invariant tori of `F ε` (hypothesis `hsol`).

Hypotheses: `T ε` is a uniform contraction (constant `L < 1`, uniformly in `ε`), the
unperturbed operator `T 0` fixes the unperturbed torus `u₀`, and the perturbation moves
`u₀` by at most `c * |ε|`.

Conclusion: for every `ε` the system `F ε` has an invariant torus with the *same* rotation
`R`, lying within `c * |ε| / (1 - L)` of the unperturbed torus (so the tori persist and
depend on `ε` in an `O(ε)` fashion), it is the unique fixed point of the invariance operator,
and at `ε = 0` it is the unperturbed torus itself (base case). -/
theorem kam_theorem {Θ P X : Type*} [MetricSpace X] [CompleteSpace X]
    (F : ℝ → P → P) (R : Θ → Θ) (emb : X → Θ → P) (T : ℝ → X → X)
    (hsol : ∀ ε u, T ε u = u → IsInvariantTorus (F ε) R (emb u))
    (L : NNReal) (hL : L < 1) (hlip : ∀ ε, LipschitzWith L (T ε))
    (u₀ : X) (h₀ : T 0 u₀ = u₀)
    (c : ℝ) (hc : ∀ ε, dist (T ε u₀) u₀ ≤ c * |ε|) (ε : ℝ) :
    ∃ u : X, IsInvariantTorus (F ε) R (emb u) ∧ T ε u = u ∧
      dist u u₀ ≤ c * |ε| / (1 - L) ∧ (∀ v, T ε v = v → v = u) ∧ (ε = 0 → u = u₀) := by
  haveI : Nonempty X := ⟨u₀⟩
  have hcon : ∀ δ : ℝ, ContractingWith L (T δ) := fun δ => ⟨hL, hlip δ⟩
  refine ⟨ContractingWith.fixedPoint (T ε) (hcon ε), ?_, ?_, ?_, ?_, ?_⟩
  · exact hsol ε _ (hcon ε).fixedPoint_isFixedPt
  · exact (hcon ε).fixedPoint_isFixedPt
  · have h1 := (hcon ε).dist_fixedPoint_le u₀
    rw [dist_comm]
    refine h1.trans ?_
    have h2 : dist u₀ (T ε u₀) ≤ c * |ε| := by rw [dist_comm]; exact hc ε
    have h3 : (0:ℝ) < 1 - L := (hcon ε).one_sub_K_pos
    gcongr
  · exact fun v hv => (hcon ε).fixedPoint_unique hv
  · rintro rfl
    exact ((hcon 0).fixedPoint_unique h₀).symm

/-! ### Base case: the unperturbed integrable system is foliated by invariant tori -/

/-- **Base case of KAM.**  For the integrable system `(p, q) ↦ (p, q + ω p)` on the phase space
`ℝⁿ × 𝕋ⁿ` (the time-one map of an integrable Hamiltonian flow with frequency map `ω`), every
torus `{p₀} × 𝕋ⁿ` is invariant and carries the rigid rotation by the frequency vector `ω p₀`. -/
theorem kam_base_case_integrable {n : ℕ} (om : (Fin n → ℝ) → (Fin n → AddCircle (1 : ℝ)))
    (p₀ : Fin n → ℝ) :
    IsInvariantTorus (fun z : (Fin n → ℝ) × (Fin n → AddCircle (1 : ℝ)) => (z.1, z.2 + om z.1))
      (fun θ : Fin n → AddCircle (1 : ℝ) => θ + om p₀) (fun θ => (p₀, θ)) :=
  fun _ => rfl

/-! ### The superconvergent (Newton) KAM iteration

The classical KAM proof replaces the contraction hypothesis of `kam_theorem` by a Newton
iteration in which each step squares the size `e n` of the remaining perturbation at the cost
of a constant `A * b ^ n` blowing up geometrically (loss of analyticity domain / small
divisors).  The following lemma is the quantitative heart of that scheme: quadratic
convergence beats the geometric loss provided the initial perturbation is small enough. -/

/-- **Convergence of the KAM Newton scheme.**  If `e n ≥ 0` satisfies the superconvergent
recursion `e (n+1) ≤ A * b ^ n * (e n) ^ 2` with `A > 0`, `b ≥ 1`, and if the initial error
satisfies the smallness condition `b * (A * e 0) ≤ 1 / 2`, then `e n → 0`; indeed
`e n ≤ (1 / A) * (1 / 2) ^ n`. -/
theorem kam_newton_scheme_tendsto_zero (e : ℕ → ℝ) (A b : ℝ) (hA : 0 < A) (hb : 1 ≤ b)
    (he : ∀ n, 0 ≤ e n) (hrec : ∀ n, e (n + 1) ≤ A * b ^ n * (e n) ^ 2)
    (hsmall : b * (A * e 0) ≤ 1 / 2) :
    (∀ n, e n ≤ (1 / A) * (1 / 2) ^ n) ∧ Filter.Tendsto e Filter.atTop (nhds 0) := by
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  set d : ℕ → ℝ := fun n => A * b ^ n * e n with hd
  have hd0 : ∀ n, 0 ≤ d n := fun n => by
    have : (0:ℝ) ≤ A * b ^ n := by positivity
    exact mul_nonneg this (he n)
  have hstep : ∀ n, b * d (n + 1) ≤ (b * d n) ^ 2 := by
    intro n
    have h1 : d (n + 1) ≤ b * (d n) ^ 2 := by
      have h2 : A * b ^ (n + 1) * e (n + 1) ≤ A * b ^ (n + 1) * (A * b ^ n * (e n) ^ 2) := by
        have : (0:ℝ) ≤ A * b ^ (n + 1) := by positivity
        exact mul_le_mul_of_nonneg_left (hrec n) this
      calc d (n + 1) = A * b ^ (n + 1) * e (n + 1) := rfl
        _ ≤ A * b ^ (n + 1) * (A * b ^ n * (e n) ^ 2) := h2
        _ = b * (A * b ^ n * e n) ^ 2 := by ring
        _ = b * (d n) ^ 2 := rfl
    calc b * d (n + 1) ≤ b * (b * (d n) ^ 2) := by
          exact mul_le_mul_of_nonneg_left h1 hb0.le
      _ = (b * d n) ^ 2 := by ring
  have hkey : ∀ n, b * d n ≤ (1 / 2) ^ (2 ^ n) := by
    intro n
    induction n with
    | zero =>
        simpa [hd] using hsmall
    | succ n ih =>
        have hnn : 0 ≤ b * d n := mul_nonneg hb0.le (hd0 n)
        calc b * d (n + 1) ≤ (b * d n) ^ 2 := hstep n
          _ ≤ ((1 / 2 : ℝ) ^ (2 ^ n)) ^ 2 := by
              exact pow_le_pow_left₀ hnn ih 2
          _ = (1 / 2 : ℝ) ^ (2 ^ (n + 1)) := by
              rw [← pow_mul, pow_succ]
  have hbound : ∀ n, e n ≤ (1 / A) * (1 / 2) ^ n := by
    intro n
    have h1 : A * e n ≤ b * d n := by
      have hbb : (1:ℝ) ≤ b ^ (n + 1) := one_le_pow₀ hb
      have : A * e n * 1 ≤ A * e n * b ^ (n + 1) :=
        mul_le_mul_of_nonneg_left hbb (mul_nonneg hA.le (he n))
      calc A * e n = A * e n * 1 := by ring
        _ ≤ A * e n * b ^ (n + 1) := this
        _ = b * d n := by rw [hd]; ring
    have h2 : ((1:ℝ) / 2) ^ (2 ^ n) ≤ (1 / 2) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.lt_two_pow_self (n := n)).le
    have h3 : A * e n ≤ (1 / 2 : ℝ) ^ n := le_trans h1 ((hkey n).trans h2)
    calc e n = (1 / A) * (A * e n) := by field_simp
      _ ≤ (1 / A) * (1 / 2 : ℝ) ^ n := by
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
  refine ⟨hbound, ?_⟩
  have hlim : Filter.Tendsto (fun n : ℕ => (1 / A) * (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1:ℝ)/2 < 1)
    simpa using this.const_mul (1 / A)
  exact squeeze_zero he hbound hlim

/-! ### A concrete system to which the theorem applies

The skew product `F ε (x, y) = (x + α, lam * y + ε * g x)` on the cylinder
`AddCircle 1 × ℝ`.  For `ε = 0` the circle `y = 0` is invariant and carries the rigid
rotation by `α`; the theorem produces, for every `ε`, a continuous invariant circle
`y = u ε x` at distance `O(ε)` from it. -/

theorem kam_invariant_circle_of_skew_product
    (α : AddCircle (1 : ℝ)) (lam : ℝ) (hlam : |lam| < 1)
    (g : C(AddCircle (1 : ℝ), ℝ)) (ε : ℝ) :
    ∃ u : C(AddCircle (1 : ℝ), ℝ),
      IsInvariantTorus (fun q : AddCircle (1 : ℝ) × ℝ => (q.1 + α, lam * q.2 + ε * g q.1))
        (fun x => x + α) (fun x => (x, u x)) ∧
      ‖u‖ ≤ |ε| * ‖g‖ / (1 - |lam|) := by
  classical
  -- the invariance operator: `u` parameterizes an invariant circle iff it is a fixed point
  set T : ℝ → C(AddCircle (1:ℝ), ℝ) → C(AddCircle (1:ℝ), ℝ) := fun δ u =>
    ⟨fun x => lam * u (x - α) + δ * g (x - α), by fun_prop⟩ with hT
  have hlip : ∀ δ : ℝ, LipschitzWith ‖lam‖₊ (T δ) := by
    intro δ
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    refine (ContinuousMap.dist_le (by positivity)).2 fun x => ?_
    have hx : dist (u (x - α)) (v (x - α)) ≤ dist u v := ContinuousMap.dist_apply_le_dist _
    have : dist ((T δ u) x) ((T δ v) x) = |lam| * dist (u (x - α)) (v (x - α)) := by
      simp [hT, Real.dist_eq, ← mul_sub, abs_mul]
    rw [this]
    have : (‖lam‖₊ : ℝ) = |lam| := by simp [Real.norm_eq_abs]
    rw [this]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg lam)
  have hzero : T 0 0 = 0 := by
    ext x; simp [hT]
  have hc : ∀ δ : ℝ, dist (T δ 0) 0 ≤ ‖g‖ * |δ| := by
    intro δ
    refine (ContinuousMap.dist_le (by positivity)).2 fun x => ?_
    have : dist ((T δ 0) x) ((0 : C(AddCircle (1:ℝ), ℝ)) x) = |δ| * |g (x - α)| := by
      simp [hT]
    rw [this, mul_comm (‖g‖) |δ|]
    have : |g (x - α)| ≤ ‖g‖ := by
      simpa [Real.norm_eq_abs] using g.norm_coe_le_norm (x - α)
    exact mul_le_mul_of_nonneg_left this (abs_nonneg δ)
  have hsol : ∀ (δ : ℝ) (u : C(AddCircle (1:ℝ), ℝ)), T δ u = u →
      IsInvariantTorus (fun q : AddCircle (1 : ℝ) × ℝ => (q.1 + α, lam * q.2 + δ * g q.1))
        (fun x => x + α) (fun x => (x, u x)) := by
    intro δ u hu x
    have hux : (T δ u) (x + α) = u (x + α) := by rw [hu]
    simp only [hT, ContinuousMap.coe_mk, add_sub_cancel_right] at hux
    simp [hux]
  have hL : ‖lam‖₊ < 1 := by
    have : (‖lam‖₊ : ℝ) = |lam| := by simp [Real.norm_eq_abs]
    rw [← NNReal.coe_lt_coe, this]
    simpa using hlam
  obtain ⟨u, hinv, -, hdist, -, -⟩ :=
    kam_theorem (fun δ => fun q : AddCircle (1 : ℝ) × ℝ => (q.1 + α, lam * q.2 + δ * g q.1))
      (fun x : AddCircle (1:ℝ) => x + α) (fun u : C(AddCircle (1:ℝ), ℝ) => fun x => (x, u x)) T
      hsol ‖lam‖₊ hL hlip 0 hzero ‖g‖ hc ε
  refine ⟨u, hinv, ?_⟩
  have hnorm : ‖u‖ = dist u 0 := by simp [dist_eq_norm]
  have hcoe : ((‖lam‖₊ : ℝ)) = |lam| := by simp [Real.norm_eq_abs]
  rw [hnorm]
  calc dist u 0 ≤ ‖g‖ * |ε| / (1 - (‖lam‖₊ : ℝ)) := hdist
    _ = |ε| * ‖g‖ / (1 - |lam|) := by rw [hcoe, mul_comm]

end Frontier

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

