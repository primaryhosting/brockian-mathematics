/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

namespace Frontier

open MeasureTheory

/-- The Lieb–Thirring constant appearing in the kinetic energy inequality that is dual to
the Lieb–Thirring eigenvalue bound with constant `L` (in dimension `3`, exponent `γ = 1`). -/
noncomputable def ltKineticConst (L : ℝ) : ℝ := (3 / 5) * (2 / (5 * L)) ^ ((2 : ℝ) / 3)

lemma ltKineticConst_pos {L : ℝ} (hL : 0 < L) : 0 < ltKineticConst L := by
  unfold ltKineticConst
  positivity

/-- **Sharp Young inequality behind the Lieb–Thirring duality.** For nonnegative `a, b` and
`L > 0` we have `a * b ≤ K_L * a^(5/3) + L * b^(5/2)`, with the same constant
`K_L = ltKineticConst L` as in the kinetic energy inequality. Equality is attained at
`b = (2a/(5L))^(2/3)`, so the constant is optimal. -/
theorem young_liebThirring {L a b : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ ltKineticConst L * a ^ ((5 : ℝ) / 3) + L * b ^ ((5 : ℝ) / 2) := by
  have hconj : Real.HolderConjugate ((5 : ℝ) / 3) ((5 : ℝ) / 2) := by constructor <;> norm_num
  set s : ℝ := 2 / (5 * L) with hs_def
  have hs : 0 < s := by positivity
  set t : ℝ := s ^ ((2 : ℝ) / 5) with ht_def
  have ht : 0 < t := Real.rpow_pos_of_pos hs _
  have hyoung := Real.young_inequality_of_nonneg (a := t * a) (b := b / t)
    (mul_nonneg ht.le ha) (div_nonneg hb ht.le) hconj
  have e0 : (t * a) * (b / t) = a * b := by field_simp
  have e1 : (t * a) ^ ((5 : ℝ) / 3) = s ^ ((2 : ℝ) / 3) * a ^ ((5 : ℝ) / 3) := by
    rw [Real.mul_rpow ht.le ha, ht_def, ← Real.rpow_mul hs.le]
    norm_num
  have e2 : (b / t) ^ ((5 : ℝ) / 2) = b ^ ((5 : ℝ) / 2) / s := by
    rw [Real.div_rpow hb ht.le, ht_def, ← Real.rpow_mul hs.le]
    norm_num
  rw [e0, e1, e2] at hyoung
  have key : s ^ ((2 : ℝ) / 3) * a ^ ((5 : ℝ) / 3) / (5 / 3) + b ^ ((5 : ℝ) / 2) / s / (5 / 2)
      = ltKineticConst L * a ^ ((5 : ℝ) / 3) + L * b ^ ((5 : ℝ) / 2) := by
    rw [ltKineticConst, ← hs_def, hs_def]
    field_simp
  linarith [hyoung, key.le, key.ge]

/-- **Legendre duality step.** If for every nonnegative potential `V` the kinetic energy `T`
of the state dominates `∫ V ρ - L ∫ V ^ (5/2)` (this is exactly what the Lieb–Thirring
eigenvalue bound `∑ |λ_j(-Δ - V)| ≤ L ∫ V₊^(5/2)` gives for a fermionic state with
one-particle density `ρ`), then `T` obeys the Thomas–Fermi type kinetic energy inequality
`T ≥ K_L ∫ ρ^(5/3)`. -/
theorem kinetic_of_liebThirring
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (ρ : α → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (T L : ℝ) (hL : 0 < L)
    (hint : Integrable (fun x => (ρ x) ^ ((5 : ℝ) / 3)) μ)
    (hLT : ∀ V : α → ℝ, (∀ x, 0 ≤ V x) →
        Integrable (fun x => V x * ρ x) μ →
        Integrable (fun x => (V x) ^ ((5 : ℝ) / 2)) μ →
        T - ∫ x, V x * ρ x ∂μ ≥ - L * ∫ x, (V x) ^ ((5 : ℝ) / 2) ∂μ) :
    T ≥ ltKineticConst L * ∫ x, (ρ x) ^ ((5 : ℝ) / 3) ∂μ := by
  set a : ℝ := 2 / (5 * L) with ha_def
  have ha : 0 < a := by positivity
  set c : ℝ := a ^ ((2 : ℝ) / 3) with hc_def
  have hc : 0 < c := Real.rpow_pos_of_pos ha _
  set V : α → ℝ := fun x => c * (ρ x) ^ ((2 : ℝ) / 3) with hV_def
  have hVnn : ∀ x, 0 ≤ V x := fun x => mul_nonneg hc.le (Real.rpow_nonneg (hρ x) _)
  have h1 : ∀ x, V x * ρ x = c * (ρ x) ^ ((5 : ℝ) / 3) := by
    intro x
    have h : (ρ x) ^ ((2 : ℝ) / 3) * (ρ x) = (ρ x) ^ ((5 : ℝ) / 3) := by
      rw [show (5 : ℝ) / 3 = 2 / 3 + 1 by norm_num, Real.rpow_add' (hρ x) (by norm_num),
        Real.rpow_one]
    simp only [hV_def]
    rw [mul_assoc, h]
  have h2 : ∀ x, (V x) ^ ((5 : ℝ) / 2) = c ^ ((5 : ℝ) / 2) * (ρ x) ^ ((5 : ℝ) / 3) := by
    intro x
    simp only [hV_def]
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg (hρ x) _), ← Real.rpow_mul (hρ x)]
    norm_num
  have hi1 : Integrable (fun x => V x * ρ x) μ := by
    simpa only [h1] using hint.const_mul c
  have hi2 : Integrable (fun x => (V x) ^ ((5 : ℝ) / 2)) μ := by
    simpa only [h2] using hint.const_mul (c ^ ((5 : ℝ) / 2))
  have key := hLT V hVnn hi1 hi2
  set X : ℝ := ∫ x, (ρ x) ^ ((5 : ℝ) / 3) ∂μ with hX_def
  have hX0 : 0 ≤ X := integral_nonneg (fun x => Real.rpow_nonneg (hρ x) _)
  rw [show (∫ x, V x * ρ x ∂μ) = c * X by simp only [h1]; rw [integral_const_mul],
      show (∫ x, (V x) ^ ((5 : ℝ) / 2) ∂μ) = c ^ ((5 : ℝ) / 2) * X by
        simp only [h2]; rw [integral_const_mul]] at key
  have hcpow : c ^ ((5 : ℝ) / 2) = a ^ ((5 : ℝ) / 3) := by
    rw [hc_def, ← Real.rpow_mul ha.le]; norm_num
  have hLa : L * a ^ ((5 : ℝ) / 3) = (2 / 5) * a ^ ((2 : ℝ) / 3) := by
    have h : a ^ ((5 : ℝ) / 3) = a ^ ((2 : ℝ) / 3) * a := by
      rw [show (5 : ℝ) / 3 = 2 / 3 + 1 by norm_num, Real.rpow_add' ha.le (by norm_num),
        Real.rpow_one]
    rw [h, ha_def]
    field_simp
  have hconst : c - L * c ^ ((5 : ℝ) / 2) = ltKineticConst L := by
    rw [hcpow, hLa, ltKineticConst, hc_def, ← ha_def]
    ring
  nlinarith [key, hX0, hconst]

/-- **The Lieb–Thirring hypothesis is satisfiable, with `ltKineticConst L` optimal.**
For any nonnegative density `ρ` with finite Thomas–Fermi energy, the value
`T = K_L ∫ ρ^(5/3)` already satisfies the variational Lieb–Thirring hypothesis. Combined
with `kinetic_of_liebThirring` (which gives `T ≥ K_L ∫ ρ^(5/3)`), this shows that the
constant `K_L` obtained by the duality argument cannot be improved, and in particular that
the hypotheses of the reduction are not vacuous. -/
theorem liebThirring_dual_hypothesis_sharp
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (ρ : α → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (L : ℝ) (hL : 0 < L)
    (hint : Integrable (fun x => (ρ x) ^ ((5 : ℝ) / 3)) μ) :
    ∀ V : α → ℝ, (∀ x, 0 ≤ V x) →
      Integrable (fun x => V x * ρ x) μ →
      Integrable (fun x => (V x) ^ ((5 : ℝ) / 2)) μ →
      (ltKineticConst L * ∫ x, (ρ x) ^ ((5 : ℝ) / 3) ∂μ) - ∫ x, V x * ρ x ∂μ
        ≥ - L * ∫ x, (V x) ^ ((5 : ℝ) / 2) ∂μ := by
  intro V hV hi1 hi2
  have hmono : (∫ x, V x * ρ x ∂μ)
      ≤ ∫ x, (ltKineticConst L * (ρ x) ^ ((5 : ℝ) / 3) + L * (V x) ^ ((5 : ℝ) / 2)) ∂μ := by
    refine integral_mono hi1 ((hint.const_mul _).add (hi2.const_mul _)) (fun x => ?_)
    simpa [mul_comm] using young_liebThirring (L := L) (a := ρ x) (b := V x) hL (hρ x) (hV x)
  rw [integral_add (hint.const_mul _) (hi2.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  linarith

/-- **Optimality of the constant.** If a constant `K'` works in the kinetic energy
inequality for every state satisfying the variational Lieb–Thirring hypothesis (tested here
on the one-point measure space, where `ρ ≡ 1`), then `K' ≤ K_L`. -/
theorem ltKineticConst_optimal {L K' : ℝ} (hL : 0 < L)
    (h : ∀ (T : ℝ),
      (∀ V : Unit → ℝ, (∀ x, 0 ≤ V x) →
        Integrable (fun x => V x * (1 : ℝ)) (Measure.dirac ()) →
        Integrable (fun x => (V x) ^ ((5 : ℝ) / 2)) (Measure.dirac ()) →
        T - ∫ x, V x * (1 : ℝ) ∂(Measure.dirac ())
          ≥ - L * ∫ x, (V x) ^ ((5 : ℝ) / 2) ∂(Measure.dirac ())) →
      T ≥ K' * ∫ _x : Unit, (1 : ℝ) ^ ((5 : ℝ) / 3) ∂(Measure.dirac ())) :
    K' ≤ ltKineticConst L := by
  have hone : (∫ _x : Unit, (1 : ℝ) ^ ((5 : ℝ) / 3) ∂(Measure.dirac ())) = 1 := by simp
  have hhyp := liebThirring_dual_hypothesis_sharp (μ := Measure.dirac ())
    (fun _ : Unit => (1 : ℝ)) (fun _ => zero_le_one) L hL Integrable.of_finite
  rw [hone] at hhyp
  have hK := h (ltKineticConst L * 1) (by simpa using hhyp)
  rw [hone] at hK
  linarith

/-- **Scalar stability step.** If the kinetic energy dominates `K * X` and the total
attraction is bounded by `C * X ^ (1/2) * N ^ (1/2)` (the scaling-correct Coulomb bound),
then the total energy is bounded below by `-C^2 N / (4K)`, i.e. linearly in the particle
number. -/
theorem energy_lower_bound_of_bounds
    {K C X N T A E : ℝ} (hK : 0 < K) (hX : 0 ≤ X) (hN : 0 ≤ N)
    (hT : T ≥ K * X) (hA : A ≤ C * Real.sqrt X * Real.sqrt N) (hE : E = T - A) :
    E ≥ - (C ^ 2 * N) / (4 * K) := by
  obtain ⟨u, hu0, hu⟩ : ∃ u : ℝ, 0 ≤ u ∧ X = u ^ 2 :=
    ⟨Real.sqrt X, Real.sqrt_nonneg X, (Real.sq_sqrt hX).symm⟩
  obtain ⟨v, hv0, hv⟩ : ∃ v : ℝ, 0 ≤ v ∧ N = v ^ 2 :=
    ⟨Real.sqrt N, Real.sqrt_nonneg N, (Real.sq_sqrt hN).symm⟩
  have hsu : Real.sqrt X = u := by rw [hu, Real.sqrt_sq hu0]
  have hsv : Real.sqrt N = v := by rw [hv, Real.sqrt_sq hv0]
  rw [hsu, hsv] at hA
  have key : K * X - C * u * v ≥ - (C ^ 2 * N) / (4 * K) := by
    rw [ge_iff_le, div_le_iff₀ (by positivity), hu, hv]
    nlinarith [sq_nonneg (2 * K * u - C * v)]
  linarith

/-- **Lieb–Thirring inequality and stability of matter.**

A Lean-checked reduction of stability of matter to the Lieb–Thirring inequality.

Assume:
* `ρ ≥ 0` is the one-particle density of a fermionic state, with `∫ ρ = N` particles and
  finite Thomas–Fermi energy `∫ ρ^(5/3)`;
* `hLT`: the Lieb–Thirring eigenvalue bound in its variational (dual) form, i.e. for every
  nonnegative potential `V`, the kinetic energy satisfies
  `T - ∫ V ρ ≥ -L ∫ V^(5/2)` — this is precisely the statement that the sum of the negative
  eigenvalues of `-Δ - V` is at least `-L ∫ V₊^(5/2)`, applied to the given state;
* `hCoul`: the (scaling correct) bound on the attractive Coulomb energy
  `A ≤ C * (∫ ρ^(5/3))^(1/2) * N^(1/2)`.

Then the total energy `E = T - A` satisfies the stability bound `E ≥ -c N` with the
explicit constant `c = C² / (4 K_L)`, `K_L = (3/5) (2/(5L))^(2/3)`: the energy is bounded
below by a constant times the number of particles. -/
theorem lieb_thirring_stability
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (ρ : α → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (T L N A E C : ℝ) (hL : 0 < L)
    (hint : Integrable (fun x => (ρ x) ^ ((5 : ℝ) / 3)) μ)
    (hN : 0 ≤ N)
    (hLT : ∀ V : α → ℝ, (∀ x, 0 ≤ V x) →
        Integrable (fun x => V x * ρ x) μ →
        Integrable (fun x => (V x) ^ ((5 : ℝ) / 2)) μ →
        T - ∫ x, V x * ρ x ∂μ ≥ - L * ∫ x, (V x) ^ ((5 : ℝ) / 2) ∂μ)
    (hCoul : A ≤ C * Real.sqrt (∫ x, (ρ x) ^ ((5 : ℝ) / 3) ∂μ) * Real.sqrt N)
    (hE : E = T - A) :
    E ≥ - (C ^ 2 / (4 * ltKineticConst L)) * N := by
  have hK : 0 < ltKineticConst L := ltKineticConst_pos hL
  have hT : T ≥ ltKineticConst L * ∫ x, (ρ x) ^ ((5 : ℝ) / 3) ∂μ :=
    kinetic_of_liebThirring ρ hρ T L hL hint hLT
  have hX0 : (0 : ℝ) ≤ ∫ x, (ρ x) ^ ((5 : ℝ) / 3) ∂μ :=
    integral_nonneg (fun x => Real.rpow_nonneg (hρ x) _)
  have h := energy_lower_bound_of_bounds (K := ltKineticConst L) (C := C)
    (X := ∫ x, (ρ x) ^ ((5 : ℝ) / 3) ∂μ) (N := N) (T := T) (A := A) (E := E)
    hK hX0 hN hT hCoul hE
  have heq : - (C ^ 2 * N) / (4 * ltKineticConst L) = - (C ^ 2 / (4 * ltKineticConst L)) * N := by
    field_simp
  linarith [h, heq.le, heq.ge]

end Frontier

