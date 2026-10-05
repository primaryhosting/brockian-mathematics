import Mathlib
/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
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

set_option grind.warning false

namespace Frontier

/-! ## Part 1: elementary finite information theory -/

/-- Kullback–Leibler divergence of `p` from `q`, over a finite alphabet.
With the `Real.log` conventions, terms with `p i = 0` contribute `0`. -/

theorem EI_eq_zero_of_cut (S : System V) (A : Finset V)
    (hcut : ∀ u v, S.E u v → (u ∈ A ↔ v ∈ A)) : EI S A = 0 := by
  set r1 : {v // v ∈ A} → Bool := fun _ => false with hr1
  set r2 : {v // v ∉ A} → Bool := fun _ => false with hr2
  set wA : ℝ := ((2 : ℝ) ^ Fintype.card {v // v ∈ A})⁻¹ with hwA
  set wB : ℝ := ((2 : ℝ) ^ Fintype.card {v // v ∉ A})⁻¹ with hwB
  set g : (({v // v ∈ A} → Bool) × ({v // v ∈ A} → Bool)) → ℝ :=
    fun x => wA * ∏ v : {v // v ∈ A}, S.f v (comb A x.1 r2) (x.2 v) with hg
  set h : (({v // v ∉ A} → Bool) × ({v // v ∉ A} → Bool)) → ℝ :=
    fun y => wB * ∏ v : {v // v ∉ A}, S.f v (comb A r1 y.1) (y.2 v) with hh
  refine MI_eq_zero_of_indep _ g h ?_ ?_ ?_
  · -- factorisation
    intro x y
    have hw : ((2 : ℝ) ^ Fintype.card V)⁻¹ = wA * wB := by
      rw [hwA, hwB, ← mul_inv, ← pow_add, card_part_add]
    have hA' : ∀ v : {v // v ∈ A},
        S.f v (comb A x.1 y.1) (comb A x.2 y.2 v) = S.f v (comb A x.1 r2) (x.2 v) := by
      rintro ⟨v, hv⟩
      have h1 : S.f v (comb A x.1 y.1) = S.f v (comb A x.1 r2) := by
        refine S.f_local v _ _ ?_
        intro u hu
        have : u ∈ A := (hcut u v hu).mpr hv
        simp [comb, this]
      rw [h1]
      simp [comb, hv]
    have hB' : ∀ v : {v // v ∉ A},
        S.f v (comb A x.1 y.1) (comb A x.2 y.2 v) = S.f v (comb A r1 y.1) (y.2 v) := by
      rintro ⟨v, hv⟩
      have h1 : S.f v (comb A x.1 y.1) = S.f v (comb A r1 y.1) := by
        refine S.f_local v _ _ ?_
        intro u hu
        have : u ∉ A := fun hu' => hv ((hcut u v hu).mp hu')
        simp [comb, this]
      rw [h1]
      simp [comb, hv]
    simp only [partJoint, joint, transProb, hg, hh]
    rw [← prod_split A (fun v => S.f v (comb A x.1 y.1) (comb A x.2 y.2 v)), hw]
    rw [Finset.prod_congr rfl (fun v _ => hA' v), Finset.prod_congr rfl (fun v _ => hB' v)]
    ring
  · -- `g` is a probability distribution
    rw [Fintype.sum_prod_type]
    have hinner : ∀ x1 : {v // v ∈ A} → Bool,
        ∑ x2 : {v // v ∈ A} → Bool, g (x1, x2) = wA := by
      intro x1
      simp only [hg, ← Finset.mul_sum]
      have hone : (∑ t : {v // v ∈ A} → Bool, ∏ v : {v // v ∈ A},
          S.f v (comb A x1 r2) (t v)) = 1 :=
        sum_prod_node (ι := {v // v ∈ A}) (fun v b => S.f v (comb A x1 r2) b)
          (fun v => S.f_sum v (comb A x1 r2))
      rw [hone, mul_one]
    simp only [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
      Fintype.card_bool, hwA]
    have : ((2 : ℕ) : ℝ) ^ Fintype.card {v // v ∈ A} ≠ 0 := by positivity
    push_cast
    field_simp
  · -- `h` is a probability distribution
    rw [Fintype.sum_prod_type]
    have hinner : ∀ y1 : {v // v ∉ A} → Bool,
        ∑ y2 : {v // v ∉ A} → Bool, h (y1, y2) = wB := by
      intro y1
      simp only [hh, ← Finset.mul_sum]
      have hone : (∑ t : {v // v ∉ A} → Bool, ∏ v : {v // v ∉ A},
          S.f v (comb A r1 y1) (t v)) = 1 :=
        sum_prod_node (ι := {v // v ∉ A}) (fun v b => S.f v (comb A r1 y1) b)
          (fun v => S.f_sum v (comb A r1 y1))
      rw [hone, mul_one]
    simp only [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
      Fintype.card_bool, hwB]
    have : ((2 : ℕ) : ℝ) ^ Fintype.card {v // v ∉ A} ≠ 0 := by positivity
    push_cast
    field_simp

/-- **Integrated information vanishes for a disconnected system.**

If the connectivity of the system admits a bipartition into two nonempty parts `A` and `Aᶜ`
with no connection crossing between them, then the integrated information `Φ`, defined as the
minimum over bipartitions of the effective information across the bipartition, is zero. -/
