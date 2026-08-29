/-
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

namespace Frontier

section Mixing

variable {n : ℕ}

/-- The bilinear form `xᵀ A y` associated with a real matrix `A`. -/
noncomputable def bil (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * A i j * y j

lemma bil_add_left (A : Matrix (Fin n) (Fin n) ℝ) (u v w : Fin n → ℝ) :
    bil A (fun i => u i + v i) w = bil A u w + bil A v w := by
  unfold bil
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma bil_sub_left (A : Matrix (Fin n) (Fin n) ℝ) (u v w : Fin n → ℝ) :
    bil A (fun i => u i - v i) w = bil A u w - bil A v w := by
  unfold bil
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma bil_add_right (A : Matrix (Fin n) (Fin n) ℝ) (u v w : Fin n → ℝ) :
    bil A u (fun j => v j + w j) = bil A u v + bil A u w := by
  unfold bil
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma bil_sub_right (A : Matrix (Fin n) (Fin n) ℝ) (u v w : Fin n → ℝ) :
    bil A u (fun j => v j - w j) = bil A u v - bil A u w := by
  unfold bil
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma bil_smul_left (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (u w : Fin n → ℝ) :
    bil A (fun i => c * u i) w = c * bil A u w := by
  unfold bil
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma bil_smul_right (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (u w : Fin n → ℝ) :
    bil A u (fun j => c * w j) = c * bil A u w := by
  unfold bil
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma bil_comm {A : Matrix (Fin n) (Fin n) ℝ} (hsymm : A.IsSymm) (x y : Fin n → ℝ) :
    bil A x y = bil A y x := by
  unfold bil
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have h : A j i = A i j := by
    have := congrFun (congrFun hsymm i) j
    simpa [Matrix.transpose_apply] using this
  rw [h]; ring

/-- Pairing a constant vector on the right. -/
lemma bil_const_right {A : Matrix (Fin n) (Fin n) ℝ} {d : ℝ}
    (hreg : ∀ i, ∑ j, A i j = d) (x : Fin n → ℝ) (b : ℝ) :
    bil A x (fun _ => b) = b * d * ∑ i, x i := by
  unfold bil
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ∑ j, x i * A i j * b = (x i * b) * ∑ j, A i j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, hreg i]; ring

/-- Pairing a constant vector on the left. -/
lemma bil_const_left {A : Matrix (Fin n) (Fin n) ℝ} (hsymm : A.IsSymm) {d : ℝ}
    (hreg : ∀ i, ∑ j, A i j = d) (y : Fin n → ℝ) (a : ℝ) :
    bil A (fun _ => a) y = a * d * ∑ i, y i := by
  rw [bil_comm hsymm, bil_const_right hreg]

/-- Squared Euclidean norm of a vector. -/
noncomputable def nsq (x : Fin n → ℝ) : ℝ := ∑ i, (x i) ^ 2

lemma nsq_nonneg (x : Fin n → ℝ) : 0 ≤ nsq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma nsq_eq_zero_iff (x : Fin n → ℝ) : nsq x = 0 ↔ ∀ i, x i = 0 := by
  unfold nsq
  constructor
  · intro h i
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => sq_nonneg (x j))).1 h i (Finset.mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
  · intro h
    exact Finset.sum_eq_zero fun i _ => by rw [h i]; ring

/-- Polarization: the bilinear form is controlled by the quadratic form. -/
lemma bil_polarization {A : Matrix (Fin n) (Fin n) ℝ} (hsymm : A.IsSymm) (u v : Fin n → ℝ) :
    4 * bil A u v =
      bil A (fun i => u i + v i) (fun i => u i + v i)
        - bil A (fun i => u i - v i) (fun i => u i - v i) := by
  rw [bil_add_left, bil_sub_left, bil_add_right, bil_add_right,
    bil_sub_right, bil_sub_right, bil_comm hsymm v u]
  ring

lemma nsq_add_sub (u v : Fin n → ℝ) :
    nsq (fun i => u i + v i) + nsq (fun i => u i - v i) = 2 * nsq u + 2 * nsq v := by
  unfold nsq
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- If the quadratic form is bounded by `lam` on the space of vectors summing to zero,
then the bilinear form obeys the corresponding Cauchy-Schwarz-type bound there. -/
lemma bil_bound_of_quad_bound {A : Matrix (Fin n) (Fin n) ℝ} (hsymm : A.IsSymm) {lam : ℝ}
    (hlam : ∀ x : Fin n → ℝ, (∑ i, x i) = 0 → |bil A x x| ≤ lam * nsq x)
    (x y : Fin n → ℝ) (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) :
    |bil A x y| ≤ lam * Real.sqrt (nsq x) * Real.sqrt (nsq y) := by
  rcases eq_or_lt_of_le (nsq_nonneg x) with hx0 | hxpos
  · have hz : ∀ i, x i = 0 := (nsq_eq_zero_iff x).1 hx0.symm
    have hb : bil A x y = 0 := by
      unfold bil
      exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by rw [hz i]; ring
    rw [hb, ← hx0]
    simp
  rcases eq_or_lt_of_le (nsq_nonneg y) with hy0 | hypos
  · have hz : ∀ i, y i = 0 := (nsq_eq_zero_iff y).1 hy0.symm
    have hb : bil A x y = 0 := by
      unfold bil
      exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by rw [hz j]; ring
    rw [hb, ← hy0]
    simp
  set p := Real.sqrt (nsq x) with hp
  set q := Real.sqrt (nsq y) with hq
  have hppos : 0 < p := Real.sqrt_pos.2 hxpos
  have hqpos : 0 < q := Real.sqrt_pos.2 hypos
  have hp2 : p ^ 2 = nsq x := Real.sq_sqrt hxpos.le
  have hq2 : q ^ 2 = nsq y := Real.sq_sqrt hypos.le
  set u : Fin n → ℝ := fun i => p⁻¹ * x i with hu
  set v : Fin n → ℝ := fun i => q⁻¹ * y i with hv
  have hsu : ∑ i, u i = 0 := by
    rw [hu, ← Finset.mul_sum, hx, mul_zero]
  have hsv : ∑ i, v i = 0 := by
    rw [hv, ← Finset.mul_sum, hy, mul_zero]
  have hnu : nsq u = 1 := by
    have h3 : nsq u = p⁻¹ ^ 2 * nsq x := by
      unfold nsq
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hu]; ring
    rw [h3, ← hp2]
    field_simp
  have hnv : nsq v = 1 := by
    have h3 : nsq v = q⁻¹ ^ 2 * nsq y := by
      unfold nsq
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hv]; ring
    rw [h3, ← hq2]
    field_simp
  have hbuv : bil A u v = (p * q)⁻¹ * bil A x y := by
    rw [hu, hv, bil_smul_left, bil_smul_right]
    field_simp
  have hsadd : ∑ i, (u i + v i) = 0 := by
    rw [Finset.sum_add_distrib, hsu, hsv]; ring
  have hssub : ∑ i, (u i - v i) = 0 := by
    rw [Finset.sum_sub_distrib, hsu, hsv]; ring
  have h1 := hlam (fun i => u i + v i) hsadd
  have h2 := hlam (fun i => u i - v i) hssub
  have hpol := bil_polarization hsymm u v
  have hkey : 4 * |bil A u v| ≤ lam * (nsq (fun i => u i + v i) + nsq (fun i => u i - v i)) := by
    have h4 : |4 * bil A u v| ≤ lam * nsq (fun i => u i + v i) + lam * nsq (fun i => u i - v i) := by
      rw [hpol]
      calc |bil A (fun i => u i + v i) (fun i => u i + v i)
              - bil A (fun i => u i - v i) (fun i => u i - v i)|
          ≤ |bil A (fun i => u i + v i) (fun i => u i + v i)|
              + |bil A (fun i => u i - v i) (fun i => u i - v i)| := abs_sub _ _
        _ ≤ lam * nsq (fun i => u i + v i) + lam * nsq (fun i => u i - v i) :=
            add_le_add h1 h2
    rw [abs_mul] at h4
    simp only [Nat.abs_ofNat] at h4
    linarith [h4]
  rw [nsq_add_sub, hnu, hnv] at hkey
  have hlam_nonneg : 0 ≤ lam := by nlinarith [abs_nonneg (bil A u v)]
  have hle : |bil A u v| ≤ lam := by linarith
  rw [hbuv, abs_mul] at hle
  have habs : |(p * q)⁻¹| = (p * q)⁻¹ := abs_of_pos (by positivity)
  rw [habs] at hle
  have hpq : (0:ℝ) < p * q := by positivity
  have hmul : |bil A x y| ≤ lam * (p * q) := by
    calc |bil A x y| = (p * q) * ((p * q)⁻¹ * |bil A x y|) := by field_simp
      _ ≤ (p * q) * lam := mul_le_mul_of_nonneg_left hle hpq.le
      _ = lam * (p * q) := by ring
  linarith [hmul]

/-- Shifting both arguments of the bilinear form by constants. -/
lemma bil_shift {A : Matrix (Fin n) (Fin n) ℝ} (hsymm : A.IsSymm) {d : ℝ}
    (hreg : ∀ i, ∑ j, A i j = d) (x y : Fin n → ℝ) (a b : ℝ) :
    bil A (fun i => x i + a) (fun j => y j + b)
      = bil A x y + b * d * (∑ i, x i) + a * d * (∑ j, y j) + a * b * d * n := by
  rw [bil_add_left, bil_add_right, bil_add_right, bil_const_right hreg,
    bil_const_left hsymm hreg, bil_const_right hreg]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The number of edges between `S` and `T` as a value of the bilinear form. -/
lemma bil_indicator (A : Matrix (Fin n) (Fin n) ℝ) (S T : Finset (Fin n)) :
    bil A (fun i => if i ∈ S then (1:ℝ) else 0) (fun j => if j ∈ T then (1:ℝ) else 0)
      = ∑ i ∈ S, ∑ j ∈ T, A i j := by
  unfold bil
  simp [ite_mul, mul_ite, Finset.sum_ite_mem]

lemma sum_centered (hn : 0 < n) (S : Finset (Fin n)) :
    ∑ i, ((if i ∈ S then (1:ℝ) else 0) - (S.card : ℝ) / n) = 0 := by
  have hns : (0:ℝ) < n := by exact_mod_cast hn
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  field_simp
  ring

lemma nsq_centered_le (hn : 0 < n) (S : Finset (Fin n)) :
    nsq (fun i => (if i ∈ S then (1:ℝ) else 0) - (S.card : ℝ) / n) ≤ (S.card : ℝ) := by
  have hns : (0:ℝ) < n := by exact_mod_cast hn
  have hexp : nsq (fun i => (if i ∈ S then (1:ℝ) else 0) - (S.card : ℝ) / n)
      = (S.card : ℝ) - (S.card : ℝ) ^ 2 / n := by
    unfold nsq
    have hpt : ∀ i : Fin n, ((if i ∈ S then (1:ℝ) else 0) - (S.card : ℝ) / n) ^ 2
        = (if i ∈ S then (1:ℝ) else 0) * (1 - 2 * ((S.card : ℝ) / n))
            + ((S.card : ℝ) / n) ^ 2 := by
      intro i
      by_cases h : i ∈ S
      · simp [h]; ring
      · simp [h]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hpt i), Finset.sum_add_distrib,
      ← Finset.sum_mul]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_mem, Finset.univ_inter, mul_one]
    field_simp
    ring
  rw [hexp]
  have : (0:ℝ) ≤ (S.card : ℝ) ^ 2 / n := by positivity
  linarith

/-- **Expander mixing lemma** (Alon–Chung; see Hoory–Linial–Wigderson).

Let `A` be the (real, symmetric) adjacency matrix of a `d`-regular graph on `n` vertices,
and suppose the quadratic form of `A` is bounded in absolute value by `lam` on the space of
vectors orthogonal to the all-ones vector (i.e. `lam` bounds the non-trivial eigenvalues in
absolute value).  Then for all vertex subsets `S`, `T`, the number of edges from `S` to `T`
(counted with the adjacency matrix) deviates from its "expected" value `d|S||T|/n` by at most
`lam * sqrt(|S||T|)`. -/
theorem wigderson_expander_mixing
    {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) (hsymm : A.IsSymm)
    (d lam : ℝ) (hlam0 : 0 ≤ lam)
    (hreg : ∀ i, ∑ j, A i j = d)
    (hspec : ∀ x : Fin n → ℝ, (∑ i, x i) = 0 →
      |∑ i, ∑ j, x i * A i j * x j| ≤ lam * ∑ i, (x i) ^ 2)
    (S T : Finset (Fin n)) :
    |(∑ i ∈ S, ∑ j ∈ T, A i j) - d * S.card * T.card / n|
      ≤ lam * Real.sqrt ((S.card : ℝ) * T.card) := by
  have hns : (0:ℝ) < n := by exact_mod_cast hn
  set a : ℝ := (S.card : ℝ) / n with ha
  set b : ℝ := (T.card : ℝ) / n with hb
  set cS : Fin n → ℝ := fun i => (if i ∈ S then (1:ℝ) else 0) - a with hcS
  set cT : Fin n → ℝ := fun j => (if j ∈ T then (1:ℝ) else 0) - b with hcT
  have hSsum : ∑ i, cS i = 0 := sum_centered hn S
  have hTsum : ∑ i, cT i = 0 := sum_centered hn T
  -- rewrite the indicator vectors as centered vectors plus constants
  have eS : (fun i => (if i ∈ S then (1:ℝ) else 0)) = fun i => cS i + a := by
    funext i; rw [hcS]; ring
  have eT : (fun j => (if j ∈ T then (1:ℝ) else 0)) = fun j => cT j + b := by
    funext j; rw [hcT]; ring
  have hdecomp : (∑ i ∈ S, ∑ j ∈ T, A i j) = bil A cS cT + d * S.card * T.card / n := by
    rw [← bil_indicator A S T, eS, eT, bil_shift hsymm hreg, hSsum, hTsum, ha, hb]
    field_simp
    ring
  rw [hdecomp]
  have hcancel : bil A cS cT + d * S.card * T.card / n - d * S.card * T.card / n
      = bil A cS cT := by ring
  rw [hcancel]
  -- the spectral hypothesis in terms of `bil` and `nsq`
  have hlam : ∀ x : Fin n → ℝ, (∑ i, x i) = 0 → |bil A x x| ≤ lam * nsq x := by
    intro x hx
    exact hspec x hx
  have hmain := bil_bound_of_quad_bound hsymm hlam cS cT hSsum hTsum
  have hSb : Real.sqrt (nsq cS) ≤ Real.sqrt (S.card : ℝ) :=
    Real.sqrt_le_sqrt (nsq_centered_le hn S)
  have hTb : Real.sqrt (nsq cT) ≤ Real.sqrt (T.card : ℝ) :=
    Real.sqrt_le_sqrt (nsq_centered_le hn T)
  have hprod : lam * Real.sqrt (nsq cS) * Real.sqrt (nsq cT)
      ≤ lam * Real.sqrt ((S.card : ℝ) * T.card) := by
    rw [Real.sqrt_mul (by positivity)]
    have h1 : lam * Real.sqrt (nsq cS) ≤ lam * Real.sqrt (S.card : ℝ) :=
      mul_le_mul_of_nonneg_left hSb hlam0
    have h2 : (0:ℝ) ≤ Real.sqrt (nsq cT) := Real.sqrt_nonneg _
    calc lam * Real.sqrt (nsq cS) * Real.sqrt (nsq cT)
        ≤ lam * Real.sqrt (S.card : ℝ) * Real.sqrt (nsq cT) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ ≤ lam * Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ) :=
          mul_le_mul_of_nonneg_left hTb (by positivity)
      _ = lam * (Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ)) := by ring
  exact le_trans hmain hprod

end Mixing

end Frontier

#print axioms Frontier.wigderson_expander_mixing

