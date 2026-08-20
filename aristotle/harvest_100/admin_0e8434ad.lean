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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- Cauchy–Schwarz in the form `|⟪f, g⟫| ≤ ‖f‖ ‖g‖` for finite sums of reals. -/
lemma abs_sum_mul_le_sqrt_mul_sqrt {V : Type*} [Fintype V] (f g : V → ℝ) :
    |∑ i, f i * g i| ≤ Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := by
  have h : (∑ i, f i * g i) ^ 2 ≤ (∑ i, f i ^ 2) * ∑ i, g i ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  calc |∑ i, f i * g i| = Real.sqrt ((∑ i, f i * g i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i, f i ^ 2) * ∑ i, g i ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) :=
        Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _) _

/-- The centered indicator vector of a set `S` has zero coordinate sum. -/
lemma sum_centered_indicator {V : Type*} [Fintype V] (S : Finset V)
    (hn : (0 : ℝ) < Fintype.card V) :
    ∑ i, ((if i ∈ S then (1 : ℝ) else 0) - S.card / Fintype.card V) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
  field_simp
  ring

/-- The squared norm of the centered indicator vector of `S` is at most `|S|`. -/
lemma sum_sq_centered_indicator_le {V : Type*} [Fintype V] (S : Finset V)
    (hn : (0 : ℝ) < Fintype.card V) :
    ∑ i, ((if i ∈ S then (1 : ℝ) else 0) - S.card / Fintype.card V) ^ 2 ≤ S.card := by
  have hexp : ∀ i : V, ((if i ∈ S then (1 : ℝ) else 0) - S.card / Fintype.card V) ^ 2
      = (if i ∈ S then (1 : ℝ) else 0)
        - 2 * (S.card / Fintype.card V) * (if i ∈ S then (1 : ℝ) else 0)
        + (S.card / Fintype.card V) ^ 2 := by
    intro i
    by_cases h : i ∈ S
    · rw [if_pos h]; ring
    · rw [if_neg h]; ring
  rw [Finset.sum_congr rfl fun i _ => hexp i]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    nsmul_eq_mul]
  have hcard : (Fintype.card V : ℝ) ≠ 0 := ne_of_gt hn
  have h2 : 0 ≤ (S.card : ℝ) ^ 2 / Fintype.card V := by positivity
  have h3 : (Fintype.card V : ℝ) * ((S.card : ℝ) / Fintype.card V) ^ 2
      = (S.card : ℝ) ^ 2 / Fintype.card V := by field_simp
  have h4 : 2 * ((S.card : ℝ) / Fintype.card V) * ((S.card : ℝ) * 1)
      = 2 * ((S.card : ℝ) ^ 2 / Fintype.card V) := by field_simp
  rw [h3, h4]
  linarith

/-- **Expander mixing lemma** (Alon–Chung / Wigderson form).

Let `A` be a real symmetric matrix on a finite nonempty vertex set `V` (the adjacency
matrix of a `d`-regular graph), with all row sums equal to `d`, and suppose that `A`
contracts every vector orthogonal to the all-ones vector by a factor at most `lam`
(i.e. `lam` bounds the second largest eigenvalue in absolute value). Then for all
sets `S`, `T` of vertices, the number of edges between `S` and `T` (counted via `A`)
deviates from its "random graph" expectation `d |S| |T| / n` by at most
`lam * sqrt (|S| |T|)`. -/
theorem wigderson_expander_mixing {V : Type*} [Fintype V] [Nonempty V]
    (A : Matrix V V ℝ) (hA : A.IsSymm) (d lam : ℝ) (hlam : 0 ≤ lam)
    (hrow : ∀ i, ∑ j, A i j = d)
    (hspec : ∀ y : V → ℝ, ∑ i, y i = 0 →
      ∑ i, (A.mulVec y i) ^ 2 ≤ lam ^ 2 * ∑ i, (y i) ^ 2)
    (S T : Finset V) :
    |(∑ i ∈ S, ∑ j ∈ T, A i j) - d * S.card * T.card / Fintype.card V|
      ≤ lam * Real.sqrt (S.card * T.card) := by
  have hn : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  have hncast : (Fintype.card V : ℝ) ≠ 0 := ne_of_gt hn
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  set s : ℝ := (S.card : ℝ) with hsdef
  set t : ℝ := (T.card : ℝ) with htdef
  set x : V → ℝ := fun i => (if i ∈ S then (1 : ℝ) else 0) - s / n with hxdef
  set y : V → ℝ := fun i => (if i ∈ T then (1 : ℝ) else 0) - t / n with hydef
  -- column sums are also `d`
  have hcol : ∀ j, ∑ i, A i j = d := by
    intro j
    have : ∀ i, A i j = A j i := by
      intro i
      have := congrFun (congrFun hA i) j
      simpa [Matrix.transpose] using this.symm
    simp only [this]
    exact hrow j
  -- the coordinates of `A.mulVec y`
  have hmul : ∀ i, A.mulVec y i = (∑ j ∈ T, A i j) - (t / n) * d := by
    intro i
    simp only [Matrix.mulVec, dotProduct, hydef, mul_sub, Finset.sum_sub_distrib,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_mul]
    rw [hrow i]
    ring
  have hxsum : ∑ i, x i = 0 := sum_centered_indicator S hn
  have hysum : ∑ i, y i = 0 := sum_centered_indicator T hn
  -- key identity: the discrepancy equals the bilinear form on centered vectors
  have hkey : ∑ i, x i * A.mulVec y i
      = (∑ i ∈ S, ∑ j ∈ T, A i j) - d * s * t / n := by
    have hstep : ∀ i : V, x i * A.mulVec y i
        = (if i ∈ S then (1 : ℝ) else 0) * (∑ j ∈ T, A i j)
          - (t / n) * d * (if i ∈ S then (1 : ℝ) else 0)
          - (s / n) * (∑ j ∈ T, A i j) + (s / n) * ((t / n) * d) := by
      intro i
      rw [hmul i, hxdef]
      ring
    rw [Finset.sum_congr rfl fun i _ => hstep i]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have h1 : ∑ i, (if i ∈ S then (1 : ℝ) else 0) * (∑ j ∈ T, A i j)
        = ∑ i ∈ S, ∑ j ∈ T, A i j := by
      rw [Finset.sum_congr rfl fun i _ => rfl]
      simp [ite_mul, Finset.sum_ite_mem, Finset.univ_inter]
    have h2 : ∑ _i : V, (t / n) * d * (if _i ∈ S then (1 : ℝ) else 0) = (t / n) * d * s := by
      rw [← Finset.mul_sum]
      simp [Finset.sum_ite_mem, Finset.univ_inter, hsdef]
    have h3 : ∑ i : V, (s / n) * (∑ j ∈ T, A i j) = (s / n) * (t * d) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      rw [Finset.sum_congr rfl fun j _ => hcol j, Finset.sum_const, nsmul_eq_mul, htdef]
    have h4 : ∑ _i : V, (s / n) * ((t / n) * d) = n * ((s / n) * ((t / n) * d)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hndef]
    rw [h1, h2, h3, h4]
    field_simp
    ring
  -- the two norm bounds
  have hxnorm : ∑ i, (x i) ^ 2 ≤ s := sum_sq_centered_indicator_le S hn
  have hynorm : ∑ i, (y i) ^ 2 ≤ t := sum_sq_centered_indicator_le T hn
  have hAy : Real.sqrt (∑ i, (A.mulVec y i) ^ 2) ≤ lam * Real.sqrt t := by
    have h := hspec y hysum
    calc Real.sqrt (∑ i, (A.mulVec y i) ^ 2) ≤ Real.sqrt (lam ^ 2 * ∑ i, (y i) ^ 2) :=
          Real.sqrt_le_sqrt h
      _ = lam * Real.sqrt (∑ i, (y i) ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg lam), Real.sqrt_sq hlam]
      _ ≤ lam * Real.sqrt t := by
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hynorm) hlam
  have hxs : Real.sqrt (∑ i, (x i) ^ 2) ≤ Real.sqrt s := Real.sqrt_le_sqrt hxnorm
  have hbound : |∑ i, x i * A.mulVec y i| ≤ lam * Real.sqrt (s * t) := by
    have hcs := abs_sum_mul_le_sqrt_mul_sqrt x (fun i => A.mulVec y i)
    have hst : Real.sqrt (s * t) = Real.sqrt s * Real.sqrt t :=
      Real.sqrt_mul (by positivity) _
    calc |∑ i, x i * A.mulVec y i|
        ≤ Real.sqrt (∑ i, (x i) ^ 2) * Real.sqrt (∑ i, (A.mulVec y i) ^ 2) := hcs
      _ ≤ Real.sqrt s * (lam * Real.sqrt t) := by
          apply mul_le_mul hxs hAy (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = lam * Real.sqrt (s * t) := by rw [hst]; ring
  rw [hkey] at hbound
  convert hbound using 3

/-- Sanity check that the hypotheses of `wigderson_expander_mixing` are satisfiable in a
nontrivial way: the all-ones matrix (the complete graph with loops) is symmetric, has all row
sums equal to `n`, and annihilates every vector orthogonal to the all-ones vector, so it
satisfies the spectral hypothesis with `lam = 0`. -/
example {V : Type*} [Fintype V] [Nonempty V] (S T : Finset V) :
    |(∑ _i ∈ S, ∑ _j ∈ T, (1 : ℝ)) - (Fintype.card V : ℝ) * S.card * T.card / Fintype.card V|
      ≤ 0 * Real.sqrt (S.card * T.card) := by
  refine wigderson_expander_mixing (Matrix.of fun _ _ => (1 : ℝ)) rfl (Fintype.card V) 0 le_rfl
    (fun i => by simp) (fun y hy => ?_) S T
  have : ∀ i : V, (Matrix.of fun _ _ => (1 : ℝ)).mulVec y i = 0 := by
    intro i
    simp [Matrix.mulVec, dotProduct, hy]
  simp [this]

end Frontier

