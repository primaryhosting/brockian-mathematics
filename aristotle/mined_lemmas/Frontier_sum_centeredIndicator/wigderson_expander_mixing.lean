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

set_option grind.warning false

namespace Frontier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The "centered indicator" of a finite set `S`: the indicator of `S` minus its mean value.
It is orthogonal to the all-ones vector. -/

theorem wigderson_expander_mixing [Nonempty V]
    (A : Matrix V V ℝ) (d lam : ℝ) (hlam : 0 ≤ lam)
    (hrow : ∀ i, ∑ j, A i j = d) (hcol : ∀ j, ∑ i, A i j = d)
    (hspec : ∀ x y : V → ℝ, (∑ i, x i) = 0 → (∑ i, y i) = 0 →
      |∑ i, ∑ j, x i * A i j * y j| ≤
        lam * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2))
    (S T : Finset V) :
    |(∑ i ∈ S, ∑ j ∈ T, A i j) - d * S.card * T.card / (Fintype.card V)|
      ≤ lam * Real.sqrt (S.card * T.card) := by
  have hV : (Fintype.card V) ≠ 0 := Fintype.card_ne_zero
  have hbil := bilinear_centeredIndicator hV A d hrow hcol S T
  have hb := hspec (centeredIndicator S) (centeredIndicator T)
      (sum_centeredIndicator hV S) (sum_centeredIndicator hV T)
  rw [hbil] at hb
  refine hb.trans ?_
  have h1 : Real.sqrt (∑ i, (centeredIndicator S i) ^ 2) ≤ Real.sqrt (S.card : ℝ) :=
    Real.sqrt_le_sqrt (sum_sq_centeredIndicator_le hV S)
  have h2 : Real.sqrt (∑ i, (centeredIndicator T i) ^ 2) ≤ Real.sqrt (T.card : ℝ) :=
    Real.sqrt_le_sqrt (sum_sq_centeredIndicator_le hV T)
  have hsq : Real.sqrt ((S.card : ℝ) * (T.card : ℝ))
      = Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ) :=
    Real.sqrt_mul (by positivity) _
  rw [hsq]
  have hnn1 : (0:ℝ) ≤ Real.sqrt (∑ i, (centeredIndicator S i) ^ 2) := Real.sqrt_nonneg _
  have hnn2 : (0:ℝ) ≤ Real.sqrt (∑ i, (centeredIndicator T i) ^ 2) := Real.sqrt_nonneg _
  have hs : (0:ℝ) ≤ Real.sqrt (S.card : ℝ) := Real.sqrt_nonneg _
  calc lam * Real.sqrt (∑ i, (centeredIndicator S i) ^ 2)
        * Real.sqrt (∑ i, (centeredIndicator T i) ^ 2)
      ≤ lam * Real.sqrt (S.card : ℝ) * Real.sqrt (∑ i, (centeredIndicator T i) ^ 2) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hlam) hnn2
    _ ≤ lam * Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ) := by
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = lam * (Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ)) := by ring

/-- Sanity check: the hypotheses of `wigderson_expander_mixing` are satisfiable nondegenerately.
The "flat" matrix `A i j = d / n` is `d`-regular and annihilates every vector orthogonal to the
all-ones vector, so it satisfies the spectral hypothesis with `lam = 0`; the lemma then says that
the edge count between any two sets is *exactly* `d |S| |T| / n`. -/
example [Nonempty V] (d : ℝ) (S T : Finset V) :
    |(∑ _i ∈ S, ∑ _j ∈ T, d / (Fintype.card V))
        - d * S.card * T.card / (Fintype.card V)| ≤ 0 * Real.sqrt (S.card * T.card) := by
  have hn : ((Fintype.card V : ℝ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card V ≠ 0)
  refine wigderson_expander_mixing (Matrix.of fun _ _ => d / (Fintype.card V)) d 0 le_rfl
    (fun _ => ?_) (fun _ => ?_) (fun x y hx _hy => ?_) S T
  · simp [Finset.card_univ]
    field_simp
  · simp [Finset.card_univ]
    field_simp
  · have : ∑ i, ∑ j, x i * (d / (Fintype.card V)) * y j
        = (d / (Fintype.card V)) * ((∑ i, x i) * (∑ j, y j)) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    simp [Matrix.of_apply, this, hx]

end Frontier

