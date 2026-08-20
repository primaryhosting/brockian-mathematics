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

/-
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Brockian.Equidistribution

/-- Triangular numbers: `T m = 1 + 2 + ⋯ + m = m (m+1) / 2`. -/

lemma Cnt_T (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (M : ℕ) :
    |(Cnt a b (T M) : ℝ) - (b - a) * T M| ≤ M := by
  induction M with
  | zero => simp [Cnt, T]
  | succ n ih =>
      have hstep := block_card n a b ha hab hb
      have hT : T (n + 1) = T n + (n + 1) := T_succ n
      have hc := Cnt_add a b (T n) (n + 1)
      rw [hT, hc]
      push_cast [hT]
      have hsplit : ((Cnt a b (T n) : ℝ) +
            (((Finset.range (n + 1)).filter (fun k => u (T n + k) ∈ Set.Ico a b)).card : ℝ)) -
          (b - a) * ((T n : ℝ) + ((n : ℝ) + 1)) =
          ((Cnt a b (T n) : ℝ) - (b - a) * (T n : ℝ)) +
          ((((Finset.range (n + 1)).filter (fun k => u (T n + k) ∈ Set.Ico a b)).card : ℝ) -
            (b - a) * ((n : ℝ) + 1)) := by ring
      rw [hsplit]
      calc |((Cnt a b (T n) : ℝ) - (b - a) * (T n : ℝ)) +
              ((((Finset.range (n + 1)).filter (fun k => u (T n + k) ∈ Set.Ico a b)).card : ℝ) -
                (b - a) * ((n : ℝ) + 1))|
          ≤ |(Cnt a b (T n) : ℝ) - (b - a) * (T n : ℝ)| +
              |(((Finset.range (n + 1)).filter (fun k => u (T n + k) ∈ Set.Ico a b)).card : ℝ) -
                (b - a) * ((n : ℝ) + 1)| := abs_add_le _ _
        _ ≤ (n : ℝ) + 1 := by linarith

