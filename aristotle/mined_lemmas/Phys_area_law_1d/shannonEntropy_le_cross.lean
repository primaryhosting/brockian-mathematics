import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header block is required to be the first content of the file; Lean 4 requires
`import` statements to precede every other command, including module docstrings, so the
single `import Mathlib` line above is the only thing preceding it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

namespace Phys

/-! ## Shannon entropy of a finite spectrum -/

/-- Shannon (von Neumann) entropy of a finite family of probabilities. -/

lemma shannonEntropy_le_cross {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hq : ∀ i, 0 < q i) (hqsum : ∑ i, q i ≤ 1) :
    shannonEntropy p ≤ ∑ i, p i * (-Real.log (q i)) := by
  have key : ∀ i, Real.negMulLog (p i) ≤ p i * (-Real.log (q i)) + (q i - p i) := by
    intro i
    rcases eq_or_lt_of_le (hp i) with h0 | h0
    · simp [Real.negMulLog, ← h0]
      linarith [(hq i).le]
    · have hlog : Real.log (q i / p i) ≤ q i / p i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (hq i) h0)
      have hmul : p i * Real.log (q i / p i) ≤ p i * (q i / p i - 1) :=
        mul_le_mul_of_nonneg_left hlog h0.le
      have hdiv : p i * (q i / p i - 1) = q i - p i := by
        field_simp
      rw [hdiv] at hmul
      have hsplit : Real.log (q i / p i) = Real.log (q i) - Real.log (p i) :=
        Real.log_div (hq i).ne' h0.ne'
      rw [hsplit] at hmul
      simp only [Real.negMulLog]
      nlinarith [hmul]
  calc shannonEntropy p ≤ ∑ i, (p i * (-Real.log (q i)) + (q i - p i)) :=
        Finset.sum_le_sum (fun i _ => key i)
    _ = (∑ i, p i * (-Real.log (q i))) + ((∑ i, q i) - ∑ i, p i) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ ≤ ∑ i, p i * (-Real.log (q i)) := by rw [hpsum]; linarith

/-- With exponentially decaying weights the mean rank is bounded by a constant. -/
