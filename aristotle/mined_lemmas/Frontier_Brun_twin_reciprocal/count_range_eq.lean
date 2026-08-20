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
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as an ordinary block comment.)

import RequestProject.Brun.Summable

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.
Here the index type is the set of primes `p` such that `p + 2` is also prime. -/

lemma count_range_eq (y : ℕ) {d : ℕ} (hd : 0 < d) :
    ((range y).filter (fun n => d ∣ n * (n + 2))).card
      = ∑ c ∈ sols d, (y / d + if c % d < y % d then 1 else 0) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun n => n % d) (t := sols d) ?_]
  · refine Finset.sum_congr rfl fun c hc => ?_
    obtain ⟨hcd, hcs⟩ := mem_sols.mp hc
    have heq : ((range y).filter (fun n => d ∣ n * (n + 2))).filter (fun n => n % d = c)
        = (range y).filter (fun n => n ≡ c [MOD d]) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Nat.ModEq]
      constructor
      · rintro ⟨⟨hn, -⟩, hmod⟩
        exact ⟨hn, by rw [hmod, Nat.mod_eq_of_lt hcd]⟩
      · rintro ⟨hn, hmod⟩
        rw [Nat.mod_eq_of_lt hcd] at hmod
        exact ⟨⟨hn, by rw [dvd_mul_add_two_iff, hmod]; exact hcs⟩, hmod⟩
    rw [heq, ← Nat.count_eq_card_filter_range]
    exact Nat.count_modEq_card _ hd c
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
    exact Finset.mem_coe.mpr
      (mem_sols.mpr ⟨Nat.mod_lt _ hd, by rw [← dvd_mul_add_two_iff]; exact hn.2⟩)

