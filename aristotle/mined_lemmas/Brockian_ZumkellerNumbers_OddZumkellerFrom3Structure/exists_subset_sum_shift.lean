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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian.ZumkellerNumbers

/-- A positive integer `n` is a *Zumkeller number* if its set of divisors can be split into
two parts with equal sums, i.e. there is a set `A` of divisors of `n` whose sum is exactly
half of `σ(n)`. -/

lemma exists_subset_sum_shift : ∀ (b : ℕ), 3 ≤ b → ∀ δ : ℤ, -12 ≤ δ → δ ≤ 12 →
    ∃ A ⊆ (3 ^ b * 35 : ℕ).divisors, (∑ d ∈ A, (d : ℤ)) = 12 * (3 ^ (b + 1) - 1) + δ := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base =>
      intro δ h1 h2
      have hkey : ∀ V : Finset ℕ, (∀ x ∈ V, x ∣ 945) →
          (∑ d ∈ V, (d : ℤ)) = 12 * (3 ^ (3 + 1) - 1) + δ →
          ∃ A ⊆ (3 ^ 3 * 35 : ℕ).divisors, (∑ d ∈ A, (d : ℤ)) = 12 * (3 ^ (3 + 1) - 1) + δ := by
        intro V hV hsum
        refine ⟨V, fun x hx => Nat.mem_divisors.mpr ⟨?_, by norm_num⟩, hsum⟩
        have h945 : ((3 : ℕ) ^ 3 * 35) = 945 := by norm_num
        rw [h945]
        exact hV x hx
      interval_cases δ
      · exact hkey {945, 3} (by decide) (by norm_num)
      · exact hkey {945, 1, 3} (by decide) (by norm_num)
      · exact hkey {945, 5} (by decide) (by norm_num)
      · exact hkey {945, 1, 5} (by decide) (by norm_num)
      · exact hkey {945, 7} (by decide) (by norm_num)
      · exact hkey {945, 1, 7} (by decide) (by norm_num)
      · exact hkey {945, 9} (by decide) (by norm_num)
      · exact hkey {945, 1, 9} (by decide) (by norm_num)
      · exact hkey {945, 1, 3, 7} (by decide) (by norm_num)
      · exact hkey {945, 3, 9} (by decide) (by norm_num)
      · exact hkey {945, 1, 3, 9} (by decide) (by norm_num)
      · exact hkey {945, 5, 9} (by decide) (by norm_num)
      · exact hkey {945, 15} (by decide) (by norm_num)
      · exact hkey {945, 1, 15} (by decide) (by norm_num)
      · exact hkey {945, 3, 5, 9} (by decide) (by norm_num)
      · exact hkey {945, 3, 15} (by decide) (by norm_num)
      · exact hkey {945, 1, 3, 15} (by decide) (by norm_num)
      · exact hkey {945, 5, 15} (by decide) (by norm_num)
      · exact hkey {945, 21} (by decide) (by norm_num)
      · exact hkey {945, 1, 21} (by decide) (by norm_num)
      · exact hkey {945, 1, 7, 15} (by decide) (by norm_num)
      · exact hkey {945, 3, 21} (by decide) (by norm_num)
      · exact hkey {945, 1, 3, 21} (by decide) (by norm_num)
      · exact hkey {945, 5, 21} (by decide) (by norm_num)
      · exact hkey {945, 27} (by decide) (by norm_num)
  | succ n hn ih =>
      intro δ h1 h2
      have main : ∀ (T : Finset ℕ) (δ' : ℤ), (∀ x ∈ T, x ∣ 35) → -12 ≤ δ' → δ' ≤ 12 →
          (∑ d ∈ T, (d : ℤ)) + 3 * δ' - 24 = δ →
          ∃ A ⊆ (3 ^ (n + 1) * 35 : ℕ).divisors,
            (∑ d ∈ A, (d : ℤ)) = 12 * (3 ^ (n + 1 + 1) - 1) + δ := by
        intro T δ' hT hd1 hd2 hrel
        obtain ⟨A, hA, hAsum⟩ := ih δ' hd1 hd2
        obtain ⟨hsub, hsum⟩ := step_aux hT hA
        refine ⟨_, hsub, ?_⟩
        rw [hsum, hAsum]
        have hp : (3 : ℤ) ^ (n + 1 + 1) = 3 * 3 ^ (n + 1) := by ring
        rw [hp]
        linarith
      rcases (by omega : δ % 3 = 0 ∨ δ % 3 = 1 ∨ δ % 3 = 2) with h | h | h
      · exact main {5, 7} ((δ + 12) / 3) (by decide) (by omega) (by omega) (by norm_num; omega)
      · exact main {1, 5, 7} ((δ + 11) / 3) (by decide) (by omega) (by omega) (by norm_num; omega)
      · exact main {1, 7} ((δ + 16) / 3) (by decide) (by omega) (by omega) (by norm_num; omega)

/-- For every `b ≥ 3`, the odd number `3 ^ b * 35` is a Zumkeller number. -/
