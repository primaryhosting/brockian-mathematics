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
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the header above is a plain block comment
-- and is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.WeirdNumbers

/-! ## Setup

We use Mathlib's `Nat.Weird`: `n` is weird if it is *abundant*
(`n < ∑ i ∈ n.properDivisors, i`) but not *pseudoperfect* (no subset of its proper divisors
sums to `n`).

The statement "there exists an odd weird number" is an open problem, so the target
`OddWeirdExists` is formalised as a **conditional reduction**: from a verifiable criterion on a
single odd number we deduce the existence of an odd weird number.  The criterion involves the
*abundance* `∑ i ∈ n.properDivisors, i - n`, which is typically far smaller than `n`, so it is a
genuine reduction of the search problem.
-/

/-- The abundance of `n`: the sum of the proper divisors of `n` minus `n` (truncated
subtraction). -/
def abundance (n : ℕ) : ℕ := (∑ i ∈ n.properDivisors, i) - n

/-- The statement of the open problem: there exists an odd weird number. -/
def OddWeirdStatement : Prop := ∃ n : ℕ, Odd n ∧ n.Weird

/-! ## The complement / abundance criterion -/

/-- The sum over the complement of a set of proper divisors. -/
theorem sum_sdiff_properDivisors {n : ℕ} {s : Finset ℕ} (hs : s ⊆ n.properDivisors) :
    ∑ i ∈ n.properDivisors \ s, i = (∑ i ∈ n.properDivisors, i) - ∑ i ∈ s, i := by
  have h : (∑ i ∈ n.properDivisors \ s, i) + ∑ i ∈ s, i = ∑ i ∈ n.properDivisors, i :=
    Finset.sum_sdiff hs
  omega

/-- If some subset of the proper divisors of `n` sums to `n`, then the complementary subset sums
to the abundance of `n`. -/
theorem exists_subset_sum_eq_abundance_of_pseudoperfect {n : ℕ} (h : n.Pseudoperfect) :
    ∃ s ⊆ n.properDivisors, ∑ i ∈ s, i = abundance n := by
  obtain ⟨-, s, hs, hsum⟩ := h
  refine ⟨n.properDivisors \ s, Finset.sdiff_subset, ?_⟩
  rw [sum_sdiff_properDivisors hs, hsum, abundance]

/-- Conversely, if some subset of the proper divisors of an abundant number `n` sums to the
abundance of `n`, then `n` is pseudoperfect. -/
theorem pseudoperfect_of_exists_subset_sum_eq_abundance {n : ℕ} (hn : 0 < n) (hab : n.Abundant)
    (h : ∃ s ⊆ n.properDivisors, ∑ i ∈ s, i = abundance n) : n.Pseudoperfect := by
  obtain ⟨s, hs, hsum⟩ := h
  refine ⟨hn, n.properDivisors \ s, Finset.sdiff_subset, ?_⟩
  rw [sum_sdiff_properDivisors hs, hsum]
  have : n ≤ ∑ i ∈ n.properDivisors, i := le_of_lt hab
  simp only [abundance]
  omega

/-- **Abundance criterion.**  A positive abundant number is pseudoperfect if and only if some
subset of its proper divisors sums to its abundance. -/
theorem pseudoperfect_iff_exists_subset_sum_eq_abundance {n : ℕ} (hn : 0 < n) (hab : n.Abundant) :
    n.Pseudoperfect ↔ ∃ s ⊆ n.properDivisors, ∑ i ∈ s, i = abundance n :=
  ⟨exists_subset_sum_eq_abundance_of_pseudoperfect,
    pseudoperfect_of_exists_subset_sum_eq_abundance hn hab⟩

/-- **Weirdness criterion.**  A positive number is weird iff it is abundant and no subset of its
proper divisors sums to its abundance. -/
theorem weird_iff {n : ℕ} (hn : 0 < n) :
    n.Weird ↔ n.Abundant ∧ ∀ s ⊆ n.properDivisors, ∑ i ∈ s, i ≠ abundance n := by
  constructor
  · rintro ⟨hab, hp⟩
    refine ⟨hab, fun s hs hsum => hp ?_⟩
    exact pseudoperfect_of_exists_subset_sum_eq_abundance hn hab ⟨s, hs, hsum⟩
  · rintro ⟨hab, h⟩
    refine ⟨hab, fun hp => ?_⟩
    obtain ⟨s, hs, hsum⟩ := exists_subset_sum_eq_abundance_of_pseudoperfect hp
    exact h s hs hsum

/-! ## The target: a conditional reduction -/

/-- **Odd weird exists (conditional reduction).**  If `n` is an odd abundant number such that no
subset of its proper divisors sums to its abundance `∑ i ∈ n.properDivisors, i - n`, then an odd
weird number exists.

The existence of an odd weird number is an open problem; this theorem reduces it to the
(much smaller) search for a representation of the abundance. -/
theorem OddWeirdExists {n : ℕ} (hodd : Odd n) (hab : n.Abundant)
    (hrep : ∀ s ⊆ n.properDivisors, ∑ i ∈ s, i ≠ abundance n) :
    OddWeirdStatement := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [Nat.Abundant] at hab
    · exact h
  exact ⟨n, hodd, (weird_iff hn).2 ⟨hab, hrep⟩⟩

/-! ## Further structural results

Weird numbers cannot have pseudoperfect proper divisors; in particular they have no perfect
proper divisors.  This restricts the shape of a hypothetical odd weird number. -/

/-- A proper multiple of a pseudoperfect number is pseudoperfect. -/
theorem Pseudoperfect.mul_of_dvd {m n : ℕ} (hm : m.Pseudoperfect) (hdvd : m ∣ n) (hmn : m < n) :
    n.Pseudoperfect := by
  obtain ⟨hm0, s, hs, hsum⟩ := hm
  obtain ⟨k, rfl⟩ := hdvd
  have hk : 1 < k := by
    by_contra h
    interval_cases k <;> omega
  have hk0 : 0 < k := by omega
  refine ⟨by positivity, s.image (fun d => k * d), ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    have hd' := hs hd
    rw [Nat.mem_properDivisors] at hd' ⊢
    refine ⟨by rw [mul_comm m k]; exact mul_dvd_mul_left k hd'.1, ?_⟩
    calc k * d < k * m := (Nat.mul_lt_mul_left hk0).2 hd'.2
      _ = m * k := by ring
  · rw [Finset.sum_image (by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hk0 hab)]
    rw [← Finset.mul_sum, hsum]
    ring

/-- A weird number has no pseudoperfect proper divisor. -/
theorem Weird.not_pseudoperfect_of_dvd {m n : ℕ} (hn : n.Weird) (hdvd : m ∣ n) (hmn : m < n) :
    ¬ m.Pseudoperfect := fun hm => hn.2 (Pseudoperfect.mul_of_dvd hm hdvd hmn)

/-- A weird number has no perfect proper divisor. -/
theorem Weird.not_perfect_of_dvd {m n : ℕ} (hn : n.Weird) (hdvd : m ∣ n) (hmn : m < n) :
    ¬ m.Perfect := fun hm =>
      Weird.not_pseudoperfect_of_dvd hn hdvd hmn (Nat.Perfect.pseudoperfect hm)

/-- A weird number is not itself perfect. -/
theorem Weird.not_perfect {n : ℕ} (hn : n.Weird) : ¬ n.Perfect :=
  fun hp => hn.2 (Nat.Perfect.pseudoperfect hp)

/-- If the abundance of `n` is itself a proper divisor of `n`, then `n` is pseudoperfect; hence a
weird number never has its abundance among its proper divisors. -/
theorem Weird.abundance_not_mem_properDivisors {n : ℕ} (hn : n.Weird) :
    abundance n ∉ n.properDivisors := by
  intro hmem
  have hlt := (Nat.mem_properDivisors.1 hmem).2
  refine hn.2 (pseudoperfect_of_exists_subset_sum_eq_abundance (by omega) hn.1
    ⟨{abundance n}, ?_, ?_⟩)
  · simpa using hmem
  · simp

/-- A weird number is never divisible by its own abundance (when the abundance is smaller than the
number, which is the only possible case for a positive divisor). -/
theorem Weird.not_dvd_abundance {n : ℕ} (hn : n.Weird) (hlt : abundance n < n) :
    ¬ abundance n ∣ n := by
  intro hdvd
  exact Weird.abundance_not_mem_properDivisors hn (Nat.mem_properDivisors.2 ⟨hdvd, hlt⟩)

/-! ## An unconditional example: weird numbers do exist (`70` is weird) -/

set_option maxRecDepth 10000 in
/-- `70` is a weird number. -/
theorem weird_seventy : Nat.Weird 70 := by decide

/-- Weird numbers exist (the even case is unconditional). -/
theorem exists_weird : ∃ n : ℕ, n.Weird := ⟨70, weird_seventy⟩

/-! ## A partial result towards the conjecture: no odd weird number below `1000` -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The only odd abundant number below `1000` is `945`. -/
theorem odd_abundant_lt_1000 (n : ℕ) (hlt : n < 1000) (hodd : Odd n) (hab : n.Abundant) :
    n = 945 := by
  revert hlt hodd hab; revert n; decide

set_option maxRecDepth 100000 in
/-- The sum of the proper divisors of `945` is `975`, so its abundance is `30 = 3 + 27`. -/
theorem sum_properDivisors_945 : (∑ i ∈ Nat.properDivisors 945, i) = 975 := by decide

set_option maxRecDepth 100000 in
/-- `945`, the smallest odd abundant number, is pseudoperfect: `945 = 975 - (3 + 27)`. -/
theorem pseudoperfect_945 : Nat.Pseudoperfect 945 := by
  refine pseudoperfect_of_exists_subset_sum_eq_abundance (by norm_num) ?_ ⟨{3, 27}, by decide, ?_⟩
  · show (945 : ℕ) < ∑ i ∈ Nat.properDivisors 945, i
    rw [sum_properDivisors_945]; norm_num
  · rw [abundance, sum_properDivisors_945]
    decide

/-- **Partial result.**  There is no odd weird number below `1000`. -/
theorem no_odd_weird_lt_1000 (n : ℕ) (hlt : n < 1000) (hodd : Odd n) : ¬ n.Weird := by
  intro hw
  have : n = 945 := odd_abundant_lt_1000 n hlt hodd hw.1
  subst this
  exact hw.2 pseudoperfect_945

end Brockian.WeirdNumbers

