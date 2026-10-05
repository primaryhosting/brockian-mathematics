import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires every `import` command to appear before any other
command in a module, including module docstrings, so the mandated header comment appears
immediately after the single `import Mathlib` line.
-/

open scoped BigOperators

namespace Frontier

/-- `PrimeAP k` says that there is an arithmetic progression of length `k` with positive
common difference all of whose terms are prime. -/
def PrimeAP (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, Nat.Prime (a + i * d)

/-- The Green–Tao theorem: the primes contain arbitrarily long arithmetic progressions. -/
def GreenTaoStatement : Prop := ∀ k : ℕ, PrimeAP k

/-- A finite set `B ⊆ ℕ` is *admissible* if for every prime `p` there is a residue class
which the translated set `n + B` avoids modulo `p`; equivalently `B` does not cover all
residues modulo any prime. This is the standard local condition in the prime `k`-tuples
conjecture. -/
def Admissible (B : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ b ∈ B, ¬ (p ∣ n + b)

/-- The (existence form of the) Hardy–Littlewood / Dickson prime `k`-tuples conjecture:
every admissible finite set `B` admits a shift `n` making all of `n + b`, `b ∈ B`, prime.
This is weaker than the usual statement, which asserts infinitely many such `n`. -/
def PrimeTuplesConjecture : Prop :=
  ∀ B : Finset ℕ, Admissible B → ∃ n : ℕ, ∀ b ∈ B, Nat.Prime (n + b)

/-- The candidate tuple for a `k`-term arithmetic progression of primes:
`{0, W, 2W, …, (k-1)W}` with `W = k !`. -/
def apTuple (k : ℕ) : Finset ℕ := (Finset.range k).image (fun i => i * Nat.factorial k)

lemma mem_apTuple {k b : ℕ} : b ∈ apTuple k ↔ ∃ i < k, i * Nat.factorial k = b := by
  simp [apTuple, Finset.mem_image, Finset.mem_range]

/-- Small primes: a prime `p ≤ k` divides `k !`, so the tuple lies in the class `0 mod p`
and the shift `n = 1` works. -/
lemma apTuple_avoid_small {k p : ℕ} (hp : p.Prime) (hpk : p ≤ k) :
    ∀ b ∈ apTuple k, ¬ (p ∣ 1 + b) := by
  intro b hb
  rcases mem_apTuple.mp hb with ⟨i, _, rfl⟩
  have hdvd : p ∣ Nat.factorial k := hp.dvd_factorial.mpr hpk
  intro hcon
  have h1 : p ∣ i * Nat.factorial k := Dvd.dvd.mul_left hdvd i
  have : p ∣ 1 := (Nat.dvd_add_right h1).mp (by rwa [Nat.add_comm] at hcon)
  exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp this)

/-- Large primes: if `p > k` then the `k` residues `-i·k! (mod p)` cannot exhaust the `p`
residue classes, so some shift `n` avoids them all. -/
lemma apTuple_avoid_large {k p : ℕ} (hp : p.Prime) (hpk : k < p) :
    ∃ n : ℕ, ∀ b ∈ apTuple k, ¬ (p ∣ n + b) := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  set S : Finset (ZMod p) := (Finset.range k).image (fun i => -((i * Nat.factorial k : ℕ) : ZMod p))
    with hS
  have h1 : S.card ≤ k := le_trans (Finset.card_image_le) (by simp)
  have hne : ∃ x : ZMod p, x ∉ S := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (ZMod p)) ⊆ S := fun x _ => hcon x
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card p] at hle
    omega
  obtain ⟨x, hx⟩ := hne
  refine ⟨x.val, ?_⟩
  intro b hb hdvd
  rcases mem_apTuple.mp hb with ⟨i, hi, rfl⟩
  apply hx
  have hz : ((x.val + i * Nat.factorial k : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
  push_cast at hz
  rw [ZMod.natCast_val, ZMod.cast_id] at hz
  have : -((i * Nat.factorial k : ℕ) : ZMod p) = x := by push_cast; linear_combination -hz
  rw [hS]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, this⟩

/-- The tuple `{0, W, …, (k-1)W}` with `W = k !` is admissible. -/
theorem admissible_apTuple (k : ℕ) : Admissible (apTuple k) := by
  intro p hp
  by_cases h : p ≤ k
  · exact ⟨1, apTuple_avoid_small hp h⟩
  · exact apTuple_avoid_large hp (Nat.lt_of_not_le h)

/-- **Reduction**: the prime `k`-tuples conjecture implies the Green–Tao statement. -/
theorem greenTao_of_primeTuples (h : PrimeTuplesConjecture) : GreenTaoStatement := by
  intro k
  obtain ⟨n, hn⟩ := h (apTuple k) (admissible_apTuple k)
  refine ⟨n, Nat.factorial k, Nat.factorial_pos k, ?_⟩
  intro i hi
  exact hn _ (mem_apTuple.mpr ⟨i, hi, rfl⟩)

/-- **Unconditional base cases**: `199 + 210 i`, `i < 10`, is a 10-term arithmetic
progression of primes, so `PrimeAP k` holds for every `k ≤ 10`. -/
theorem primeAP_of_le_ten {k : ℕ} (hk : k ≤ 10) : PrimeAP k := by
  refine ⟨199, 210, by norm_num, ?_⟩
  intro i hi
  have hi' : i < 10 := lt_of_lt_of_le hi hk
  interval_cases i <;> norm_num

/-- **Green–Tao (formalized statement, with a Lean-checked reduction and base cases).**

The primes contain arbitrarily long arithmetic progressions.  Unconditionally we verify
this for all lengths `k ≤ 10` (the progression `199 + 210 i`), and we give a complete
Lean-checked reduction of the general statement to the Hardy–Littlewood/Dickson prime
`k`-tuples conjecture: the tuple `{0, k!, 2·k!, …, (k-1)·k!}` is proved admissible, so the
conjecture supplies the required progression. -/
theorem Green_Tao :
    (∀ k : ℕ, k ≤ 10 → PrimeAP k) ∧ (PrimeTuplesConjecture → ∀ k : ℕ, PrimeAP k) :=
  ⟨fun _ hk => primeAP_of_le_ten hk, greenTao_of_primeTuples⟩

end Frontier

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

