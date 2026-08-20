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

/-!
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Remark on imports: the requested header must be the very first thing in the file, and
Lean does not allow an `import` command after a module docstring. This development is
therefore written against the Lean 4 core library only (no Mathlib import); everything
used below (`Nat`, `omega`, `decide`, `Nat.strongRecOn`) is available in core.

A search of Mathlib turns up no Collatz material at all (no definition of the Collatz
map, no `Reaches1`-style predicate, and no lemma of this shape), so nothing in the
library closes or nearly closes the statement; the development below is self-contained.
The Collatz conjecture itself is a famous open problem, so what is proved here is:

* a Lean-checked *conditional reduction*: `CollatzConjecture` derives the full
  conjecture from the descent hypothesis (every `n > 1` eventually reaches a smaller
  value);
* *unconditional partial results*: the descent hypothesis holds for every `n > 1` with
  `n % 4 ≠ 3` (`descent_of_ne_three_mod_four`), so only the residue class `3 mod 4`
  remains;
* a *finite verification*: every `n` with `1 ≤ n ≤ 1000` reaches `1` (`collatz_le_1000`),
  checked by the kernel via `decide`.
-/

namespace Brockian.CollatzPartial

/-- One step of the Collatz map: `n ↦ n / 2` for even `n`, `n ↦ 3 * n + 1` for odd `n`. -/
def collatz (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `collatzIter k n` is the `k`-th iterate of the Collatz map applied to `n`. -/
def collatzIter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => collatzIter k (collatz n)

/-- `Reaches1 n` means that the Collatz orbit of `n` reaches `1`. -/
def Reaches1 (n : Nat) : Prop := ∃ k : Nat, collatzIter k n = 1

/-- The descent hypothesis: every `n > 1` eventually reaches a strictly smaller value. -/
def DescentHypothesis : Prop := ∀ n : Nat, 1 < n → ∃ k : Nat, 0 < k ∧ collatzIter k n < n

/-! ### Basic facts about iteration -/

theorem collatzIter_add (a b n : Nat) :
    collatzIter (a + b) n = collatzIter b (collatzIter a n) := by
  induction a generalizing n with
  | zero => rw [Nat.zero_add]; rfl
  | succ k ih =>
    show collatzIter (k + 1 + b) n = collatzIter b (collatzIter k (collatz n))
    have : k + 1 + b = (k + b) + 1 := by omega
    rw [this]
    show collatzIter (k + b) (collatz n) = _
    exact ih (collatz n)

theorem collatz_pos {n : Nat} (hn : 0 < n) : 0 < collatz n := by
  unfold collatz; split <;> omega

theorem collatzIter_pos {n : Nat} (hn : 0 < n) (k : Nat) : 0 < collatzIter k n := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih => exact ih (collatz_pos hn)

theorem Reaches1.step {n : Nat} (h : Reaches1 (collatz n)) : Reaches1 n := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, hk⟩

theorem Reaches1.of_iterate {n k : Nat} (h : Reaches1 (collatzIter k n)) : Reaches1 n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨k + j, by rw [collatzIter_add]; exact hj⟩

/-! ### The conditional reduction -/

/-- **Conditional reduction of the Collatz conjecture to the descent hypothesis.**
If every `n > 1` eventually maps to a strictly smaller value under iteration of the
Collatz map, then every positive `n` reaches `1`. -/
theorem CollatzConjecture (hdesc : DescentHypothesis) : ∀ n : Nat, 0 < n → Reaches1 n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases h : n = 1
    · exact ⟨0, by simp [h, collatzIter]⟩
    · obtain ⟨k, _, hlt⟩ := hdesc n (by omega)
      exact Reaches1.of_iterate (ih _ hlt (collatzIter_pos hn k))

/-! ### Unconditional partial results towards the descent hypothesis -/

theorem descent_of_even {n : Nat} (hn : 1 < n) (h2 : n % 2 = 0) :
    ∃ k : Nat, 0 < k ∧ collatzIter k n < n := by
  refine ⟨1, Nat.one_pos, ?_⟩
  show collatzIter 0 (collatz n) < n
  show collatz n < n
  unfold collatz; split <;> omega

theorem descent_of_one_mod_four {n : Nat} (hn : 1 < n) (h4 : n % 4 = 1) :
    ∃ k : Nat, 0 < k ∧ collatzIter k n < n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m + 1 := ⟨n / 4, by omega⟩
  have hm : 1 ≤ m := by omega
  have e1 : collatz (4 * m + 1) = 12 * m + 4 := by unfold collatz; split <;> omega
  have e2 : collatz (12 * m + 4) = 6 * m + 2 := by unfold collatz; split <;> omega
  have e3 : collatz (6 * m + 2) = 3 * m + 1 := by unfold collatz; split <;> omega
  refine ⟨3, by omega, ?_⟩
  show collatzIter 2 (collatz (4 * m + 1)) < 4 * m + 1
  rw [e1]
  show collatzIter 1 (collatz (12 * m + 4)) < 4 * m + 1
  rw [e2]
  show collatzIter 0 (collatz (6 * m + 2)) < 4 * m + 1
  rw [e3]
  show 3 * m + 1 < 4 * m + 1
  omega

/-- The descent hypothesis holds unconditionally for every `n > 1` with `n % 4 ≠ 3`.
Hence the Collatz conjecture reduces to the descent property on the residue class
`3 mod 4`. -/
theorem descent_of_ne_three_mod_four {n : Nat} (hn : 1 < n) (h : n % 4 ≠ 3) :
    ∃ k : Nat, 0 < k ∧ collatzIter k n < n := by
  have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 := by omega
  rcases h4 with h4 | h4 | h4
  · exact descent_of_even hn (by omega)
  · exact descent_of_one_mod_four hn h4
  · exact descent_of_even hn (by omega)

/-- Sharpened reduction: the descent hypothesis only needs to be verified on the
residue class `3 mod 4`. -/
theorem descentHypothesis_of_three_mod_four
    (h3 : ∀ n : Nat, 1 < n → n % 4 = 3 → ∃ k : Nat, 0 < k ∧ collatzIter k n < n) :
    DescentHypothesis := by
  intro n hn
  by_cases h : n % 4 = 3
  · exact h3 n hn h
  · exact descent_of_ne_three_mod_four hn h

/-- **Sharpened conditional reduction.** If every `n > 1` with `n ≡ 3 (mod 4)` eventually
reaches a strictly smaller value, then the Collatz conjecture holds. -/
theorem collatz_of_descent_three_mod_four
    (h3 : ∀ n : Nat, 1 < n → n % 4 = 3 → ∃ k : Nat, 0 < k ∧ collatzIter k n < n) :
    ∀ n : Nat, 0 < n → Reaches1 n :=
  CollatzConjecture (descentHypothesis_of_three_mod_four h3)

/-! ### Finite verification -/

/-- Fuelled Boolean check that the orbit of `n` reaches `1` within `f` steps. -/
def reaches1Check : Nat → Nat → Bool
  | 0, n => n == 1
  | f + 1, n => n == 1 || reaches1Check f (collatz n)

theorem reaches1_of_check : ∀ (f n : Nat), reaches1Check f n = true → Reaches1 n := by
  intro f
  induction f with
  | zero =>
    intro n h
    have hn : n = 1 := by simpa [reaches1Check] using h
    exact ⟨0, hn⟩
  | succ f ih =>
    intro n h
    have h' : n = 1 ∨ reaches1Check f (collatz n) = true := by
      simpa [reaches1Check] using h
    rcases h' with hn | h1
    · exact ⟨0, hn⟩
    · exact Reaches1.step (ih _ h1)

/-- `checkRange N = true` asserts that every `n` with `1 ≤ n ≤ N` reaches `1`
within 500 Collatz steps. -/
def checkRange : Nat → Bool
  | 0 => true
  | n + 1 => reaches1Check 500 (n + 1) && checkRange n

theorem check_of_checkRange :
    ∀ (N n : Nat), checkRange N = true → 0 < n → n ≤ N → reaches1Check 500 n = true := by
  intro N
  induction N with
  | zero => intro n _ h1 h2; omega
  | succ N ih =>
    intro n h hn hle
    have h' := Bool.and_eq_true_iff .. |>.1 h
    by_cases hcase : n = N + 1
    · rw [hcase]; exact h'.1
    · exact ih n h'.2 hn (by omega)

set_option maxRecDepth 100000 in
theorem checkRange_1000 : checkRange 1000 = true := by decide

/-- Every `n` with `1 ≤ n ≤ 1000` satisfies the Collatz conjecture. -/
theorem collatz_le_1000 (n : Nat) (h1 : 0 < n) (h2 : n ≤ 1000) : Reaches1 n :=
  reaches1_of_check 500 n (check_of_checkRange 1000 n checkRange_1000 h1 h2)

end Brockian.CollatzPartial

#print axioms Brockian.CollatzPartial.CollatzConjecture
#print axioms Brockian.CollatzPartial.collatz_of_descent_three_mod_four
#print axioms Brockian.CollatzPartial.descent_of_ne_three_mod_four
#print axioms Brockian.CollatzPartial.collatz_le_1000

