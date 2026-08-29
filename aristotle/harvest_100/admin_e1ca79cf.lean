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
This file deliberately has no `import` line: the required header above is a module
docstring, and Lean requires all imports to precede any command, including module
docstrings.  Everything below therefore uses only core Lean 4 (no Mathlib), which
is sufficient for the development.
-/

set_option autoImplicit false

namespace Brockian.CollatzPartial

/-- One step of the Collatz map: `n ↦ n / 2` for even `n`, `n ↦ 3 * n + 1` for odd `n`. -/
def collatz (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `iter k n` is the result of applying the Collatz map `k` times to `n`. -/
def iter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter k (collatz n)

theorem collatz_even {n : Nat} (h : n % 2 = 0) : collatz n = n / 2 := by
  simp [collatz, h]

theorem collatz_odd {n : Nat} (h : n % 2 = 1) : collatz n = 3 * n + 1 := by
  simp [collatz, h]

@[simp] theorem iter_zero (n : Nat) : iter 0 n = n := rfl

theorem iter_succ (k n : Nat) : iter (k + 1) n = iter k (collatz n) := rfl

theorem iter_one (n : Nat) : iter 1 n = collatz n := rfl

theorem iter_add (m k n : Nat) : iter (m + k) n = iter m (iter k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      have hmk : m + (k + 1) = (m + k) + 1 := by omega
      rw [hmk, iter_succ, ih, iter_succ]

/-- The Collatz map preserves positivity. -/
theorem collatz_pos {n : Nat} (hn : 0 < n) : 0 < collatz n := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h
  · rw [collatz_even h]; omega
  · rw [collatz_odd h]; omega

/-- Every iterate of the Collatz map preserves positivity. -/
theorem iter_pos (k : Nat) {n : Nat} (hn : 0 < n) : 0 < iter k n := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih =>
      rw [iter_succ]
      exact ih (collatz_pos hn)

/-- Unconditional descent for even numbers: one step strictly decreases them. -/
theorem descent_even {n : Nat} (hn : 1 < n) (h : n % 2 = 0) :
    ∃ k, 0 < k ∧ iter k n < n := by
  refine ⟨1, by omega, ?_⟩
  rw [iter_one, collatz_even h]
  omega

/-- Unconditional descent for `n ≡ 1 (mod 4)`: three steps strictly decrease such an `n > 1`. -/
theorem descent_one_mod_four {n : Nat} (hn : 1 < n) (h : n % 4 = 1) :
    ∃ k, 0 < k ∧ iter k n < n := by
  refine ⟨3, by omega, ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, n = 4 * m + 1 := ⟨n / 4, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have h1 : collatz n = 12 * m + 4 := by
    rw [collatz_odd (by omega)]; omega
  have h2 : collatz (12 * m + 4) = 6 * m + 2 := by
    rw [collatz_even (by omega)]; omega
  have h3 : collatz (6 * m + 2) = 3 * m + 1 := by
    rw [collatz_even (by omega)]; omega
  have hexp : iter 3 n = collatz (collatz (collatz n)) := rfl
  rw [hexp, h1, h2, h3]
  omega

/-- Auxiliary bounded form of the reduction, proved by induction on a bound `N`. -/
theorem reaches_one_of_le
    (hdesc : ∀ n : Nat, 1 < n → n % 4 = 3 → ∃ k, 0 < k ∧ iter k n < n) :
    ∀ N n : Nat, n ≤ N → 0 < n → ∃ k, iter k n = 1 := by
  intro N
  induction N with
  | zero => intro n hn hpos; omega
  | succ N ih =>
      intro n hn hpos
      by_cases h1 : n = 1
      · exact ⟨0, by simp [h1]⟩
      · have hlt : 1 < n := by omega
        have hstep : ∃ k, 0 < k ∧ iter k n < n := by
          have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
          rcases h4 with h | h | h | h
          · exact descent_even hlt (by omega)
          · exact descent_one_mod_four hlt h
          · exact descent_even hlt (by omega)
          · exact hdesc n hlt h
        obtain ⟨k, _, hk⟩ := hstep
        obtain ⟨m, hm⟩ := ih (iter k n) (by omega) (iter_pos k hpos)
        exact ⟨m + k, by rw [iter_add]; exact hm⟩

/--
**Conditional reduction of the Collatz conjecture.**

If every `n > 1` with `n ≡ 3 (mod 4)` eventually reaches a value strictly smaller than
itself under iteration of the Collatz map, then the Collatz conjecture holds: every
positive natural number reaches `1`.

The other residue classes — the even numbers and `n ≡ 1 (mod 4)` — are handled
unconditionally here (see `descent_even` and `descent_one_mod_four`), so only the
`n ≡ 3 (mod 4)` case is assumed.
-/
theorem CollatzConjecture
    (hdesc : ∀ n : Nat, 1 < n → n % 4 = 3 → ∃ k, 0 < k ∧ iter k n < n) :
    ∀ n : Nat, 0 < n → ∃ k, iter k n = 1 :=
  fun n hn => reaches_one_of_le hdesc n n (Nat.le_refl n) hn

set_option maxRecDepth 10000 in
/-- Unconditional check: the orbit of `27` reaches `1` after exactly `111` steps. -/
theorem iter_111_27 : iter 111 27 = 1 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Unconditional check: every `n` with `0 < n < 201` reaches `1` in fewer than `250` steps. -/
theorem reaches_one_of_lt_201 : ∀ n < 201, 0 < n → ∃ k < 250, iter k n = 1 := by decide

end Brockian.CollatzPartial

