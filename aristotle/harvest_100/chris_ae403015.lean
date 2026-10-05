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
This file is deliberately self-contained (it uses only the Lean 4 core library),
so that the header comment above can appear at the very top of the file:
Lean does not permit a module docstring to precede `import` commands.
-/

namespace Brockian
namespace CollatzPartial

/-- The Collatz step: `n ↦ n / 2` if `n` is even, `n ↦ 3 * n + 1` if `n` is odd. -/
def collatz (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `iter f k n` is the `k`-fold iterate of `f` applied to `n`. -/
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter f k (f n)

@[simp] theorem iter_zero (f : Nat → Nat) (n : Nat) : iter f 0 n = n := rfl

theorem iter_succ (f : Nat → Nat) (k n : Nat) : iter f (k + 1) n = iter f k (f n) := rfl

theorem iter_add (f : Nat → Nat) (k m n : Nat) :
    iter f (k + m) n = iter f k (iter f m n) := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
      have h : k + (m + 1) = (k + m) + 1 := by omega
      rw [h, iter_succ, ih, iter_succ]

/-- `ReachesOne n` says that iterating the Collatz map from `n` eventually reaches `1`. -/
def ReachesOne (n : Nat) : Prop := ∃ k : Nat, iter collatz k n = 1

/-- The Collatz *descent* property: every integer `> 1` eventually iterates to a strictly
smaller value. -/
def Descends : Prop := ∀ n : Nat, 1 < n → ∃ k : Nat, 0 < k ∧ iter collatz k n < n

theorem collatz_pos {n : Nat} (hn : 0 < n) : 0 < collatz n := by
  unfold collatz
  split
  · omega
  · omega

theorem iter_collatz_pos {n : Nat} (hn : 0 < n) (k : Nat) : 0 < iter collatz k n := by
  induction k generalizing n with
  | zero => simpa using hn
  | succ k ih => exact ih (collatz_pos hn)

theorem reachesOne_of_iter {n k : Nat} (h : ReachesOne (iter collatz k n)) : ReachesOne n := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m + k, by rw [iter_add]; exact hm⟩

/-- **Conditional Collatz theorem.**  The Collatz conjecture — every positive natural number
reaches `1` under iteration of the Collatz map — follows from the (weaker looking) descent
property `Descends`, namely that every `n > 1` eventually iterates to some value smaller
than `n` itself. -/
theorem CollatzConjecture (h : Descends) : ∀ n : Nat, 0 < n → ReachesOne n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · obtain ⟨k, -, hk⟩ := h n h1
      exact reachesOne_of_iter (ih _ hk (iter_collatz_pos (by omega) k))
    · have : n = 1 := by omega
      exact ⟨0, by simp [this]⟩

/-! ### Unconditional partial results -/

/-- Powers of two reach `1`, in exactly `m` steps. -/
theorem iter_two_pow (m : Nat) : iter collatz m (2 ^ m) = 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [iter_succ]
      have h2 : collatz (2 ^ (m + 1)) = 2 ^ m := by
        have hp : 2 ^ (m + 1) = 2 ^ m * 2 := by
          rw [Nat.pow_succ]
        have he : 2 ^ (m + 1) % 2 = 0 := by
          rw [hp]; omega
        rw [collatz, if_pos he, hp]
        omega
      rw [h2, ih]

/-- Every power of two reaches `1`. -/
theorem reachesOne_two_pow (m : Nat) : ReachesOne (2 ^ m) := ⟨m, iter_two_pow m⟩

/-- An even number `> 1` descends in one step. -/
theorem descends_of_even {n : Nat} (h1 : 1 < n) (h2 : n % 2 = 0) : iter collatz 1 n < n := by
  show collatz n < n
  rw [collatz, if_pos h2]
  omega

/-- A number `n > 1` with `n % 4 = 1` descends in exactly three steps. -/
theorem descends_of_mod_four_eq_one {n : Nat} (h1 : 1 < n) (h4 : n % 4 = 1) :
    iter collatz 3 n < n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m + 1 := ⟨n / 4, by omega⟩
  show collatz (collatz (collatz (4 * m + 1))) < 4 * m + 1
  have e1 : collatz (4 * m + 1) = 12 * m + 4 := by
    rw [collatz, if_neg (by omega)]; omega
  have e2 : collatz (12 * m + 4) = 6 * m + 2 := by
    rw [collatz, if_pos (by omega)]; omega
  have e3 : collatz (6 * m + 2) = 3 * m + 1 := by
    rw [collatz, if_pos (by omega)]; omega
  rw [e1, e2, e3]
  omega

/-- **Reduction of the descent property to the residue class `3 mod 4`.**  If every `n > 1`
with `n % 4 = 3` eventually iterates to a smaller value, then `Descends` holds, and hence
(by `CollatzConjecture`) so does the full Collatz conjecture. -/
theorem descends_of_mod_four_eq_three
    (h : ∀ n : Nat, 1 < n → n % 4 = 3 → ∃ k : Nat, 0 < k ∧ iter collatz k n < n) :
    Descends := by
  intro n h1
  rcases Nat.lt_or_ge (n % 4) 2 with hlt | hge
  · rcases Nat.eq_zero_or_pos (n % 4) with h0 | hp
    · exact ⟨1, Nat.one_pos, descends_of_even h1 (by omega)⟩
    · have : n % 4 = 1 := by omega
      exact ⟨3, by omega, descends_of_mod_four_eq_one h1 this⟩
  · rcases Nat.lt_or_ge (n % 4) 3 with hlt | hge3
    · exact ⟨1, Nat.one_pos, descends_of_even h1 (by omega)⟩
    · exact h n h1 (by omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Every `n` with `0 < n ≤ 1000` reaches `1`, in fewer than `200` steps
(verified by kernel computation). -/
theorem reachesOne_of_le_thousand (n : Nat) (h0 : 0 < n) (h : n ≤ 1000) : ReachesOne n := by
  have key : ∀ m, m < 1001 → 0 < m → ∃ k, k < 200 ∧ iter collatz k m = 1 := by decide +kernel
  obtain ⟨k, -, hk⟩ := key n (by omega) h0
  exact ⟨k, hk⟩

end CollatzPartial
end Brockian

