/-
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Barrington's theorem

We formalise Barrington's theorem: the class of Boolean function families computed by
logarithmic-depth fan-in-two Boolean circuits (`NC¹`) coincides with the class of families
computed by polynomial-length width-`5` permutation branching programs.

* `CS.Barrington.Circuit` : fan-in two Boolean circuits over `{¬, ∧, ∨}` and constants.
* `CS.Barrington.Instr`, `CS.Barrington.run` : width-5 permutation branching programs,
  i.e. lists of instructions, each of which multiplies the running value in `S₅` by a
  permutation depending on (at most) one input bit.
* `CS.Barrington.NC1` and `CS.Barrington.W5BP` : the two classes.
* `CS.barrington` : the two classes are equal.
-/

namespace CS
namespace Barrington

open Equiv

/-- The symmetric group on five points. -/
abbrev Perm5 := Equiv.Perm (Fin 5)

/-! ### Boolean circuits -/

/-- Fan-in two Boolean circuits (formulas) on `n` inputs. -/
inductive Circuit (n : ℕ) where
  | var : Fin n → Circuit n
  | const : Bool → Circuit n
  | not : Circuit n → Circuit n
  | and : Circuit n → Circuit n → Circuit n
  | or : Circuit n → Circuit n → Circuit n

/-- The Boolean function computed by a circuit. -/

theorem nc1_to_w5bp {f : (n : ℕ) → (Fin n → Bool) → Bool} (hf : NC1 f) : W5BP f := by
  obtain ⟨C, c, hC⟩ := hf
  have key : ∀ n, ∃ Q : List (Instr n), Comp Q (f n) c5 ∧ Q.length ≤ 4 ^ (C n).depth := by
    intro n
    obtain ⟨Q, hQ, hlen⟩ := circuit_to_bp (C n) 1
    refine ⟨Q, fun x => ?_, hlen⟩
    rw [hQ x]
    simp [(hC n).1 x]
  choose Q hQ hlen using key
  refine ⟨Q, max (4 ^ c) (2 * c), fun n => ⟨⟨c5, c5_ne_one, hQ n⟩, ?_⟩⟩
  have h2L : (2 : ℕ) ^ Nat.log 2 (n + 1) ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
  have h4L : (4 : ℕ) ^ Nat.log 2 (n + 1) ≤ (n + 1) ^ 2 := by
    have : (4 : ℕ) ^ Nat.log 2 (n + 1) = (2 ^ Nat.log 2 (n + 1)) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [this]
    exact Nat.pow_le_pow_left h2L 2
  have hstep : (4 : ℕ) ^ (c * Nat.log 2 (n + 1) + c) ≤ 4 ^ c * (n + 1) ^ (2 * c) := by
    have h1 : (4 : ℕ) ^ (c * Nat.log 2 (n + 1) + c)
        = 4 ^ c * (4 ^ Nat.log 2 (n + 1)) ^ c := by
      rw [pow_add, pow_mul]
      ring
    have h2 : ((4 : ℕ) ^ Nat.log 2 (n + 1)) ^ c ≤ ((n + 1) ^ 2) ^ c := Nat.pow_le_pow_left h4L c
    have h3 : ((n + 1) ^ 2 : ℕ) ^ c = (n + 1) ^ (2 * c) := by rw [← pow_mul]
    rw [h1, ← h3]
    exact Nat.mul_le_mul_left _ h2
  have hd : (4 : ℕ) ^ (C n).depth ≤ 4 ^ (c * Nat.log 2 (n + 1) + c) :=
    Nat.pow_le_pow_right (by norm_num) (hC n).2
  have hK1 : (4 : ℕ) ^ c ≤ max (4 ^ c) (2 * c) := le_max_left _ _
  have hK2 : ((n : ℕ) + 1) ^ (2 * c) ≤ (n + 1) ^ max (4 ^ c) (2 * c) :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  calc (Q n).length ≤ 4 ^ (C n).depth := hlen n
    _ ≤ 4 ^ (c * Nat.log 2 (n + 1) + c) := hd
    _ ≤ 4 ^ c * (n + 1) ^ (2 * c) := hstep
    _ ≤ max (4 ^ c) (2 * c) * (n + 1) ^ max (4 ^ c) (2 * c) := Nat.mul_le_mul hK1 hK2
    _ ≤ max (4 ^ c) (2 * c) * (n + 1) ^ max (4 ^ c) (2 * c) + max (4 ^ c) (2 * c) :=
        Nat.le_add_right _ _

