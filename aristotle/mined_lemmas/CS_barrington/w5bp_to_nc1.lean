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

theorem w5bp_to_nc1 {f : (n : ℕ) → (Fin n → Bool) → Bool} (hf : W5BP f) : NC1 f := by
  obtain ⟨P, c, hP⟩ := hf
  have key : ∀ n, ∃ D : Circuit n, (∀ x, D.eval x = f n x) ∧
      D.depth ≤ 11 * ((c + 1) * (Nat.log 2 (n + 1) + 1) + (c + 1)) + 3 := by
    intro n
    obtain ⟨⟨σ, hσ, hcomp⟩, hlen⟩ := hP n
    have hPlen : (P n).length ≤ 2 ^ ((c + 1) * (Nat.log 2 (n + 1) + 1) + (c + 1)) := by
      refine hlen.trans ?_
      have h1 : n + 1 ≤ 2 ^ (Nat.log 2 (n + 1) + 1) :=
        le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) (n + 1))
      have h2 : ((n : ℕ) + 1) ^ (c + 1) ≤ (2 ^ (Nat.log 2 (n + 1) + 1)) ^ (c + 1) :=
        Nat.pow_le_pow_left h1 _
      have hpow : (2 : ℕ) ^ ((c + 1) * (Nat.log 2 (n + 1) + 1) + (c + 1))
          = (2 ^ (Nat.log 2 (n + 1) + 1)) ^ (c + 1) * 2 ^ (c + 1) := by
        rw [pow_add, ← pow_mul, mul_comm (c + 1) (Nat.log 2 (n + 1) + 1)]
      have h3 : c + 1 ≤ 2 ^ c := Nat.lt_two_pow_self
      have h4 : ((n : ℕ) + 1) ^ c ≤ (n + 1) ^ (c + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hY : (1 : ℕ) ≤ ((n : ℕ) + 1) ^ (c + 1) := Nat.one_le_pow _ _ (by omega)
      have h6 : (2 * c + 2) * ((n : ℕ) + 1) ^ (c + 1)
          ≤ (2 ^ (Nat.log 2 (n + 1) + 1)) ^ (c + 1) * 2 ^ (c + 1) := by
        rw [mul_comm]
        refine Nat.mul_le_mul h2 ?_
        calc 2 * c + 2 ≤ 2 * 2 ^ c := by omega
          _ = 2 ^ (c + 1) := by ring
      have h7 : c * ((n : ℕ) + 1) ^ c + c ≤ (2 * c + 2) * ((n : ℕ) + 1) ^ (c + 1) := by
        have hcY : c * ((n : ℕ) + 1) ^ c ≤ c * ((n : ℕ) + 1) ^ (c + 1) :=
          Nat.mul_le_mul_left _ h4
        nlinarith [hY, hcY]
      rw [hpow]
      exact le_trans h7 h6
    refine ⟨prodCirc ((c + 1) * (Nat.log 2 (n + 1) + 1) + (c + 1)) (P n) σ, fun x => ?_,
      prodCirc_depth _ (P n) σ⟩
    rw [prodCirc_eval _ (P n) hPlen σ x, hcomp x]
    by_cases hx : f n x
    · simp [hx]
    · have hne : (1 : Perm5) ≠ σ := fun hh => hσ hh.symm
      simp [hx, hne]
  choose D hD1 hD2 using key
  refine ⟨D, 22 * (c + 1) + 3, fun n => ⟨hD1 n, ?_⟩⟩
  refine (hD2 n).trans ?_
  have hexp : 11 * ((c + 1) * (Nat.log 2 (n + 1) + 1) + (c + 1)) + 3
      = 11 * (c + 1) * Nat.log 2 (n + 1) + (22 * (c + 1) + 3) := by ring
  rw [hexp]
  have : 11 * (c + 1) * Nat.log 2 (n + 1) ≤ (22 * (c + 1) + 3) * Nat.log 2 (n + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- Sanity check that the classes are not vacuous: the family "the first input bit" is
in `NC1`, hence (by `CS.barrington`) also in `W5BP`. -/
example : NC1 (fun n (x : Fin n → Bool) => if h : 0 < n then x ⟨0, h⟩ else false) := by
  refine ⟨fun n => if h : 0 < n then Circuit.var ⟨0, h⟩ else Circuit.const false, 0,
    fun n => ⟨fun x => ?_, ?_⟩⟩
  · by_cases h : 0 < n <;> simp [h, Circuit.eval]
  · by_cases h : 0 < n <;> simp [h, Circuit.depth]

