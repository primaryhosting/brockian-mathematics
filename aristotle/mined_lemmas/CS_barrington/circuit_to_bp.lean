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

theorem circuit_to_bp {n : ℕ} (C : Circuit n) :
    ∀ ρ : Perm5, CompLen C.eval (ρ * c5 * ρ⁻¹) (4 ^ C.depth) := by
  induction C with
  | var i =>
      intro ρ
      refine ⟨[Instr.query i 1 (ρ * c5 * ρ⁻¹)], fun x => ?_, by simp [Circuit.depth]⟩
      by_cases hx : x i <;> simp [Circuit.eval, Instr.run, hx]
  | const b =>
      intro ρ
      cases b
      · exact ⟨[], fun x => by simp [Circuit.eval], by simp⟩
      · exact ⟨[Instr.const (ρ * c5 * ρ⁻¹)], fun x => by simp [Circuit.eval, Instr.run], by simp [Circuit.depth]⟩
  | not C ih =>
      intro ρ
      obtain ⟨ρ', hρ'⟩ := exists_conj_inv ρ
      have h := ih ρ'
      rw [hρ'] at h
      have h2 := h.neg
      have h3 : CompLen (Circuit.not C).eval (ρ * c5 * ρ⁻¹) (max 1 (4 ^ C.depth)) :=
        h2.of_eq (fun x => rfl)
      refine h3.mono ?_
      have h4 : (1 : ℕ) ≤ 4 ^ C.depth := Nat.one_le_pow _ _ (by norm_num)
      have h5 : 4 ^ C.depth ≤ 4 ^ (C.depth + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [Circuit.depth]
      omega
  | and C D ihC ihD =>
      intro ρ
      obtain ⟨a, b, hab⟩ := exists_conj_commutator ρ
      obtain ⟨a', ha'⟩ := exists_conj_inv a
      obtain ⟨b', hb'⟩ := exists_conj_inv b
      have h1 := ihC a
      have h2 := ihD b
      have h3 := ihC a'
      have h4 := ihD b'
      rw [ha'] at h3
      rw [hb'] at h4
      have hcomm := CompLen.commutator h1 h2 h3 h4
      rw [hab] at hcomm
      have h5 : CompLen (Circuit.and C D).eval (ρ * c5 * ρ⁻¹)
          (4 ^ C.depth + 4 ^ D.depth + 4 ^ C.depth + 4 ^ D.depth) := hcomm.of_eq (fun x => rfl)
      refine h5.mono ?_
      have hC : (4 : ℕ) ^ C.depth ≤ 4 ^ (max C.depth D.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hD : (4 : ℕ) ^ D.depth ≤ 4 ^ (max C.depth D.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have : (4 : ℕ) ^ (max C.depth D.depth + 1) = 4 * 4 ^ (max C.depth D.depth) := by ring
      simp only [Circuit.depth, this]
      omega
  | or C D ihC ihD =>
      intro ρ
      obtain ⟨ρ', hρ'⟩ := exists_conj_inv ρ
      obtain ⟨a, b, hab⟩ := exists_conj_commutator ρ'
      obtain ⟨a', ha'⟩ := exists_conj_inv a
      obtain ⟨b', hb'⟩ := exists_conj_inv b
      -- programs for the negations
      have n1 : CompLen (fun x => !C.eval x) (a * c5 * a⁻¹) (max 1 (4 ^ C.depth)) := by
        have := ihC a'
        rw [ha'] at this
        exact this.neg
      have n2 : CompLen (fun x => !D.eval x) (b * c5 * b⁻¹) (max 1 (4 ^ D.depth)) := by
        have := ihD b'
        rw [hb'] at this
        exact this.neg
      have n3 : CompLen (fun x => !C.eval x) (a * c5 * a⁻¹)⁻¹ (max 1 (4 ^ C.depth)) := by
        have := ihC a
        rw [← inv_inv (a * c5 * a⁻¹)] at this
        exact this.neg
      have n4 : CompLen (fun x => !D.eval x) (b * c5 * b⁻¹)⁻¹ (max 1 (4 ^ D.depth)) := by
        have := ihD b
        rw [← inv_inv (b * c5 * b⁻¹)] at this
        exact this.neg
      have hcomm := CompLen.commutator n1 n2 n3 n4
      rw [hab, hρ'] at hcomm
      have hneg := hcomm.neg
      have h5 : CompLen (Circuit.or C D).eval (ρ * c5 * ρ⁻¹)
          (max 1 (max 1 (4 ^ C.depth) + max 1 (4 ^ D.depth) + max 1 (4 ^ C.depth) +
            max 1 (4 ^ D.depth))) := by
        refine hneg.of_eq (fun x => ?_)
        simp [Circuit.eval]
      refine h5.mono ?_
      have hC1 : (1 : ℕ) ≤ 4 ^ C.depth := Nat.one_le_pow _ _ (by norm_num)
      have hD1 : (1 : ℕ) ≤ 4 ^ D.depth := Nat.one_le_pow _ _ (by norm_num)
      have hC : (4 : ℕ) ^ C.depth ≤ 4 ^ (max C.depth D.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hD : (4 : ℕ) ^ D.depth ≤ 4 ^ (max C.depth D.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have h6 : (4 : ℕ) ^ (max C.depth D.depth + 1) = 4 * 4 ^ (max C.depth D.depth) := by ring
      have h7 : (1 : ℕ) ≤ 4 ^ (max C.depth D.depth) := Nat.one_le_pow _ _ (by norm_num)
      simp only [Circuit.depth, h6]
      omega

/-! ### From branching programs to circuits -/

/-- A balanced disjunction of a list of circuits, with fuel `k`. -/
