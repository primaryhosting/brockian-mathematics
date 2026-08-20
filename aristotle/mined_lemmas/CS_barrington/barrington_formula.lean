import Mathlib

/-!
# Basic definitions for Barrington's theorem

* Boolean formulas over the basis `{¬, ∧, ∨}` (with constants), together with their
  depth and semantics.  Non-uniform `NC¹` is the class of families of boolean functions
  computed by formulas of logarithmic depth.
* Width-5 permutation branching programs: a program is a list of instructions, each of
  which reads one input bit and outputs one of two permutations of `Fin 5` (or is a
  constant instruction).  The value of the program is the product of the permutations
  produced by its instructions, and the program accepts iff this product lies in a
  designated set of accepting permutations.
-/

namespace CS

open Equiv Equiv.Perm

/-- Permutations of a five element set. -/
abbrev Perm5 := Equiv.Perm (Fin 5)

/-- A permutation of `Fin 5` is a five-cycle if it is a cycle whose support is everything. -/

theorem barrington_formula {n : ℕ} (φ : Formula n) :
    ∀ σ : Perm5, IsFiveCycle σ →
      ∃ P : List (Instr n), P.length ≤ 4 ^ φ.depth ∧ Computes P σ φ.eval := by
  induction φ with
  | const b =>
      intro σ _
      cases b with
      | true =>
          refine ⟨[.const σ], by simp [Formula.depth], ?_⟩
          intro x; simp [BPeval, Instr.run, Formula.eval]
      | false =>
          refine ⟨[], by simp, ?_⟩
          intro x; simp [Formula.eval]
  | var i =>
      intro σ _
      refine ⟨[.test i σ 1], by simp [Formula.depth], ?_⟩
      intro x
      by_cases h : x i <;> simp [BPeval, Instr.run, Formula.eval, h]
  | not p ih =>
      intro σ hσ
      obtain ⟨P, hlen, hP⟩ := ih σ⁻¹ hσ.inv
      refine ⟨lmulBP σ P, ?_, ?_⟩
      · rw [length_lmulBP]
        have h1 : (1 : ℕ) ≤ 4 ^ p.depth := Nat.one_le_pow _ _ (by norm_num)
        have h2 : 4 ^ p.depth ≤ 4 ^ (p.depth + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        simp only [Formula.depth, max_le_iff]
        exact ⟨le_trans hlen h2, le_trans h1 h2⟩
      · exact bp_not hP
  | and p q ihp ihq =>
      intro σ hσ
      obtain ⟨α, β, hα, hβ, hcomm⟩ := exists_commutator_eq σ hσ
      obtain ⟨P₁, hl1, hP1⟩ := ihp α hα
      obtain ⟨P₂, hl2, hP2⟩ := ihq β hβ
      obtain ⟨P₃, hl3, hP3⟩ := ihp α⁻¹ hα.inv
      obtain ⟨P₄, hl4, hP4⟩ := ihq β⁻¹ hβ.inv
      refine ⟨P₁ ++ P₂ ++ P₃ ++ P₄, ?_, ?_⟩
      · have hm : ∀ d : ℕ, d ≤ max p.depth q.depth → (4:ℕ) ^ d ≤ 4 ^ (max p.depth q.depth) :=
          fun d hd => Nat.pow_le_pow_right (by norm_num) hd
        have e1 := hm p.depth (le_max_left _ _)
        have e2 := hm q.depth (le_max_right _ _)
        simp only [List.length_append, Formula.depth, pow_succ]
        omega
      · rw [← hcomm]
        exact bp_and hP1 hP2 hP3 hP4
  | or p q ihp ihq =>
      intro σ hσ
      obtain ⟨α, β, hα, hβ, hcomm⟩ := exists_commutator_eq σ⁻¹ hσ.inv
      -- programs for the negations of `p` and `q`
      have hnot : ∀ (r : Formula n),
          (∀ γ : Perm5, IsFiveCycle γ →
            ∃ P : List (Instr n), P.length ≤ 4 ^ r.depth ∧ Computes P γ r.eval) →
          ∀ γ : Perm5, IsFiveCycle γ →
            ∃ P : List (Instr n), P.length ≤ 4 ^ r.depth ∧
              Computes P γ (fun x => !r.eval x) := by
        intro r ihr γ hγ
        obtain ⟨P, hlen, hP⟩ := ihr γ⁻¹ hγ.inv
        refine ⟨lmulBP γ P, ?_, bp_not hP⟩
        rw [length_lmulBP]
        have h1 : (1 : ℕ) ≤ 4 ^ r.depth := Nat.one_le_pow _ _ (by norm_num)
        omega
      obtain ⟨P₁, hl1, hP1⟩ := hnot p ihp α hα
      obtain ⟨P₂, hl2, hP2⟩ := hnot q ihq β hβ
      obtain ⟨P₃, hl3, hP3⟩ := hnot p ihp α⁻¹ hα.inv
      obtain ⟨P₄, hl4, hP4⟩ := hnot q ihq β⁻¹ hβ.inv
      have hQ : Computes (P₁ ++ P₂ ++ P₃ ++ P₄) σ⁻¹
          (fun x => (!p.eval x) && (!q.eval x)) := by
        rw [← hcomm]; exact bp_and hP1 hP2 hP3 hP4
      refine ⟨lmulBP σ (P₁ ++ P₂ ++ P₃ ++ P₄), ?_, ?_⟩
      · rw [length_lmulBP]
        have hm : ∀ d : ℕ, d ≤ max p.depth q.depth → (4:ℕ) ^ d ≤ 4 ^ (max p.depth q.depth) :=
          fun d hd => Nat.pow_le_pow_right (by norm_num) hd
        have e1 := hm p.depth (le_max_left _ _)
        have e2 := hm q.depth (le_max_right _ _)
        have h1 : (1 : ℕ) ≤ 4 ^ (max p.depth q.depth) := Nat.one_le_pow _ _ (by norm_num)
        simp only [List.length_append, Formula.depth, pow_succ, max_le_iff]
        omega
      · have := bp_not hQ
        intro x
        have hx := this x
        simpa [Formula.eval, Bool.not_and, Bool.or_comm] using hx

end CS

import RequestProject.Basic
import RequestProject.Forward
import RequestProject.Backward

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Barrington's theorem

`NC¹` (non-uniform: families of boolean functions computed by fan-in two boolean formulas
of logarithmic depth, `CS.InNC1`) coincides with the class of families of boolean functions
computed by polynomial-length width-5 permutation branching programs (`CS.InW5BP`).

The hard direction is Barrington's construction (`CS.barrington_formula`): a formula of
depth `d` is simulated by a program of length at most `4 ^ d`, in normal form with respect
to any prescribed five-cycle.  The easy direction (`CS.exists_formula_of_bp`) is a divide
and conquer simulation of a program of length `ℓ` by a formula of depth `O(log ℓ)`.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

open Equiv Equiv.Perm

