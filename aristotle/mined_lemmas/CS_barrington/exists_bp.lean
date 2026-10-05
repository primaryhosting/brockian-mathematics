/-
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean does not permit a module docstring `/-! ... -/` before `import`; the header above is
-- reproduced verbatim as the module docstring immediately after the import.)
import Mathlib

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace CS

open Equiv

/-! ## Boolean formulas (the `NC¹` side)

A `Formula n` is a fan-in-two Boolean formula over the variables `x 0, …, x (n-1)`.
Logarithmic-depth formulas are exactly (non-uniform) `NC¹`. -/

/-- Fan-in-two Boolean formulas over `n` variables. -/
inductive Formula (n : ℕ) : Type
  | const : Bool → Formula n
  | var : Fin n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n

namespace Formula

variable {n : ℕ}

/-- The Boolean function computed by a formula. -/

theorem exists_bp {n : ℕ} (F : Formula n) :
    ∀ σ : Perm5, IsFiveCycle σ → ∃ P : BP n, P.length ≤ 4 ^ F.depth ∧ Computes P σ F.eval := by
  induction F with
  | const b =>
      intro σ _
      refine ⟨[Instr.konst (if b then σ else 1)], by simp [Formula.depth], ?_⟩
      intro x
      simp [BP.eval, Instr.eval, Formula.eval]
  | var i =>
      intro σ _
      refine ⟨[Instr.query i 1 σ], by simp [Formula.depth], ?_⟩
      intro x
      by_cases h : x i = true <;> simp [BP.eval, Instr.eval, Formula.eval, h]
  | not F ih =>
      intro σ hσ
      obtain ⟨P, hlen, hc⟩ := ih σ hσ
      refine ⟨BP.mulLeft σ (BP.inv P), ?_, (computes_not hc).congr (fun x => rfl)⟩
      have h1 := BP.length_mulLeft σ (BP.inv P)
      have h2 : (BP.inv P).length = P.length := BP.length_inv P
      have h3 : (4 : ℕ) ^ F.depth ≤ 4 ^ (F.depth + 1) := pow4_le (Nat.le_succ _)
      have h4 : 1 ≤ (4 : ℕ) ^ (F.depth + 1) := Nat.one_le_pow _ _ (by norm_num)
      simp only [Formula.depth]
      omega
  | and F G ihF ihG =>
      intro σ hσ
      obtain ⟨τ, ρ, hτ, hρ, hc⟩ := exists_commutator σ hσ
      obtain ⟨P, hlP, hcP⟩ := ihF τ hτ
      obtain ⟨Q, hlQ, hcQ⟩ := ihG ρ hρ
      refine ⟨P ++ Q ++ BP.inv P ++ BP.inv Q, ?_,
        (computes_and hc hcP hcQ).congr (fun x => rfl)⟩
      rw [length_and_prog]
      have := two_add_pow4 F.depth G.depth (max F.depth G.depth) (le_max_left _ _)
        (le_max_right _ _)
      simp only [Formula.depth]
      omega
  | or F G ihF ihG =>
      intro σ hσ
      obtain ⟨τ, ρ, hτ, hρ, hc⟩ := exists_commutator σ hσ
      obtain ⟨P, hlP, hcP⟩ := ihF τ hτ
      obtain ⟨Q, hlQ, hcQ⟩ := ihG ρ hρ
      set N₁ : BP n := BP.mulLeft τ (BP.inv P) with hN₁
      set N₂ : BP n := BP.mulLeft ρ (BP.inv Q) with hN₂
      have hcN₁ : Computes N₁ τ (fun x => !F.eval x) := computes_not hcP
      have hcN₂ : Computes N₂ ρ (fun x => !G.eval x) := computes_not hcQ
      set R : BP n := N₁ ++ N₂ ++ BP.inv N₁ ++ BP.inv N₂ with hR
      have hcR : Computes R σ (fun x => (!F.eval x) && (!G.eval x)) :=
        computes_and hc hcN₁ hcN₂
      refine ⟨BP.mulLeft σ (BP.inv R), ?_, (computes_not hcR).congr ?_⟩
      · have e1 : N₁.length ≤ max 1 P.length := by
          rw [hN₁]; simpa using BP.length_mulLeft τ (BP.inv P)
        have e2 : N₂.length ≤ max 1 Q.length := by
          rw [hN₂]; simpa using BP.length_mulLeft ρ (BP.inv Q)
        have e3 := BP.length_mulLeft σ (BP.inv R)
        have e4 : (BP.inv R).length = R.length := BP.length_inv R
        have e5 : R.length = 2 * (N₁.length + N₂.length) := by rw [hR, length_and_prog]
        have e6 := two_add_pow4 F.depth G.depth (max F.depth G.depth) (le_max_left _ _)
          (le_max_right _ _)
        have e7 : 1 ≤ (4 : ℕ) ^ F.depth := Nat.one_le_pow _ _ (by norm_num)
        have e8 : 1 ≤ (4 : ℕ) ^ G.depth := Nat.one_le_pow _ _ (by norm_num)
        have e9 : 1 ≤ (4 : ℕ) ^ (max F.depth G.depth + 1) := Nat.one_le_pow _ _ (by norm_num)
        simp only [Formula.depth]
        omega
      · intro x
        show (!((!F.eval x) && (!G.eval x))) = (Formula.or F G).eval x
        simp [Formula.eval]

end CS

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

