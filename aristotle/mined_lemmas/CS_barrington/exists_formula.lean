/-
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 requires all `import`
-- commands to precede any module docstring.)

import Mathlib

/-!
## Barrington's theorem

We formalise Barrington's theorem, which identifies the class `NC¹` (Boolean formulas of
logarithmic depth) with the class of functions computed by *width-5 permutation branching
programs* of polynomial length.

* `CS.Formula n` are Boolean formulas in the variables `Fin n` built from `¬`, `∧`, `∨`.
  Following the usual convention for Barrington's theorem, `Formula.depth` counts the
  nesting depth of the binary gates (negations are free, since they can be pushed to the
  leaves without changing the depth).
* `CS.BProg n` is a *width-5 permutation branching program*: a list of instructions, each of
  which reads one input bit and outputs one of two permutations of `Fin 5`, depending on the
  value of that bit.  The value `BProg.eval P x` of the program on the input `x` is the
  product of the permutations selected by the instructions.

The two halves of `CS.barrington` are:

1. every formula of depth `d` is computed by a width-5 permutation branching program of
   length at most `4 ^ d`, with output the prescribed 5-cycle `σ` on accepted inputs and the
   identity on rejected inputs (this is Barrington's construction);
2. conversely, for every width-5 permutation branching program `P` of length `ℓ` and every
   target permutation `σ`, the acceptance predicate `P.eval x = σ` is computed by a formula of
   depth `O(log ℓ)` (a balanced divide-and-conquer evaluation of the product).
-/

namespace CS

open Equiv Equiv.Perm

/-- The group of permutations of five points: the "width 5" of Barrington's theorem. -/
abbrev W : Type := Equiv.Perm (Fin 5)

/-! ### Boolean formulas -/

/-- Boolean formulas over the variables `Fin n`. -/
inductive Formula (n : ℕ) where
  | var : Fin n → Formula n
  | neg : Formula n → Formula n
  | conj : Formula n → Formula n → Formula n
  | disj : Formula n → Formula n → Formula n

/-- The depth of a formula, counting binary gates only (negations are free). -/

theorem exists_formula {n : ℕ} (i : Fin n) :
    ∀ (N : ℕ) (P : BProg n), P.length ≤ N →
      ∃ φ : W → Formula n, (∀ g, (φ g).depth ≤ 121 * Nat.clog 2 P.length + 1) ∧
        (∀ g x, (φ g).eval x = decide (P.eval x = g)) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro P hPN
    match P with
    | [] =>
        refine ⟨fun g => Formula.constF i (decide ((1 : W) = g)), by simp, ?_⟩
        intro g x
        simp
    | [I] =>
        refine ⟨fun g =>
          if I.p₀ = g then (if I.p₁ = g then Formula.trueF i else Formula.neg (.var I.idx))
          else (if I.p₁ = g then Formula.var I.idx else Formula.falseF i), ?_, ?_⟩
        · intro g
          by_cases h0 : I.p₀ = g <;> by_cases h1 : I.p₁ = g <;>
            simp [h0, h1, Formula.trueF, Formula.falseF, Formula.depth]
        · intro g x
          have hev : (([I] : BProg n)).eval x = if x I.idx then I.p₁ else I.p₀ := by
            simp [BProg.eval, Instr.val]
          rw [hev]
          by_cases h0 : I.p₀ = g <;> by_cases h1 : I.p₁ = g <;>
            simp [h0, h1, Formula.trueF, Formula.falseF, Formula.eval] <;>
            cases hx : x I.idx <;> simp_all
    | I :: J :: P'' =>
      set Q : BProg n := I :: J :: P'' with hQdef
      have hlen2 : 2 ≤ Q.length := by simp [hQdef]
      set k := Q.length / 2 with hk
      have hk1 : 1 ≤ k := by omega
      have hk2 : k < Q.length := by omega
      have hlen1 : (Q.take k).length = k := by
        rw [List.length_take]; omega
      have hlen3 : (Q.drop k).length = Q.length - k := by
        rw [List.length_drop]
      obtain ⟨φ1, hd1, he1⟩ := IH (Q.length - 1) (by omega) (Q.take k) (by omega)
      obtain ⟨φ2, hd2, he2⟩ := IH (Q.length - 1) (by omega) (Q.drop k) (by omega)
      -- the bound
      have hclog : Nat.clog 2 (Q.length - k) + 1 = Nat.clog 2 Q.length := by
        rw [Nat.clog_of_two_le (by norm_num) hlen2]
        congr 1
        congr 1
        omega
      have hmono : Nat.clog 2 (Q.take k).length ≤ Nat.clog 2 (Q.drop k).length := by
        rw [hlen1, hlen3]
        exact Nat.clog_mono_right _ (by omega)
      set D := 121 * Nat.clog 2 (Q.drop k).length + 1 with hD
      refine ⟨fun g => Formula.orList i
        ((Finset.univ : Finset W).toList.map (fun a => Formula.conj (φ1 a) (φ2 (a⁻¹ * g)))), ?_, ?_⟩
      · intro g
        have hcard : ((Finset.univ : Finset W).toList.map
            (fun a => Formula.conj (φ1 a) (φ2 (a⁻¹ * g)))).length = 120 := by
          rw [List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin]
          rfl
        have hbnd : ∀ f ∈ ((Finset.univ : Finset W).toList.map
            (fun a => Formula.conj (φ1 a) (φ2 (a⁻¹ * g)))), f.depth ≤ D + 1 := by
          intro f hf
          rw [List.mem_map] at hf
          obtain ⟨a, _, rfl⟩ := hf
          have b1 : (φ1 a).depth ≤ D := by
            refine (hd1 a).trans ?_
            rw [hD]
            have := hmono
            omega
          have b2 : (φ2 (a⁻¹ * g)).depth ≤ D := hd2 _
          simp only [Formula.depth]
          omega
        have := Formula.depth_orList i _ hbnd (by omega)
        rw [hcard] at this
        refine this.trans ?_
        rw [hD, hlen3]
        omega
      · intro g x
        rw [Formula.eval_orList]
        have hsplit : Q.eval x = (Q.take k).eval x * (Q.drop k).eval x := by
          rw [← BProg.eval_append, List.take_append_drop]
        rw [hsplit]
        simp only [List.any_map, List.any_eq_true, Finset.mem_toList, Finset.mem_univ,
          Function.comp_apply, true_and, Formula.eval, he1, he2, Bool.and_eq_true,
          decide_eq_true_eq]
        by_cases hgoal : (Q.take k).eval x * (Q.drop k).eval x = g
        · simp only [hgoal, decide_true, eq_iff_iff, iff_true]
          exact ⟨(Q.take k).eval x, rfl, by rw [← hgoal]; group⟩
        · simp only [hgoal, decide_false, eq_iff_iff, iff_false, not_exists]
          rintro a ⟨rfl, h2⟩
          rw [h2] at hgoal
          exact hgoal (by group)

/-! ### Barrington's theorem -/

/-- **Barrington's theorem**: `NC¹` equals width-5 permutation branching programs.

The first component is the hard direction: any Boolean formula of depth `d` (with negations
free, i.e. `d` is the nesting depth of the binary gates) is computed by a width-5 permutation
branching program of length at most `4 ^ d`, whose output is a prescribed 5-cycle `σ` on
accepted inputs and the identity on rejected inputs.  In particular formulas of depth
`O(log n)` — i.e. functions in `NC¹` — are computed by width-5 permutation branching programs
of polynomial length.

The second component is the converse: the acceptance predicate `P.eval x = σ` of a width-5
permutation branching program of length `ℓ` is computed by a Boolean formula of depth at most
`121 * ⌈log₂ ℓ⌉ + 1`, so a polynomial-length program yields a logarithmic-depth formula. -/
