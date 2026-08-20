import Mathlib

/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean 4 requires `import` statements to precede every other command, including module
docstrings, so the required header comment appears immediately after `import Mathlib`.
-/

open Nat.Partrec Nat.Partrec.Code Denumerable Encodable

namespace CS

/-- A language is a decision predicate on (natural-number encoded) inputs. -/
abbrev Lang := ℕ → Bool

/-- `TIME t` is the class of languages decided by some partial-recursive code within
`t n` steps of the step-indexed evaluator `Nat.Partrec.Code.evaln` on input `n`. -/

theorem diag_mem_TIME (t : ℕ → ℕ) (ht : Computable t) :
    ∃ T : ℕ → ℕ, (∀ n, t n ≤ T n) ∧ diag t ∈ TIME T := by
  have hE : Computable fun n => evaln (t n) (ofNat Code n) n :=
    primrec_evaln.to_comp.comp ((ht.pair (Primrec.ofNat Code).to_comp).pair Computable.id)
  have hprim : Primrec₂ (fun a b : Option ℕ => decide (a = b)) :=
    (Primrec.eq (α := Option ℕ)).decide
  have hd : Computable (diag t) :=
    Primrec.not.to_comp.comp
      (hprim.to_comp.comp hE (Computable.const (some 1)))
  have hf : Computable fun n => cond (diag t n) 1 0 :=
    hd.cond (Computable.const 1) (Computable.const 0)
  obtain ⟨c, hcode⟩ :=
    Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hf.partrec)
  have hk : ∀ n, ∃ k, cond (diag t n) 1 0 ∈ evaln k c n := by
    intro n
    refine Nat.Partrec.Code.evaln_complete.1 ?_
    rw [hcode]
    simp
  refine ⟨fun n => max (t n) (Nat.find (hk n)), fun n => le_max_left _ _, c, fun n => ?_⟩
  exact evaln_mono (le_max_right _ _) (Nat.find_spec (hk n))

/-- **Time hierarchy theorem**: for every computable time bound `t` there is a strictly
larger time bound `T` whose complexity class strictly contains that of `t`; the witnessing
language is obtained by diagonalization. -/
