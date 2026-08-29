/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses no `import`, so that the module
docstring above can literally be the first thing in the file).  The definitions of `Lit`,
`Clause`, `CNF`, `Clause.eval` and `CNF.eval` below mirror `Std.Sat.Literal`,
`Std.Sat.CNF.Clause`, `Std.Sat.CNF`, `Std.Sat.CNF.Clause.eval` and `Std.Sat.CNF.eval`
from the Lean standard library.
-/

namespace Frontier

/-! ## Propositional formulas in conjunctive normal form -/

/-- A literal: a variable together with the sign with which it occurs. -/
abbrev Lit (V : Type) := V × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause (V : Type) := List (Lit V)

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF (V : Type) := List (Clause V)

/-- Value of a clause under an assignment. -/

theorem step_of_sat {t : Nat} (ht : t < T) :
    M.Step (cfgOf M A T x t) (cfgOf M A T x (t + 1)) := by
  have ht' : t ≤ T := by omega
  have ht1 : t + 1 ≤ T := by omega
  obtain ⟨τ, hτ, hτA⟩ := ex_trans hsat ht
  obtain ⟨q, a, q', b, d⟩ := τ
  have hmem := mem_transList.mp hτ
  simp only at hmem
  have hst := stateOf_spec hsat ht'
  have hst1 := stateOf_spec hsat ht1
  have hhd := headOf_spec hsat ht'
  have hhd1 := headOf_spec hsat ht1
  have hhdle := headOf_le hsat ht'
  have hq : q = stateOf A M.numStates t :=
    uniq_state hsat ht' hmem.1 hst.1 (imp_state hsat ht hτ hτA) hst.2
  have hrd : A (vC t (headOf A T t) a) = true := imp_read hsat ht hτ hhd.1 hτA hhd.2
  have ha : a = tapeOf A T x t (headOf A T t) :=
    uniq_cell hsat ht' hhd.1 hrd (tapeOf_spec hsat ht' hhd.1)
  have hq'lt : q' < M.numStates := M.step_lt q a (q', b, d) hmem.2
  have hq' : q' = stateOf A M.numStates (t + 1) :=
    uniq_state hsat ht1 hq'lt hst1.1 (imp_next_state hsat ht hτ hτA) hst1.2
  have hb : b = tapeOf A T x (t + 1) (headOf A T t) :=
    uniq_cell hsat ht1 hhd.1 (imp_write hsat ht hτ hhd.1 hτA hhd.2) (tapeOf_spec hsat ht1 hhd.1)
  have hdlt : d.apply (headOf A T t) ≤ T := by
    have := Move.apply_le d (headOf A T t); omega
  have hmv : d.apply (headOf A T t) = headOf A T (t + 1) :=
    uniq_head hsat ht1 hdlt hhd1.1 (imp_move hsat ht hτ hhd.1 hτA hhd.2) hhd1.2
  refine ⟨(q', b, d), ?_, ?_, ?_, ?_⟩
  · simp only [cfgOf_state, cfgOf_tape, cfgOf_head]
    rw [← hq, ← ha]
    exact hmem.2
  · simp only [cfgOf_state]; exact hq'.symm
  · simp only [cfgOf_tape, cfgOf_head]
    funext j
    by_cases hjh : j = headOf A T t
    · subst hjh
      simp only [writeTape, if_pos]
      exact hb.symm
    · simp only [writeTape, if_neg hjh]
      by_cases hj : j ≤ T
      · have hjf : A (vH t j) = false := by
          cases hjb : A (vH t j) with
          | false => rfl
          | true => exact absurd (uniq_head hsat ht' hj hhd.1 hjb hhd.2) hjh
        have h1 := frame_step hsat ht hj hjf (tapeOf_spec hsat ht' hj)
        exact (uniq_cell hsat ht1 hj (tapeOf_spec hsat ht1 hj) h1)
      · rw [tapeOf_out hj, tapeOf_out hj]
  · simp only [cfgOf_head]; exact hmv.symm

