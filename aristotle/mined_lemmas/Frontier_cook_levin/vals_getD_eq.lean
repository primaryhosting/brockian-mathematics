import Mathlib
import RequestProject.Hardness

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Cook–Levin theorem

`SAT` is NP-complete:

* `SAT ∈ NP`, and
* every language in `NP` reduces to `SAT`.

Here languages are sets of bit strings; a language is in `NP` when it is decided by a
family of polynomial size Boolean circuits reading the input word together with a
witness word of polynomial length (`Frontier.InNP`).  `SAT` is the set of bit strings
whose associated CNF formula is satisfiable (`Frontier.SATlang`), the association being
the occurrence-matrix encoding of `Frontier.decodeCNF`.

The reductions produced here are *projections*: each output bit is a constant, or a bit
of the input word, or the negation of a bit of the input word, and the number of output
bits is polynomial in the length of the input word (`Frontier.IsProjectionReduction`).
In particular they are computable by polynomial size circuits.

The circuit families witnessing membership in `NP` are not required to be uniformly
generated, so `Frontier.InNP` is the non-uniform version of `NP`; correspondingly the
reductions produced by the hardness proof are non-uniform (but they are projections,
which is a much more restrictive class than polynomial time computable maps).
-/

namespace Frontier

/-- `L₁` reduces to `L₂` by a projection reduction. -/

theorem vals_getD_eq (x : ℕ → Bool) {gs : Circ} {j : ℕ} {g : Gate}
    (hwf : ∀ k g', gs[k]? = some g' → Gate.WFAt k g') (hj : gs[j]? = some g) :
    (vals x gs).getD j false = Gate.eval x (vals x gs) g := by
  have hjlt : j < gs.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hj
    exact absurd hj (by simp)
  obtain ⟨pre, suf, hpre, hsplit⟩ : ∃ pre suf : Circ, pre.length = j ∧ gs = (pre ++ [g]) ++ suf := by
    refine ⟨gs.take j, gs.drop (j + 1), by simp; omega, ?_⟩
    have hget : gs[j] = g := by
      have h := List.getElem?_eq_getElem hjlt
      rw [h] at hj
      exact Option.some.inj hj
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.drop_eq_getElem_cons hjlt, hget]
    simp
  have hstable : ∀ k, k < j → (vals x gs).getD k false = (vals x pre).getD k false := by
    intro k hk
    conv_lhs => rw [hsplit]
    rw [vals_getD_append x (pre ++ [g]) suf (by simp; omega),
      vals_getD_append x pre [g] (by omega)]
  have h1 : (vals x gs).getD j false = Gate.eval x (vals x pre) g := by
    conv_lhs => rw [hsplit]
    rw [vals_getD_append x (pre ++ [g]) suf (by simp; omega), ← hpre, vals_getD_concat]
  rw [h1]
  cases g with
  | inp i => simp [Gate.eval]
  | const b => simp [Gate.eval]
  | neg k =>
      have hk : k < j := hwf j _ hj
      simp only [Gate.eval, hstable k hk]
  | conj k l =>
      obtain ⟨hk, hl⟩ : k < j ∧ l < j := hwf j _ hj
      simp only [Gate.eval, hstable k hk, hstable l hl]
  | disj k l =>
      obtain ⟨hk, hl⟩ : k < j ∧ l < j := hwf j _ hj
      simp only [Gate.eval, hstable k hk, hstable l hl]

/-- Well-formedness of a circuit: every gate only refers to earlier gates. -/
