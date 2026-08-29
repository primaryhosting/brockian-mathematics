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

theorem compile_wf (t : Tree) (base : ℕ) (pre : Circ) (h : pre.length = base)
    (hpre : Circ.WF pre) : Circ.WF (pre ++ t.compile base) := by
  induction t generalizing base pre with
  | var i =>
      exact Circ.wf_concat hpre (by simp [Gate.WFAt])
  | lit b =>
      exact Circ.wf_concat hpre (by simp [Gate.WFAt])
  | neg t ih =>
      have happ : pre ++ (Tree.neg t).compile base
          = (pre ++ t.compile base) ++ [Gate.neg (base + t.size - 1)] := by
        simp [compile, List.append_assoc]
      rw [happ]
      refine Circ.wf_concat (ih base pre h hpre) ?_
      have := t.size_pos
      simp only [Gate.WFAt, List.length_append, compile_length, h]
      omega
  | conj t u iht ihu =>
      have happ : pre ++ (Tree.conj t u).compile base
          = ((pre ++ t.compile base) ++ u.compile (base + t.size)) ++
              [Gate.conj (base + t.size - 1) (base + t.size + u.size - 1)] := by
        simp [compile, List.append_assoc]
      have hlen1 : (pre ++ t.compile base).length = base + t.size := by simp [h]
      rw [happ]
      refine Circ.wf_concat (ihu (base + t.size) _ hlen1 (iht base pre h hpre)) ?_
      have h1 := t.size_pos
      have h2 := u.size_pos
      simp only [Gate.WFAt, List.length_append, compile_length, h]
      omega
  | disj t u iht ihu =>
      have happ : pre ++ (Tree.disj t u).compile base
          = ((pre ++ t.compile base) ++ u.compile (base + t.size)) ++
              [Gate.disj (base + t.size - 1) (base + t.size + u.size - 1)] := by
        simp [compile, List.append_assoc]
      have hlen1 : (pre ++ t.compile base).length = base + t.size := by simp [h]
      rw [happ]
      refine Circ.wf_concat (ihu (base + t.size) _ hlen1 (iht base pre h hpre)) ?_
      have h1 := t.size_pos
      have h2 := u.size_pos
      simp only [Gate.WFAt, List.length_append, compile_length, h]
      omega

