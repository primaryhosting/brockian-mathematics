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

theorem SATlang_inNP : InNP SATlang := by
  refine ⟨{
    wlen := fun l => Nat.sqrt (l / 2)
    circ := fun l => (satTree l).compile 0
    wf := fun l => Tree.compile_wf' _
    wlen_poly := Poly.mono Poly.id (fun n => le_trans (Nat.sqrt_le_self _) (Nat.div_le_self _ _))
    size_poly := ?_
    spec := ?_ }⟩
  · refine Poly.mono (f := fun l => ((satTree l).compile 0).length)
      (g := fun l => (9 * l + 2) * l + 1) ?_ ?_
    · exact ((Poly.mul (Poly.add (Poly.mul (Poly.const 9) Poly.id) (Poly.const 2)) Poly.id).add
        (Poly.const 1))
    · intro l
      show ((satTree l).compile 0).length ≤ (9 * l + 2) * l + 1
      rw [Tree.compile_length]
      refine le_trans (satTree_size l) ?_
      have hk : Nat.sqrt (l / 2) ≤ l := le_trans (Nat.sqrt_le_self _) (Nat.div_le_self _ _)
      exact Nat.add_le_add_right (Nat.mul_le_mul (by omega) hk) 1
  · intro s
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨(List.range (Nat.sqrt (s.length / 2))).map a, by simp, ?_⟩
      rw [satTree_correct]
      rw [eval_congr_lt (decodeCNF_vars s)
        (a := fun j => ((List.range (Nat.sqrt (s.length / 2))).map a).getD j false) (a' := a) ?_]
      · exact ha
      · intro i hi
        show ((List.range (Nat.sqrt (s.length / 2))).map a).getD i false = a i
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by simpa using hi)]
        simp
    · rintro ⟨w, _, hw⟩
      exact ⟨fun j => w.getD j false, (satTree_correct s w).mp hw⟩

end Frontier

import Mathlib

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Boolean circuits

A circuit is a straight-line program: a list of gates, where gate number `j` may refer
to the values of gates with smaller index (this is the well-formedness condition `Circ.WF`).
Gates may also read input variables, indexed by `ℕ`.

The value of the circuit is the value of its last gate.

We also introduce *formulas* (`Tree`) together with a compiler into straight-line programs;
this is only a convenience for *constructing* circuits.
-/

namespace Frontier

/-- A single gate of a straight-line program. -/
inductive Gate where
  | inp (i : ℕ)
  | const (b : Bool)
  | neg (j : ℕ)
  | conj (j k : ℕ)
  | disj (j k : ℕ)
  deriving DecidableEq, Repr

namespace Gate

/-- Value of a gate, given the input assignment `x` and the list of values of the
previous gates. -/
