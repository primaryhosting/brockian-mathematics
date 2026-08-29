import RequestProject.Encode

/-!
# The class NP, via polynomial-size verifier circuits

A language `L ⊆ {0,1}*` is in `NP` when there is a family of Boolean circuits
`circ n`, of size polynomial in `n`, such that `x ∈ L` iff some setting of the
"free" inputs (the inputs of index `≥ |x|`, i.e. the witness) makes `circ |x|`
accept the string `x`.

Note that no bound on the witness has to be imposed: a circuit of size `s` reads
at most `s` of its inputs, so the witness is automatically of polynomial length.
-/

namespace Frontier

/-- A polynomial-size verifier-circuit family witnessing that `L` is in `NP`. -/
structure NPVerifier (L : List Bool → Prop) where
  /-- The verifier circuit for inputs of length `n`. -/
  circ : ℕ → Circuit
  /-- Coefficient of the polynomial size bound. -/
  coeff : ℕ
  /-- Exponent of the polynomial size bound. -/
  exponent : ℕ
  /-- The circuit family has polynomial size. -/
  size_le : ∀ n, (circ n).length ≤ coeff * (n + 1) ^ exponent
  /-- `x ∈ L` iff some witness makes the verifier accept. -/
  spec : ∀ x : List Bool, L x ↔ ∃ w : ℕ → Bool, evalC (circ x.length) (extend x w) = true

end Frontier

import Mathlib

/-!
# Basic objects: CNF formulas and Boolean circuits

This file sets up the two computational objects used in the Cook–Levin development:

* CNF formulas over natural-number variables, and their satisfiability;
* Boolean circuits, presented as straight-line programs with *relative*
  back-references (a gate at position `i` may refer to the gate `d` steps
  before it).  Out-of-range references evaluate to `false`, so evaluation is
  total and no well-formedness side condition is ever needed.
* Boolean *expressions* (trees) together with a compiler into circuits.  This
  is only used as a convenient way of building concrete circuits.
-/

namespace Frontier

/-! ### CNF formulas -/

/-- A literal is a variable index together with the polarity it is asserted with. -/
abbrev Lit := ℕ × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Lit

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF := List Clause

/-- Is the literal `l` true under the assignment `a`? -/

theorem sat_tseitin_of_eval {C : Circuit} {x : List Bool} {w : ℕ → Bool}
    (h : evalC C (extend x w) = true) : Sat (tseitin C x) := by
  classical
  set ext := extend x w with hext
  refine ⟨fun v => if v = 0 then false else (pre C ext v).headD false, ?_⟩
  set a : ℕ → Bool := fun v => if v = 0 then false else (pre C ext v).headD false with ha
  have h0 : a 0 = false := by simp [ha]
  have hval : ∀ j, a (gv j) = (pre C ext (j + 1)).headD false := by
    intro j; simp [ha, gv]
  have hnonempty : 0 < C.length := by
    by_contra hc
    have : C = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [this] at h
    simp [evalC] at h
  have hx : ∀ i, i < x.length → ext i = x.getD i false := by
    intro i hi; simp [hext, extend, hi]
  have hinp : ∀ i, x.length ≤ i → Gate.inp i ∈ C → ext i = a (gv (firstInp C i)) := by
    intro i hi hmem
    have hlt : firstInp C i < C.length := List.idxOf_lt_length_of_mem hmem
    have hgi : gateAt C (firstInp C i) = Gate.inp i := by
      rw [show gateAt C (firstInp C i) = C[firstInp C i]'hlt from
        List.getD_eq_getElem C (Gate.cst false) hlt]
      exact List.getElem_idxOf hlt
    rw [hval, pre_succ C ext hlt, List.headD_cons, hgi]
    rfl
  refine satCNF_tseitin_of h0 (fun j hj => ?_) ?_
  · rw [gateClauses_iff hj (refv_eq C ext a h0 (le_of_lt hj) (fun k _ => hval k)) hx hinp,
      hval j, pre_succ C ext hj, List.headD_cons]
  · have : outLit C = (gv (C.length - 1), true) := by
      rw [outLit, if_neg (by omega)]
    rw [this, satLit, hval]
    have : C.length - 1 + 1 = C.length := by omega
    rw [this]
    rw [← evalC_eq_pre, h]
    rfl

/-- If the Tseitin formula is satisfiable, some completion of the input makes the
circuit output `true`. -/
