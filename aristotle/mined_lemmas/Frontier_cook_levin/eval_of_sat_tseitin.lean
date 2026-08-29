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

theorem eval_of_sat_tseitin {C : Circuit} {x : List Bool} (h : Sat (tseitin C x)) :
    ∃ w : ℕ → Bool, evalC C (extend x w) = true := by
  classical
  obtain ⟨a, ha⟩ := h
  set w : ℕ → Bool := fun i => a (gv (firstInp C i)) with hw
  refine ⟨w, ?_⟩
  set ext := extend x w with hext
  have h0 : a 0 = false := sat_tseitin_sentinel ha
  have hx : ∀ i, i < x.length → ext i = x.getD i false := by
    intro i hi; simp [hext, extend, hi]
  have hinp : ∀ i, x.length ≤ i → Gate.inp i ∈ C → ext i = a (gv (firstInp C i)) := by
    intro i hi _
    simp [hext, extend, hw, Nat.not_lt.mpr hi]
  have hval : ∀ j, j < C.length → a (gv j) = (pre C ext (j + 1)).headD false := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have hrefj := refv_eq C ext a h0 (le_of_lt hj)
        (fun k hk => ih k hk (by omega))
      have := (gateClauses_iff hj hrefj hx hinp).mp (sat_tseitin_gate ha hj)
      rw [this, pre_succ C ext hj, List.headD_cons]
  have hnonempty : 0 < C.length := by
    by_contra hc
    have hlen : C.length = 0 := by omega
    have hout := sat_tseitin_out ha
    rw [outLit, if_pos hlen] at hout
    simp [satLit, h0] at hout
  have hout := sat_tseitin_out ha
  rw [outLit, if_neg (by omega), satLit] at hout
  have h1 : a (gv (C.length - 1)) = true := by simpa using hout
  rw [hval _ (by omega), show C.length - 1 + 1 = C.length from by omega] at h1
  rw [evalC_eq_pre]
  exact h1

/-- **Correctness of the Tseitin transformation.** -/
