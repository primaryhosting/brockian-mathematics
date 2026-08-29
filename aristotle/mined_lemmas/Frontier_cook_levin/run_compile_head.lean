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

lemma run_compile_head (e : BExpr) (x : ℕ → Bool) (acc : List Bool) :
    (run (compile e) x acc).headD false = e.eval x := by
  induction e generalizing acc with
  | var i => rfl
  | cst b => rfl
  | neg e ih =>
      rw [compile, run_append, run_singleton]
      have h : (run (compile e) x acc).getD 0 false = e.eval x := by
        rw [getD_zero_eq_headD]; exact ih acc
      simp only [List.headD_cons, Gate.val, BExpr.eval, h]
  | conj a b iha ihb =>
      rw [compile, run_append, run_append, run_singleton]
      have hb2 : (run (compile b) x (run (compile a) x acc)).getD 0 false = b.eval x := by
        rw [getD_zero_eq_headD]; exact ihb _
      have ha2 : (run (compile b) x (run (compile a) x acc)).getD ((compile b).length) false
          = a.eval x := by
        have h1 := run_getD_add (compile b) x (run (compile a) x acc) 0
        rw [Nat.zero_add] at h1
        rw [h1, getD_zero_eq_headD]; exact iha acc
      simp only [List.headD_cons, Gate.val, BExpr.eval, ha2, hb2]
  | disj a b iha ihb =>
      rw [compile, run_append, run_append, run_singleton]
      have hb2 : (run (compile b) x (run (compile a) x acc)).getD 0 false = b.eval x := by
        rw [getD_zero_eq_headD]; exact ihb _
      have ha2 : (run (compile b) x (run (compile a) x acc)).getD ((compile b).length) false
          = a.eval x := by
        have h1 := run_getD_add (compile b) x (run (compile a) x acc) 0
        rw [Nat.zero_add] at h1
        rw [h1, getD_zero_eq_headD]; exact iha acc
      simp only [List.headD_cons, Gate.val, BExpr.eval, ha2, hb2]

