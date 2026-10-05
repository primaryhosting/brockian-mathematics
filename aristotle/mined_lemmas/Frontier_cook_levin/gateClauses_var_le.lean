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

lemma gateClauses_var_le {C : Circuit} {x : List Bool} {j : ℕ} (hj : j < C.length) :
    ∀ c ∈ gateClauses C x j, ∀ l ∈ c, l.1 ≤ C.length := by
  have hgv : gv j ≤ C.length := by simp only [gv]; omega
  have hrefv : ∀ d, refv j d ≤ C.length := fun d => le_trans (refv_le j d) (le_of_lt hj)
  have hzero : (0 : ℕ) ≤ C.length := Nat.zero_le _
  simp only [gateClauses]
  cases hg : gateAt C j with
  | inp i =>
      have hmem : Gate.inp i ∈ C := by
        rw [← hg, show gateAt C j = C[j]'hj from List.getD_eq_getElem C (Gate.cst false) hj]
        exact List.getElem_mem hj
      have hfi : gv (firstInp C i) ≤ C.length := by
        have := List.idxOf_lt_length_of_mem hmem
        simp only [gv, firstInp]
        omega
      split <;>
        (intro c hc l hl
         fin_cases hc <;> fin_cases hl <;> first | exact hgv | exact hfi)
  | cst b =>
      intro c hc l hl
      fin_cases hc <;> fin_cases hl <;> exact hgv
  | neg d =>
      intro c hc l hl
      fin_cases hc <;> fin_cases hl <;> first | exact hgv | exact hrefv _
  | conj d e =>
      intro c hc l hl
      fin_cases hc <;> fin_cases hl <;> first | exact hgv | exact hrefv _
  | disj d e =>
      intro c hc l hl
      fin_cases hc <;> fin_cases hl <;> first | exact hgv | exact hrefv _

