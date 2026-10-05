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

lemma gateClauses_iff {C : Circuit} {x : List Bool} {ext a : ℕ → Bool} {j : ℕ}
    (hj : j < C.length)
    (hrefj : ∀ d, a (refv j d) = (pre C ext j).getD d false)
    (hx : ∀ i, i < x.length → ext i = x.getD i false)
    (hinp : ∀ i, x.length ≤ i → Gate.inp i ∈ C → ext i = a (gv (firstInp C i))) :
    satCNF a (gateClauses C x j) = true ↔ a (gv j) = (gateAt C j).val ext (pre C ext j) := by
  have hmem : gateAt C j ∈ C := by
    rw [show gateAt C j = C[j]'hj from List.getD_eq_getElem C (Gate.cst false) hj]
    exact List.getElem_mem hj
  cases hg : gateAt C j with
  | inp i =>
      rw [hg] at hmem
      by_cases hi : i < x.length
      · simp only [gateClauses, hg, hi, if_pos, satCNF, satClause, satLit, Gate.val,
          List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.or_false,
          Bool.and_true, beq_iff_eq]
        rw [hx i hi]
      · simp only [gateClauses, hg, hi, if_neg, not_false_iff, satCNF, satClause, satLit,
          Gate.val, List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.or_false,
          Bool.and_true, beq_iff_eq, Bool.and_eq_true, Bool.or_eq_true]
        rw [hinp i (by omega) hmem]
        constructor
        · rintro ⟨h1, h2⟩
          exact bool_eq_of _ _ h1 h2
        · intro h; rw [h]
          cases a (gv (firstInp C i)) <;> simp
  | cst b =>
      simp only [gateClauses, hg, satCNF, satClause, satLit, Gate.val, List.all_cons,
        List.all_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.and_true, beq_iff_eq]
  | neg d =>
      simp only [gateClauses, hg, satCNF, satClause, satLit, Gate.val, List.all_cons,
        List.all_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.and_true, beq_iff_eq,
        Bool.and_eq_true, Bool.or_eq_true]
      rw [← hrefj d]
      constructor
      · rintro ⟨h1, h2⟩; exact bool_iff_of _ _ h1 h2
      · intro h; rw [h]; cases a (refv j d) <;> simp
  | conj d e =>
      simp only [gateClauses, hg, satCNF, satClause, satLit, Gate.val, List.all_cons,
        List.all_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.and_true, beq_iff_eq,
        Bool.and_eq_true, Bool.or_eq_true]
      rw [← hrefj d, ← hrefj e]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact bool_and_of _ _ _ h1 h2 h3
      · intro h; rw [h]; cases a (refv j d) <;> cases a (refv j e) <;> simp
  | disj d e =>
      simp only [gateClauses, hg, satCNF, satClause, satLit, Gate.val, List.all_cons,
        List.all_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.and_true, beq_iff_eq,
        Bool.and_eq_true, Bool.or_eq_true]
      rw [← hrefj d, ← hrefj e]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact bool_or_of _ _ _ h1 h2 h3
      · intro h; rw [h]; cases a (refv j d) <;> cases a (refv j e) <;> simp

/-- If some completion of the input makes the circuit output `true`, the Tseitin
formula is satisfiable. -/
