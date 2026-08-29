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

theorem satCirc_spec (x : List Bool) :
    SATLang x ↔ ∃ w : ℕ → Bool, evalC (satCirc x.length) (extend x w) = true := by
  classical
  set n := x.length with hn
  by_cases hcase : n = 2 * sqv n * sqv n
  · set v := sqv n with hv
    have hxlen : x.length = 2 * v * v := hcase
    -- the decoded formula
    have hdec : decodeCNF x = (List.range v).map (decClause x v) := by
      rw [decodeCNF, if_pos hcase]
    have hn2 : n = 2 * (v * v) := by rw [mul_assoc] at hcase; exact hcase
    have hbound : ∀ c i r, c < v → i < v → r < 2 → 2 * (c * v + i) + r < n := by
      intro c i r hc hi hr
      have h1 : c * v + i < v * v := by nlinarith
      omega
    -- reformulate the left-hand side
    have hL : SATLang x ↔ ∃ a : ℕ → Bool, ∀ c < v, ∃ i < v,
        (x.getD (2 * (c * v + i)) false = true ∧ a i = true) ∨
        (x.getD (2 * (c * v + i) + 1) false = true ∧ a i = false) := by
      rw [SATLang, Sat, hdec]
      refine exists_congr fun a => ?_
      simp only [satCNF, List.all_eq_true, List.mem_map, List.mem_range]
      constructor
      · intro h c hc
        exact (satClause_decClause a x v c).mp (h _ ⟨c, hc, rfl⟩)
      · rintro h c ⟨k, hk, rfl⟩
        exact (satClause_decClause a x v k).mpr (h k hk)
    -- reformulate the right-hand side
    have hR : (∃ w : ℕ → Bool, evalC (satCirc n) (extend x w) = true) ↔
        ∃ w : ℕ → Bool, ∀ c < v, ∃ i < v,
          (x.getD (2 * (c * v + i)) false = true ∧ w (n + i) = true) ∨
          (x.getD (2 * (c * v + i) + 1) false = true ∧ w (n + i) = false) := by
      refine exists_congr fun w => ?_
      rw [satCirc, if_pos hcase, evalC_compile, checkerExpr_eval]
      have he1 : ∀ c i r, c < v → i < v → r < 2 →
          extend x w (2 * (c * v + i) + r) = x.getD (2 * (c * v + i) + r) false := by
        intro c i r hc hi hr
        have := hbound c i r hc hi hr
        simp [extend, ← hn, this]
      have he2 : ∀ i, extend x w (n + i) = w (n + i) := by
        intro i; simp [extend, ← hn]
      constructor
      · intro h c hc
        obtain ⟨i, hi, hcase2⟩ := h c hc
        refine ⟨i, hi, ?_⟩
        rw [he2] at hcase2
        rcases hcase2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [show 2 * (c * v + i) = 2 * (c * v + i) + 0 from rfl, he1 c i 0 hc hi (by norm_num)]
            at h1
          exact Or.inl ⟨h1, h2⟩
        · rw [he1 c i 1 hc hi (by norm_num)] at h1
          exact Or.inr ⟨h1, h2⟩
      · intro h c hc
        obtain ⟨i, hi, hcase2⟩ := h c hc
        refine ⟨i, hi, ?_⟩
        rw [he2]
        rcases hcase2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · refine Or.inl ⟨?_, h2⟩
          rw [show 2 * (c * v + i) = 2 * (c * v + i) + 0 from rfl, he1 c i 0 hc hi (by norm_num)]
          exact h1
        · refine Or.inr ⟨?_, h2⟩
          rw [he1 c i 1 hc hi (by norm_num)]
          exact h1
    rw [hL, hR]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨fun k => a (k - n), fun c hc => by simpa using ha c hc⟩
    · rintro ⟨w, hw⟩
      exact ⟨fun i => w (n + i), fun c hc => hw c hc⟩
  · have hdec : decodeCNF x = [[]] := by
      rw [decodeCNF, if_neg (by rw [← hn]; exact hcase)]
    constructor
    · rintro ⟨a, ha⟩
      rw [hdec] at ha
      simp [satCNF, satClause] at ha
    · rintro ⟨w, hw⟩
      rw [satCirc, if_neg hcase] at hw
      simp [compile, evalC, run, Gate.val] at hw

/-- SAT, as a language of bit strings, belongs to NP. -/
