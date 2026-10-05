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

lemma satCNF_decode_encode (F : CNF) (a : ℕ → Bool) :
    satCNF a (decodeCNF (encode F)) = true ↔ satCNF a F = true := by
  set v := width F with hv
  rw [decode_encode]
  simp only [satCNF, List.all_eq_true, List.mem_map, List.mem_range]
  constructor
  · rintro h c hc
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    have hkv : k < v := lt_of_lt_of_le hk (length_le_width F)
    have := h _ ⟨k, hkv, rfl⟩
    obtain ⟨i, hi, hcase⟩ := (satClause_decClause a (encode F) v k).mp this
    have hbits := encode_getD F hkv hi
    have hFk : F.getD k [] = F[k] := List.getD_eq_getElem F [] hk
    rcases hcase with ⟨hb, ha⟩ | ⟨hb, ha⟩
    · rw [show 2 * (k * v + i) = 2 * (k * v + i) + 0 from rfl, hbits 0 (by norm_num)] at hb
      simp only [encPair, if_pos hk, List.getD_cons_zero, decide_eq_true_eq, hFk] at hb
      exact List.any_eq_true.mpr ⟨(i, true), hb, by simp [satLit, ha]⟩
    · rw [hbits 1 (by norm_num)] at hb
      simp only [encPair, if_pos hk, List.getD_cons_succ, List.getD_cons_zero,
        decide_eq_true_eq, hFk] at hb
      exact List.any_eq_true.mpr ⟨(i, false), hb, by simp [satLit, ha]⟩
  · rintro h c ⟨k, hkv, rfl⟩
    rw [satClause_decClause]
    by_cases hk : k < F.length
    · have hFk : F.getD k [] = F[k] := List.getD_eq_getElem F [] hk
      have hsat := h F[k] (List.getElem_mem hk)
      obtain ⟨l, hl, hl2⟩ := List.any_eq_true.mp hsat
      have hiv : l.1 < v := lt_width_of_mem (List.getElem_mem hk) hl
      refine ⟨l.1, hiv, ?_⟩
      have hbits := encode_getD F hkv hiv
      have hl' : (l.1, l.2) ∈ F[k] := by simpa using hl
      cases hb : l.2 with
      | true =>
          left
          rw [hb] at hl'
          constructor
          · rw [show 2 * (k * v + l.1) = 2 * (k * v + l.1) + 0 from rfl, hbits 0 (by norm_num)]
            simp [encPair, hk, hl']
          · simpa [satLit, hb] using hl2
      | false =>
          right
          rw [hb] at hl'
          constructor
          · rw [hbits 1 (by norm_num)]
            simp [encPair, hk, hl']
          · simpa [satLit, hb] using hl2
    · have hv0 : 0 < v := by omega
      have hbits := encode_getD F hkv hv0
      refine ⟨0, hv0, ?_⟩
      cases ha : a 0 with
      | true =>
          left
          refine ⟨?_, rfl⟩
          rw [show 2 * (k * v + 0) = 2 * (k * v + 0) + 0 from rfl, hbits 0 (by norm_num)]
          simp [encPair, hk]
      | false =>
          right
          refine ⟨?_, rfl⟩
          rw [hbits 1 (by norm_num)]
          simp [encPair, hk]

/-- The bit-string encoding preserves satisfiability. -/
