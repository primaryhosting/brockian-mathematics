import RequestProject.Tseitin

/-!
# The Cook–Levin theorem: SAT is NP-complete

We work with languages of bit strings, `L : List Bool → Prop`.

Membership in NP is expressed by a *verifier*: a family of Boolean circuits
(straight-line programs) `V.ckt n`, of size polynomial in `n`, which takes an input
`x` of length `n` together with a witness `w` of polynomially bounded length
`V.wit n`, and accepts or rejects.  A string `x` is in the language iff some witness
is accepted.

* **SAT ∈ NP** (`sat_mem_NP`): a formula `F` is satisfiable iff there is a witness
  bit string `w` of length `numVars F` such that the (explicitly cost-instrumented)
  evaluator accepts, and that evaluation costs at most `2 * cnfSize F + 1` steps,
  i.e. linear time.

* **SAT is NP-hard** (`cook_levin_hardness`): for every verifier `V` and input `x`,
  the explicitly constructed formula `cookReduction V x` — obtained by the Tseitin
  transformation of the verifier circuit with the bits of `x` hard-wired — is
  satisfiable iff `x` belongs to the language of `V`; and its size is polynomially
  bounded in `|x|`, the construction being computable in linear time in the size of
  the circuit.

Both halves are combined in `cook_levin`.
-/

namespace Frontier

/-- The assignment described by a list of bits (missing bits default to `false`). -/

lemma firstBitVerifier_lang (x : List Bool) :
    firstBitVerifier.lang x ↔ x.getD 0 false = true := by
  constructor
  · rintro ⟨w, hw, hacc⟩
    have hwnil : w = [] := List.eq_nil_of_length_eq_zero (by simpa [firstBitVerifier] using hw)
    subst hwnil
    rcases Nat.eq_zero_or_pos x.length with h | h
    · have : x = [] := List.eq_nil_of_length_eq_zero h
      subst this
      simp [Verifier.accepts, firstBitVerifier, wireVal, evalWires, wireStep, evalGate] at hacc
    · have hn : ¬ x.length = 0 := by omega
      simp only [Verifier.accepts, firstBitVerifier, hn, if_false] at hacc
      simpa [wireVal, evalWires, wireStep, evalGate, assignOf,
        List.getD_eq_getElem?_getD, List.getElem?_append_left h] using hacc
  · intro hx
    have h : 0 < x.length := by
      by_contra hcon
      have : x = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      simp at hx
    have hn : ¬ x.length = 0 := by omega
    refine ⟨[], by simp [firstBitVerifier], ?_⟩
    simp only [Verifier.accepts, firstBitVerifier, hn, if_false]
    simpa [wireVal, evalWires, wireStep, evalGate, assignOf,
      List.getD_eq_getElem?_getD, List.getElem?_append_left h] using hx

/-- The language of bit strings starting with `true` is in NP. -/
