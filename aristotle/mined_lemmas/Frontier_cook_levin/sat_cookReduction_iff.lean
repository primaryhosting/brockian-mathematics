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

theorem sat_cookReduction_iff (V : Verifier) (x : List Bool) :
    SAT (cookReduction V x) ↔ V.lang x := by
  set n := x.length with hn
  set gs := V.ckt n with hgs
  rw [cookReduction, ← hn, ← hgs,
    sat_reduceSLP_iff (V.wf n) (V.ne n) x]
  constructor
  · rintro ⟨y, hy, hout⟩
    -- read off the witness from the free assignment `y`
    refine ⟨(List.range (V.wit n)).map (fun k => y (n + k)), by simp [hn], ?_⟩
    have hagree : ∀ i, i < n + V.wit n →
        assignOf (x ++ (List.range (V.wit n)).map (fun k => y (n + k))) i = y i := by
      intro i hi
      rcases lt_or_ge i n with h | h
      · rw [assignOf_append_left (by omega)]
        rw [hy i (by omega)]
        simp [assignOf]
      · rw [assignOf_append_right (by omega)]
        have hlt : i - n < V.wit n := by omega
        simp only [assignOf, List.getD_eq_getElem?_getD]
        rw [List.getElem?_map, List.getElem?_range hlt]
        simp only [Option.map_some, Option.getD_some]
        congr 1
        omega
    unfold Verifier.accepts
    rw [← hn, ← hgs]
    rw [wireVal_congr (n := n + V.wit n) (V.reads n) hagree]
    exact hout
  · rintro ⟨w, hw, hacc⟩
    refine ⟨assignOf (x ++ w), ?_, ?_⟩
    · intro i hi
      rw [assignOf_append_left hi]
      simp [assignOf]
    · unfold Verifier.accepts at hacc
      rw [← hn, ← hgs] at hacc
      exact hacc

/-- The cost-instrumented Cook–Levin reduction: it returns the formula together with
the exact number of elementary steps used to build it. -/
