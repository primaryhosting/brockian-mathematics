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

lemma cnfSize_tseitin (gs : SLP) : cnfSize (tseitin gs) ≤ 10 * gs.length := by
  rw [tseitin, cnfSize_flatMap]
  have : ∀ n : ℕ, ((List.range n).map
      (fun j => cnfSize (tseitinGate j (gs.getD j (Gate.cst false))))).sum ≤ 10 * n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [List.range_succ, List.map_append, List.sum_append]
        have := cnfSize_tseitinGate n (gs.getD n (Gate.cst false))
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        omega
  exact this gs.length

