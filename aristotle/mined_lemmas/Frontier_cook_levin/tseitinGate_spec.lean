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

lemma tseitinGate_spec (σ : ℕ → Bool) (j : ℕ) (g : Gate) :
    evalCNF σ (tseitinGate j g) = true ↔ σ (wireVar j) = gateSem σ g := by
  cases g with
  | inp i =>
      simp only [tseitinGate, gateSem, evalCNF, evalClause, evalLit, posLit, negLit,
        List.all_cons, List.all_nil, List.any_cons, List.any_nil]
      cases σ (wireVar j) <;> cases σ (inputVar i) <;> simp
  | cst b =>
      cases b <;> cases hσ : σ (wireVar j) <;>
        simp [tseitinGate, gateSem, evalCNF, evalClause, evalLit, posLit, negLit, hσ]
  | neg a =>
      simp only [tseitinGate, gateSem, evalCNF, evalClause, evalLit, posLit, negLit,
        List.all_cons, List.all_nil, List.any_cons, List.any_nil]
      cases σ (wireVar j) <;> cases σ (wireVar a) <;> simp
  | conj a b =>
      simp only [tseitinGate, gateSem, evalCNF, evalClause, evalLit, posLit, negLit,
        List.all_cons, List.all_nil, List.any_cons, List.any_nil]
      cases σ (wireVar j) <;> cases σ (wireVar a) <;> cases σ (wireVar b) <;> simp
  | disj a b =>
      simp only [tseitinGate, gateSem, evalCNF, evalClause, evalLit, posLit, negLit,
        List.all_cons, List.all_nil, List.any_cons, List.any_nil]
      cases σ (wireVar j) <;> cases σ (wireVar a) <;> cases σ (wireVar b) <;> simp

/-- The Tseitin encoding of a straight-line program. -/
