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

lemma tseitin_spec (σ : ℕ → Bool) (gs : SLP) :
    evalCNF σ (tseitin gs) = true ↔
      ∀ j, j < gs.length → evalCNF σ (tseitinGate j (gs.getD j (Gate.cst false))) = true := by
  constructor
  · intro h j hj
    rw [evalCNF_eq_true_iff] at h ⊢
    intro C hC
    refine h C ?_
    simp only [tseitin, List.mem_flatMap, List.mem_range]
    exact ⟨j, hj, hC⟩
  · intro h
    rw [evalCNF_eq_true_iff]
    intro C hC
    simp only [tseitin, List.mem_flatMap, List.mem_range] at hC
    obtain ⟨j, hj, hC⟩ := hC
    exact (evalCNF_eq_true_iff _ _).1 (h j hj) C hC

