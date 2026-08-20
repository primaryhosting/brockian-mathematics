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

lemma fixClauses_spec (σ : ℕ → Bool) (bits : List Bool) :
    evalCNF σ (fixClauses bits) = true ↔ ∀ i, i < bits.length → σ (inputVar i) = bits.getD i false := by
  rw [evalCNF_eq_true_iff]
  constructor
  · intro h i hi
    have := h _ (by
      simp only [fixClauses, List.mem_map, List.mem_range]
      exact ⟨i, hi, rfl⟩)
    simp only [evalClause, evalLit, List.any_cons, List.any_nil] at this
    revert this
    cases σ (inputVar i) <;> cases hb : bits.getD i false <;> simp
  · intro h C hC
    simp only [fixClauses, List.mem_map, List.mem_range] at hC
    obtain ⟨i, hi, rfl⟩ := hC
    simp only [evalClause, evalLit, List.any_cons, List.any_nil]
    rw [h i hi]
    cases bits.getD i false <;> simp

/-! ### The reduction -/

/-- The CNF formula produced from a circuit `gs` together with fixed values `bits`
for its first input bits: it is satisfiable iff the circuit can output `true`. -/
