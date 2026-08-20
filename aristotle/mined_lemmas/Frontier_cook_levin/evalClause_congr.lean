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

lemma evalClause_congr {σ τ : ℕ → Bool} {C : Clause}
    (h : ∀ l ∈ C, σ l.var = τ l.var) : evalClause σ C = evalClause τ C := by
  simp only [evalClause]
  induction C with
  | nil => rfl
  | cons a C ih =>
      simp only [List.any_cons]
      rw [ih (fun l hl => h l (List.mem_cons_of_mem _ hl))]
      have : evalLit σ a = evalLit τ a := by
        simp [evalLit, h a (List.mem_cons_self ..)]
      rw [this]

/-- The truth value of a CNF formula only depends on the values of its variables. -/
