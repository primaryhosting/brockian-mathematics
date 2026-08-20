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

lemma evalCNF_congr {σ τ : ℕ → Bool} {F : CNF}
    (h : ∀ i < numVars F, σ i = τ i) : evalCNF σ F = evalCNF τ F := by
  have hcl : ∀ C ∈ F, evalClause σ C = evalClause τ C := by
    intro C hC
    exact evalClause_congr (fun l hl => h l.var (lt_numVars hC hl))
  clear h
  simp only [evalCNF]
  induction F with
  | nil => rfl
  | cons C F ih =>
      simp only [List.all_cons]
      rw [hcl C (List.mem_cons_self ..),
        ih (fun C' hC' => hcl C' (List.mem_cons_of_mem _ hC'))]

end Frontier

import RequestProject.CNF

/-!
# Boolean straight-line programs (circuits)

A *straight-line program* is a list of gates; the gate at position `j` computes the
value of wire `j` from input bits and from wires with smaller index.  This is the
standard (fan-in two) Boolean circuit model, presented in a topologically sorted way.
-/

namespace Frontier

/-- A single gate of a straight-line program.  `neg`, `conj`, `disj` refer to
previously computed wires; `inp i` reads input bit `i`; `cst b` is a constant. -/
inductive Gate
  | inp (i : ℕ)
  | cst (b : Bool)
  | neg (a : ℕ)
  | conj (a b : ℕ)
  | disj (a b : ℕ)
deriving DecidableEq, Repr

/-- A straight-line program (Boolean circuit) is a list of gates. -/
abbrev SLP := List Gate

/-- Value of a gate given the input bits `x` and the values `vs` of earlier wires. -/
