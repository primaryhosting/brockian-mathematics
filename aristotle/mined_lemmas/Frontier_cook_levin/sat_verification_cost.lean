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

theorem sat_verification_cost (F : CNF) (w : List Bool) :
    (evalCNFCost (assignOf w) F).1 = evalCNF (assignOf w) F ∧
      (evalCNFCost (assignOf w) F).2 ≤ 2 * cnfSize F + 1 :=
  ⟨evalCNFCost_fst _ _, evalCNFCost_snd_le _ _⟩

/-! ## NP via circuit verifiers -/

/-- A polynomial-time verifier, presented as a polynomial-size family of Boolean
circuits: `ckt n` is the circuit used on inputs of length `n`, it reads the `n` input
bits and `wit n` witness bits, and its last wire carries the answer. -/
structure Verifier where
  /-- Length of the witness for inputs of length `n`. -/
  wit : ℕ → ℕ
  /-- The verifier circuit for inputs of length `n`. -/
  ckt : ℕ → SLP
  /-- Each circuit is a well-formed straight-line program. -/
  wf : ∀ n, WF (ckt n)
  /-- Each circuit has at least one gate (its output). -/
  ne : ∀ n, ckt n ≠ []
  /-- The circuit reads only the input bits and the witness bits. -/
  reads : ∀ n, InputsLT (n + wit n) (ckt n)
  /-- The circuits have polynomial size. -/
  polyC : ∃ c k : ℕ, ∀ n, (ckt n).length ≤ c * (n + 1) ^ k
  /-- The witnesses have polynomially bounded length. -/
  polyW : ∃ c k : ℕ, ∀ n, wit n ≤ c * (n + 1) ^ k

namespace Verifier

variable (V : Verifier)

/-- The verifier accepts input `x` with witness `w`. -/
