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

lemma lt_numVars {F : CNF} {C : Clause} {l : Lit} (hC : C ∈ F) (hl : l ∈ C) :
    l.var < numVars F := by
  have hmem : l ∈ F.flatten := List.mem_flatten.2 ⟨C, hC, hl⟩
  have : ∀ (L : List Lit), l ∈ L → l.var + 1 ≤ (L.map (fun l => l.var + 1)).foldr max 0 := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
        intro h
        rcases List.mem_cons.1 h with h | h
        · subst h; simp
        · exact le_trans (ih h) (by simp)
  exact this _ hmem

/-- The value of a clause only depends on the values of the variables occurring in it. -/
