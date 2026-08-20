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

theorem cook_levin_hardness {L : List Bool → Prop} (hL : InNP L) :
    ∃ f : List Bool → CNF × ℕ, (∀ x, L x ↔ SAT (f x).1) ∧
      ∃ c k : ℕ, ∀ x, cnfSize (f x).1 ≤ c * (x.length + 1) ^ k ∧
        (f x).2 ≤ c * (x.length + 1) ^ k := by
  obtain ⟨V, hV⟩ := hL
  refine ⟨cookReductionRun V, fun x => ?_, ?_⟩
  · rw [cookReductionRun_fst]
    exact (hV x).trans (sat_cookReduction_iff V x).symm
  · obtain ⟨c, k, hck⟩ := cookReduction_poly V
    exact ⟨c, k, fun x => ⟨by rw [cookReductionRun_fst]; exact (hck x).1, (hck x).2⟩⟩

/-! ## The Cook–Levin theorem -/

/-- **The Cook–Levin theorem: SAT is NP-complete.**

1. *SAT is in NP*: a formula `F` is satisfiable iff there is a witness bit string of
   length `numVars F` accepted by the checker, and the checker runs in linear time
   (`2 * cnfSize F + 1` elementary steps at most).
2. *SAT is NP-hard*: for every language `L` recognized by a polynomial-size circuit
   verifier there is a many-one reduction of `L` to SAT which, on input `x`, outputs
   a formula of size polynomial in `|x|` using polynomially many elementary steps;
   the reduction is the explicit Tseitin-style construction `cookReductionRun`. -/
