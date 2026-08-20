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

theorem cookReduction_poly (V : Verifier) :
    ∃ c k : ℕ, ∀ x : List Bool,
      cnfSize (cookReduction V x) ≤ c * (x.length + 1) ^ k ∧
        (cookReductionRun V x).2 ≤ c * (x.length + 1) ^ k := by
  obtain ⟨c, k, hc⟩ := V.polyC
  refine ⟨11 * c + 5, k + 1, ?_⟩
  intro x
  set n := x.length with hn
  have h1 : cnfSize (cookReduction V x) ≤ 10 * (V.ckt n).length + 2 * n + 2 :=
    cnfSize_reduceSLP _ _
  have h1' : (cookReductionRun V x).2 = 11 * (V.ckt n).length + 2 * n + 3 :=
    reduceBuild_snd _ _
  have h2 : (V.ckt n).length ≤ c * (n + 1) ^ k := hc n
  have h3 : (n + 1) ^ k ≤ (n + 1) ^ (k + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : n + 1 ≤ (n + 1) ^ (k + 1) := Nat.le_self_pow (by omega) _
  have h5 : c * (n + 1) ^ k ≤ c * (n + 1) ^ (k + 1) := Nat.mul_le_mul_left _ h3
  have key : 11 * (V.ckt n).length + 2 * n + 3
      ≤ (11 * c + 5) * (n + 1) ^ (k + 1) := by
    calc 11 * (V.ckt n).length + 2 * n + 3
        ≤ 11 * (c * (n + 1) ^ k) + 5 * (n + 1) := by omega
      _ ≤ 11 * (c * (n + 1) ^ (k + 1)) + 5 * (n + 1) ^ (k + 1) := by omega
      _ ≤ (11 * c + 5) * (n + 1) ^ (k + 1) := by ring_nf; omega
  exact ⟨by omega, by omega⟩

/-- **NP-hardness of SAT**, stated for an arbitrary language in NP: every such
language many-one reduces to SAT via the explicit reduction `cookReduction`, which
produces a formula of polynomial size in polynomially many steps. -/
