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

theorem sat_reduceSLP_iff {gs : SLP} (hwf : WF gs) (hne : gs ≠ []) (bits : List Bool) :
    SAT (reduceSLP gs bits) ↔
      ∃ x : ℕ → Bool, (∀ i, i < bits.length → x i = bits.getD i false) ∧
        wireVal x gs (gs.length - 1) = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    simp only [reduceSLP, evalCNF_append, Bool.and_eq_true] at hσ
    obtain ⟨⟨h1, h2⟩, h3⟩ := hσ
    refine ⟨fun i => σ (inputVar i), ?_, ?_⟩
    · exact (fixClauses_spec σ bits).1 h2
    · have hlen : 0 < gs.length := List.length_pos_iff.2 hne
      have hj : gs.length - 1 < gs.length := by omega
      have := tseitin_sound hwf h1 (gs.length - 1) hj
      rw [← this]
      simpa [evalCNF, evalClause, evalLit, posLit] using h3
  · rintro ⟨x, hbits, hout⟩
    refine ⟨canonAssign x gs, ?_⟩
    simp only [reduceSLP, evalCNF_append, Bool.and_eq_true]
    refine ⟨⟨canonAssign_sat hwf x, ?_⟩, ?_⟩
    · rw [fixClauses_spec]
      intro i hi
      rw [canonAssign_inputVar]
      exact hbits i hi
    · simp [evalCNF, evalClause, evalLit, posLit, hout]

/-! ### Size of the reduction -/

