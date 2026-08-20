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

lemma evalWires_congr {x y : ℕ → Bool} {n : ℕ} {gs : SLP}
    (hin : InputsLT n gs) (hxy : ∀ i < n, x i = y i) :
    evalWires x gs = evalWires y gs := by
  suffices h : ∀ (k : ℕ) (gs : SLP), gs.length ≤ k → InputsLT n gs →
      evalWires x gs = evalWires y gs from h gs.length gs le_rfl hin
  intro k
  induction k with
  | zero =>
      intro gs hk _
      have : gs = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [this, evalWires]
  | succ k ih =>
      intro gs hk hin
      rcases List.eq_nil_or_concat gs with h | ⟨gs', g, h⟩
      · simp [h, evalWires]
      · rw [List.concat_eq_append] at h
        subst h
        have hlen : gs'.length ≤ k := by
          simp at hk; omega
        have hin' : InputsLT n gs' := by
          intro j hj
          have hj' : j < (gs' ++ [g]).length := by simp; omega
          have := hin j hj'
          rwa [List.getElem_append_left hj] at this
        have hgin : g.inpLT n := by
          have hj' : gs'.length < (gs' ++ [g]).length := by simp
          have h2 := hin gs'.length hj'
          rw [List.getElem_append_right (by omega)] at h2
          simpa using h2
        have hrec := ih gs' hlen hin'
        have hgate : evalGate x (evalWires x gs') g = evalGate y (evalWires y gs') g := by
          cases hg : g with
          | inp i =>
              rw [hg] at hgin
              simp [evalGate, hxy i hgin]
          | cst b => simp [evalGate]
          | neg a => simp [evalGate, hrec]
          | conj a b => simp [evalGate, hrec]
          | disj a b => simp [evalGate, hrec]
        simp only [evalWires, List.foldl_append, List.foldl_cons, List.foldl_nil, wireStep]
        simp only [evalWires] at hrec hgate
        rw [hgate, hrec]

