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

lemma wireVal_eq_evalGate (x : ℕ → Bool) {gs : SLP} (hwf : WF gs) {j : ℕ}
    (hj : j < gs.length) :
    wireVal x gs j = evalGate x (evalWires x gs) (gs[j]'hj) := by
  have htake : gs.take (j + 1) = gs.take j ++ [gs[j]'hj] := by
    rw [List.take_add_one]
    congr 1
    simp [List.getElem?_eq_getElem hj]
  have hEval : evalWires x (gs.take (j+1))
      = evalWires x (gs.take j) ++ [evalGate x (evalWires x (gs.take j)) (gs[j]'hj)] := by
    rw [htake]
    simp only [evalWires, List.foldl_append, List.foldl_cons, List.foldl_nil, wireStep]
  have hlen : (evalWires x (gs.take j)).length = j := by
    rw [evalWires_length, List.length_take]; omega
  -- value of wire j computed inside the prefix of length j+1
  have h1 : wireVal x gs j = wireVal x (gs.take (j+1)) j :=
    wireVal_take x gs (by omega) (by omega)
  have h2 : wireVal x (gs.take (j+1)) j = evalGate x (evalWires x (gs.take j)) (gs[j]'hj) := by
    simp only [wireVal, hEval, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hlen]
  -- the gate only refers to earlier wires, whose values agree with those in the prefix
  have hrefs := hwf j hj
  have key : evalGate x (evalWires x (gs.take j)) (gs[j]'hj)
      = evalGate x (evalWires x gs) (gs[j]'hj) := by
    have hstab : ∀ a, a < j → (evalWires x (gs.take j))[a]?.getD false
        = (evalWires x gs)[a]?.getD false := by
      intro a ha
      simpa [List.getD_eq_getElem?_getD] using (wireVal_take x gs ha (by omega)).symm
    cases hg : (gs[j]'hj) with
    | inp i => simp [evalGate]
    | cst b => simp [evalGate]
    | neg a =>
        rw [hg] at hrefs
        simp [evalGate, hstab a hrefs]
    | conj a b =>
        rw [hg] at hrefs
        simp [evalGate, hstab a hrefs.1, hstab b hrefs.2]
    | disj a b =>
        rw [hg] at hrefs
        simp [evalGate, hstab a hrefs.1, hstab b hrefs.2]
  rw [h1, h2, key]

/-! ### Dependence only on the relevant input bits -/

