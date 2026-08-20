/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is self-contained (no imports): it builds, from scratch,

* propositional formulas in conjunctive normal form (CNF) and satisfiability,
* Boolean circuits (as formulas over a fixed set of input variables),
* the Tseitin transformation from circuits to CNF, with its correctness proof
  and a linear size bound,
* the notion of an `NP` verifier (a polynomial-size circuit family together
  with a polynomially bounded witness length),

and proves the Cook–Levin theorem in the following form.

`Frontier.cook_levin`: every language `L` admitting a polynomial-size circuit
verifier reduces to `SAT` by an (explicitly constructed, hence computable)
map `f` such that `x ∈ L ↔ f x` is satisfiable, and the size of `f x` is
bounded by a polynomial in the length of `x`.

`Frontier.sat_in_np`: conversely, `SAT` itself lies in `NP`: a CNF `c` is
satisfiable iff there is a witness (a Boolean word of length the number of
variables of `c`) accepted by a circuit of size linear in `c`, which is
constructed from `c` by the explicit map `cnfCircuit`.

## Scope

Membership in `NP` is formalised here through *verifier circuits* rather than
through Turing machines: a language is in `NP` when there are a circuit family
`V` of polynomially bounded size and a witness-length function `m` such that
`V n` accepts exactly the pairs (input of length `n`, witness of length `m n`)
that certify membership. The step which is proved is therefore the
circuit-satisfiability core of Cook–Levin (the Tseitin translation of an
arbitrary verifier circuit into an equisatisfiable CNF of linear size, together
with the hard-wiring of the input), and not the simulation of a
polynomial-time Turing machine by a polynomial-size circuit family. All
constructions here are explicit computable functions, and the size bounds are
proved, not assumed.
-/

namespace Frontier

/-! ## Polynomial bounds -/

/-- A function `Nat → Nat` is polynomially bounded. The shifted base `n+1`
avoids degenerate behaviour at `n = 0`. -/

theorem reduction_correct (V : Nat → Circuit) (m : Nat → Nat)
    (hvars : ∀ n, (V n).VarsBelow (n + m n)) (x : List Bool) :
    Sat (reduction V x) ↔
      ∃ w : List Bool, w.length = m x.length ∧
        (V x.length).eval (fun i => (x ++ w).getD i false) = true := by
  rw [reduction, sat_cnfMap_iff sumEnc_injective]
  constructor
  · rintro ⟨σ, hσ⟩
    rw [cnfEval_append, cnfEval_append, Bool.and_eq_true, Bool.and_eq_true] at hσ
    obtain ⟨⟨hcls, hin⟩, hout⟩ := hσ
    have hsound := tseitin_sound (V x.length) 0 σ hcls
    have houttrue : litEval σ (tseitin (V x.length) 0).out = true := by
      simpa [cnfEval] using hout
    have hev : (V x.length).eval (fun i => σ (Sum.inl i)) = true := by
      rw [← hsound]; exact houttrue
    have hinput := (cnfEval_inputClauses_iff σ x).1 hin
    refine ⟨(List.range (m x.length)).map (fun j => σ (Sum.inl (x.length + j))), by simp, ?_⟩
    rw [Circuit.eval_congr (hvars x.length) (τ₂ := fun i => σ (Sum.inl i)) ?_]
    · exact hev
    · intro i hi
      by_cases hlt : i < x.length
      · rw [getD_append_left _ _ _ hlt]
        exact (hinput i hlt).symm
      · have hge : x.length ≤ i := by omega
        rw [getD_append_right _ _ _ hge]
        have hidx : i - x.length < m x.length := by omega
        rw [List.getD_eq_getElem?_getD]
        simp only [List.getElem?_map, List.getElem?_range, hidx, Option.map_some,
          Option.getD_some]
        congr 2
        omega
  · rintro ⟨w, hwlen, hw⟩
    obtain ⟨σ, hl, -, hc, ho⟩ := tseitin_complete (V x.length) 0
      (fun i => (x ++ w).getD i false)
      (Sum.elim (fun i => (x ++ w).getD i false) (fun _ => false)) (fun _ => rfl)
    refine ⟨σ, ?_⟩
    rw [cnfEval_append, cnfEval_append, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨hc, ?_⟩, ?_⟩
    · rw [cnfEval_inputClauses_iff]
      intro i hi
      rw [hl i, getD_append_left _ _ _ hi]
    · simp only [cnfEval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
        Bool.or_false, Bool.and_true]
      rw [ho, hw]

