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

theorem tseitin_complete (c : Circuit) : ∀ (k : Nat) (τ : Nat → Bool) (σ₀ : Nat ⊕ Nat → Bool),
    (∀ i, σ₀ (Sum.inl i) = τ i) →
    ∃ σ : Nat ⊕ Nat → Bool,
      (∀ i, σ (Sum.inl i) = τ i) ∧
      (∀ j, (j < k ∨ (tseitin c k).next ≤ j) → σ (Sum.inr j) = σ₀ (Sum.inr j)) ∧
      cnfEval σ (tseitin c k).cls = true ∧
      litEval σ (tseitin c k).out = c.eval τ := by
  induction c with
  | var i =>
      intro k τ σ₀ h₀
      exact ⟨σ₀, h₀, fun j _ => rfl, by simp [tseitin, cnfEval],
        by simp [tseitin, Circuit.eval, h₀]⟩
  | tru =>
      intro k τ σ₀ h₀
      refine ⟨updAt σ₀ k true, fun i => h₀ i, ?_, ?_, ?_⟩
      · intro j hj
        simp only [tseitin] at hj
        exact updAt_inr_ne _ _ (by omega)
      · simp [tseitin, cnfEval]
      · simp [tseitin, Circuit.eval]
  | fls =>
      intro k τ σ₀ h₀
      refine ⟨updAt σ₀ k false, fun i => h₀ i, ?_, ?_, ?_⟩
      · intro j hj
        simp only [tseitin] at hj
        exact updAt_inr_ne _ _ (by omega)
      · simp [tseitin, cnfEval]
      · simp [tseitin, Circuit.eval]
  | neg a ih =>
      intro k τ σ₀ h₀
      obtain ⟨σ, hl, hr, hc, ho⟩ := ih k τ σ₀ h₀
      refine ⟨σ, hl, ?_, ?_, ?_⟩
      · simpa only [tseitin] using hr
      · simpa only [tseitin] using hc
      · simp only [tseitin, litEval_negLit, ho, Circuit.eval]
  | conj a b iha ihb =>
      intro k τ σ₀ h₀
      obtain ⟨σ1, h1l, h1r, h1c, h1o⟩ := iha k τ σ₀ h₀
      obtain ⟨σ2, h2l, h2r, h2c, h2o⟩ := ihb (tseitin a k).next τ σ1 h1l
      have hk1 := tseitin_next_ge a k
      have hk2 := tseitin_next_ge b (tseitin a k).next
      have hinl1 : ∀ i, updAt σ2 (tseitin b (tseitin a k).next).next
          (a.eval τ && b.eval τ) (Sum.inl i) = σ1 (Sum.inl i) := by
        intro i; rw [updAt_inl, h2l i, ← h1l i]
      have hinl2 : ∀ i, updAt σ2 (tseitin b (tseitin a k).next).next
          (a.eval τ && b.eval τ) (Sum.inl i) = σ2 (Sum.inl i) := fun _ => rfl
      have hAgreeA : ∀ j, k ≤ j → j < (tseitin a k).next →
          updAt σ2 (tseitin b (tseitin a k).next).next
            (a.eval τ && b.eval τ) (Sum.inr j) = σ1 (Sum.inr j) := by
        intro j hlo hhi
        rw [updAt_inr_ne _ _ (by omega)]
        exact h2r j (Or.inl (by omega))
      have hAgreeB : ∀ j, (tseitin a k).next ≤ j → j < (tseitin b (tseitin a k).next).next →
          updAt σ2 (tseitin b (tseitin a k).next).next
            (a.eval τ && b.eval τ) (Sum.inr j) = σ2 (Sum.inr j) := by
        intro j _ hhi
        exact updAt_inr_ne _ _ (by omega)
      refine ⟨updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ && b.eval τ),
        fun i => h2l i, ?_, ?_, ?_⟩
      · intro j hj
        simp only [tseitin] at hj
        rw [updAt_inr_ne _ _ (by omega), h2r j (by omega)]
        exact h1r j (by omega)
      · have ea : litEval (updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ && b.eval τ))
            (tseitin a k).out = a.eval τ := by
          rw [litEval_out_congr a k hinl1 hAgreeA]; exact h1o
        have eb : litEval (updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ && b.eval τ))
            (tseitin b (tseitin a k).next).out = b.eval τ := by
          rw [litEval_out_congr b _ hinl2 hAgreeB]; exact h2o
        have ca : cnfEval (updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ && b.eval τ))
            (tseitin a k).cls = true := by
          rw [cnfEval_congr_vars (tseitin_vars a k) hinl1 hAgreeA]; exact h1c
        have cb : cnfEval (updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ && b.eval τ))
            (tseitin b (tseitin a k).next).cls = true := by
          rw [cnfEval_congr_vars (tseitin_vars b _) hinl2 hAgreeB]; exact h2c
        simp only [tseitin, cnfEval, List.all_cons, List.all_append, List.any_cons, List.any_nil,
          Bool.or_false, Bool.and_eq_true, litEval_negLit, litEval_mk_true, updAt_inr_self, ea, eb]
        refine ⟨?_, ?_, ?_, ca, cb⟩ <;>
          cases hA : a.eval τ <;> cases hB : b.eval τ <;> rfl
      · simp [tseitin, Circuit.eval]
  | disj a b iha ihb =>
      intro k τ σ₀ h₀
      obtain ⟨σ1, h1l, h1r, h1c, h1o⟩ := iha k τ σ₀ h₀
      obtain ⟨σ2, h2l, h2r, h2c, h2o⟩ := ihb (tseitin a k).next τ σ1 h1l
      have hk1 := tseitin_next_ge a k
      have hk2 := tseitin_next_ge b (tseitin a k).next
      have hinl1 : ∀ i, updAt σ2 (tseitin b (tseitin a k).next).next
          (a.eval τ || b.eval τ) (Sum.inl i) = σ1 (Sum.inl i) := by
        intro i; rw [updAt_inl, h2l i, ← h1l i]
      have hinl2 : ∀ i, updAt σ2 (tseitin b (tseitin a k).next).next
          (a.eval τ || b.eval τ) (Sum.inl i) = σ2 (Sum.inl i) := fun _ => rfl
      have hAgreeA : ∀ j, k ≤ j → j < (tseitin a k).next →
          updAt σ2 (tseitin b (tseitin a k).next).next
            (a.eval τ || b.eval τ) (Sum.inr j) = σ1 (Sum.inr j) := by
        intro j hlo hhi
        rw [updAt_inr_ne _ _ (by omega)]
        exact h2r j (Or.inl (by omega))
      have hAgreeB : ∀ j, (tseitin a k).next ≤ j → j < (tseitin b (tseitin a k).next).next →
          updAt σ2 (tseitin b (tseitin a k).next).next
            (a.eval τ || b.eval τ) (Sum.inr j) = σ2 (Sum.inr j) := by
        intro j _ hhi
        exact updAt_inr_ne _ _ (by omega)
      refine ⟨updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ || b.eval τ),
        fun i => h2l i, ?_, ?_, ?_⟩
      · intro j hj
        simp only [tseitin] at hj
        rw [updAt_inr_ne _ _ (by omega), h2r j (by omega)]
        exact h1r j (by omega)
      · have ea : litEval (updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ || b.eval τ))
            (tseitin a k).out = a.eval τ := by
          rw [litEval_out_congr a k hinl1 hAgreeA]; exact h1o
        have eb : litEval (updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ || b.eval τ))
            (tseitin b (tseitin a k).next).out = b.eval τ := by
          rw [litEval_out_congr b _ hinl2 hAgreeB]; exact h2o
        have ca : cnfEval (updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ || b.eval τ))
            (tseitin a k).cls = true := by
          rw [cnfEval_congr_vars (tseitin_vars a k) hinl1 hAgreeA]; exact h1c
        have cb : cnfEval (updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ || b.eval τ))
            (tseitin b (tseitin a k).next).cls = true := by
          rw [cnfEval_congr_vars (tseitin_vars b _) hinl2 hAgreeB]; exact h2c
        simp only [tseitin, cnfEval, List.all_cons, List.all_append, List.any_cons, List.any_nil,
          Bool.or_false, Bool.and_eq_true, litEval_negLit, litEval_mk_true, updAt_inr_self, ea, eb]
        refine ⟨?_, ?_, ?_, ca, cb⟩ <;>
          cases hA : a.eval τ <;> cases hB : b.eval τ <;> rfl
      · simp [tseitin, Circuit.eval]

