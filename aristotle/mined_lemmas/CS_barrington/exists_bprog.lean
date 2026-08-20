import Mathlib

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Barrington's theorem: the Boolean functions computed by fan-in-two Boolean circuits of
depth `d` are exactly the ones computed by width-5 permutation branching programs of
length `4 ^ d` (up to a constant factor in the exponent / a logarithm in the length).

We formalise the two quantitative directions:

* `CS.exists_bprog`  : a circuit of depth `d` is simulated by a width-5 permutation
  branching program of length at most `4 ^ d`  (the hard direction of Barrington's theorem);
* `CS.exists_circuit`: a width-5 permutation branching program of length `L` is simulated
  by a circuit of depth at most `4 * ⌈log₂ L⌉ + 6` (the easy direction).

Together (`CS.barrington`) these say `NC¹ = width-5 permutation branching programs`:
logarithmic depth corresponds to polynomial length.
-/

namespace CS

open Equiv

/-! ## Boolean circuits -/

/-- Boolean circuits with fan-in two `∧`/`∨` gates and `¬` gates, over the variables
`x 0, x 1, …`. -/
inductive Circuit where
  | const : Bool → Circuit
  | var : ℕ → Circuit
  | not : Circuit → Circuit
  | and : Circuit → Circuit → Circuit
  | or : Circuit → Circuit → Circuit
  deriving Inhabited

/-- The Boolean function computed by a circuit. -/

theorem exists_bprog (c : Circuit) : ∀ γ : Perm (Fin 5), Conj5 γ →
    ∃ P : BProg, P ≠ [] ∧ P.length ≤ 4 ^ c.depth ∧ Computes P γ c.eval := by
  induction c with
  | const b =>
      intro γ _
      refine ⟨[(0, if b then γ else 1, if b then γ else 1)], by simp, by simp [Circuit.depth], ?_⟩
      intro x
      simp only [BProg.eval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        Instr.run, mul_one, Circuit.eval]
      split <;> rfl
  | var i =>
      intro γ _
      refine ⟨[(i, γ, 1)], by simp, by simp [Circuit.depth], ?_⟩
      intro x
      simp only [BProg.eval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        Instr.run, mul_one, Circuit.eval]
  | not c ih =>
      intro γ hγ
      obtain ⟨P, hne, hlen, hP⟩ := ih γ⁻¹ hγ.inv
      refine ⟨P.pre γ, BProg.pre_ne_nil γ hne, ?_, ?_⟩
      · rw [BProg.length_pre]
        exact hlen.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
      · intro x; exact neg_computes hne hP x
  | and a b iha ihb =>
      intro γ hγ
      obtain ⟨σ, τ, hσ, hτ, hc⟩ := hγ.commutator
      obtain ⟨P, hPne, hPlen, hP⟩ := iha σ hσ
      obtain ⟨Q, hQne, hQlen, hQ⟩ := ihb τ hτ
      refine ⟨P ++ Q ++ P.inv ++ Q.inv, comb_ne_nil hPne, ?_, ?_⟩
      · rw [length_comb]
        exact length_bound hPlen hQlen
      · intro x
        have h := and_computes hP hQ x
        rw [hc] at h
        exact h
  | or a b iha ihb =>
      intro γ hγ
      obtain ⟨σ, τ, hσ, hτ, hc⟩ := hγ.inv.commutator
      obtain ⟨P, hPne, hPlen, hP⟩ := iha σ⁻¹ hσ.inv
      obtain ⟨Q, hQne, hQlen, hQ⟩ := ihb τ⁻¹ hτ.inv
      have hP' : Computes (P.pre σ) σ (fun x => !a.eval x) := neg_computes hPne hP
      have hQ' : Computes (Q.pre τ) τ (fun x => !b.eval x) := neg_computes hQne hQ
      have hne' : (P.pre σ) ++ (Q.pre τ) ++ (P.pre σ).inv ++ (Q.pre τ).inv ≠ [] :=
        comb_ne_nil (BProg.pre_ne_nil σ hPne)
      refine ⟨(((P.pre σ) ++ (Q.pre τ) ++ (P.pre σ).inv ++ (Q.pre τ).inv).pre γ),
        BProg.pre_ne_nil γ hne', ?_, ?_⟩
      · rw [BProg.length_pre, length_comb, BProg.length_pre, BProg.length_pre]
        exact length_bound hPlen hQlen
      · have hand := and_computes hP' hQ'
        rw [hc] at hand
        intro x
        have h := neg_computes hne' hand x
        simp only [Bool.not_and, Bool.not_not] at h
        exact h

/-! ## The easy direction: simulating a branching program by a shallow circuit -/

