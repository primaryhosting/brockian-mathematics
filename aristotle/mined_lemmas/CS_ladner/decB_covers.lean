/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## Ladner's theorem

  If `P ≠ NP` then `NP`-intermediate problems exist: there is a language in `NP` which is
  neither in `P` nor `NP`-hard.

Languages are modelled as predicates on the natural numbers (natural numbers stand for the
strings over the underlying alphabet, under a fixed encoding), and `len x` is the length of
the string encoded by `x`.

The development is organised around a `CS.Setting`, which bundles the data and the standard
structural facts about polynomial-time computation used by Ladner's proof:

* `P ⊆ NP`, closure of `P` under finite variations, and the fact that `P` is *recursively
  presentable*, i.e. it comes with an enumeration `Penum` of all of its members;
* an enumeration `redFun` of the polynomial-time computable functions, such that `Red A B`
  ("`A` reduces to `B`") holds exactly when some `redFun i` is a many-one reduction of `A` to
  `B`, together with the downward closure of `P` under `Red`;
* an `NP`-complete language `SAT`;
* the *effectiveness* input of Ladner's proof: the language produced by the delayed
  diagonalisation construction below (`ladnerLang`) belongs to `NP`.  In the concrete setting
  this holds because Ladner's stage function is polynomial-time computable, so that the
  constructed language is the intersection of `SAT` with a polynomial-time decidable set of
  lengths.

What is proved here from `P ≠ NP` is the delayed diagonalisation ("looking back") argument
itself: the constructed language is not in `P`, and `SAT` does not reduce to it, so it is
`NP`-intermediate.

The file is deliberately self-contained: it uses only the Lean 4 core library.
-/

namespace CS

/-- A language: a set of natural numbers, where natural numbers encode strings. -/
abbrev Lang := Nat → Prop

/-! ### Two elementary facts about the natural numbers -/

/-- Classical least-witness principle. -/

theorem decB_covers : ∀ (N : Nat) (A : Nat → Prop), (∀ x, N ≤ x → ¬ A x) →
    ∃ i, ∀ x, (A x ↔ decB i x = true) := by
  classical
  intro N
  induction N with
  | zero =>
      intro A hA
      refine ⟨0, fun x => ?_⟩
      have h1 : ¬ A x := hA x (Nat.zero_le x)
      have h2 : decB 0 x = false := decB_eq_false_of_le (Nat.zero_le x)
      constructor
      · intro h; exact absurd h h1
      · intro h; rw [h2] at h; exact absurd h (by simp)
  | succ N ih =>
      intro A hA
      have ⟨i', hi'⟩ := ih (fun y => A (y + 1)) (fun y hy => hA (y + 1) (by omega))
      refine ⟨(if A 0 then 1 else 0) + 2 * i', fun x => ?_⟩
      cases x with
      | zero =>
          by_cases hA0 : A 0
          · have h : ((if A 0 then 1 else 0) + 2 * i') % 2 = 1 := by
              rw [if_pos hA0]; omega
            constructor
            · intro _; show (_ == 1) = true; rw [h]; rfl
            · intro _; exact hA0
          · have h : ((if A 0 then 1 else 0) + 2 * i') % 2 = 0 := by
              rw [if_neg hA0]; omega
            constructor
            · intro hc; exact absurd hc hA0
            · intro hc
              have : ((if A 0 then 1 else 0) + 2 * i') % 2 = 1 := by
                have := hc
                simp only [decB, beq_iff_eq] at this
                exact this
              omega
      | succ x =>
          have hdiv : ((if A 0 then 1 else 0) + 2 * i') / 2 = i' := by
            by_cases hA0 : A 0
            · rw [if_pos hA0]; omega
            · rw [if_neg hA0]; omega
          show A (x + 1) ↔ decB (((if A 0 then 1 else 0) + 2 * i') / 2) x = true
          rw [hdiv]
          exact hi' x

/-- The length function of the model: numbers are their own length. -/
