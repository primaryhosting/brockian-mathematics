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

theorem ladner (S : Setting) (hPNP : S.P ≠ S.NP) :
    ∃ L : Lang, S.NP L ∧ ¬ S.P L ∧ ¬ (∀ A : Lang, S.NP A → S.Red A L) := by
  classical
  refine ⟨S.L, S.ladnerLang_mem_NP, ?_, ?_⟩
  · -- the constructed language is not in `P`
    intro hLP
    have ⟨i, hi⟩ := S.Penum_covers S.L hLP
    have ⟨n, hfn, hdone⟩ := S.exists_done hPNP (2 * i)
    have heven : S.f n % 2 = 0 := by omega
    have hdiv : S.f n / 2 = i := by omega
    cases hdone with
    | inl hd =>
        have ⟨_, x, _, hxs⟩ := hd
        rw [hdiv] at hxs
        have hx : S.L x ↔ ¬ S.Penum i x := hxs
        have hcontra : S.Penum i x ↔ ¬ S.Penum i x := Iff.trans (hi x).symm hx
        by_cases hp : S.Penum i x
        · exact (hcontra.mp hp) hp
        · exact hp (hcontra.mpr hp)
    | inr hd =>
        have ⟨ho, _⟩ := hd
        omega
  · -- `SAT` does not reduce to the constructed language
    intro hall
    have ⟨i, hi⟩ := (S.Red_iff S.SAT S.L).mp (hall S.SAT S.SAT_mem_NP)
    have ⟨n, hfn, hdone⟩ := S.exists_done hPNP (2 * i + 1)
    cases hdone with
    | inl hd =>
        have ⟨he, _⟩ := hd
        omega
    | inr hd =>
        have ⟨_, x, _, _, hxs⟩ := hd
        have hdiv : S.f n / 2 = i := by omega
        rw [hdiv] at hxs
        exact hxs (hi x)

/-! ### Consistency of the setting

The axioms bundled in `CS.Setting` are consistent: a (degenerate) model is exhibited below,
so that Ladner's theorem above is not vacuous for trivial reasons.  In this model `P = NP`
holds, so it does not, of course, provide any information about the real classes; producing a
model with `P ≠ NP` would require the whole of complexity theory (and, in particular, an
effective version of the construction). -/

namespace Consistency

/-- Decoding a natural number as a finite set of naturals: `decB i x` is the `x`-th binary
digit of `i`. -/
