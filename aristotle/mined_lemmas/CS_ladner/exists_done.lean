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

theorem exists_done (hPNP : S.P ≠ S.NP) (c : Nat) : ∃ n, S.f n = c ∧ S.SDone n := by
  classical
  have h : ∃ n, c + 1 ≤ S.f n := S.f_unbounded hPNP (c + 1)
  have ⟨m, hm, hmin⟩ := exists_least (fun n => c + 1 ≤ S.f n) h
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, S.f_zero] at hm
    omega
  have ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  subst hk
  have hkmin : ¬ (c + 1 ≤ S.f k) := hmin k (by omega)
  have h1 : S.f (k + 1) ≤ S.f k + 1 := S.f_succ_le k
  have hfk : S.f k = c := by omega
  refine ⟨k, hfk, ?_⟩
  by_cases hd : S.SDone k
  · exact hd
  · exfalso
    have := S.f_not_done hd
    omega

end Setting

/-! ### Ladner's theorem -/

/-- **Ladner's theorem.**  If `P ≠ NP`, then there exists an `NP`-intermediate language: a
language which lies in `NP`, does not lie in `P`, and is not `NP`-hard (in particular it is
not `NP`-complete). -/
