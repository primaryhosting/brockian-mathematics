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

def toySetting : Setting where
  len := toyLen
  Penum := toyPenum
  redFun := toyRedFun
  SAT := toySAT
  P := toyP
  NP := toyP
  Red := toyRed
  P_subset_NP := fun _ h => h
  empty_mem_P := ⟨0, fun _ _ h => h⟩
  P_variation := by
    intro A B hA hvar
    have ⟨N₁, h₁⟩ := hA
    have ⟨N₂, h₂⟩ := hvar
    refine ⟨N₁ + N₂, fun x hx hB => ?_⟩
    have hx2 : N₂ ≤ toyLen x := show N₂ ≤ x by omega
    exact h₁ x (by omega) ((h₂ x hx2).mpr hB)
  Penum_mem := fun i => ⟨i, fun x hx hc => by
    have hc' : decB i x = true := hc
    rw [decB_eq_false_of_le hx] at hc'
    exact Bool.noConfusion hc'⟩
  Penum_covers := by
    intro A hA
    have ⟨N, hN⟩ := hA
    exact decB_covers N A hN
  Red_iff := fun _ _ => Iff.rfl
  Red_P := by
    intro A B hAB hB
    have ⟨i, hi⟩ := hAB
    have ⟨N, hN⟩ := hB
    refine ⟨N + i, fun x hx hA => ?_⟩
    have hfalse : decB i x = false := decB_eq_false_of_le (by omega)
    have hred : toyRedFun i x = x + 1 := by
      show (if decB i x then 0 else x + 1) = x + 1
      rw [hfalse]; rfl
    have : B (toyRedFun i x) := (hi x).mp hA
    rw [hred] at this
    exact hN (x + 1) (by omega) this
  SAT_mem_NP := ⟨1, fun x hx hc => by
    have : x = 0 := hc
    omega⟩
  SAT_complete := by
    intro A hA
    have ⟨N, hN⟩ := hA
    have ⟨i, hi⟩ := decB_covers N A hN
    refine ⟨i, fun x => ?_⟩
    show A x ↔ (toyRedFun i x = 0)
    by_cases hb : decB i x = true
    · have hred : toyRedFun i x = 0 := by
        show (if decB i x then 0 else x + 1) = 0
        rw [hb]; rfl
      constructor
      · intro _; exact hred
      · intro _; exact (hi x).mpr hb
    · have hb' : decB i x = false := by
        cases h : decB i x with
        | false => rfl
        | true => exact absurd h hb
      have hred : toyRedFun i x = x + 1 := by
        show (if decB i x then 0 else x + 1) = x + 1
        rw [hb']; rfl
      constructor
      · intro hc; exact absurd ((hi x).mp hc) hb
      · intro hc; rw [hred] at hc; omega
  ladnerLang_mem_NP := ⟨1, fun x hx hc => by
    have h0 : toySAT x := hc.1
    have : x = 0 := h0
    omega⟩

/-- In the model above the two classes coincide, so Ladner's theorem says nothing there. -/
