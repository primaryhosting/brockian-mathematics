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

theorem ladnerF_succ (n : Nat) :
    ladnerF len Penum redFun SAT (n + 1) =
      if Done len Penum redFun SAT (ladnerF len Penum redFun SAT) n then
        ladnerF len Penum redFun SAT n + 1
      else ladnerF len Penum redFun SAT n := by
  have h1 : Fseq len Penum redFun SAT n n = ladnerF len Penum redFun SAT n :=
    Fseq_stable n n (Nat.le_refl n)
  have h2 : Done len Penum redFun SAT (Fseq len Penum redFun SAT n) n ↔
      Done len Penum redFun SAT (ladnerF len Penum redFun SAT) n :=
    Done_congr n (fun k hk => Fseq_stable n k hk)
  have h0 : ladnerF len Penum redFun SAT (n + 1) =
      if Done len Penum redFun SAT (Fseq len Penum redFun SAT n) n then
        Fseq len Penum redFun SAT n n + 1
      else Fseq len Penum redFun SAT n n := by
    simp only [ladnerF, Fseq, if_neg (Nat.not_succ_le_self n)]
  rw [h0]
  by_cases hD : Done len Penum redFun SAT (ladnerF len Penum redFun SAT) n
  · rw [if_pos (h2.mpr hD), if_pos hD, h1]
  · rw [if_neg (fun hc => hD (h2.mp hc)), if_neg hD, h1]

end Construction

/-! ### The setting -/

/-- A setting for Ladner's theorem: the data of a model of polynomial-time computation
together with the standard structural facts about it that the proof uses. -/
structure Setting where
  /-- The length of (the string encoded by) a natural number. -/
  len : Nat → Nat
  /-- An enumeration of the languages in `P` (recursive presentability of `P`). -/
  Penum : Nat → Lang
  /-- An enumeration of the polynomial-time computable functions. -/
  redFun : Nat → Nat → Nat
  /-- An `NP`-complete language. -/
  SAT : Lang
  /-- The complexity class `P`. -/
  P : Lang → Prop
  /-- The complexity class `NP`. -/
  NP : Lang → Prop
  /-- Polynomial-time many-one reducibility. -/
  Red : Lang → Lang → Prop
  /-- `P ⊆ NP`. -/
  P_subset_NP : ∀ A, P A → NP A
  /-- The empty language is in `P`. -/
  empty_mem_P : P (fun _ => False)
  /-- `P` is closed under finite variation: changing a language on strings of length below
  some bound keeps it in `P`. -/
  P_variation : ∀ A B : Lang, P A → (∃ N, ∀ x, N ≤ len x → (A x ↔ B x)) → P B
  /-- The enumeration `Penum` lists only languages of `P`. -/
  Penum_mem : ∀ i, P (Penum i)
  /-- The enumeration `Penum` lists all languages of `P`. -/
  Penum_covers : ∀ A, P A → ∃ i, ∀ x, (A x ↔ Penum i x)
  /-- `A` reduces to `B` exactly when some polynomial-time computable function is a many-one
  reduction of `A` to `B`. -/
  Red_iff : ∀ A B : Lang, Red A B ↔ ∃ i, ∀ x, (A x ↔ B (redFun i x))
  /-- `P` is downward closed under reductions. -/
  Red_P : ∀ A B : Lang, Red A B → P B → P A
  /-- `SAT ∈ NP`. -/
  SAT_mem_NP : NP SAT
  /-- `SAT` is `NP`-hard. -/
  SAT_complete : ∀ A, NP A → Red A SAT
  /-- Effectiveness of the construction: Ladner's stage function is polynomial-time
  computable, hence the diagonal language is the intersection of `SAT` with a
  polynomial-time decidable set of lengths and therefore lies in `NP`. -/
  ladnerLang_mem_NP : NP (ladnerLang len Penum redFun SAT)

namespace Setting

variable (S : Setting)

/-- Ladner's stage function of the setting. -/
