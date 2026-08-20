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

theorem f_unbounded (hPNP : S.P ≠ S.NP) : ∀ c, ∃ n, c ≤ S.f n := by
  classical
  intro c
  by_cases hcon : ∃ n, c ≤ S.f n
  · exact hcon
  · exfalso
    have hb : ∀ n, S.f n ≤ c := by
      intro n
      by_cases h : S.f n ≤ c
      · exact h
      · exact absurd ⟨n, by omega⟩ hcon
    have ⟨N, hN⟩ := eventually_const S.f S.f_mono c hb
    -- from `N` on, the stage function is constant, so no requirement is ever met again
    have hnd : ∀ n, N ≤ n → ¬ S.SDone n := by
      intro n hn hd
      have h1 : S.f (n + 1) = S.f n + 1 := S.f_done hd
      have h2 : S.f (n + 1) = S.f N := hN (n + 1) (Nat.le_trans hn (Nat.le_succ n))
      have h3 : S.f n = S.f N := hN n hn
      omega
    by_cases hpar : S.f N % 2 = 0
    · -- even stage `2 * i`: the constructed language equals `Penum i ∈ P`, and it differs
      -- from `SAT` only on short strings, so `SAT ∈ P`
      have hfN : S.f N = 2 * (S.f N / 2) := by omega
      have hi : ∀ x, S.L x ↔ S.Penum (S.f N / 2) x := by
        intro x
        have hn1 : N ≤ max N (S.len x) := Nat.le_max_left _ _
        have hlen : S.len x ≤ max N (S.len x) := Nat.le_max_right _ _
        have hfn : S.f (max N (S.len x)) = S.f N := hN _ hn1
        have hnot := hnd _ hn1
        have heven : S.f (max N (S.len x)) % 2 = 0 := by rw [hfn]; exact hpar
        have hdiv : S.f (max N (S.len x)) / 2 = S.f N / 2 := by rw [hfn]
        have hkey : ¬ (S.L x ↔ ¬ S.Penum (S.f N / 2) x) := by
          intro hc
          refine hnot (Or.inl ⟨heven, x, hlen, ?_⟩)
          rw [hdiv]
          exact hc
        exact iff_of_not_iff_not _ _ hkey
      have hLP : S.P S.L :=
        S.P_variation (S.Penum (S.f N / 2)) S.L (S.Penum_mem _) ⟨0, fun x _ => (hi x).symm⟩
      have hSAT : S.P S.SAT := by
        refine S.P_variation S.L S.SAT hLP ⟨N, fun x hx => ?_⟩
        have hfx : S.f (S.len x) = S.f N := hN _ hx
        constructor
        · intro h; exact ((S.mem_L_iff x).mp h).1
        · intro h; exact (S.mem_L_iff x).mpr ⟨h, by rw [hfx]; exact hpar⟩
      exact S.SAT_not_mem_P hPNP hSAT
    · -- odd stage `2 * i + 1`: the constructed language is finite, hence in `P`, but `SAT`
      -- reduces to it
      have hodd : S.f N % 2 = 1 := by omega
      have hshort : ∀ x, S.L x → S.len x < N := by
        intro x hx
        by_cases h : S.len x < N
        · exact h
        · exfalso
          have hfx : S.f (S.len x) = S.f N := hN _ (by omega)
          have := ((S.mem_L_iff x).mp hx).2
          rw [hfx] at this
          omega
      have hLP : S.P S.L := by
        refine S.P_variation (fun _ => False) S.L S.empty_mem_P ⟨N, fun x hx => ?_⟩
        constructor
        · intro h; exact absurd h (fun h => h)
        · intro h; exact absurd (hshort x h) (by omega)
      have hred : ∀ x, S.SAT x ↔ S.L (S.redFun (S.f N / 2) x) := by
        intro x
        have hn1 : N ≤ max (max N (S.len x)) (S.len (S.redFun (S.f N / 2) x)) :=
          Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
        have hlen : S.len x ≤ max (max N (S.len x)) (S.len (S.redFun (S.f N / 2) x)) :=
          Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
        have hlen2 : S.len (S.redFun (S.f N / 2) x)
            ≤ max (max N (S.len x)) (S.len (S.redFun (S.f N / 2) x)) := Nat.le_max_right _ _
        have hfn : S.f (max (max N (S.len x)) (S.len (S.redFun (S.f N / 2) x))) = S.f N :=
          hN _ hn1
        have hnot := hnd _ hn1
        have hoddn : S.f (max (max N (S.len x)) (S.len (S.redFun (S.f N / 2) x))) % 2 = 1 := by
          rw [hfn]; exact hodd
        have hdiv : S.f (max (max N (S.len x)) (S.len (S.redFun (S.f N / 2) x))) / 2
            = S.f N / 2 := by rw [hfn]
        by_cases hc : S.SAT x ↔ S.L (S.redFun (S.f N / 2) x)
        · exact hc
        · exfalso
          refine hnot (Or.inr ⟨hoddn, x, hlen, ?_, ?_⟩)
          · rw [hdiv]; exact hlen2
          · rw [hdiv]; exact hc
      have : S.Red S.SAT S.L := (S.Red_iff S.SAT S.L).mpr ⟨S.f N / 2, hred⟩
      exact S.SAT_not_mem_P hPNP (S.Red_P S.SAT S.L this hLP)

/-- Every stage is reached, and its diagonalisation requirement is eventually met. -/
