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
theorem exists_least (p : Nat → Prop) (h : ∃ n, p n) :
    ∃ n, p n ∧ ∀ m, m < n → ¬ p m := by
  classical
  have key : ∀ n, p n → ∃ k, p k ∧ ∀ m, m < k → ¬ p m := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
        intro hpn
        by_cases hex : ∃ m, m < n ∧ p m
        · have ⟨m, hm, hpm⟩ := hex
          exact ih m hm hpm
        · exact ⟨n, hpn, fun m hm hpm => hex ⟨m, hm, hpm⟩⟩
  have ⟨n, hn⟩ := h
  exact key n hn

/-- A bounded monotone sequence of naturals is eventually constant. -/
theorem eventually_const (g : Nat → Nat) (hmono : ∀ m n, m ≤ n → g m ≤ g n) :
    ∀ c, (∀ n, g n ≤ c) → ∃ N, ∀ n, N ≤ n → g n = g N := by
  classical
  intro c
  induction c with
  | zero =>
      intro hb
      exact ⟨0, fun n _ => by have := hb n; have := hb 0; omega⟩
  | succ c ih =>
      intro hb
      by_cases hex : ∃ N, g N = c + 1
      · have ⟨N, hN⟩ := hex
        refine ⟨N, fun n hn => ?_⟩
        have h1 := hmono N n hn
        have h2 := hb n
        omega
      · refine ih (fun n => ?_)
        have h1 := hb n
        have h2 : g n ≠ c + 1 := fun hc => hex ⟨n, hc⟩
        omega

/-- If `A ↔ ¬ B` fails then `A ↔ B`. -/
theorem iff_of_not_iff_not (A B : Prop) (h : ¬ (A ↔ ¬ B)) : A ↔ B := by
  classical
  by_cases hb : B
  · refine ⟨fun _ => hb, fun _ => ?_⟩
    by_cases ha : A
    · exact ha
    · exact absurd (Iff.intro (fun x => absurd x ha) (fun x => absurd hb x)) h
  · exact ⟨fun ha => absurd (Iff.intro (fun _ => hb) (fun _ => ha)) h, fun x => absurd x hb⟩

/-! ### Ladner's delayed diagonalisation -/

section Construction

variable (len : Nat → Nat) (Penum : Nat → Lang) (redFun : Nat → Nat → Nat) (SAT : Lang)

/-- The language `SAT ∩ {x | g (len x) is even}`, where `g` is a "stage function". -/
def slice (g : Nat → Nat) : Lang := fun x => SAT x ∧ g (len x) % 2 = 0

/-- The diagonalisation requirement of the current stage `g n` is met by length `n`.

If the current stage `g n = 2 * i` is even we look for a string of length at most `n` on which
the `i`-th language of `P` differs from the constructed language; if `g n = 2 * i + 1` is odd
we look for a string of length at most `n` witnessing that the `i`-th polynomial-time function
is not a many-one reduction of `SAT` to the constructed language. -/
def Done (g : Nat → Nat) (n : Nat) : Prop :=
  (g n % 2 = 0 ∧ ∃ x, len x ≤ n ∧ (slice len SAT g x ↔ ¬ Penum (g n / 2) x)) ∨
  (g n % 2 = 1 ∧ ∃ x, len x ≤ n ∧ len (redFun (g n / 2) x) ≤ n ∧
      ¬ (SAT x ↔ slice len SAT g (redFun (g n / 2) x)))

open Classical in
/-- Auxiliary recursion: `Fseq n` agrees with Ladner's stage function on all arguments `≤ n`. -/
noncomputable def Fseq : Nat → Nat → Nat
  | 0 => fun _ => 0
  | (n + 1) => fun k =>
      if k ≤ n then Fseq n k
      else if Done len Penum redFun SAT (Fseq n) n then Fseq n n + 1 else Fseq n n

/-- Ladner's stage function: it starts at `0` and increases by one exactly at those lengths at
which the diagonalisation requirement of the current stage has just been met. -/
noncomputable def ladnerF (n : Nat) : Nat := Fseq len Penum redFun SAT n n

/-- The language constructed by Ladner's delayed diagonalisation. -/
def ladnerLang : Lang := slice len SAT (ladnerF len Penum redFun SAT)

variable {len Penum redFun SAT}

theorem Fseq_stable : ∀ (n k : Nat), k ≤ n →
    Fseq len Penum redFun SAT n k = ladnerF len Penum redFun SAT k := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      rfl
  | succ n ih =>
      intro k hk
      by_cases h : k ≤ n
      · have e : Fseq len Penum redFun SAT (n + 1) k = Fseq len Penum redFun SAT n k := by
          simp only [Fseq, if_pos h]
        rw [e, ih k h]
      · have hkeq : k = n + 1 := by omega
        subst hkeq
        rfl

theorem slice_congr {g h : Nat → Nat} {x : Nat} (hx : g (len x) = h (len x)) :
    slice len SAT g x ↔ slice len SAT h x := by
  simp only [slice, hx]

theorem Done_congr {g h : Nat → Nat} (n : Nat) (H : ∀ k, k ≤ n → g k = h k) :
    Done len Penum redFun SAT g n ↔ Done len Penum redFun SAT h n := by
  have hn : g n = h n := H n (Nat.le_refl n)
  unfold Done
  rw [hn]
  constructor
  · intro hd
    cases hd with
    | inl hd =>
        have ⟨he, x, hx, hxs⟩ := hd
        exact Or.inl ⟨he, x, hx, Iff.trans (slice_congr (H _ hx)).symm hxs⟩
    | inr hd =>
        have ⟨he, x, hx, hx2, hxs⟩ := hd
        exact Or.inr ⟨he, x, hx, hx2,
          fun hc => hxs (Iff.trans hc (slice_congr (H _ hx2)).symm)⟩
  · intro hd
    cases hd with
    | inl hd =>
        have ⟨he, x, hx, hxs⟩ := hd
        exact Or.inl ⟨he, x, hx, Iff.trans (slice_congr (H _ hx)) hxs⟩
    | inr hd =>
        have ⟨he, x, hx, hx2, hxs⟩ := hd
        exact Or.inr ⟨he, x, hx, hx2,
          fun hc => hxs (Iff.trans hc (slice_congr (H _ hx2)))⟩

theorem ladnerF_zero : ladnerF len Penum redFun SAT 0 = 0 := rfl

open Classical in
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
noncomputable def f : Nat → Nat := ladnerF S.len S.Penum S.redFun S.SAT

/-- The language constructed by Ladner's delayed diagonalisation in the setting. -/
def L : Lang := ladnerLang S.len S.Penum S.redFun S.SAT

/-- The diagonalisation requirement of the current stage is met by length `n`. -/
def SDone (n : Nat) : Prop := Done S.len S.Penum S.redFun S.SAT S.f n

theorem mem_L_iff (x : Nat) : S.L x ↔ (S.SAT x ∧ S.f (S.len x) % 2 = 0) := Iff.rfl

theorem f_zero : S.f 0 = 0 := rfl

open Classical in
theorem f_succ (n : Nat) : S.f (n + 1) = if S.SDone n then S.f n + 1 else S.f n :=
  ladnerF_succ n

theorem f_done {n : Nat} (h : S.SDone n) : S.f (n + 1) = S.f n + 1 := by
  classical
  rw [f_succ, if_pos h]

theorem f_not_done {n : Nat} (h : ¬ S.SDone n) : S.f (n + 1) = S.f n := by
  classical
  rw [f_succ, if_neg h]

theorem f_le_succ (n : Nat) : S.f n ≤ S.f (n + 1) := by
  classical
  rw [f_succ]; split <;> omega

theorem f_succ_le (n : Nat) : S.f (n + 1) ≤ S.f n + 1 := by
  classical
  rw [f_succ]; split <;> omega

theorem f_mono : ∀ m n, m ≤ n → S.f m ≤ S.f n := by
  intro m n h
  induction n with
  | zero =>
      have : m = 0 := Nat.le_zero.mp h
      subst this
      exact Nat.le_refl _
  | succ n ih =>
      by_cases hm : m ≤ n
      · exact Nat.le_trans (ih hm) (S.f_le_succ n)
      · have : m = n + 1 := by omega
        subst this
        exact Nat.le_refl _

theorem SAT_not_mem_P (hPNP : S.P ≠ S.NP) : ¬ S.P S.SAT := by
  intro hs
  exact hPNP (funext (fun A => propext
    ⟨fun h => S.P_subset_NP A h, fun h => S.Red_P A S.SAT (S.SAT_complete A h) hs⟩))

/-- The heart of Ladner's argument: the stage function is unbounded, i.e. every
diagonalisation requirement is eventually met. -/
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
def decB : Nat → Nat → Bool
  | i, 0 => i % 2 == 1
  | i, x + 1 => decB (i / 2) x

theorem decB_eq_false : ∀ (x i : Nat), i < 2 ^ x → decB i x = false := by
  intro x
  induction x with
  | zero =>
      intro i hi
      have : i = 0 := by simpa using hi
      subst this
      rfl
  | succ x ih =>
      intro i hi
      have h2 : (2 : Nat) ^ (x + 1) = 2 * 2 ^ x := by
        rw [Nat.pow_succ]; omega
      have hlt : i / 2 < 2 ^ x := by omega
      show decB (i / 2) x = false
      exact ih _ hlt

theorem decB_eq_false_of_le {i x : Nat} (h : i ≤ x) : decB i x = false := by
  refine decB_eq_false x i (Nat.lt_of_lt_of_le Nat.lt_two_pow_self ?_)
  exact Nat.pow_le_pow_right (by omega) h

/-- Every language with bounded support is decoded from some natural number. -/
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
def toyLen : Nat → Nat := fun x => x

/-- The enumeration of the "easy" languages of the model: the languages with bounded
support. -/
def toyPenum (i : Nat) : Lang := fun x => decB i x = true

/-- The enumeration of the "reductions" of the model. -/
def toyRedFun (i x : Nat) : Nat := if decB i x then 0 else x + 1

/-- The "complete" language of the model. -/
def toySAT : Lang := fun x => x = 0

/-- The class `P` (= `NP`) of the model: the languages with bounded support. -/
def toyP : Lang → Prop := fun A => ∃ N, ∀ x, N ≤ x → ¬ A x

/-- Reducibility in the model. -/
def toyRed (A B : Lang) : Prop := ∃ i, ∀ x, (A x ↔ B (toyRedFun i x))

/-- A model of `CS.Setting`; it witnesses that the assumptions collected there are
consistent.  (It is degenerate: in it `P = NP`.) -/
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
theorem toySetting_P_eq_NP : toySetting.P = toySetting.NP := rfl

end Consistency

end CS

