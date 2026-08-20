import RequestProject.Main

/-!
# A consistency witness for `CS.LadnerSetup`

`CS.ladner` is stated relative to the abstract axiomatisation `CS.LadnerSetup`.
To rule out the possibility that this package of hypotheses is contradictory
(in which case the theorem would be vacuous), we build an explicit model of it.

The model takes both classes to be the class `FC` of languages that are *finite
variations of a constant language* (equivalently: finite or cofinite sets), which
is enumerable, closed under finite variation, contains the finite languages and is
closed downwards under the reductions of the model; `SAT` is taken to be the
cofinite language `{x | x ≠ 0}`, which is complete for `FC` under those
reductions, and the clock is taken to be constant (so all four clock-semantics
fields hold trivially or vacuously).

Of course `P = NP` holds in this model, so `CS.ladner` says nothing about it; the
point of the construction is only that the hypotheses of `CS.LadnerSetup` are
jointly satisfiable, hence consistent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CS

namespace FinCofinModel

attribute [local instance] Classical.propDecidable

/-! ### Binary digits -/

/-- `bit n x` says that the `x`-th binary digit of `n` is `1`. -/
def bit (n x : Nat) : Prop := n / 2 ^ x % 2 = 1

theorem bit_zero_iff (c m : Nat) (hc : c < 2) : bit (c + 2 * m) 0 ↔ c = 1 := by
  unfold bit
  rw [Nat.pow_zero, Nat.div_one]
  omega

theorem bit_succ_iff (c m x : Nat) (hc : c < 2) : bit (c + 2 * m) (x + 1) ↔ bit m x := by
  unfold bit
  have hp : (2 : Nat) ^ (x + 1) = 2 * 2 ^ x := by
    rw [Nat.pow_succ]
    omega
  have hhalf : (c + 2 * m) / 2 = m := by omega
  rw [hp, ← Nat.div_div_eq_div_mul, hhalf]

theorem bit_of_lt (n x : Nat) (h : n < 2 ^ x) : ¬ bit n x := by
  unfold bit
  rw [Nat.div_eq_of_lt h]
  omega

/-- `bit n x` is false as soon as `x` is at least `n`. -/
theorem bit_high (n x : Nat) (h : n ≤ x) : ¬ bit n x := by
  refine bit_of_lt n x ?_
  have h1 : n < 2 ^ n := Nat.lt_two_pow_self
  have h2 : (2 : Nat) ^ n ≤ 2 ^ x := Nat.pow_le_pow_right (by omega) h
  omega

/-! ### Encoding a finite pattern of digits -/

/-- The natural number whose `x`-th binary digit, for `x < len`, records whether
`d (start + x)` holds. -/
noncomputable def encFrom (d : Nat → Prop) (start : Nat) : Nat → Nat
  | 0 => 0
  | len + 1 => (if d start then 1 else 0) + 2 * encFrom d (start + 1) len

theorem encFrom_lt_two (d : Nat → Prop) (start : Nat) :
    (if d start then 1 else 0) < 2 := by
  by_cases hd : d start
  · rw [if_pos hd]; omega
  · rw [if_neg hd]; omega

theorem encFrom_bit (d : Nat → Prop) :
    ∀ (len start x : Nat), x < len → (bit (encFrom d start len) x ↔ d (start + x)) := by
  intro len
  induction len with
  | zero =>
      intro start x hx
      exact absurd hx (Nat.not_lt_zero x)
  | succ len ih =>
      intro start x hx
      have hc := encFrom_lt_two d start
      cases x with
      | zero =>
          show bit ((if d start then 1 else 0) + 2 * encFrom d (start + 1) len) 0 ↔ _
          rw [bit_zero_iff _ _ hc]
          have hzero : start + 0 = start := by omega
          rw [hzero]
          by_cases hd : d start
          · rw [if_pos hd]
            exact ⟨fun _ => hd, fun _ => rfl⟩
          · rw [if_neg hd]
            exact ⟨fun hcc => absurd hcc (by omega), fun hcc => absurd hcc hd⟩
      | succ x =>
          show bit ((if d start then 1 else 0) + 2 * encFrom d (start + 1) len) (x + 1) ↔ _
          rw [bit_succ_iff _ _ _ hc, ih (start + 1) x (by omega)]
          have hs : start + 1 + x = start + (x + 1) := by omega
          rw [hs]

theorem encFrom_bit_high (d : Nat → Prop) :
    ∀ (len start x : Nat), len ≤ x → ¬ bit (encFrom d start len) x := by
  intro len
  induction len with
  | zero =>
      intro start x _
      show ¬ bit 0 x
      exact bit_high 0 x (Nat.zero_le _)
  | succ len ih =>
      intro start x hx
      have hc := encFrom_lt_two d start
      cases x with
      | zero => exact absurd hx (by omega)
      | succ x =>
          show ¬ bit ((if d start then 1 else 0) + 2 * encFrom d (start + 1) len) (x + 1)
          rw [bit_succ_iff _ _ _ hc]
          exact ih (start + 1) x (by omega)

/-! ### The class of finite variations of constant languages -/

/-- `FC A` says that `A` agrees with a fixed truth value on all large inputs, i.e.
`A` is finite or cofinite. -/
def FC (A : Lang) : Prop := ∃ (N : Nat) (b : Prop), ∀ x : Nat, N ≤ x → (A x ↔ b)

theorem FC_congr {A B : Lang} (h : ∀ x, (A x ↔ B x)) (hA : FC A) : FC B := by
  obtain ⟨N, b, hb⟩ := hA
  exact ⟨N, b, fun x hx => Iff.trans (h x).symm (hb x hx)⟩

/-- The language decoded from `n`: the constant `n % 2 = 1`, flipped at the binary
digit positions of `n / 2`. -/
noncomputable def dec (n : Nat) : Lang :=
  fun x => if n % 2 = 1 then ¬ bit (n / 2) x else bit (n / 2) x

theorem dec_FC (n : Nat) : FC (dec n) := by
  refine ⟨n, (n % 2 = 1), fun x hx => ?_⟩
  have hb : ¬ bit (n / 2) x := bit_high (n / 2) x (by omega)
  unfold dec
  by_cases h : n % 2 = 1
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => hb⟩
  · rw [if_neg h]
    exact ⟨fun hc => absurd hc hb, fun hc => absurd hc h⟩

/-- Every finite variation of a constant language is decoded from some natural number. -/
theorem FC_exists_code {A : Lang} (hA : FC A) : ∃ n : Nat, ∀ x, (A x ↔ dec n x) := by
  obtain ⟨N, b, hb⟩ := hA
  by_cases hbb : b
  · -- the eventual value is `True`; encode the positions where `A` fails
    refine ⟨1 + 2 * encFrom (fun y => ¬ A y) 0 N, fun x => ?_⟩
    have hmod : (1 + 2 * encFrom (fun y => ¬ A y) 0 N) % 2 = 1 := by omega
    have hdiv : (1 + 2 * encFrom (fun y => ¬ A y) 0 N) / 2
        = encFrom (fun y => ¬ A y) 0 N := by omega
    unfold dec
    rw [hmod, hdiv, if_pos rfl]
    by_cases hx : x < N
    · have hbit := encFrom_bit (fun y => ¬ A y) N 0 x hx
      have hzero : 0 + x = x := by omega
      rw [hzero] at hbit
      rw [hbit]
      exact ⟨fun h hn => hn h, fun h => Classical.byContradiction h⟩
    · have hbit := encFrom_bit_high (fun y => ¬ A y) N 0 x (by omega)
      have hAx : A x := (hb x (by omega)).mpr hbb
      exact ⟨fun _ => hbit, fun _ => hAx⟩
  · -- the eventual value is `False`; encode the positions where `A` holds
    refine ⟨2 * encFrom (fun y => A y) 0 N, fun x => ?_⟩
    have hmod : (2 * encFrom (fun y => A y) 0 N) % 2 = 0 := by omega
    have hdiv : (2 * encFrom (fun y => A y) 0 N) / 2 = encFrom (fun y => A y) 0 N := by omega
    unfold dec
    rw [hmod, hdiv, if_neg (by omega : ¬ (0 = 1))]
    by_cases hx : x < N
    · have hbit := encFrom_bit (fun y => A y) N 0 x hx
      have hzero : 0 + x = x := by omega
      rw [hzero] at hbit
      exact hbit.symm
    · have hbit := encFrom_bit_high (fun y => A y) N 0 x (by omega)
      have hAx : ¬ A x := fun hc => hbb ((hb x (by omega)).mp hc)
      exact ⟨fun hc => absurd hc hAx, fun hc => absurd hc hbit⟩

/-! ### The model -/

/-- The complete language of the model. -/
def satL : Lang := fun x => x ≠ 0

theorem satL_FC : FC satL :=
  ⟨1, True, fun x hx => ⟨fun _ => trivial, fun _ => by unfold satL; omega⟩⟩

/-- The enumeration of the class: index `0` gives `satL`, every other index decodes
a binary code. -/
noncomputable def pEnumM (n : Nat) : Lang := if n = 0 then satL else dec (n - 1)

theorem pEnumM_FC (n : Nat) : FC (pEnumM n) := by
  unfold pEnumM
  by_cases h : n = 0
  · rw [if_pos h]; exact satL_FC
  · rw [if_neg h]; exact dec_FC (n - 1)

theorem pEnumM_succ (n x : Nat) : pEnumM (n + 1) x ↔ dec n x := by
  unfold pEnumM
  rw [if_neg (by omega : ¬ (n + 1 = 0))]
  exact Iff.rfl

/-- The reductions of the model: the `{0,1}`-valued eventually constant functions. -/
noncomputable def redEnumM (i x : Nat) : Nat := if dec i x then 1 else 0

theorem redEnumM_spec (i x : Nat) : satL (redEnumM i x) ↔ dec i x := by
  unfold satL redEnumM
  by_cases h : dec i x
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => by omega⟩
  · rw [if_neg h]
    exact ⟨fun hne => absurd rfl hne, fun hc => absurd hc h⟩

/-- A model of `CS.LadnerSetup`, in which both complexity classes are the class of
finite variations of constant languages. -/
noncomputable def model : LadnerSetup where
  P := FC
  NP := FC
  SAT := satL
  pEnum := pEnumM
  redEnum := redEnumM
  clock := fun _ => 0
  P_iff_range := by
    intro A
    constructor
    · intro hA
      obtain ⟨n, hn⟩ := FC_exists_code hA
      exact ⟨n + 1, fun x => Iff.trans (hn x) (pEnumM_succ n x).symm⟩
    · intro h
      obtain ⟨i, hi⟩ := h
      exact FC_congr (fun x => (hi x).symm) (pEnumM_FC i)
  P_subset_NP := fun _ h => h
  SAT_mem_NP := satL_FC
  SAT_hard := by
    intro A hA
    obtain ⟨n, hn⟩ := FC_exists_code hA
    exact ⟨n, fun x => Iff.trans (hn x) (redEnumM_spec n x).symm⟩
  P_reduce := by
    intro A B h _
    obtain ⟨i, hi⟩ := h
    obtain ⟨N, b, hb⟩ := dec_FC i
    by_cases hbb : b
    · refine ⟨N, B 1, fun x hx => ?_⟩
      have hd : dec i x := (hb x hx).mpr hbb
      have hval : redEnumM i x = 1 := by unfold redEnumM; rw [if_pos hd]
      rw [hi x, hval]
    · refine ⟨N, B 0, fun x hx => ?_⟩
      have hd : ¬ dec i x := fun hc => hbb ((hb x hx).mp hc)
      have hval : redEnumM i x = 0 := by unfold redEnumM; rw [if_neg hd]
      rw [hi x, hval]
  P_finVar := by
    intro A B hA h
    obtain ⟨N₁, b, hb⟩ := hA
    obtain ⟨N₂, hN₂⟩ := h
    exact ⟨N₁ + N₂, b, fun x hx => Iff.trans (hN₂ x (by omega)).symm (hb x (by omega))⟩
  P_finite := by
    intro A h
    obtain ⟨N, hN⟩ := h
    exact ⟨N, False, fun x hx => ⟨fun hAx => hN x hx hAx, fun hf => hf.elim⟩⟩
  NP_inter_P := by
    intro A B hA hB
    obtain ⟨N₁, b₁, hb₁⟩ := hA
    obtain ⟨N₂, b₂, hb₂⟩ := hB
    refine ⟨N₁ + N₂, b₁ ∧ b₂, fun x hx => ?_⟩
    have h1 := hb₁ x (by omega)
    have h2 := hb₂ x (by omega)
    exact ⟨fun h => ⟨h1.1 h.1, h2.1 h.2⟩, fun h => ⟨h1.2 h.1, h2.2 h.2⟩⟩
  clock_mono := fun _ _ _ => Nat.le_refl 0
  gap_mem_P := ⟨0, True, fun _ _ => ⟨fun _ => trivial, fun _ => rfl⟩⟩
  clock_stuck_even := by
    intro i N h x _
    have h0 : (0 : Nat) = 2 * i := h N (Nat.le_refl N)
    have hi : i = 0 := by omega
    subst hi
    unfold pEnumM
    rw [if_pos rfl]
  clock_stuck_odd := by
    intro i N h
    have h0 : (0 : Nat) = 2 * i + 1 := h N (Nat.le_refl N)
    exact absurd h0 (by omega)
  clock_pass_even := by
    intro i h
    obtain ⟨x, hx⟩ := h
    exact absurd hx (Nat.not_lt_zero _)
  clock_pass_odd := by
    intro i h
    obtain ⟨x, hx⟩ := h
    exact absurd hx (Nat.not_lt_zero _)

end FinCofinModel

/-- The hypotheses packaged in `CS.LadnerSetup` are consistent: they have a model.
(In that model `P = NP`, so `CS.ladner` applies to it only vacuously; the purpose of
the model is exactly to show that the axiomatisation is satisfiable.) -/
theorem ladnerSetup_nonempty : Nonempty LadnerSetup := ⟨FinCofinModel.model⟩

end CS

/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This file is deliberately import-free: Lean does not allow an `import` command
-- after the header comment above, and the whole development below is elementary
-- (only natural-number arithmetic and propositional logic are needed).
-- `RequestProject/Model.lean` complements it with an explicit model of the
-- axiomatisation `CS.LadnerSetup` used here, certifying that the hypotheses are
-- consistent.

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CS

/-- A *language* is a set of natural numbers (strings encoded as naturals),
represented as a predicate on `Nat`. -/
abbrev Lang := Nat → Prop

/--
An abstract axiomatisation of the ingredients of Ladner's theorem.

The complexity-theoretic input is packaged as explicit data together with
hypotheses.  Every hypothesis field is a statement that is a standard fact about
the real classes `P`, `NP`, polynomial-time many-one reducibility and `SAT`.

* `pEnum` is a *recursive presentation* of `P`: every polynomial-time language
  occurs in the enumeration, and nothing else does.
* `redEnum` enumerates the polynomial-time computable functions; a
  polynomial-time many-one reduction is by definition given by one of them
  (see `LadnerSetup.Reduces`).
* `clock` is Ladner's *clocked* stage function `f`.  Ladner's construction
  produces a polynomial-time computable, nondecreasing `f : Nat → Nat` whose
  associated gap set `{x | f x` is even `}` is in `P`, and which, on input `x`,
  runs a search bounded by `x` for a witness defeating the requirement of the
  current stage.  The four fields `clock_stuck_even`, `clock_stuck_odd`,
  `clock_pass_even`, `clock_pass_odd` record exactly the semantics of that
  search: if the clock gets stuck at stage `k` for ever, then the requirement of
  stage `k` has no witness at all, and if the clock passes stage `k`, then a
  witness for the requirement of stage `k` was found.

  Even stages diagonalise against membership in `P` (against `pEnum i`), odd
  stages diagonalise against reductions from `SAT` (against `redEnum i`).

No field asserts that the clock is unbounded.  That the clock *must* be unbounded
when `P ≠ NP` is the mathematical content of Ladner's argument, and it is proved
below as `LadnerSetup.clock_unbounded`.
-/
structure LadnerSetup where
  /-- The class of polynomial-time decidable languages. -/
  P : Lang → Prop
  /-- The class of languages decidable in nondeterministic polynomial time. -/
  NP : Lang → Prop
  /-- An `NP`-complete language. -/
  SAT : Lang
  /-- A recursive presentation (enumeration) of `P`. -/
  pEnum : Nat → Lang
  /-- An enumeration of the polynomial-time computable functions. -/
  redEnum : Nat → Nat → Nat
  /-- Ladner's clocked stage function. -/
  clock : Nat → Nat
  /-- `pEnum` enumerates exactly the languages of `P`. -/
  P_iff_range : ∀ A : Lang, P A ↔ ∃ i : Nat, ∀ x : Nat, (A x ↔ pEnum i x)
  /-- Deterministic polynomial time is contained in nondeterministic polynomial time. -/
  P_subset_NP : ∀ A : Lang, P A → NP A
  /-- `SAT` belongs to `NP`. -/
  SAT_mem_NP : NP SAT
  /-- `SAT` is `NP`-hard. -/
  SAT_hard : ∀ A : Lang, NP A → ∃ i : Nat, ∀ x : Nat, (A x ↔ SAT (redEnum i x))
  /-- `P` is closed downwards under polynomial-time many-one reducibility. -/
  P_reduce : ∀ A B : Lang, (∃ i : Nat, ∀ x : Nat, (A x ↔ B (redEnum i x))) → P B → P A
  /-- `P` is closed under finite variation. -/
  P_finVar : ∀ A B : Lang, P A → (∃ N : Nat, ∀ x : Nat, N ≤ x → (A x ↔ B x)) → P B
  /-- Finite (that is, bounded) languages are polynomial-time decidable. -/
  P_finite : ∀ A : Lang, (∃ N : Nat, ∀ x : Nat, N ≤ x → ¬ A x) → P A
  /-- `NP` is closed under intersection with a polynomial-time language. -/
  NP_inter_P : ∀ A B : Lang, NP A → P B → NP (fun x => A x ∧ B x)
  /-- The clock is nondecreasing. -/
  clock_mono : ∀ a b : Nat, a ≤ b → clock a ≤ clock b
  /-- The gap set of the clock is polynomial-time decidable. -/
  gap_mem_P : P (fun x => clock x % 2 = 0)
  /-- If the clock is stuck at the even stage `2 * i` from `N` on, then the search for
  a point where `pEnum i` differs from `SAT` never succeeded, i.e. there is no such
  point beyond `N`. -/
  clock_stuck_even : ∀ i N : Nat, (∀ x : Nat, N ≤ x → clock x = 2 * i) →
      ∀ x : Nat, N ≤ x → (SAT x ↔ pEnum i x)
  /-- If the clock is stuck at the odd stage `2 * i + 1` from `N` on, then the search
  for a point where the reduction `redEnum i` from `SAT` to Ladner's language fails
  never succeeded, i.e. that reduction is correct. -/
  clock_stuck_odd : ∀ i N : Nat, (∀ x : Nat, N ≤ x → clock x = 2 * i + 1) →
      ∀ x : Nat, (SAT x ↔ (SAT (redEnum i x) ∧ clock (redEnum i x) % 2 = 0))
  /-- If the clock passes the even stage `2 * i`, then a point of the gap set at which
  `pEnum i` differs from `SAT` was found. -/
  clock_pass_even : ∀ i : Nat, (∃ x : Nat, 2 * i < clock x) →
      ∃ x : Nat, clock x % 2 = 0 ∧ (SAT x ↔ ¬ pEnum i x)
  /-- If the clock passes the odd stage `2 * i + 1`, then a point at which the
  reduction `redEnum i` from `SAT` to Ladner's language fails was found. -/
  clock_pass_odd : ∀ i : Nat, (∃ x : Nat, 2 * i + 1 < clock x) →
      ∃ x : Nat, ¬ (SAT x ↔ (SAT (redEnum i x) ∧ clock (redEnum i x) % 2 = 0))

namespace LadnerSetup

variable (S : LadnerSetup)

/-- Polynomial-time many-one reducibility: `A` reduces to `B` iff some
polynomial-time computable function `redEnum i` is a many-one reduction from
`A` to `B`. -/
def Reduces (A B : Lang) : Prop := ∃ i : Nat, ∀ x : Nat, (A x ↔ B (S.redEnum i x))

/-- `L` is `NP`-hard when every language of `NP` reduces to it. -/
def NPHard (L : Lang) : Prop := ∀ A : Lang, S.NP A → S.Reduces A L

/-- `L` is `NP`-intermediate: it lies in `NP`, is not in `P`, and is not `NP`-hard
(in particular, it is not `NP`-complete). -/
def NPIntermediate (L : Lang) : Prop := S.NP L ∧ ¬ S.P L ∧ ¬ S.NPHard L

/-- Ladner's language: `SAT` intersected with the gap set of the clock. -/
def ladnerLang : Lang := fun x => S.SAT x ∧ S.clock x % 2 = 0

/-- If `P ≠ NP`, then `SAT`, being `NP`-complete, is not in `P`. -/
theorem SAT_not_mem_P (hPNP : S.P ≠ S.NP) : ¬ S.P S.SAT := by
  intro hSAT
  apply hPNP
  funext A
  exact propext ⟨S.P_subset_NP A, fun hA => S.P_reduce A S.SAT (S.SAT_hard A hA) hSAT⟩

/-- A nondecreasing function `Nat → Nat` bounded by `n` is eventually constant. -/
theorem eventually_const_of_bounded :
    ∀ (n : Nat) (g : Nat → Nat), (∀ a b : Nat, a ≤ b → g a ≤ g b) → (∀ x : Nat, g x ≤ n) →
      ∃ c N : Nat, ∀ x : Nat, N ≤ x → g x = c := by
  intro n
  induction n with
  | zero =>
      intro g _ hb
      exact ⟨0, 0, fun x _ => Nat.le_antisymm (hb x) (Nat.zero_le _)⟩
  | succ n ih =>
      intro g hmono hb
      by_cases hconst : ∀ x : Nat, g x = g 0
      · exact ⟨g 0, 0, fun x _ => hconst x⟩
      · have hex : ∃ x : Nat, g x ≠ g 0 :=
          Classical.byContradiction fun hne =>
            hconst fun x => Classical.byContradiction fun hx => hne ⟨x, hx⟩
        obtain ⟨x₀, hx₀⟩ := hex
        have h0 : g 0 ≤ g x₀ := hmono 0 x₀ (Nat.zero_le _)
        have hpos : ∀ x : Nat, 1 ≤ g (x₀ + x) := by
          intro x
          have h1 : g x₀ ≤ g (x₀ + x) := hmono x₀ (x₀ + x) (Nat.le_add_right _ _)
          omega
        have hmono' : ∀ a b : Nat, a ≤ b → g (x₀ + a) - 1 ≤ g (x₀ + b) - 1 := by
          intro a b hab
          have h1 := hmono (x₀ + a) (x₀ + b) (Nat.add_le_add_left hab x₀)
          omega
        have hb' : ∀ x : Nat, g (x₀ + x) - 1 ≤ n := by
          intro x
          have h1 := hb (x₀ + x)
          have h2 := hpos x
          omega
        obtain ⟨c, N, hcN⟩ := ih (fun x => g (x₀ + x) - 1) hmono' hb'
        refine ⟨c + 1, x₀ + N, ?_⟩
        intro x hx
        have hle : N ≤ x - x₀ := by omega
        have h1 := hcN (x - x₀) hle
        have h2 := hpos (x - x₀)
        have hxx : x₀ + (x - x₀) = x := by omega
        rw [hxx] at h1 h2
        omega

/-- **Key lemma.**  If `P ≠ NP`, then Ladner's clock is unbounded: the construction
never gets stuck at a stage.

Indeed, suppose the clock were eventually constant with value `c`.  If `c = 2 * i`
is even, then `SAT` agrees with the polynomial-time language `pEnum i` on all
sufficiently large inputs, so `SAT ∈ P` by closure of `P` under finite variation,
contradicting `P ≠ NP`.  If `c = 2 * i + 1` is odd, then Ladner's language is
finite (its gap set is bounded), hence in `P`, and `redEnum i` reduces `SAT` to it,
so again `SAT ∈ P`, a contradiction. -/
theorem clock_unbounded (hPNP : S.P ≠ S.NP) : ∀ n : Nat, ∃ x : Nat, n < S.clock x := by
  intro n
  apply Classical.byContradiction
  intro hcontra
  have hcon : ∀ x : Nat, S.clock x ≤ n := by
    intro x
    apply Classical.byContradiction
    intro hx
    exact hcontra ⟨x, by omega⟩
  obtain ⟨c, N, hcN⟩ := eventually_const_of_bounded n S.clock S.clock_mono hcon
  rcases (show c % 2 = 0 ∨ c % 2 = 1 by omega) with hc | hc
  · -- stuck at an even stage: `SAT` is a finite variant of `pEnum i ∈ P`
    refine S.SAT_not_mem_P hPNP ?_
    obtain ⟨i, hi⟩ : ∃ i : Nat, c = 2 * i := ⟨c / 2, by omega⟩
    have hstage : ∀ x : Nat, N ≤ x → S.clock x = 2 * i := by
      intro x hx
      rw [hcN x hx, hi]
    have hagree := S.clock_stuck_even i N hstage
    have hmem : S.P (S.pEnum i) := (S.P_iff_range _).2 ⟨i, fun _ => Iff.rfl⟩
    exact S.P_finVar (S.pEnum i) S.SAT hmem ⟨N, fun x hx => (hagree x hx).symm⟩
  · -- stuck at an odd stage: Ladner's language is finite and `SAT` reduces to it
    refine S.SAT_not_mem_P hPNP ?_
    obtain ⟨i, hi⟩ : ∃ i : Nat, c = 2 * i + 1 := ⟨c / 2, by omega⟩
    have hstage : ∀ x : Nat, N ≤ x → S.clock x = 2 * i + 1 := by
      intro x hx
      rw [hcN x hx, hi]
    have hred := S.clock_stuck_odd i N hstage
    have hfin : S.P (fun x => S.SAT x ∧ S.clock x % 2 = 0) := by
      refine S.P_finite _ ⟨N, ?_⟩
      intro x hx hmem
      have h1 := hstage x hx
      have h2 := hmem.2
      omega
    exact S.P_reduce _ _ ⟨i, hred⟩ hfin

/-- Ladner's language lies in `NP`. -/
theorem ladnerLang_mem_NP : S.NP S.ladnerLang :=
  S.NP_inter_P _ _ S.SAT_mem_NP S.gap_mem_P

/-- Ladner's language is not in `P`. -/
theorem ladnerLang_not_mem_P (hPNP : S.P ≠ S.NP) : ¬ S.P S.ladnerLang := by
  intro hmem
  obtain ⟨i, hi⟩ := (S.P_iff_range _).1 hmem
  obtain ⟨x, hxgap, hxiff⟩ := S.clock_pass_even i (S.clock_unbounded hPNP (2 * i))
  have hxL : S.ladnerLang x ↔ S.SAT x :=
    ⟨fun h => h.1, fun h => ⟨h, hxgap⟩⟩
  have hix := hi x
  by_cases hsat : S.SAT x
  · exact (hxiff.1 hsat) (hix.1 (hxL.2 hsat))
  · have hp : S.pEnum i x := Classical.byContradiction fun hp => hsat (hxiff.2 hp)
    exact hsat (hxL.1 (hix.2 hp))

/-- Ladner's language is not `NP`-hard: `SAT` does not reduce to it. -/
theorem ladnerLang_not_NPHard (hPNP : S.P ≠ S.NP) : ¬ S.NPHard S.ladnerLang := by
  intro hhard
  obtain ⟨i, hi⟩ := hhard S.SAT S.SAT_mem_NP
  obtain ⟨x, hx⟩ := S.clock_pass_odd i (S.clock_unbounded hPNP (2 * i + 1))
  exact hx (hi x)

/-- Ladner's language is `NP`-intermediate. -/
theorem ladnerLang_NPIntermediate (hPNP : S.P ≠ S.NP) :
    S.NPIntermediate S.ladnerLang :=
  ⟨S.ladnerLang_mem_NP, S.ladnerLang_not_mem_P hPNP, S.ladnerLang_not_NPHard hPNP⟩

end LadnerSetup

/--
**Ladner's theorem.**  If `P ≠ NP`, then `NP`-intermediate problems exist: there is
a language `L` in `NP` which is neither in `P` nor `NP`-hard (in particular, `L` is
not `NP`-complete).

The statement is relative to an abstract `LadnerSetup`, which packages the
complexity-theoretic data (the classes `P` and `NP`, an `NP`-complete language
`SAT`, an enumeration of `P`, an enumeration of the polynomial-time reductions and
Ladner's clocked stage function) together with standard closure properties.
The language exhibited is Ladner's `SAT ∩ {x | f x` is even `}`.
-/
theorem ladner (S : LadnerSetup) (hPNP : S.P ≠ S.NP) :
    ∃ L : Lang, S.NP L ∧ ¬ S.P L ∧ ¬ S.NPHard L :=
  ⟨S.ladnerLang, S.ladnerLang_NPIntermediate hPNP⟩

end CS

