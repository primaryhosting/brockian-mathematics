/-
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
This file formalizes Ladner's theorem: *if `P ≠ NP` then there are `NP`-intermediate
languages*, i.e. languages that are in `NP`, not in `P`, and not `NP`-complete.

The proof is Ladner's delayed ("lazy") diagonalization: one builds a nondecreasing "hole"
function `hole : ℕ → ℕ` and looks at the language

  `A = K ∩ { x | hole (bit length of x) is even }`,

where `K` is an `NP`-complete language.  While `hole` sits at an even value `2 i` the
construction searches, with a growing step budget, for an input on which the `i`-th
polynomial-time machine disagrees with `A`; while it sits at an odd value `2 j + 1` it
searches for an input witnessing that the `j`-th polynomial-time function fails to reduce
`K` to `A`.  Each time such a witness is found the hole function moves on to the next stage.

If `hole` were bounded it would be eventually constant, and then either `A` would be decided
by a polynomial-time machine while differing from `K` only on finitely many inputs (even
case), or `A` would be finite while `K` reduces to it (odd case); both put `K` in `P`,
contradicting `P ≠ NP`.  Hence `hole` is unbounded, and therefore no machine decides `A` and
no polynomial-time function reduces `K` to `A`; that is, `A` is `NP`-intermediate.

The classes `P` and `NP` are not available in Mathlib, so they are axiomatized here by the
structure `CS.World`, which collects exactly the properties of `P`, `NP`, polynomial-time
many-one reductions, machine enumerations and step-bounded simulations that the argument
uses.  Section "A model" builds an explicit `World`, so that the axiom system is consistent
(of course no `World` with `inP ≠ inNP` can be exhibited, since `P` vs `NP` is open).
-/

namespace CS

/-- A language is a Boolean predicate on `ℕ`; inputs (strings) are encoded as natural
numbers, and `Nat.size x` is the bit length of the input `x`. -/
abbrev Lang := ℕ → Bool

/-- The bit length of `x` is at most `x`. -/
lemma size_le_self (x : ℕ) : Nat.size x ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self

/-- Inputs of value at least `2 ^ N` have bit length at least `N`. -/
lemma le_size_of_pow_le {N x : ℕ} (hx : 2 ^ N ≤ x) : N ≤ Nat.size x :=
  le_of_lt (Nat.lt_size.mpr hx)

/-! ### Two elementary facts about `ℕ`-valued sequences -/

/-- A sequence starting at `0` whose steps are at most `+1` and which is unbounded takes
every value. -/
lemma exists_eq_of_step {f : ℕ → ℕ} (h0 : f 0 = 0) (hstep : ∀ n, f (n + 1) ≤ f n + 1)
    (hunb : ∀ B, ∃ n, B ≤ f n) : ∀ v, ∃ n, f n = v := by
  classical
  intro v
  match v with
  | 0 => exact ⟨0, h0⟩
  | (v + 1) =>
    have hex : ∃ n, v + 1 ≤ f n := hunb (v + 1)
    have hspec : v + 1 ≤ f (Nat.find hex) := Nat.find_spec hex
    have hpos : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hp
      · rw [hz, h0] at hspec; omega
      · exact hp
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin : ¬ (v + 1 ≤ f m) := Nat.find_min hex (by omega)
    rw [hm] at hspec
    have := hstep m
    exact ⟨m + 1, by omega⟩

/-- A bounded monotone `ℕ`-valued sequence is eventually constant. -/
lemma eventually_const {f : ℕ → ℕ} (hmono : Monotone f) {B : ℕ} (hB : ∀ n, f n ≤ B) :
    ∃ N, ∀ n, N ≤ n → f n = f N := by
  have hne : (Set.range f).Nonempty := ⟨f 0, ⟨0, rfl⟩⟩
  have hbdd : BddAbove (Set.range f) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  obtain ⟨N, hN⟩ := Nat.sSup_mem hne hbdd
  refine ⟨N, fun n hn => ?_⟩
  have h1 : f N ≤ f n := hmono hn
  have h2 : f n ≤ sSup (Set.range f) := le_csSup hbdd ⟨n, rfl⟩
  rw [← hN] at h2
  omega

/-- Pointwise congruence for bounded existential searches. -/
lemma any_range_congr {n : ℕ} {p q : ℕ → Bool} (h : ∀ x < n, p x = q x) :
    (List.range n).any p = (List.range n).any q := by
  refine Bool.eq_iff_iff.mpr ?_
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨x, hx, hb⟩; exact ⟨x, hx, by rw [← h x hx]; exact hb⟩
  · rintro ⟨x, hx, hb⟩; exact ⟨x, hx, by rw [h x hx]; exact hb⟩

/-! ### The delayed diagonalization ("hole") construction -/

/-- Membership in the Ladner language, relative to a table `g` of values of the hole
function: `x` belongs iff `x ∈ K` and the hole function is even at the bit length of `x`. -/
def diag (K : Lang) (g : ℕ → ℕ) (x : ℕ) : Bool := K x && decide (Even (g (Nat.size x)))

/-- Budgeted search for a witness that machine `i` does *not* decide the diagonal language:
we look at inputs `x < n`, simulating machine `i` on `x` for `n` steps. -/
def witEven (K : Lang) (sim : ℕ → ℕ → ℕ → Option Bool) (i : ℕ) (g : ℕ → ℕ) (n : ℕ) : Bool :=
  (List.range n).any fun x => sim i x n == some (! diag K g x)

/-- Budgeted search for a witness that the `j`-th polynomial-time function is *not* a
many-one reduction of `K` to the diagonal language. -/
def witOdd (K : Lang) (simR : ℕ → ℕ → ℕ → Option ℕ) (j : ℕ) (g : ℕ → ℕ) (n : ℕ) : Bool :=
  (List.range n).any fun x =>
    (List.range (n + 1)).any fun y => (simR j x n == some y) && (K x != diag K g y)

/-- One step of the hole function: given the values `g` of the hole function up to `n`,
this is its value at `n + 1`. -/
def newval (K : Lang) (sim : ℕ → ℕ → ℕ → Option Bool) (simR : ℕ → ℕ → ℕ → Option ℕ)
    (g : ℕ → ℕ) (n : ℕ) : ℕ :=
  if Even (g n) then (if witEven K sim (g n / 2) g n then g n + 1 else g n)
  else (if witOdd K simR (g n / 2) g n then g n + 1 else g n)

/-- Course-of-values table for the hole function: `histTable K sim simR m x` agrees with the
hole function for all `x ≤ m`. -/
def histTable (K : Lang) (sim : ℕ → ℕ → ℕ → Option Bool) (simR : ℕ → ℕ → ℕ → Option ℕ) :
    ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | n + 1 => fun x =>
      if x ≤ n then histTable K sim simR n x
      else newval K sim simR (histTable K sim simR n) n

/-- The hole (delayed diagonalization) function of Ladner's construction. -/
def hole (K : Lang) (sim : ℕ → ℕ → ℕ → Option Bool) (simR : ℕ → ℕ → ℕ → Option ℕ) (n : ℕ) : ℕ :=
  histTable K sim simR n n

/-- The Ladner language `K ∩ {x | the hole function is even at the length of x}`. -/
def ladnerLang (K : Lang) (sim : ℕ → ℕ → ℕ → Option Bool) (simR : ℕ → ℕ → ℕ → Option ℕ) :
    Lang := diag K (hole K sim simR)

section Basic

variable {K : Lang} {sim : ℕ → ℕ → ℕ → Option Bool} {simR : ℕ → ℕ → ℕ → Option ℕ}
  {g g' : ℕ → ℕ} {n : ℕ}

lemma diag_congr (h : ∀ y ≤ n, g y = g' y) {x : ℕ} (hx : x ≤ n) :
    diag K g x = diag K g' x := by
  unfold diag
  rw [h (Nat.size x) (le_trans (size_le_self x) hx)]

lemma witEven_congr (h : ∀ y ≤ n, g y = g' y) (i : ℕ) :
    witEven K sim i g n = witEven K sim i g' n := by
  refine any_range_congr fun x hx => ?_
  rw [diag_congr h hx.le]

lemma witOdd_congr (h : ∀ y ≤ n, g y = g' y) (j : ℕ) :
    witOdd K simR j g n = witOdd K simR j g' n := by
  refine any_range_congr fun x _ => ?_
  refine any_range_congr fun y hy => ?_
  rw [diag_congr h (by omega : y ≤ n)]

lemma newval_congr (h : ∀ y ≤ n, g y = g' y) :
    newval K sim simR g n = newval K sim simR g' n := by
  unfold newval
  rw [h n le_rfl, witEven_congr h, witOdd_congr h]

lemma histTable_eq (K : Lang) (sim : ℕ → ℕ → ℕ → Option Bool) (simR : ℕ → ℕ → ℕ → Option ℕ) :
    ∀ m x, x ≤ m → histTable K sim simR m x = hole K sim simR x := by
  intro m
  induction m with
  | zero =>
    intro x hx
    have : x = 0 := Nat.le_zero.mp hx
    subst this
    rfl
  | succ n ih =>
    intro x hx
    by_cases hxn : x ≤ n
    · show (if x ≤ n then histTable K sim simR n x
          else newval K sim simR (histTable K sim simR n) n) = _
      rw [if_pos hxn]
      exact ih x hxn
    · have : x = n + 1 := by omega
      subst this
      rfl

lemma hole_zero (K : Lang) (sim : ℕ → ℕ → ℕ → Option Bool) (simR : ℕ → ℕ → ℕ → Option ℕ) :
    hole K sim simR 0 = 0 := rfl

/-- The defining recurrence of the hole function. -/
lemma hole_succ (K : Lang) (sim : ℕ → ℕ → ℕ → Option Bool) (simR : ℕ → ℕ → ℕ → Option ℕ)
    (n : ℕ) : hole K sim simR (n + 1) = newval K sim simR (hole K sim simR) n := by
  have h : histTable K sim simR (n + 1) (n + 1)
      = newval K sim simR (histTable K sim simR n) n := by
    show (if n + 1 ≤ n then histTable K sim simR n (n + 1)
        else newval K sim simR (histTable K sim simR n) n) = _
    rw [if_neg (by omega)]
  rw [hole, h]
  exact newval_congr (fun y hy => histTable_eq K sim simR n y hy)

lemma hole_succ_even (K : Lang) (sim : ℕ → ℕ → ℕ → Option Bool) (simR : ℕ → ℕ → ℕ → Option ℕ)
    {n : ℕ} (h : Even (hole K sim simR n)) :
    hole K sim simR (n + 1) =
      if witEven K sim (hole K sim simR n / 2) (hole K sim simR) n
        then hole K sim simR n + 1 else hole K sim simR n := by
  rw [hole_succ]
  unfold newval
  rw [if_pos h]

lemma hole_succ_odd (K : Lang) (sim : ℕ → ℕ → ℕ → Option Bool) (simR : ℕ → ℕ → ℕ → Option ℕ)
    {n : ℕ} (h : ¬ Even (hole K sim simR n)) :
    hole K sim simR (n + 1) =
      if witOdd K simR (hole K sim simR n / 2) (hole K sim simR) n
        then hole K sim simR n + 1 else hole K sim simR n := by
  rw [hole_succ]
  unfold newval
  rw [if_neg h]

lemma hole_le_succ (K : Lang) (sim : ℕ → ℕ → ℕ → Option Bool) (simR : ℕ → ℕ → ℕ → Option ℕ)
    (n : ℕ) : hole K sim simR (n + 1) ≤ hole K sim simR n + 1 := by
  rcases Nat.even_or_odd (hole K sim simR n) with he | ho
  · rw [hole_succ_even K sim simR he]; split <;> omega
  · rw [hole_succ_odd K sim simR (by simpa [Nat.not_even_iff_odd] using ho)]
    split <;> omega

lemma hole_mono (K : Lang) (sim : ℕ → ℕ → ℕ → Option Bool) (simR : ℕ → ℕ → ℕ → Option ℕ) :
    Monotone (hole K sim simR) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases Nat.even_or_odd (hole K sim simR n) with he | ho
  · rw [hole_succ_even K sim simR he]; split <;> omega
  · rw [hole_succ_odd K sim simR (by simpa [Nat.not_even_iff_odd] using ho)]
    split <;> omega

/-- If some machine `i` (whose simulation is sound for the language `D`) decides the Ladner
language, then the hole function never gets past the stage `2 i`. -/
lemma hole_le_of_decides {D : Lang} {i : ℕ}
    (hsound : ∀ x t b, sim i x t = some b → b = D x)
    (hD : ∀ x, D x = ladnerLang K sim simR x) :
    ∀ n, hole K sim simR n ≤ 2 * i := by
  intro n
  induction n with
  | zero => simp [hole_zero]
  | succ n ih =>
    rcases lt_or_eq_of_le ih with hlt | heq
    · have := hole_le_succ K sim simR n; omega
    · have hev : Even (hole K sim simR n) := by rw [heq]; exact even_two_mul i
      have hrec := hole_succ_even K sim simR hev
      rw [heq] at hrec
      simp only [Nat.mul_div_cancel_left i (by norm_num : 0 < 2)] at hrec
      have hwf : witEven K sim i (hole K sim simR) n = false := by
        by_contra hw
        simp only [Bool.not_eq_false, witEven, List.any_eq_true, List.mem_range] at hw
        obtain ⟨x, -, hx⟩ := hw
        have hb := hsound x n _ (by simpa using hx)
        rw [hD x] at hb
        have hAx : ladnerLang K sim simR x = diag K (hole K sim simR) x := rfl
        rw [hAx] at hb
        cases hd : diag K (hole K sim simR) x <;> rw [hd] at hb <;> simp at hb
      rw [hwf, if_neg (by simp)] at hrec
      omega

end Basic

/-! ### An abstract complexity-theoretic world

The structure `World` axiomatizes exactly the features of the classes `P`, `NP` and of
polynomial-time many-one reductions that Ladner's argument uses:

* `P ⊆ NP`, `P` is closed under extensional equality, contains the empty language, is closed
  under finite variations and under polynomial-time many-one reductions, and `NP` is closed
  under intersection with a language in `P`;
* `P` is presentable: `M` enumerates exactly the languages of `P` and `sim i x t` is the
  outcome of running the `i`-th (clocked, always halting) machine on input `x` for `t`
  steps; analogously `R` enumerates the polynomial-time functions, with step-bounded
  simulation `simR`;
* `K` is a designated `NP`-complete language (in the intended interpretation, `SAT`);
* `hole_inP` is the complexity-theoretic bookkeeping of Ladner's proof: the delayed
  diagonalization function built from the clocked simulations is polynomial-time computable
  in the length of the input, i.e. the "hole" set belongs to `P`.
-/

/-- An abstract world of complexity classes satisfying the hypotheses of Ladner's theorem. -/
structure World where
  /-- The class `P`. -/
  inP : Lang → Prop
  /-- The class `NP`. -/
  inNP : Lang → Prop
  /-- The class of polynomial-time computable functions. -/
  polyFun : (ℕ → ℕ) → Prop
  /-- An enumeration of the languages of `P`. -/
  M : ℕ → Lang
  /-- Step-bounded simulation of the machine deciding `M i`. -/
  sim : ℕ → ℕ → ℕ → Option Bool
  /-- An enumeration of the polynomial-time functions. -/
  R : ℕ → ℕ → ℕ
  /-- Step-bounded simulation of the machine computing `R j`. -/
  simR : ℕ → ℕ → ℕ → Option ℕ
  /-- A designated `NP`-complete language. -/
  K : Lang
  P_subset_NP : ∀ L, inP L → inNP L
  P_congr : ∀ L L', (∀ x, L x = L' x) → inP L → inP L'
  P_empty : inP (fun _ => false)
  P_finvar : ∀ (L L' : Lang) (N : ℕ), (∀ x, N ≤ x → L x = L' x) → inP L → inP L'
  P_red : ∀ (A B : Lang) (r : ℕ → ℕ), polyFun r → (∀ x, A x = B (r x)) → inP B → inP A
  NP_inter_P : ∀ A B : Lang, inNP A → inP B → inNP (fun x => A x && B x)
  M_mem : ∀ i, inP (M i)
  M_surj : ∀ L, inP L → ∃ i, ∀ x, M i x = L x
  sim_mono : ∀ i x t t' b, t ≤ t' → sim i x t = some b → sim i x t' = some b
  sim_sound : ∀ i x t b, sim i x t = some b → b = M i x
  sim_halts : ∀ i x, ∃ t, sim i x t = some (M i x)
  R_poly : ∀ j, polyFun (R j)
  R_surj : ∀ r, polyFun r → ∃ j, ∀ x, R j x = r x
  simR_mono : ∀ j x t t' y, t ≤ t' → simR j x t = some y → simR j x t' = some y
  simR_sound : ∀ j x t y, simR j x t = some y → y = R j x
  simR_halts : ∀ j x, ∃ t, simR j x t = some (R j x)
  K_NP : inNP K
  K_hard : ∀ A, inNP A → ∃ r, polyFun r ∧ ∀ x, A x = K (r x)
  hole_inP : inP (fun x => decide (Even (hole K sim simR (Nat.size x))))

namespace World

variable (W : World)

/-- Polynomial-time many-one reducibility. -/
def Reduces (A B : Lang) : Prop := ∃ r, W.polyFun r ∧ ∀ x, A x = B (r x)

/-- `NP`-completeness (with respect to polynomial-time many-one reductions). -/
def NPComplete (L : Lang) : Prop := W.inNP L ∧ ∀ A, W.inNP A → W.Reduces A L

/-- An `NP`-intermediate language: in `NP`, not in `P`, and not `NP`-complete. -/
def NPIntermediate (L : Lang) : Prop := W.inNP L ∧ ¬ W.inP L ∧ ¬ W.NPComplete L

/-- The designated language `K` is indeed `NP`-complete. -/
lemma K_complete : W.NPComplete W.K := ⟨W.K_NP, fun A hA => W.K_hard A hA⟩

end World

/-! ### The two stabilization lemmas -/

section Ladner

variable (W : World)

local notation "F" => hole W.K W.sim W.simR

/-- If the hole function stabilizes at an even value `2 i` from `N` on, then machine `i`
decides the Ladner language. -/
lemma agrees_of_stable_even (N : ℕ) (hstab : ∀ n, N ≤ n → F n = F N) (i : ℕ)
    (hi : F N = 2 * i) : ∀ x, W.M i x = ladnerLang W.K W.sim W.simR x := by
  have hwit : ∀ n, N ≤ n → witEven W.K W.sim i F n = false := by
    intro n hn
    have h1 : F n = F N := hstab n hn
    have h2 : F (n + 1) = F N := hstab (n + 1) (by omega)
    have hev : Even (F n) := by rw [h1, hi]; exact even_two_mul i
    have hrec := hole_succ_even W.K W.sim W.simR hev
    rw [h1, hi] at hrec
    simp only [Nat.mul_div_cancel_left i (by norm_num : 0 < 2)] at hrec
    by_cases hw : witEven W.K W.sim i F n = true
    · rw [hw, if_pos rfl] at hrec
      rw [h2, hi] at hrec
      omega
    · simpa using hw
  intro x
  obtain ⟨t, ht⟩ := W.sim_halts i x
  set n := max (max N (x + 1)) t with hn
  have hsim : W.sim i x n = some (W.M i x) :=
    W.sim_mono i x t n _ (le_max_right _ _) ht
  have hw := hwit n (le_trans (le_max_left N (x + 1)) (le_max_left _ _))
  have hxn : x < n := lt_of_lt_of_le (Nat.lt_succ_self x)
    (le_trans (le_max_right N (x + 1)) (le_max_left _ _))
  by_contra hne
  have hflip : W.M i x = ! diag W.K F x := by
    have hAx : ladnerLang W.K W.sim W.simR x = diag W.K F x := rfl
    rw [hAx] at hne
    cases hb : W.M i x <;> cases hd : diag W.K F x <;> simp [hb, hd] at hne ⊢
  have : witEven W.K W.sim i F n = true := by
    simp only [witEven, List.any_eq_true, List.mem_range]
    exact ⟨x, hxn, by rw [hsim, hflip]; simp⟩
  rw [hw] at this
  exact Bool.false_ne_true this

/-- If the hole function stabilizes at an odd value `2 j + 1` from `N` on, then `R j` is a
many-one reduction of `K` to the Ladner language. -/
lemma reduces_of_stable_odd (N : ℕ) (hstab : ∀ n, N ≤ n → F n = F N) (j : ℕ)
    (hj : F N = 2 * j + 1) : ∀ x, W.K x = ladnerLang W.K W.sim W.simR (W.R j x) := by
  have hwit : ∀ n, N ≤ n → witOdd W.K W.simR j F n = false := by
    intro n hn
    have h1 : F n = F N := hstab n hn
    have h2 : F (n + 1) = F N := hstab (n + 1) (by omega)
    have hod : ¬ Even (F n) := by
      rw [h1, hj]
      simp [parity_simps]
    have hrec := hole_succ_odd W.K W.sim W.simR hod
    rw [h1, hj] at hrec
    have hdiv : (2 * j + 1) / 2 = j := by omega
    rw [hdiv] at hrec
    by_cases hw : witOdd W.K W.simR j F n = true
    · rw [hw, if_pos rfl] at hrec
      rw [h2, hj] at hrec
      omega
    · simpa using hw
  intro x
  obtain ⟨t, ht⟩ := W.simR_halts j x
  set n := max (max N (x + 1)) (max t (W.R j x)) with hn
  have hsim : W.simR j x n = some (W.R j x) :=
    W.simR_mono j x t n _ (le_trans (le_max_left t (W.R j x)) (le_max_right _ _)) ht
  have hw := hwit n (le_trans (le_max_left N (x + 1)) (le_max_left _ _))
  have hxn : x < n := lt_of_lt_of_le (Nat.lt_succ_self x)
    (le_trans (le_max_right N (x + 1)) (le_max_left _ _))
  have hyn : W.R j x < n + 1 :=
    Nat.lt_succ_of_le (le_trans (le_max_right t (W.R j x)) (le_max_right _ _))
  by_contra hne
  have : witOdd W.K W.simR j F n = true := by
    simp only [witOdd, List.any_eq_true, List.mem_range]
    refine ⟨x, hxn, W.R j x, hyn, ?_⟩
    have hdd : ladnerLang W.K W.sim W.simR (W.R j x) = diag W.K F (W.R j x) := rfl
    rw [hdd] at hne
    rw [hsim]
    cases hb : W.K x <;> cases hd : diag W.K F (W.R j x) <;> simp [hb, hd] at hne ⊢
  rw [hw] at this
  exact Bool.false_ne_true this

end Ladner

/-! ### Ladner's theorem -/

/-- **Ladner's theorem.** In any abstract complexity world (see `CS.World`), if `P ≠ NP`
then there is an `NP`-intermediate language: a language which is in `NP`, is not in `P`,
and is not `NP`-complete. -/
theorem ladner (W : World) (h : W.inP ≠ W.inNP) : ∃ L : Lang, W.NPIntermediate L := by
  classical
  have hL0 : ∃ L, W.inNP L ∧ ¬ W.inP L := by
    by_contra hc
    push_neg at hc
    exact h (funext fun L => propext ⟨W.P_subset_NP L, hc L⟩)
  obtain ⟨L0, hL0NP, hL0P⟩ := hL0
  have hKP : ¬ W.inP W.K := by
    intro hKP
    obtain ⟨r, hr, hrx⟩ := W.K_hard L0 hL0NP
    exact hL0P (W.P_red L0 W.K r hr hrx hKP)
  set A := ladnerLang W.K W.sim W.simR with hA
  have hAdef : ∀ x, A x = (W.K x && decide (Even (hole W.K W.sim W.simR (Nat.size x)))) :=
    fun _ => rfl
  -- The hole function is unbounded.
  have hunb : ∀ B, ∃ n, B ≤ hole W.K W.sim W.simR n := by
    by_contra hbd
    push_neg at hbd
    obtain ⟨B, hB⟩ := hbd
    obtain ⟨N, hN⟩ := eventually_const (hole_mono W.K W.sim W.simR) (fun n => (hB n).le)
    rcases Nat.even_or_odd (hole W.K W.sim W.simR N) with hev | hod
    · obtain ⟨i, hi⟩ := hev
      have hi' : hole W.K W.sim W.simR N = 2 * i := by omega
      have hAi := agrees_of_stable_even W N hN i hi'
      have hAP : W.inP A := W.P_congr _ _ hAi (W.M_mem i)
      refine hKP (W.P_finvar A W.K (2 ^ N) ?_ hAP)
      intro x hx
      have hsz : hole W.K W.sim W.simR (Nat.size x) = hole W.K W.sim W.simR N :=
        hN _ (le_size_of_pow_le hx)
      rw [hAdef x, hsz, hi']
      simp
    · obtain ⟨j, hj⟩ := hod
      have hj' : hole W.K W.sim W.simR N = 2 * j + 1 := by omega
      have hred := reduces_of_stable_odd W N hN j hj'
      have hAP : W.inP A := by
        refine W.P_finvar (fun _ => false) A (2 ^ N) ?_ W.P_empty
        intro x hx
        have hsz : hole W.K W.sim W.simR (Nat.size x) = hole W.K W.sim W.simR N :=
          hN _ (le_size_of_pow_le hx)
        rw [hAdef x, hsz, hj']
        simp [parity_simps]
      exact hKP (W.P_red W.K A (W.R j) (W.R_poly j) hred hAP)
  have hhits : ∀ v, ∃ n, hole W.K W.sim W.simR n = v :=
    exists_eq_of_step (hole_zero W.K W.sim W.simR) (hole_le_succ W.K W.sim W.simR) hunb
  -- `A` belongs to `NP`.
  have hANP : W.inNP A :=
    W.NP_inter_P W.K (fun x => decide (Even (hole W.K W.sim W.simR (Nat.size x)))) W.K_NP
      W.hole_inP
  -- `A` does not belong to `P`.
  have hAnotP : ¬ W.inP A := by
    intro hAP
    obtain ⟨i, hi⟩ := W.M_surj A hAP
    have hbd := hole_le_of_decides (K := W.K) (sim := W.sim) (simR := W.simR)
      (D := W.M i) (i := i) (fun x t b hb => W.sim_sound i x t b hb) hi
    obtain ⟨n, hn⟩ := hunb (2 * i + 1)
    have := hbd n
    omega
  -- `A` is not `NP`-complete.
  have hAnotC : ¬ W.NPComplete A := by
    rintro ⟨-, hcomp⟩
    obtain ⟨r, hr, hrx⟩ := hcomp W.K W.K_NP
    obtain ⟨j, hj⟩ := W.R_surj r hr
    obtain ⟨n0, hn0⟩ := hhits (2 * j + 1)
    have hKA : ∀ x, W.K x = A (W.R j x) := by
      intro x; rw [hj x]; exact hrx x
    have hstick : ∀ m, n0 ≤ m → hole W.K W.sim W.simR m = 2 * j + 1 := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact hn0
      | succ m hm ih =>
        have hod : ¬ Even (hole W.K W.sim W.simR m) := by
          rw [ih]; simp [parity_simps]
        have hrec := hole_succ_odd W.K W.sim W.simR hod
        rw [ih] at hrec
        have hdiv : (2 * j + 1) / 2 = j := by omega
        rw [hdiv] at hrec
        have hwf : witOdd W.K W.simR j (hole W.K W.sim W.simR) m = false := by
          by_contra hw
          simp only [Bool.not_eq_false, witOdd, List.any_eq_true, List.mem_range,
            Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hw
          obtain ⟨x, -, y, -, hxy, hne⟩ := hw
          have hy : y = W.R j x := W.simR_sound j x m y hxy
          subst hy
          exact hne (by rw [hKA x]; rfl)
        rw [hwf, if_neg (by simp)] at hrec
        exact hrec
    obtain ⟨n, hn⟩ := hunb (2 * j + 2)
    have h1 : hole W.K W.sim W.simR (max n n0) = 2 * j + 1 := hstick _ (le_max_right _ _)
    have h2 : hole W.K W.sim W.simR n ≤ hole W.K W.sim W.simR (max n n0) :=
      hole_mono W.K W.sim W.simR (le_max_left _ _)
    omega
  exact ⟨A, hANP, hAnotP, hAnotC⟩

/-! ### A model

To make sure that the axioms collected in `CS.World` are consistent we exhibit a concrete
world: the "classes" are the eventually constant languages, the polynomial-time functions
are the `0/1`-valued functions given by such languages, and the designated complete language
is `{1}`.  (Of course this world satisfies `P = NP`; no world with `P ≠ NP` can be exhibited,
since `P` vs `NP` is open.) -/

namespace Model

/-- Eventually constant languages. -/
def EC (L : Lang) : Prop := ∃ N b, ∀ x, N ≤ x → L x = b

/-- An enumeration of all eventually constant languages. -/
def enum (i : ℕ) : Lang :=
  match (Encodable.decode (α := List Bool × Bool) i) with
  | some p => fun x => (p.1[x]?).getD p.2
  | none => fun _ => false

lemma enum_mem (i : ℕ) : EC (enum i) := by
  unfold enum
  rcases hd : (Encodable.decode (α := List Bool × Bool) i) with _ | p
  · exact ⟨0, false, fun x _ => rfl⟩
  · refine ⟨p.1.length, p.2, fun x hx => ?_⟩
    simp [List.getElem?_eq_none hx]

lemma enum_surj {L : Lang} (hL : EC L) : ∃ i, ∀ x, enum i x = L x := by
  obtain ⟨N, b, hb⟩ := hL
  refine ⟨Encodable.encode (((List.range N).map L), b), fun x => ?_⟩
  unfold enum
  rw [Encodable.encodek]
  by_cases hx : x < N
  · simp [hx]
  · have hlen : ((List.range N).map L).length ≤ x := by simpa using Nat.le_of_not_lt hx
    simp [List.getElem?_eq_none hlen, (hb x (Nat.le_of_not_lt hx)).symm]

/-- The class of "polynomial-time functions" of the model. -/
def polyFun (r : ℕ → ℕ) : Prop := ∃ i, ∀ x, r x = if enum i x then 1 else 0

/-- The enumeration of the "polynomial-time functions" of the model. -/
def R (j : ℕ) : ℕ → ℕ := fun x => if enum j x then 1 else 0

/-- The designated complete language of the model. -/
def Kmodel : Lang := fun x => decide (x = 1)

/-- Step-bounded simulation in the model (all machines answer immediately). -/
def sim (i x : ℕ) (_t : ℕ) : Option Bool := some (enum i x)

/-- Step-bounded simulation of the reductions in the model. -/
def simR (j x : ℕ) (_t : ℕ) : Option ℕ := some (R j x)

lemma hole_one : hole Kmodel sim simR 1 = 0 := by
  rw [hole_succ]
  simp [newval, witEven, hole_zero]

/-- In the model, the Ladner language is just `K` itself. -/
lemma ladner_eq : ∀ x, ladnerLang Kmodel sim simR x = Kmodel x := by
  intro x
  show (Kmodel x && decide (Even (hole Kmodel sim simR (Nat.size x)))) = Kmodel x
  by_cases hx : x = 1
  · subst hx
    have : Nat.size 1 = 1 := by simp
    rw [this, hole_one]
    simp [Kmodel]
  · simp [Kmodel, hx]

lemma hole_bounded : ∃ B, ∀ n, hole Kmodel sim simR n ≤ B := by
  obtain ⟨i, hi⟩ := enum_surj (L := Kmodel) ⟨2, false, fun x hx => by
    simp [Kmodel]; omega⟩
  refine ⟨2 * i, hole_le_of_decides (D := enum i) (i := i) ?_ ?_⟩
  · intro x t b hb
    simpa [sim, eq_comm] using hb
  · intro x
    rw [hi x, ladner_eq x]

/-- The model satisfies all the axioms of `CS.World`. -/
def world : World where
  inP := EC
  inNP := EC
  polyFun := polyFun
  M := enum
  sim := sim
  R := R
  simR := simR
  K := Kmodel
  P_subset_NP := fun _ h => h
  P_congr := by
    rintro L L' hLL' ⟨N, b, hb⟩
    exact ⟨N, b, fun x hx => by rw [← hLL' x]; exact hb x hx⟩
  P_empty := ⟨0, false, fun _ _ => rfl⟩
  P_finvar := by
    rintro L L' N hagree ⟨N1, b, hb⟩
    refine ⟨max N N1, b, fun x hx => ?_⟩
    rw [← hagree x (le_trans (le_max_left _ _) hx)]
    exact hb x (le_trans (le_max_right _ _) hx)
  P_red := by
    rintro A B r ⟨i, hr⟩ hAB hB
    obtain ⟨N', b', hE⟩ := enum_mem i
    refine ⟨N', if b' then B 1 else B 0, fun x hx => ?_⟩
    rw [hAB x, hr x, hE x hx]
    cases b' <;> simp
  NP_inter_P := by
    rintro A B ⟨N1, b1, h1⟩ ⟨N2, b2, h2⟩
    refine ⟨max N1 N2, b1 && b2, fun x hx => ?_⟩
    show (A x && B x) = (b1 && b2)
    rw [h1 x (le_trans (le_max_left _ _) hx), h2 x (le_trans (le_max_right _ _) hx)]
  M_mem := enum_mem
  M_surj := fun _ h => enum_surj h
  sim_mono := by rintro i x t t' b - hb; exact hb
  sim_sound := by rintro i x t b hb; simpa [sim, eq_comm] using hb
  sim_halts := fun i x => ⟨0, rfl⟩
  R_poly := fun j => ⟨j, fun _ => rfl⟩
  R_surj := fun r ⟨i, hi⟩ => ⟨i, fun x => (hi x).symm⟩
  simR_mono := by rintro j x t t' y - hy; exact hy
  simR_sound := by rintro j x t y hy; simpa [simR, eq_comm] using hy
  simR_halts := fun j x => ⟨0, rfl⟩
  K_NP := ⟨2, false, fun x hx => by simp [Kmodel]; omega⟩
  K_hard := by
    rintro A hA
    obtain ⟨i, hi⟩ := enum_surj hA
    refine ⟨R i, ⟨i, fun _ => rfl⟩, fun x => ?_⟩
    rw [← hi x]
    cases hb : enum i x <;> simp [R, hb, Kmodel]
  hole_inP := by
    obtain ⟨B, hB⟩ := hole_bounded
    obtain ⟨N, hN⟩ := eventually_const (hole_mono Kmodel sim simR) hB
    refine ⟨2 ^ N, decide (Even (hole Kmodel sim simR N)), fun x hx => ?_⟩
    show decide (Even (hole Kmodel sim simR (Nat.size x))) = _
    rw [hN _ (le_size_of_pow_le hx)]

end Model

/-- The axioms collected in `CS.World` are consistent: there is at least one world. -/
theorem world_nonempty : Nonempty World := ⟨Model.world⟩

end CS

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

