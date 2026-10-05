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
