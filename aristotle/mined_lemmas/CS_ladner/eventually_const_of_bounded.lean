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
