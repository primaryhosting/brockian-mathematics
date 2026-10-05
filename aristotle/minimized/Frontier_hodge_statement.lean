import Mathlib
/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

open TensorProduct

/-- Complex conjugation acting on the complexification `ℂ ⊗[ℚ] V` of a rational vector
space `V` (conjugation on the left factor, identity on `V`).  It is only `ℚ`-linear
(it is conjugate-linear over `ℂ`). -/

noncomputable def hodgeClasses (X : HodgeVariety H) (p : ℕ) : Submodule ℚ (H p) :=
  Submodule.comap (TensorProduct.mk ℚ ℂ (H p) 1) (((X.hs p).piece p p).restrictScalars ℚ)

def HodgeConjectureAt (X : HodgeVariety H) (p : ℕ) : Prop :=
  X.alg p = hodgeClasses X p

/-- The Hodge conjecture for `X`: in every codimension, the Hodge classes are exactly the
rational combinations of algebraic cycle classes. -/

def HodgeConjecture (X : HodgeVariety H) : Prop :=
  ∀ p : ℕ, HodgeConjectureAt X p

/-- One inclusion always holds: algebraic cycle classes are Hodge classes. -/

theorem alg_le_hodgeClasses (X : HodgeVariety H) (p : ℕ) :
    X.alg p ≤ hodgeClasses X p := fun _ hv => X.alg_isHodge p _ hv

/-- Contrapositive reformulation: the Hodge conjecture in codimension `p` holds iff there
is no non-algebraic Hodge class of codimension `p`. -/

theorem hodgeConjectureAt_iff_no_nonalgebraic (X : HodgeVariety H) (p : ℕ) :
    HodgeConjectureAt X p ↔ ¬ ∃ v : H p, v ∈ hodgeClasses X p ∧ v ∉ X.alg p := by
  constructor
  · rintro h ⟨v, hv, hv'⟩
    exact hv' (h ▸ hv)
  · intro h
    refine le_antisymm (alg_le_hodgeClasses X p) fun v hv => ?_
    by_contra hv'
    exact h ⟨v, hv, hv'⟩

/-- Equivalent "surjectivity" form of the whole conjecture. -/

theorem hodgeConjecture_iff (X : HodgeVariety H) :
    HodgeConjecture X ↔ ∀ p : ℕ, hodgeClasses X p ≤ X.alg p := by
  constructor
  · intro h p
    exact (h p).ge
  · intro h p
    exact le_antisymm (alg_le_hodgeClasses X p) (h p)

/-- If the `(p,p)`-part of the Hodge decomposition vanishes, then there are no nonzero
Hodge classes of codimension `p`. -/

theorem hodgeClasses_eq_bot_of_piece_eq_bot (X : HodgeVariety H) (p : ℕ)
    (hp : (X.hs p).piece p p = ⊥) : hodgeClasses X p = ⊥ := by
  refine le_antisymm (fun v hv => ?_) bot_le
  have hv' : (1 : ℂ) ⊗ₜ[ℚ] v ∈ (X.hs p).piece p p := hv
  rw [hp, Submodule.mem_bot] at hv'
  have hinj : Function.Injective ((TensorProduct.mk ℚ ℂ (H p)) 1) :=
    Module.FaithfullyFlat.tensorProduct_mk_injective (H p)
  have : v = 0 := by
    have h0 : ((TensorProduct.mk ℚ ℂ (H p)) 1) v = ((TensorProduct.mk ℚ ℂ (H p)) 1) 0 := by
      simpa using hv'
    exact hinj h0
  simp [this]

/-- Vanishing case of the Hodge conjecture: if `H^{p,p} = 0` then the conjecture holds in
codimension `p` (both sides are zero). -/

theorem hodgeConjectureAt_of_piece_eq_bot (X : HodgeVariety H) (p : ℕ)
    (hp : (X.hs p).piece p p = ⊥) : HodgeConjectureAt X p := by
  have hb := hodgeClasses_eq_bot_of_piece_eq_bot X p hp
  have hle := alg_le_hodgeClasses X p
  rw [hb] at hle
  rw [HodgeConjectureAt, hb, le_bot_iff.mp hle]

/-- Base case of the Hodge conjecture: it holds in codimension `0`, where every class is a
Hodge class and every class is a rational multiple of the fundamental class. -/

theorem hodgeConjectureAt_zero (X : HodgeVariety H) : HodgeConjectureAt X 0 := by
  have h : hodgeClasses X 0 = ⊤ := by
    refine le_antisymm le_top fun v _ => ?_
    show (1 : ℂ) ⊗ₜ[ℚ] v ∈ (X.hs 0).piece 0 0
    rw [X.degree_zero_type]
    exact Submodule.mem_top
  rw [HodgeConjectureAt, h, X.alg_degree_zero]

/-- **The Hodge conjecture, stated, together with the Lean-checked reductions and base
cases that are proved here.**

For every smooth complex projective variety `X` (represented by its cohomological Hodge
data), the *Hodge conjecture* asserts

  `HodgeConjecture X : ∀ p, X.alg p = hodgeClasses X p`,

i.e. every rational cohomology class of type `(p,p)` is a rational linear combination of
classes of algebraic cycles.  The statement below records:

1. the always-valid inclusion: algebraic classes are Hodge classes;
2. the contrapositive reformulation in each codimension: the conjecture holds in
   codimension `p` iff no Hodge class fails to be algebraic;
3. the global reduction of the conjecture to the single inclusion
   `hodgeClasses X p ≤ X.alg p`;
4. the base case `p = 0`, which is proved unconditionally;
5. the vanishing case: whenever `H^{p,p} = 0`, the conjecture holds in codimension `p`. -/

theorem hodge_statement :
    ∀ {H : ℕ → Type} [∀ p, AddCommGroup (H p)] [∀ p, Module ℚ (H p)]
      (X : HodgeVariety H),
      (∀ p : ℕ, X.alg p ≤ hodgeClasses X p) ∧
      (∀ p : ℕ, HodgeConjectureAt X p ↔ ¬ ∃ v : H p, v ∈ hodgeClasses X p ∧ v ∉ X.alg p) ∧
      (HodgeConjecture X ↔ ∀ p : ℕ, hodgeClasses X p ≤ X.alg p) ∧
      HodgeConjectureAt X 0 ∧
      (∀ p : ℕ, (X.hs p).piece p p = ⊥ → HodgeConjectureAt X p) := by
  intro H _ _ X
  exact ⟨alg_le_hodgeClasses X, hodgeConjectureAt_iff_no_nonalgebraic X,
    hodgeConjecture_iff X, hodgeConjectureAt_zero X,
    fun p hp => hodgeConjectureAt_of_piece_eq_bot X p hp⟩

end Frontier
