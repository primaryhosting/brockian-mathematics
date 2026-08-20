/-
# Langlands Reciprocity
Category: Frontier Abel
Target: Frontier.langlands_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Langlands Reciprocity
Category: Frontier Abel
Target: Frontier.langlands_reciprocity
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-!
## The shape of the conjecture

Langlands reciprocity predicts that every `d`-dimensional (continuous, complex) representation
`ρ` of the absolute Galois group of a number field is *automorphic*: there is an automorphic
representation `π` of `GL_d` over that field whose local data (Satake parameters / Hecke
eigenvalues) match the Frobenius data of `ρ`, so that `L(s, ρ) = L(s, π)`.

For `d = 1` over `ℚ` the automorphic representations of `GL_1` of finite order are exactly the
Dirichlet characters, and the predicted matching is provided by the Artin reciprocity map.  This
degree-one case is the classical base case of the conjecture (abelian class field theory), and it
is the case formalized and proved here.

`IsArtinReciprocity art` below is the precise degree-one reciprocity statement relative to a
reciprocity ("Artin") map `art : G →* (ZMod n)ˣ`: *every* one-dimensional Galois representation of
`G` is matched by a *unique* Dirichlet character modulo `n`, the matching being
`χ (art g) = ρ g`.
-/

/-- A degree-one Galois representation of a group `G`: a character `G →* ℂˣ`.
(For a finite Galois group every homomorphism to `ℂˣ` is automatically continuous with finite
image, so this is exactly the notion of an Artin character of degree one.) -/
abbrev GaloisChar (G : Type*) [Group G] := G →* ℂˣ

/-- **Degree-one Langlands reciprocity relative to a reciprocity map `art`.**

Every one-dimensional Galois representation `ρ : G →* ℂˣ` is automorphic: there is a *unique*
Dirichlet character `χ` modulo `n` (i.e. a unique automorphic representation of `GL₁` of
conductor dividing `n`) whose value at `art g` is `ρ g` for all `g`. -/

theorem cyclotomicArtinMap_eq_of_pow_eq (ζ : K) (hζ : IsPrimitiveRoot ζ n) (σ : K ≃ₐ[ℚ] K)
    (a : ℕ) (ha : σ ζ = ζ ^ a) :
    (a : ZMod n) = ((cyclotomicArtinMap n K σ : (ZMod n)ˣ) : ZMod n) := by
  have h1 : σ ζ = ζ ^ ((cyclotomicArtinMap n K σ : ZMod n).val) :=
    cyclotomicArtinMap_spec n K σ hζ.pow_eq_one
  have h2 : ζ ^ a = ζ ^ ((cyclotomicArtinMap n K σ : ZMod n).val) := by rw [← ha, h1]
  have hmod : ∀ m : ℕ, ζ ^ m = ζ ^ (m % n) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m n]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have h4 : a % n = (cyclotomicArtinMap n K σ : ZMod n).val := by
    refine hζ.pow_inj (Nat.mod_lt _ (NeZero.pos n)) (ZMod.val_lt _) ?_
    rw [← hmod a, h2]
  have h5 : ((a : ZMod n)) = (((cyclotomicArtinMap n K σ : ZMod n).val : ℕ) : ZMod n) := by
    rw [← h4, ZMod.natCast_mod]
  rw [h5, ZMod.natCast_val, ZMod.cast_id]

/-- Degree-one Langlands reciprocity for the cyclotomic field `ℚ(ζₙ)`, phrased through the
cyclotomic Artin map. -/
