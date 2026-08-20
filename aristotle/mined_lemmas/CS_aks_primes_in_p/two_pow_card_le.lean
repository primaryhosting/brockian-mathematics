/-
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.AKS.Algorithm
import RequestProject.AKS.Cost

/-!
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 8000000

namespace CS

/-- **PRIMES is in P** (Agrawal–Kayal–Saxena).

`AKS.aksBool : ℕ → Bool` is an explicit, fully computable implementation of the AKS primality
test.  On input `n` it checks that `n ≥ 2`, that `n` is not a perfect power, that no `a ≤ r`
shares a nontrivial factor with `n`, and — unless `n ≤ r` — that the congruences
`(X + a)^n = X^n + a` hold in `(ZMod n)[X]/(X^r - 1)` for all `1 ≤ a ≤ ℓ`, where `r = AKS.rAlg n`
is the least modulus for which the multiplicative order of `n` exceeds `(bit length)^4` and
`ℓ = AKS.ellAlg n`.  The congruences are evaluated by repeated squaring in a computable
coefficient-vector model of the quotient ring.

`AKS.aksI : ℕ → Bool × ℕ` is the same algorithm instrumented with a counter: it is a structural
copy of every function involved, threading a count of the primitive operations performed
(see `RequestProject/AKS/Cost.lean` for the cost assigned to each leaf primitive: `r * r`
coefficient multiplications for one cyclic convolution, `bits n` for one `Nat.gcd`, and so on).
Costs are therefore measured in arithmetic operations on numbers of `O(log n)` bits, not in
bit operations.

The statement below records:

* **the instrumented algorithm computes the same answer** as the plain one;
* **correctness**: `AKS.aksBool` decides primality exactly;
* **polynomial running time**: on every input `n ≥ 2` the algorithm performs at most
  `(bit length of n) ^ 45` primitive operations;
* **polynomial size of the parameters**: `r ≤ 2 · (bit length)^12` and `ℓ ≤ 4 · (bit length)^7 + 2`.
-/

theorem two_pow_card_le {t u₁ u₂ : ℕ} (hp : p.Prime) (hr : 2 ≤ r)
    {ζ : F} (hζ : IsPrimitiveRoot ζ r)
    (B : Finset ℕ) (hBp : ∀ a ∈ B, a < p)
    (hBne : ∀ a ∈ B, ζ + (algebraMap (ZMod p) F) (a : ZMod p) ≠ 0)
    (G : Finset (ZMod r)) (hGcard : t ≤ G.card)
    (hG : ∀ x : ZMod r, x ∈ G → ∃ u : ℕ, ((u : ℕ) : ZMod r) = x ∧
            ∀ a ∈ B, Intro p r u (X + C (a : ZMod p)))
    (hdeg : B.card < t)
    (hu₁ : ∀ a ∈ B, Intro p r u₁ (X + C (a : ZMod p)))
    (hu₂ : ∀ a ∈ B, Intro p r u₂ (X + C (a : ZMod p)))
    (hlt : u₂ < u₁) (hcong : ((u₁ : ℕ) : ZMod r) = ((u₂ : ℕ) : ZMod r)) :
    2 ^ B.card ≤ u₁ - u₂ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero r := ⟨by omega⟩
  have hζr : ζ ^ r = 1 := hζ.pow_eq_one
  set φ : ZMod p →+* F := algebraMap (ZMod p) F with hφ
  set v : Finset ℕ → F := fun S => ∏ a ∈ S, (ζ + φ (a : ZMod p)) with hv
  have hveq : ∀ S : Finset ℕ, Polynomial.aeval ζ (prodPoly p S) = v S := fun S =>
    aeval_prodPoly ζ S
  have hintroProd : ∀ (u : ℕ), (∀ a ∈ B, Intro p r u (X + C (a : ZMod p))) → ∀ S ⊆ B,
      Intro p r u (prodPoly p S) := by
    intro u hu S hS
    exact Intro.prod S _ (fun a ha => hu a (hS ha))
  -- the key evaluation identity
  have hkey : ∀ (u : ℕ), (∀ a ∈ B, Intro p r u (X + C (a : ZMod p))) → ∀ S ⊆ B,
      Polynomial.aeval (ζ ^ u) (prodPoly p S) = (v S) ^ u := by
    intro u hu S hS
    rw [← hveq S]
    exact ((hintroProd u hu S hS).aeval hζr).symm
  -- Step 1: the map `v` is injective on subsets of `B`
  have hsub : ∀ S ⊆ B, ∀ S' ⊆ B, v S = v S' → S ⊆ S' := by
    intro S hS S' hS' hvv a₀ ha₀S
    by_contra ha₀S'
    set Q : (ZMod p)[X] := prodPoly p S - prodPoly p S' with hQ
    have hcastinj : ∀ a ∈ B, ∀ b ∈ B, ((a : ZMod p) = (b : ZMod p)) → a = b := by
      intro a ha b hb hab
      have := congrArg ZMod.val hab
      rwa [ZMod.val_natCast_of_lt (hBp a ha), ZMod.val_natCast_of_lt (hBp b hb)] at this
    have hQne : Q ≠ 0 := by
      intro h0
      have h1 : Polynomial.eval (-(a₀ : ZMod p)) (prodPoly p S) = 0 := by
        rw [prodPoly, Polynomial.eval_prod]
        exact Finset.prod_eq_zero ha₀S (by simp)
      have h2 : Polynomial.eval (-(a₀ : ZMod p)) (prodPoly p S') ≠ 0 := by
        rw [prodPoly, Polynomial.eval_prod]
        refine Finset.prod_ne_zero_iff.mpr ?_
        intro a ha
        simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
        intro hcon
        have : (a : ZMod p) = (a₀ : ZMod p) := by linear_combination hcon
        exact ha₀S' ((hcastinj a (hS' ha) a₀ (hS ha₀S) this) ▸ ha)
      have : Polynomial.eval (-(a₀ : ZMod p)) Q = 0 := by rw [h0]; simp
      rw [hQ, Polynomial.eval_sub, h1, zero_sub, neg_eq_zero] at this
      exact h2 this
    have hdegQ : Q.natDegree ≤ B.card := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      simp only [natDegree_prodPoly]
      exact max_le (Finset.card_le_card hS) (Finset.card_le_card hS')
    set Qf : F[X] := Q.map φ with hQf
    have hQfne : Qf ≠ 0 := by
      rw [hQf, Ne, Polynomial.map_eq_zero_iff φ.injective]
      exact hQne
    have hdegQf : Qf.natDegree ≤ B.card := by
      rw [hQf, Polynomial.natDegree_map_eq_of_injective φ.injective]
      exact hdegQ
    -- the `t` roots
    set T : Finset F := G.image (fun x => ζ ^ (ZMod.val x)) with hT
    have hTcard : T.card = G.card := by
      refine Finset.card_image_of_injOn ?_
      intro x _ y _ hxy
      exact ZMod.val_injective r (hζ.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) hxy)
    have hTroots : T ⊆ Qf.roots.toFinset := by
      intro y hy
      simp only [hT, Finset.mem_image] at hy
      obtain ⟨x, hxG, rfl⟩ := hy
      obtain ⟨u, hu1, hu2⟩ := hG x hxG
      have hval : ZMod.val x = u % r := by rw [← hu1, ZMod.val_natCast]
      have hpow : ζ ^ (ZMod.val x) = ζ ^ u := by rw [hval, ← pow_eq_pow_mod ζ hζr u]
      have hzero : Polynomial.aeval (ζ ^ u) Q = 0 := by
        rw [hQ, map_sub, hkey u hu2 S hS, hkey u hu2 S' hS', hvv, sub_self]
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hQfne]
      rw [Polynomial.IsRoot, hQf, Polynomial.eval_map, ← Polynomial.aeval_def, hpow]
      exact hzero
    have : t ≤ B.card := by
      calc t ≤ G.card := hGcard
        _ = T.card := hTcard.symm
        _ ≤ Qf.roots.toFinset.card := Finset.card_le_card hTroots
        _ ≤ Multiset.card Qf.roots := Multiset.toFinset_card_le _
        _ ≤ Qf.natDegree := Polynomial.card_roots' _
        _ ≤ B.card := hdegQf
    omega
  have hinj : Set.InjOn v (B.powerset : Set (Finset ℕ)) := by
    intro S hS S' hS' hvv
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at hS hS'
    exact Finset.Subset.antisymm (hsub S hS S' hS' hvv) (hsub S' hS' S hS hvv.symm)
  -- Step 2: every value is a root of `Y ^ (u₁ - u₂) - 1`
  set D := u₁ - u₂ with hDdef
  have hD : 0 < D := by omega
  have hvne : ∀ S ⊆ B, v S ≠ 0 := by
    intro S hS
    exact Finset.prod_ne_zero_iff.mpr (fun a ha => hBne a (hS ha))
  have hζeq : ζ ^ u₁ = ζ ^ u₂ := by
    have h1 : u₁ % r = u₂ % r := by
      have := congrArg ZMod.val hcong
      rwa [ZMod.val_natCast, ZMod.val_natCast] at this
    rw [pow_eq_pow_mod ζ hζr u₁, pow_eq_pow_mod ζ hζr u₂, h1]
  have hpowD : ∀ S ⊆ B, (v S) ^ D = 1 := by
    intro S hS
    have e1 : (v S) ^ u₁ = (v S) ^ u₂ := by
      rw [← hkey u₁ hu₁ S hS, ← hkey u₂ hu₂ S hS, hζeq]
    have : (v S) ^ u₂ * (v S) ^ D = (v S) ^ u₂ * 1 := by
      rw [mul_one, ← pow_add]
      rw [show u₂ + D = u₁ by omega]
      exact e1
    exact mul_left_cancel₀ (pow_ne_zero _ (hvne S hS)) this
  -- Step 3: count
  have hsubset : (B.powerset.image v) ⊆ (X ^ D - C (1 : F)).roots.toFinset := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_powerset] at hy
    obtain ⟨S, hS, rfl⟩ := hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero hD 1)]
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, hpowD S hS, sub_self]
  calc 2 ^ B.card = B.powerset.card := by rw [Finset.card_powerset]
    _ = (B.powerset.image v).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (X ^ D - C (1 : F)).roots.toFinset.card := Finset.card_le_card hsubset
    _ ≤ Multiset.card (X ^ D - C (1 : F)).roots := Multiset.toFinset_card_le _
    _ ≤ (X ^ D - C (1 : F)).natDegree := Polynomial.card_roots' _
    _ = D := Polynomial.natDegree_X_pow_sub_C

end Counting

end AKS

/-
Definitions for the Agrawal-Kayal-Saxena primality criterion.
-/
import Mathlib

open Polynomial

namespace AKS

/-- Bit length of `n`: the least `k` with `n < 2 ^ k`. -/
