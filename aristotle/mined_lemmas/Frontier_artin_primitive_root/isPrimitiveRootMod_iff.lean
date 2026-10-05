import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- docstrings, so the header block above sits immediately after the single import.)

namespace Frontier

/-! ## Definitions -/

/-- `a : ℤ` is a *primitive root* modulo `p` when the residue of `a` generates the
multiplicative group of `ZMod p`, i.e. it has multiplicative order `p - 1`. -/

theorem isPrimitiveRootMod_iff (a : ℤ) (p : ℕ) (hp : p.Prime) :
    IsPrimitiveRootMod a p ↔
      ((a : ZMod p) ≠ 0 ∧ ∀ x : ZMod p, x ≠ 0 → ∃ k : ℕ, ((a : ZMod p)) ^ k = x) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [IsPrimitiveRootMod]
  constructor
  · intro hord
    have hne : ((a : ZMod p)) ≠ 0 := by
      intro h
      have h1 := pow_orderOf_eq_one ((a : ZMod p))
      rw [h] at h1 hord
      rw [hord, zero_pow (by have := hp.two_le; omega)] at h1
      exact zero_ne_one h1
    refine ⟨hne, fun x hx => ?_⟩
    obtain ⟨u, hu⟩ := hne.isUnit
    obtain ⟨v, hv⟩ := hx.isUnit
    have hcard : orderOf u = Nat.card (ZMod p)ˣ := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units p, ← hord, ← hu, orderOf_units]
    have htop : Subgroup.zpowers u = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hcard])
    have hvv : v ∈ Subgroup.zpowers u := htop ▸ Subgroup.mem_top v
    rw [← mem_powers_iff_mem_zpowers] at hvv
    obtain ⟨k, hk⟩ := hvv
    exact ⟨k, by rw [← hu, ← hv, ← hk]; push_cast; ring⟩
  · rintro ⟨hne, hgen⟩
    obtain ⟨u, hu⟩ := hne.isUnit
    have hall : ∀ v : (ZMod p)ˣ, v ∈ Submonoid.powers u := by
      intro v
      obtain ⟨k, hk⟩ := hgen (v : ZMod p) v.ne_zero
      exact ⟨k, Units.ext (by rw [Units.val_pow_eq_pow_val, hu, hk])⟩
    have hcard := orderOf_eq_card_of_forall_mem_powers hall
    rw [← orderOf_units, hu] at hcard
    rw [hcard, Nat.card_eq_fintype_card, ZMod.card_units p]

/-! ## The Lean-checked reduction: the excluded cases are genuinely exceptional -/

/-- If `a = -1` or `a` is a perfect square, then `a` is not a primitive root modulo any
prime `p > 3`. -/
