import Mathlib

/-!
# Little-endian byte strings

Basic infrastructure for the Ed25519 certificate model: conversion between
natural numbers and fixed-width little-endian byte strings, together with the
round-trip and injectivity lemmas that make byte-level canonicality arguments
possible.
-/

namespace PCA

/-- Value of a little-endian byte string (least significant byte first). -/

theorem verify_iff (pkb msg sigb : List UInt8) :
    p.verify pkb msg sigb = true ↔
      sigb.length = 64 ∧
        ∃ A R : G, ∃ S : ZMod L,
          p.decPt pkb = some A ∧ p.decPt (sigb.take 32) = some R ∧
            decScalar L (sigb.drop 32) = some S ∧
            S • p.B = R + p.H (sigb.take 32) pkb msg • A := by
  unfold verify
  cases hA : p.decPt pkb with
  | none => simp
  | some A =>
    cases hR : p.decPt (sigb.take 32) with
    | none => simp
    | some R =>
      cases hS : decScalar L (sigb.drop 32) with
      | none => simp
      | some S =>
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨hlen, heq⟩
          exact ⟨hlen, A, R, S, rfl, rfl, rfl, heq⟩
        · rintro ⟨hlen, A', R', S', hA', hR', hS', heq⟩
          obtain rfl := Option.some.inj hA'
          obtain rfl := Option.some.inj hR'
          obtain rfl := Option.some.inj hS'
          exact ⟨hlen, heq⟩

end Params

section Theorems

variable {G : Type*} {L : ℕ} [AddCommGroup G] [Module (ZMod L) G] [DecidableEq G] [NeZero L]
variable (p : Params G L)

/-- **Completeness.** A signature produced by `sign` with secret scalar `a` is
accepted under the public key of `a`. -/
