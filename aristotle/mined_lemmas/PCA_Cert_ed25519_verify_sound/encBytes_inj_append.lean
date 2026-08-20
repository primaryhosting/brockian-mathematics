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

theorem encBytes_inj_append {a b x y : List UInt8} (ha : ShortBytes a) (hb : ShortBytes b)
    (h : encBytes a ++ x = encBytes b ++ y) : a = b ∧ x = y := by
  have h4a : (natToLe a.length 4).length = 4 := length_natToLe _ _
  have h4b : (natToLe b.length 4).length = 4 := length_natToLe _ _
  have h' : natToLe a.length 4 ++ (a ++ x) = natToLe b.length 4 ++ (b ++ y) := by
    simpa [encBytes, List.append_assoc] using h
  obtain ⟨hpre, hrest⟩ := List.append_inj h' (by rw [h4a, h4b])
  have hlen : a.length = b.length := by
    have := congrArg leToNat hpre
    rw [leToNat_natToLe_of_lt (by simpa [ShortBytes] using ha),
      leToNat_natToLe_of_lt (by simpa [ShortBytes] using hb)] at this
    exact this
  exact List.append_inj hrest hlen

