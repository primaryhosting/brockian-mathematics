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

theorem encList_inj_append :
    ∀ {as bs : List (List UInt8)} {x y : List UInt8},
      (∀ a ∈ as, ShortBytes a) → (∀ b ∈ bs, ShortBytes b) → as.length = bs.length →
      encList as ++ x = encList bs ++ y → as = bs ∧ x = y
  | [], [], x, y, _, _, _, h => ⟨rfl, by simpa [encList] using h⟩
  | [], _ :: _, _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, hlen, _ => by simp at hlen
  | a :: as, b :: bs, x, y, ha, hb, hlen, h => by
      have h' : encBytes a ++ (encList as ++ x) = encBytes b ++ (encList bs ++ y) := by
        simpa [encList, List.append_assoc] using h
      obtain ⟨hab, hrest⟩ :=
        encBytes_inj_append (ha a (by simp)) (hb b (by simp)) h'
      obtain ⟨hasbs, hxy⟩ :=
        encList_inj_append (fun c hc => ha c (by simp [hc]))
          (fun c hc => hb c (by simp [hc])) (by simpa using hlen) hrest
      exact ⟨by rw [hab, hasbs], hxy⟩

/-! ## Certificates -/

/-- A capability certificate: it names a subject and the resources that subject
may access. -/
structure CapCert where
  /-- The subject the certificate is issued to. -/
  subject : List UInt8
  /-- The resources the subject may access. -/
  caps : List (List UInt8)
  deriving DecidableEq

/-- Serialization of a certificate: length-prefixed subject, then the number of
capabilities, then the length-prefixed capabilities. -/
