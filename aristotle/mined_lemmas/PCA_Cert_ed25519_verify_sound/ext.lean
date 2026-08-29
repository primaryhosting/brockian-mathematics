/-!
# Ed 25519 Verify Sound
Category: Proof-Carrying Apps
Target: PCA.Cert.ed25519_verify_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## An abstract model of Ed25519 signature verification

We model the Ed25519 signature scheme inside the prime-order subgroup of the
twisted Edwards curve `edwards25519`.  The group is kept abstract: it is any
commutative group `G` (class `PCA.Cert.PointGroup`) together with a base point
`B` whose additive order is the Ed25519 group order

  `ell = 2^252 + 27742317777372353535851937790883648493`.

Scalars are natural numbers acting on points by repeated addition
(`PCA.Cert.PointGroup.nsmul`).  The challenge hash `H` (computing
`k = H(R, A, M)`) is abstract as well: no property of it is assumed, so all the
results below hold for every instantiation of the hash.

Main results:

* `PCA.Cert.ed25519_verify_complete` -- honestly produced signatures verify;
* `PCA.Cert.ed25519_verify_sound`    -- conversely, if the verification equation
  holds for the public key `A = s * B` and the signature's commitment is
  `R = r * B`, then the signature is *exactly* the honest signature for the
  secret scalar `s`, nonce `r` and message `m`.  In other words the verifier
  accepts no pair `(R, S)` other than the unique one prescribed by the Ed25519
  signing equation `S = r + H(R, A, M) * s  (mod ell)`.

The development is self-contained: it depends only on the Lean 4 core library.
-/

namespace PCA.Cert

/-- The order of the prime-order subgroup of `edwards25519` used by Ed25519. -/

theorem ext {a b : Zell} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

instance : PointGroup Zell where
  add a b := ⟨(a.val + b.val) % ell, Nat.mod_lt _ ell_pos⟩
  zero := ⟨0, ell_pos⟩
  neg a := ⟨(ell - a.val) % ell, Nat.mod_lt _ ell_pos⟩
  add_assoc a b c := by
    refine ext ?_
    show ((a.val + b.val) % ell + c.val) % ell
        = (a.val + (b.val + c.val) % ell) % ell
    rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
  add_comm a b := by
    refine ext ?_
    show (a.val + b.val) % ell = (b.val + a.val) % ell
    rw [Nat.add_comm]
  zero_add a := by
    refine ext ?_
    show (0 + a.val) % ell = a.val
    rw [Nat.zero_add, Nat.mod_eq_of_lt a.isLt]
  neg_add a := by
    refine ext ?_
    show ((ell - a.val) % ell + a.val) % ell = 0
    rw [Nat.mod_add_mod, Nat.sub_add_cancel (Nat.le_of_lt a.isLt), Nat.mod_self]

