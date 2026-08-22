# Phase-1 Proof-of-Life — Two Independent Provers, One Re-Checkable Certificate

This is the artifact that turns the Verification Foundry pitch from *a concept* into *a delivered asset*. Our own "we raise the objections first" section says it plainly: *until a real obligation is cleared by two independent provers with a re-checkable certificate, it's a concept, not an asset.* This closes that gap.

## What it is

Five **real crypto-implementation obligations** over 32-bit bitvectors — the kind of impl-vs-spec facts SAW discharges every day — each **proved twice, by two genuinely independent cores**, with the results bound into one **hash-sealed, re-checkable certificate** (SHA-256 content digest — tamper-evident, not a keyed signature):

| obligation | statement | why it's real |
|---|---|---|
| `otp_involution` | `(m ^ k) ^ k = m` | stream-cipher / one-time-pad decryption inverts encryption |
| `mask_select_identity` | `(mask & a) \| (~mask & a) = a` | the masking identity behind constant-time select |
| `ct_select_true` | `ctSelect(all-ones, a, b) = a` | constant-time conditional (data-oblivious) selects a |
| `ct_select_false` | `ctSelect(0, a, b) = b` | constant-time conditional selects b |
| `xor_swap` | XOR-swap returns `(b, a)` | in-place swap idiom, no temporary |

## The two independent provers

- **Z3 4.16.0** (SMT/SAT) — runs the SMT-LIB2 query in `obligations/*.smt2`, bit-blasting to SAT. Each query asserts the *negation* of the property; `unsat` is the proof.
- **Lean 4 kernel + AXLE** — a proof by *different mathematics*, re-verified by the AXLE cloud prover (`lean-4.32.2`) and **axiom-audited** (axioms ⊆ `{propext, Classical.choice, Quot.sound}`; no `sorry`/`admit`/`native_decide`). Module: `Brockian.HighAssurance.CryptoIdioms`.

  A finding worth stating plainly (the prover surfaced it, we kept it): we *tried* `bv_decide` first — it bit-blasts to a SAT backend and emits an LRAT certificate. **AXLE's axiom gate rejects that**: `bv_decide`'s native SAT axiom is outside the allowed standard set. So the three non-trivial obligations are closed by **kernel-checked BitVec algebra** (Mathlib rewrite lemmas), and the two constant-mask selects by `bv_decide`'s constant-folding preprocessing (no SAT axiom emitted). The Lean leg is therefore **not a second SAT solver** — it is an algebraic, kernel-checked proof.

This is the opposite of a weakness. The two provers use genuinely **different mathematics** — Z3 does a propositional SAT search; Lean does algebraic reasoning checked by a small trusted kernel. Agreement across two *different methods* is stronger evidence than agreement across two SAT engines. An obligation is **CROSS-VERIFIED** only when both agree.

## The certificate travels

`certificate.json` embeds, per obligation, the exact SMT-LIB2 query and the Lean theorem name, and carries a **SHA-256 over the mathematical payload**. A third party needs nothing from us to trust it:

```bash
python3 phase1/prove.py                       # discharge with both provers, emit the certificate
python3 phase1/recheck.py phase1/certificate.json   # independently re-verify: recompute the hash + re-run the SMT queries
```

`recheck.py` (1) recomputes the SHA-256 and confirms the certificate wasn't altered — edit any statement, query, or verdict and the hash breaks — and (2) re-runs an SMT solver on each embedded query, reproducing the Z3 leg **without our pipeline**. Point it at `cvc5` with `--solver=cvc5` for a *third* independent check.

## Honest scope (stated, not buried)

These are small, decidable `QF_BV` obligations. The point of Phase-1 is the **discipline** — two genuinely independent provers, agreement required, a portable tamper-evident certificate anyone can re-check — not proof depth. Scaling this to a full SAW obligation (e.g. an HMAC/SHA equivalence) with a proof-carrying certificate is the joint Phase-1 engineering in the partnership plan. What is delivered here is real: run the two scripts and watch it re-verify.
