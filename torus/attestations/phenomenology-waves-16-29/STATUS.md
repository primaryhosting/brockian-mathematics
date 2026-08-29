# STAGING STATUS — Phenomenological Mathematics Waves 16–29

**State:** 🟡 **STAGED — NOT PUBLISHED.** Do not push to `torus.riemannlab.com` yet.

## Publish gate (honesty firewall)

Per `torus/README.md`: *"A proof is a proof; a conjecture is not."* A green verified
badge requires a reproduced machine check. This attestation is currently **PARTIAL**:

| Layer | Status | Eligible for green badge? |
|---|---|---|
| Source identity (32/32 SHA-256 vs manifest) | ✅ done | — |
| Forbidden-construct scan (0 sorry/admit/native_decide/axiom) | ✅ done | — |
| **Lean compile under v4.32.0** | ⏸️ **DEFERRED (host RAM)** | **NO — blocks publish** |
| **`#print axioms` reproduction (181 decls)** | ⏸️ **DEFERRED** | **NO — blocks publish** |

**→ Until the compile is independently reproduced, these waves must NOT appear as
"verified" on the public site**, and must NOT be added to `public/verified-registry.json`
(they are not in the prover-owned registry yet — no `Wave*.lean` in the repo build).

## Promotion checklist (run in order)

1. Free ~1 GB RAM (`orb stop`) or wait off-peak.
2. `bash run-deferred-compile.sh /path/to/aristotle-full-available-corpus-2026-08-29`
   → build GREEN + `AXIOM-FOOTPRINTS.reproduced.txt`.
3. Confirm reproduced footprints = 111 axiom-free + 70 propext-only, **0 non-standard**.
   Any non-standard axiom → STOP, it's a finding, do not publish.
4. Register the 34 firewall theorems (or all 181) into the prover registry, regenerate
   `public/verified-registry.json` via `scripts/export_public_registry.py` (never hand-edit).
5. Flip `draft-page.md` from "static-verified / compile pending" to "independently verified,"
   publish to Lovable `dd8308ac`, and keep the firewall framing (Book Four = non-entailments).

## Firewall reminder (always, even when green)

A passing build proves consequences of the submitted formal models ONLY. It does not
establish historical fidelity, empirical adequacy, standards conformance, interoperability,
novelty, or priority. Book Four's theorems exist to *prevent* that upgrade.
