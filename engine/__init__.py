"""engine — the unified proof engine's shared machinery.

One place that verifies (`engine.verify`), one place that decides a register
(`engine.register`). See docs/superpowers/specs/2026-08-20-unified-proof-engine-design.md.
The two registers (registry/theorems.json, registry/domains.json) stay separate; only the
machinery beneath them is shared.
"""
