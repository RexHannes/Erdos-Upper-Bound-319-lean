# Lean formalization: a finite top-layer exclusion lemma for Erdős problem #319

This repository contains a small Lean 4 formalization of a finite obstruction lemma for Erdős problem #319.

It **does not prove Erdős #319**. It proves a Lean-checked finite top-layer exclusion lemma that can be used as partial progress toward upper bounds for the maximum size of a primitive signed reciprocal zero-sum support.

## Main theorem

The main theorem is in [`RequestProject/Main.lean`](RequestProject/Main.lean):

```lean
theorem Erdos319.erdos319_top_layer_exclusion
```

Informally, let

- `p` be prime,
- `A ⊆ {1, …, N}` be a signed-zero support,
- `δ : ℕ → ℤ` satisfy `δ n = ±1` on `A`,
- `A` be primitive in the official same-`δ` sense,
- `t = N / p`,
- `L t = lcm(1, …, t)`,
- `H t = ∑_{m=1}^t 1/m`.

If

```text
N / p < |A|
and
L(t) * H(t) < p,
```

then no element of `A` is divisible by `p`.

The Lean statement keeps the requested auxiliary hypothesis `N < p * p`; the proof currently clears it because the formal conclusion follows from the other hypotheses plus the bound. This condition remains useful informally because it helps make the bound attainable.

## Proof idea

Let `T = A.filter (fun n => p ∣ n)` be the `p`-divisible layer. Clearing denominators in the global signed-zero identity and reducing modulo `p` gives that a certain cleared top-layer integer `topW` is divisible by `p`.

The inequality `|topW| ≤ L(t) * H(t) < p` forces `topW = 0`, hence `T` is itself a signed-zero subset. By primitivity, either `T = ∅` or `T = A`. If `T = A`, then `|A| ≤ N / p`, contradicting `N / p < |A|`. Therefore `T = ∅`.

## How to verify

With Lean 4 and Lake:

```bash
lake exe cache get
lake build
```

The project uses:

```text
leanprover/lean4:v4.28.0
mathlib v4.28.0
```

You can also inspect the axioms of the main theorem in Lean:

```lean
#print axioms Erdos319.erdos319_top_layer_exclusion
```

## Provenance

This project was developed with help from Aristotle/Harmonic and AI-assisted proof engineering.

Suggested attribution for Aristotle-assisted commits:

```text
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

## Status

- finite Lean theorem: formalized
- asymptotic corollary such as `M(N) ≤ N - Ω(N log log N / log N)`: not formalized here
- full Erdős problem #319: still open
