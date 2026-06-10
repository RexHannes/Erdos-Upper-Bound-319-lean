# Summary of changes for run 3bf96c52-b59f-400f-89c8-43a4a5b04fc3

I formalized and proved the finite Erdős 319 top-layer exclusion lemma in `RequestProject/Main.lean` (namespace `Erdos319`). The build is clean (no warnings, no errors), contains no `sorry`, and the main theorem depends only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

Definitions (matching the official same-δ formulation):
- `SignedZero A δ : Prop := ∑ n ∈ A, (δ n : ℚ) / n = 0`.
- `DeltaPrimitive A δ : Prop := SignedZero A δ ∧ ∀ B, B ⊂ A → B.Nonempty → ¬ SignedZero B δ` (no nonempty proper subset is a signed-zero set, same δ).
- `Lfun t = lcm(1,…,t)` and `Hfun t = ∑_{m=1}^t 1/m`.

Main theorem `erdos319_top_layer_exclusion`: for prime `p`, `t = N / p`, `A ⊆ Finset.Icc 1 N`, and `δ : ℕ → ℤ` with `δ = ±1` on `A`, assuming `DeltaPrimitive A δ`, `t < A.card`, `N < p*p`, and `(L t : ℚ) * H t < p`, then `∀ n ∈ A, ¬ p ∣ n`.

Proof structure follows the suggested argument, decomposed into reusable lemmas:
- `topW` — the cleared-denominator integer `w = ∑_{p·m ∈ A, 1 ≤ m ≤ t} δ(p·m)·(L t / m)`.
- `signedZero_T_eq_topW` — reindexing the top layer `T = A.filter (p ∣ ·)` via `n ↦ n/p` shows `∑_{n∈T} δ n / n = w / (p·L t)`.
- `topW_abs_le` — `|w| ≤ L t · H t` (since `|δ| = 1` and each `m ∣ L t`).
- `p_dvd_topW` — clearing the denominators of the complementary (p-coprime) part and using that its product is coprime to `p` gives `p ∣ w`.
- `signedZero_filter_p` — combining `p ∣ w` with `|w| ≤ L t · H t < p` forces `w = 0`, hence the top layer is itself a signed-zero set.
- `card_le_t_of_all_dvd` — a set of multiples of `p` inside `{1,…,N}` has cardinality `≤ N/p`.

The main theorem assembles these: if some element of `A` is divisible by `p`, the top layer `T` is a nonempty signed-zero subset, so by primitivity `T = A`; then all of `A` consists of multiples of `p`, giving `A.card ≤ N/p`, contradicting `t < A.card`.

Note: the proof discovered is slightly stronger than requested — the hypothesis `N < p*p` is not actually needed for the implication. As requested it is kept in the statement (named `_hNpp` to mark it intentionally unused), and the docstring explains that its only role is to make the bound `L t · H t < p` attainable (it forces `t < p`).
