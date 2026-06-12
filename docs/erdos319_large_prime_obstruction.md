# A large-prime obstruction for Erdős Problem #319

**Status.**

- **Lean-verified:** the finite top-layer exclusion lemma in [`RequestProject/Main.lean`](../RequestProject/Main.lean), theorem `Erdos319.erdos319_top_layer_exclusion`.
- **Human proof:** the asymptotic corollaries in this note, using the Lean-verified finite lemma plus standard analytic number theory.
- **Optional / not yet Lean-formalized:** the second-order near-full-layer deterministic union-bound refinement in Section 7. The main advertised result uses only Sections 2--6.
- **Not claimed:** a solution to Erdős Problem #319.

**Rendering note.** This Markdown file intentionally uses plain-text formula blocks instead of GitHub-rendered LaTeX. This avoids GitHub/KaTeX parser errors such as “Extra open brace or missing close brace”. The mathematical content is the same proof note, but optimized for stable viewing on GitHub.

This note records a complementary upper-bound observation for [Erdős Problem #319](https://www.erdosproblems.com/319). It should be read together with the Lean formalization and [`ARISTOTLE_SUMMARY.md`](../ARISTOTLE_SUMMARY.md).

The finite Lean theorem proves a local obstruction: under explicit hypotheses, a primitive signed reciprocal zero-sum support cannot contain an element divisible by a large prime `p`. The asymptotic upper bound below is a human mathematical corollary of that finite lemma.

The note was prepared with GPT-5.5 Pro assistance. The finite Lean proof was produced with Aristotle/Harmonic and AI-assisted proof engineering.

---

## 1. Definition and main statement

All logarithms are natural. Let `M(N)` denote the maximum cardinality of a same-`δ` primitive signed reciprocal zero-sum support `A ⊆ [1,N]`.

Thus `A ⊆ [1,N]` is admissible if there is a sign function `δ : A → {-1,1}` such that

```text
sum_{n in A} δ(n)/n = 0,
```

and for every non-empty proper subset `B ⊊ A`,

```text
sum_{n in B} δ(n)/n != 0.
```

Here the signs on `B` are the inherited signs from the original `δ`. This is the same-`δ` support-minimality condition formalized in Lean as `DeltaPrimitive`.

The first-order conclusion is

```text
M(N) <= N - (1 + o(1)) * N log log N / log N.
```

A slightly sharper version gives

```text
M(N) <= N - (N / log N) * (log log N + γ - 1 + o(1)),
```

where `γ` is Euler's constant. This is only an `N-o(N)` upper bound, complementary to the Adenwalla--Croot lower bound recorded on the problem page.

---

## 2. The finite top-layer exclusion lemma

For `t >= 1`, write

```text
L_t = lcm(1,2,...,t),
H_t = sum_{m=1}^t 1/m.
```

### Lemma 1: finite top-layer exclusion

Let `p` be prime, let `A ⊆ [1,N]` be admissible with sign function `δ`, and put

```text
t = floor(N/p).
```

Assume the two separate hypotheses

```text
t < |A|,
```

and

```text
L_t * H_t < p.
```

Then no element of `A` is divisible by `p`; equivalently,

```text
A ∩ pZ = ∅.
```

This is the finite obstruction formalized in Lean as

```lean
theorem Erdos319.erdos319_top_layer_exclusion
```

in [`RequestProject/Main.lean`](../RequestProject/Main.lean).

### Lean audit note for Lemma 1

The potentially delicate `p`-adic layer isolation is not treated as a black box. In Lean it is split into separate lemmas, including:

1. `signedZero_T_eq_topW`, identifying the `p`-divisible layer sum with the cleared numerator `topW/(p*L_t)`;
2. `p_dvd_topW`, proving `p ∣ topW` after clearing the complementary `p`-coprime denominators;
3. `topW_abs_le`, bounding `|topW|` by `L_t H_t`;
4. `signedZero_filter_p`, concluding that the `p`-divisible layer is itself a same-`δ` signed-zero subset.

Thus the proof does not rely on an informal assertion that “lower layers vanish”; the top-layer extraction, divisibility, smallness, and primitive-support step are separated.

Prime powers require no separate treatment: the layer is defined by divisibility by `p`, not by exact valuation one.

### Proof of Lemma 1

Let

```text
T = { n in A : p divides n }
```

be the `p`-divisible layer of `A`. Every element of `T` has the form `pm`, where `1 <= m <= t`.

Define the cleared top-layer integer

```text
W_p(A,δ) = sum_{1 <= m <= t, pm in A} δ(pm) * L_t/m.
```

This is an integer because `m` divides `L_t` for every `1 <= m <= t`. The coefficients remain exactly the inherited signs `δ(pm)`; clearing denominators introduces the weights `L_t/m`, but after dividing by `L_t` this is exactly the original same-`δ` layer sum. No new signed representation with altered coefficients is being used.

The signed reciprocal sum over the top layer is

```text
sum_{n in T} δ(n)/n
  = sum_{1 <= m <= t, pm in A} δ(pm)/(pm)
  = W_p(A,δ)/(p L_t).
```

Now decompose `A = T disjoint-union R`, where

```text
R = { n in A : p does not divide n }.
```

The global zero-sum condition gives

```text
sum_{n in T} δ(n)/n + sum_{n in R} δ(n)/n = 0.
```

Let

```text
D = product_{n in R} n.
```

Since `p` divides no element of `R`, we have `p` does not divide `D`. Clearing denominators in the `R`-sum gives an integer `U` such that

```text
sum_{n in R} δ(n)/n = U/D.
```

Therefore

```text
W_p(A,δ)/(p L_t) + U/D = 0.
```

Multiplying by `p L_t D`, we get

```text
D W_p(A,δ) + p L_t U = 0.
```

Hence `p` divides `D W_p(A,δ)`. Since `p` does not divide `D`, it follows that

```text
p divides W_p(A,δ).
```

Next,

```text
|W_p(A,δ)|
  <= sum_{1 <= m <= t, pm in A} L_t/m
  <= sum_{m=1}^t L_t/m
  = L_t H_t.
```

By hypothesis, `L_t H_t < p`. Thus `|W_p(A,δ)| < p` and `p` divides `W_p(A,δ)`, so

```text
W_p(A,δ) = 0.
```

Consequently,

```text
sum_{n in T} δ(n)/n = 0.
```

So `T` is a same-`δ` zero-sum subset of `A`.

The primitive-support step is the following dichotomy. If `T = ∅`, we are done. If `T != ∅`, then `T` is a non-empty same-`δ` signed-zero subset of `A`. Since `A` is primitive, `T` cannot be a non-empty proper subset of `A`; hence `T = A`.

But if `T = A`, then every element of `A` is a multiple of `p`, and all such multiples inside `[1,N]` are

```text
p, 2p, ..., tp.
```

Therefore `|A| <= t`, contradicting `t < |A|`. Hence `T = ∅`, proving the lemma.

---

## 3. Making the lemma asymptotic

Let

```text
ψ(x) = log lcm(1,2,...,floor(x)).
```

By the prime number theorem in Chebyshev form,

```text
ψ(x) = x + o(x).
```

Also,

```text
H_t = sum_{m=1}^t 1/m = log t + γ + o(1).
```

Fix `0 < c < 1`, and put

```text
k_0 = floor(c log N).
```

Let `p > N/k_0`, and put

```text
t = floor(N/p).
```

Then `t < k_0 <= c log N`. We claim that, for all sufficiently large `N`,

```text
L_t H_t < p.
```

Indeed,

```text
log(L_t H_t)
  = log L_t + log H_t
  = ψ(t) + O(log log t).
```

Since `t <= c log N`, the prime number theorem gives

```text
ψ(t) <= (1+o(1)) t <= (c+o(1)) log N.
```

Because `c < 1`,

```text
(c+o(1)) log N + O(log log log N)
  < log N - log log N + O(1).
```

On the other hand, `p > N/k_0`, so

```text
log p > log N - log log N + O(1).
```

Thus, for large `N`, `log(L_t H_t) < log p`, and hence `L_t H_t < p`.

Therefore Lemma 1 applies to every prime

```text
p > N/k_0
```

whenever `|A| > k_0`. Hence an admissible support `A` with `|A| > k_0` contains no integer `n <= N` having a prime factor `p > N/k_0`.

---

## 4. Counting the excluded integers

For large `N`, an integer `n <= N` cannot have two distinct prime factors both exceeding `N/k_0`, because then

```text
n >= pq > N^2/k_0^2 > N,
```

since `k_0^2 = o(N)`. Therefore the excluded integers are counted without overlap by

```text
sum_{N/k_0 < p <= N} floor(N/p).
```

Prime powers do not create an overlap problem: the exclusion is attached to the unique large prime divisor `p`, and every multiple `pm <= N` is counted once through that prime.

We use the following standard estimate.

### Lemma 2: large-prime layer count

Let `K = K(N) -> infinity` with `K = O(log N)`. Then

```text
sum_{N/K < p <= N} floor(N/p)
  = (N/log N) * (log K + γ - 1 + o(1)).
```

### Proof of Lemma 2

Write `L = log N`. For a prime `p > N/K`,

```text
floor(N/p) = sum_{1 <= m < K} 1_{p <= N/m},
```

up to harmless endpoint errors. Therefore

```text
sum_{N/K < p <= N} floor(N/p)
  = sum_{1 <= m < K} (π(N/m) - π(N/K)) + o(N/log N).
```

Using the prime number theorem in the uniform form

```text
π(x) = x/log x + O(x/(log x)^2)
```

for `x >= N/K`, and using `K = O(log N)`, we have

```text
π(N/m) = (N/m)/(L - log m) + O((N/m)/L^2).
```

Hence

```text
sum_{1 <= m < K} π(N/m)
  = N sum_{1 <= m < K} 1/(m(L-log m))
    + O((N/L^2) sum_{1 <= m < K} 1/m).
```

Since

```text
1/(L-log m) = 1/L + O((log m)/L^2),
```

we get

```text
sum_{1 <= m < K} 1/(m(L-log m))
  = (1/L) sum_{1 <= m < K} 1/m
    + O((1/L^2) sum_{1 <= m < K} (log m)/m).
```

Now

```text
sum_{1 <= m < K} 1/m = log K + γ + o(1),
```

and

```text
sum_{1 <= m < K} (log m)/m = O((log K)^2) = o(L).
```

Thus

```text
sum_{1 <= m < K} π(N/m)
  = (N/L)(log K + γ + o(1)).
```

Also,

```text
(K-1)π(N/K) = N/L + o(N/L).
```

Therefore

```text
sum_{N/K < p <= N} floor(N/p)
  = (N/L)(log K + γ - 1 + o(1)),
```

as claimed.

---

## 5. First-order upper bound

Let `0 < c < 1` and `k_0 = floor(c log N)`.

If `|A| <= k_0`, then `|A| = O(log N)`, so the desired upper bound is trivial. Assume `|A| > k_0`.

By Lemma 1 and Section 3, `A` avoids every integer `n <= N` having a prime factor `p > N/k_0`. Hence

```text
N - |A| >= sum_{N/k_0 < p <= N} floor(N/p).
```

By Lemma 2,

```text
sum_{N/k_0 < p <= N} floor(N/p)
  = (N/log N)(log k_0 + γ - 1 + o(1)).
```

Since `k_0 = c log N + O(1)`,

```text
log k_0 = log log N + log c + o(1).
```

Thus

```text
N - |A|
  >= (N/log N)(log log N + log c + γ - 1 + o(1)).
```

For fixed `0 < c < 1`, this implies

```text
N - |A| >= (1+o(1)) N log log N / log N.
```

Therefore

```text
M(N) <= N - (1+o(1)) N log log N / log N.
```

---

## 6. Sharpening the constant to `γ-1`

The fixed-`c` proof gives

```text
N - |A|
  >= (N/log N)(log log N + log c + γ - 1 + o(1)).
```

To remove the `log c` loss, choose a cutoff

```text
K_N = (1 - η_N) log N,
```

where `η_N -> 0` and

```text
η_N log N / log log N -> infinity.
```

We also choose `η_N` slowly enough to dominate the relevant uniform error in `ψ(t)=t+o(t)` up to `t <= log N`. To make this quantifier explicit, choose a function `ρ(X) -> 0` such that, for all sufficiently large `X`,

```text
|ψ(x)-x| <= ρ(X) x       for all x >= X.
```

Let `X_N -> infinity` with `X_N = o(log N)`, for instance

```text
X_N = sqrt(log N).
```

For `t <= X_N`, we have

```text
ψ(t) + O(log log t) = o(log N),
```

so `L_t H_t < p` is immediate for every `p > N/K_N`.

For `X_N < t <= K_N`, we have

```text
ψ(t) <= (1+ρ(X_N)) t.
```

Choose `η_N` so slowly that

```text
η_N log N >> ρ(X_N) log N + log log N.
```

Then for every `t <= (1-η_N)log N`,

```text
ψ(t) + O(log log t)
  <= log N - η_N log N + o(η_N log N)
  < log N - log log N + O(1).
```

On the other hand, if `p > N/K_N`, then

```text
log p >= log N - log K_N
       = log N - log log N + o(1).
```

Thus

```text
L_t H_t < p
```

holds uniformly for all `t <= K_N` and all `p > N/K_N`.

Lemma 1 therefore excludes all multiples of primes `p > N/K_N`, and Lemma 2 gives

```text
N - |A| >= (N/log N)(log K_N + γ - 1 + o(1)).
```

Since `K_N = (1-o(1)) log N`,

```text
log K_N = log log N + o(1).
```

Therefore

```text
M(N) <= N - (N/log N)(log log N + γ - 1 + o(1)).
```

This is the cleanest human-verifiable asymptotic corollary of the Lean-checked finite lemma.

---

## 7. Optional deterministic union-bound refinement for near-full layers

This section is **not Lean-formalized** and should not be used to support the main advertised theorem. The main theorem of this note is contained in Sections 2--6. This section records a further human deterministic union-bound refinement suggested by counting possible cleared numerators of near-full `p`-adic layers.

Let `1 < β < 1/log 2` and `0 < δ < 1/2` satisfy

```text
β(log 2 + H(δ)) < 1,
```

where

```text
H(δ) = -δ log δ - (1-δ) log(1-δ).
```

The proposed refinement is

```text
M(N) <= N - (N/log N)(log log N + γ - 1 + δ log β + o(1)).
```

The extra term comes from primes with

```text
K_N < floor(N/p) <= B_N,
B_N = floor(β log N - 2β log log N).
```

For such primes, a deterministic union-bound argument shows that, for all but a negligible weighted set of primes, a `(1-δ)`-full `p`-layer is impossible inside a primitive support. Thus at least a `δ` proportion of each such layer must be missing.

The relevant counting input is the following.

### Lemma 3: near-full layers are impossible for almost all relevant primes

Let

```text
a = log 2 + H(δ),
aβ < 1.
```

For each `t`, define the prime interval

```text
I_t(N) = (N/(t+1), N/t].
```

For a subset `S ⊆ {1,...,t}` and signs `ε_m ∈ {-1,1}`, define

```text
W_{t,S,ε} = sum_{m in S} ε_m L_t/m.
```

Call a prime `p in I_t(N)` bad if there exists `S ⊆ {1,...,t}` with `|S| >= (1-δ)t` and signs `ε_m ∈ {-1,1}` such that

```text
W_{t,S,ε} != 0
and
p divides W_{t,S,ε}.
```

Then, in the range `t <= β log p`, the total weighted contribution of bad primes satisfies

```text
sum_{p bad, t=floor(N/p)} t = o(N/log N).
```

### Proof sketch of Lemma 3

For fixed `t`, the number of near-full subsets `S` is at most

```text
sum_{j <= δt} binom(t,j) <= exp((H(δ)+o(1))t).
```

For each such `S`, there are at most `2^t` sign choices. Hence the number of possible nonzero integers `W_{t,S,ε}` is at most

```text
exp((log 2 + H(δ) + o(1))t) = exp((a+o(1))t).
```

This is only a union bound over possible cleared numerators; no probabilistic independence between layers or primes is being assumed.

For fixed `t`, a fixed nonzero `W_{t,S,ε}` has at most one prime divisor in `I_t(N)` for large `N`: indeed,

```text
|W_{t,S,ε}| <= L_t H_t = exp((1+o(1))t),
```

while the product of two distinct primes in `I_t(N)` is at least

```text
(N/(t+1))^2 = N^(2-o(1)).
```

Since `t <= β log p` and `β < 1/log 2 < 2`, this product eventually exceeds `|W_{t,S,ε}|`. Therefore the number of bad primes in the `t`-th layer is at most `exp((a+o(1))t)`.

Summing over `t <= (β+o(1))log N`, the bad weighted contribution is at most

```text
sum_{t <= (β+o(1))log N} t exp((a+o(1))t) = o(N/log N),
```

because `aβ < 1`.

### Zero-numerator case and primitivity

Suppose a near-full `p`-layer occurs in a primitive support `A`. Let `S` be its index set and let `W_{t,S,ε}` be the corresponding cleared numerator. The same `p`-adic extraction as in Lemma 1 gives

```text
p divides W_{t,S,ε}.
```

If `W_{t,S,ε} != 0`, then `p` is bad by definition.

If `W_{t,S,ε} = 0`, then the `p`-layer is itself a nonempty same-`δ` signed-zero subset of `A`. In the Section 7 application we are in the case `|A| > B_N`, while the `p`-layer has size at most `t <= B_N`; hence this layer cannot equal all of `A`. It is therefore a nonempty proper same-`δ` zero-subset, contradicting primitivity.

Therefore, for a good prime in the Section 7 range, a near-full `p`-layer cannot occur.

### Consequence for the upper bound

For good primes in the range `K_N < t <= B_N`, the `p`-layer of a primitive support cannot be `(1-δ)`-full. Thus at least `δt+O(1)` multiples of `p` are missing.

The relevant layers are disjoint because an integer `n <= N` cannot have two prime factors both exceeding `N/B_N`, and `B_N = O(log N)`.

The first-stage exclusion contributes

```text
(N/log N)(log log N + γ - 1 + o(1)),
```

and the second-stage near-full exclusion contributes

```text
δ sum_{N/B_N < p <= N/K_N} floor(N/p)
  = δ (N/log N)(log β + o(1)).
```

Combining the two stages gives

```text
M(N) <= N - (N/log N)(log log N + γ - 1 + δ log β + o(1)).
```

For example, taking `δ=0.04` and `β=1.16`,

```text
β(log 2 + H(δ)) ≈ 0.9988 < 1,
δ log β ≈ 0.00594.
```

This improves only the `N/log N`-level constant, not the leading term. Again, this entire section remains a separate human refinement pending Lean verification.

---

## 8. Verification status

The best status split is:

1. **Lean-verified finite theorem.**
   `Erdos319.erdos319_top_layer_exclusion` is formalized in Lean 4.

2. **Human-verifiable asymptotic corollary.**
   The bound

   ```text
   M(N) <= N - (1+o(1)) N log log N / log N
   ```

   follows from the Lean lemma plus standard analytic number theory.

3. **Sharper human-verifiable corollary.**
   With a moving cutoff,

   ```text
   M(N) <= N - (N/log N)(log log N + γ - 1 + o(1)).
   ```

4. **Optional / not yet Lean-formalized.**
   The second-order refinement

   ```text
   M(N) <= N - (N/log N)(log log N + γ - 1 + δ log β + o(1))
   ```

   depends on the additional deterministic union-bound near-full-layer argument in Section 7. It should be treated as a separate lemma pending formal verification.

Again, none of the above is claimed as a solution to Erdős Problem #319.
