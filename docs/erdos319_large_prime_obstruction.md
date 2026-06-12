# A large-prime obstruction for Erdős Problem #319

**Status.**

- **Lean-verified:** the finite top-layer exclusion lemma in [`RequestProject/Main.lean`](../RequestProject/Main.lean), theorem `Erdos319.erdos319_top_layer_exclusion`.
- **Human proof:** the asymptotic corollaries in this note, using the Lean-verified finite lemma plus standard analytic number theory.
- **Not yet Lean-formalized:** the second-order near-full-layer refinement in Section 6.
- **Not claimed:** a solution to Erdős Problem #319.

This note records a complementary upper-bound observation for [Erdős Problem #319](https://www.erdosproblems.com/319). It should be read together with the Lean formalization and [`ARISTOTLE_SUMMARY.md`](../ARISTOTLE_SUMMARY.md).

The finite Lean theorem proves a local obstruction: under explicit hypotheses, a primitive signed reciprocal zero-sum support cannot contain an element divisible by a large prime `p`. The asymptotic upper bound below is a human mathematical corollary of that finite lemma.

The note was prepared with GPT-5.5 Pro assistance. The finite Lean proof was produced with Aristotle/Harmonic and AI-assisted proof engineering.

---

## 1. Definition and main asymptotic statement

All logarithms are natural. Let `M(N)` denote the maximum cardinality of a same-`δ` primitive signed reciprocal zero-sum support `A ⊆ [1,N]`.

Thus `A ⊆ [1,N]` is admissible if there is a sign function `δ : A → {-1,1}` such that

$$
\sum_{n\in A}\frac{\delta(n)}{n}=0,
$$

and for every non-empty proper subset `B ⊊ A`,

$$
\sum_{n\in B}\frac{\delta(n)}{n}\ne 0.
$$

The first-order conclusion is

$$
M(N)\le N-(1+o(1))\frac{N\log\log N}{\log N}.
$$

A slightly sharper version gives

$$
M(N)\le
N-\frac{N}{\log N}\left(\log\log N+\gamma-1+o(1)\right),
$$

where `γ` is Euler's constant.

This is only an `N-o(N)` upper bound. It is complementary to the Adenwalla--Croot lower bound recorded on the problem page.

---

## 2. The finite top-layer exclusion lemma

For `t ≥ 1`, write

$$
L_t=\operatorname{lcm}(1,2,\ldots,t),
\qquad
H_t=\sum_{m=1}^{t}\frac1m.
$$

### Lemma 1: finite top-layer exclusion

Let `p` be prime, let `A ⊆ [1,N]` be admissible with sign function `δ`, and put

$$
t=\left\lfloor\frac{N}{p}\right\rfloor.
$$

Assume

$$
t<|A|
\qquad\text{and}\qquad
L_tH_t<p.
$$

Then no element of `A` is divisible by `p`; equivalently,

$$
A\cap p\mathbb Z=\varnothing.
$$

This is the finite obstruction formalized in Lean as

```lean
theorem Erdos319.erdos319_top_layer_exclusion
```

in [`RequestProject/Main.lean`](../RequestProject/Main.lean).

### Proof of Lemma 1

Let

$$
T=\{n\in A:p\mid n\}
$$

be the `p`-divisible layer of `A`. Every `n ∈ T` has the form `n=pm`, where `1≤m≤t`.

Define the cleared top-layer integer

$$
W_p(A,\delta)
=
\sum_{\substack{1\le m\le t\\ pm\in A}}
\delta(pm)\frac{L_t}{m}.
$$

This is an integer because `m | L_t` for every `1≤m≤t`. The signed reciprocal sum over the top layer is

$$
\sum_{n\in T}\frac{\delta(n)}{n}
=
\sum_{\substack{1\le m\le t\\ pm\in A}}\frac{\delta(pm)}{pm}
=
\frac{W_p(A,\delta)}{pL_t}.
$$

Now decompose `A=T ⊔ R`, where

$$
R=\{n\in A:p\nmid n\}.
$$

The global zero-sum condition gives

$$
\sum_{n\in T}\frac{\delta(n)}{n}
+
\sum_{n\in R}\frac{\delta(n)}{n}
=0.
$$

Let

$$
D=\prod_{n\in R}n.
$$

Since `p ∤ n` for every `n ∈ R`, we have `p ∤ D`. Clearing denominators in the `R`-sum gives an integer `U` such that

$$
\sum_{n\in R}\frac{\delta(n)}{n}=\frac{U}{D}.
$$

Therefore

$$
\frac{W_p(A,\delta)}{pL_t}+\frac{U}{D}=0.
$$

Multiplying by `pL_tD`, we get

$$
DW_p(A,\delta)+pL_tU=0.
$$

Hence `p | DW_p(A,δ)`. Since `p ∤ D`, it follows that

$$
p\mid W_p(A,\delta).
$$

Next,

$$
|W_p(A,\delta)|
\le
\sum_{\substack{1\le m\le t\\ pm\in A}}
\frac{L_t}{m}
\le
\sum_{m=1}^{t}\frac{L_t}{m}
=L_tH_t.
$$

By hypothesis, `L_tH_t<p`. Thus `|W_p(A,δ)|<p` and `p | W_p(A,δ)`, so

$$
W_p(A,\delta)=0.
$$

Consequently,

$$
\sum_{n\in T}\frac{\delta(n)}{n}=0.
$$

So `T` is a same-`δ` zero-sum subset of `A`.

If `T=∅`, we are done. Suppose `T≠∅`. Since `A` is primitive, no non-empty proper subset of `A` can be a same-`δ` zero-sum. Hence `T=A`.

But if `T=A`, then every element of `A` is a multiple of `p`, and all such multiples inside `[1,N]` are

$$
p,2p,\ldots,tp.
$$

Therefore `|A|≤t`, contradicting `t<|A|`. Hence `T=∅`, proving the lemma.

---

## 3. Making the lemma asymptotic

Let

$$
\psi(x)=\log\operatorname{lcm}(1,2,\ldots,\lfloor x\rfloor).
$$

By the prime number theorem in Chebyshev form,

$$
\psi(x)=x+o(x).
$$

Also,

$$
H_t=\sum_{m=1}^{t}\frac1m=\log t+\gamma+o(1).
$$

Fix `0<c<1`, and put

$$
k_0=\lfloor c\log N\rfloor.
$$

Let `p>N/k_0`, and let

$$
t=\left\lfloor\frac{N}{p}\right\rfloor.
$$

Then `t<k_0≤c log N`. We claim that for all sufficiently large `N`,

$$
L_tH_t<p.
$$

Indeed,

$$
\log(L_tH_t)
=\log L_t+\log H_t
=\psi(t)+O(\log\log t).
$$

Since `t≤c log N`, the prime number theorem gives

$$
\psi(t)\le (1+o(1))t\le (c+o(1))\log N.
$$

Because `c<1`,

$$
(c+o(1))\log N+O(\log\log\log N)
<
\log N-\log\log N+O(1).
$$

On the other hand, `p>N/k_0`, so

$$
\log p>
\log N-\log\log N+O(1).
$$

Thus, for large `N`,

$$
\log(L_tH_t)<\log p,
$$

and hence `L_tH_t<p`.

Therefore Lemma 1 applies to every prime

$$
p>\frac{N}{k_0}
$$

whenever `|A|>k_0`. Hence an admissible support `A` with `|A|>k_0` contains no integer `n≤N` having a prime factor `p>N/k_0`.

---

## 4. Counting the excluded integers

For large `N`, an integer `n≤N` cannot have two distinct prime factors both exceeding `N/k_0`, because then

$$
n\ge pq>\frac{N^2}{k_0^2}>N,
$$

since `k_0^2=o(N)`. Therefore the excluded integers are counted without overlap by

$$
\sum_{N/k_0<p\le N}\left\lfloor\frac{N}{p}\right\rfloor.
$$

We use the following standard estimate.

### Lemma 2: large-prime layer count

Let `K=K(N)→∞` with `K=O(log N)`. Then

$$
\sum_{N/K<p\le N}\left\lfloor\frac{N}{p}\right\rfloor
=
\frac{N}{\log N}\left(\log K+\gamma-1+o(1)\right).
$$

### Proof of Lemma 2

Write `L=log N`. For a prime `p>N/K`,

$$
\left\lfloor\frac{N}{p}\right\rfloor
=
\sum_{1\le m<K}\mathbf 1_{p\le N/m},
$$

up to harmless endpoint errors. Therefore

$$
\sum_{N/K<p\le N}\left\lfloor\frac{N}{p}\right\rfloor
=
\sum_{1\le m<K}\left(\pi(N/m)-\pi(N/K)\right)+o\left(\frac{N}{\log N}\right).
$$

Using the prime number theorem in the uniform form

$$
\pi(x)=\frac{x}{\log x}+O\left(\frac{x}{(\log x)^2}\right)
$$

for `x≥N/K`, and using `K=O(log N)`, we have

$$
\pi(N/m)
=
\frac{N/m}{L-\log m}+O\left(\frac{N/m}{L^2}\right).
$$

Hence

$$
\sum_{1\le m<K}\pi(N/m)
=
N\sum_{1\le m<K}\frac{1}{m(L-\log m)}
+O\left(\frac{N}{L^2}\sum_{1\le m<K}\frac1m\right).
$$

Since

$$
\frac1{L-\log m}
=
\frac1L+O\left(\frac{\log m}{L^2}\right),
$$

we get

$$
\sum_{1\le m<K}\frac{1}{m(L-\log m)}
=
\frac1L\sum_{1\le m<K}\frac1m
+O\left(\frac1{L^2}\sum_{1\le m<K}\frac{\log m}{m}\right).
$$

Now

$$
\sum_{1\le m<K}\frac1m=\log K+\gamma+o(1),
$$

and

$$
\sum_{1\le m<K}\frac{\log m}{m}=O((\log K)^2)=o(L).
$$

Thus

$$
\sum_{1\le m<K}\pi(N/m)
=
\frac{N}{L}(\log K+\gamma+o(1)).
$$

Also,

$$
(K-1)\pi(N/K)=\frac{N}{L}+o\left(\frac{N}{L}\right).
$$

Therefore

$$
\sum_{N/K<p\le N}\left\lfloor\frac{N}{p}\right\rfloor
=
\frac{N}{L}\left(\log K+\gamma-1+o(1)\right),
$$

as claimed.

---

## 5. First-order upper bound

Let `0<c<1` and `k_0=⌊c log N⌋`.

If `|A|≤k_0`, then `|A|=O(log N)`, so the desired upper bound is trivial. Assume `|A|>k_0`.

By Lemma 1 and Section 3, `A` avoids every integer `n≤N` having a prime factor `p>N/k_0`. Hence

$$
N-|A|
\ge
\sum_{N/k_0<p\le N}\left\lfloor\frac{N}{p}\right\rfloor.
$$

By Lemma 2,

$$
\sum_{N/k_0<p\le N}\left\lfloor\frac{N}{p}\right\rfloor
=
\frac{N}{\log N}\left(\log k_0+\gamma-1+o(1)\right).
$$

Since `k_0=c log N+O(1)`,

$$
\log k_0=\log\log N+\log c+o(1).
$$

Thus

$$
N-|A|
\ge
\frac{N}{\log N}\left(\log\log N+\log c+\gamma-1+o(1)\right).
$$

For fixed `0<c<1`, this implies

$$
N-|A|\ge(1+o(1))\frac{N\log\log N}{\log N}.
$$

Therefore

$$
M(N)\le N-(1+o(1))\frac{N\log\log N}{\log N}.
$$

---

## 6. Sharpening the constant to `γ-1`

The fixed-`c` proof gives

$$
N-|A|
\ge
\frac{N}{\log N}\left(\log\log N+\log c+\gamma-1+o(1)\right).
$$

To remove the `log c` loss, choose a cutoff

$$
K_N=(1-\eta_N)\log N,
$$

where `η_N→0`, `η_N log N / log log N →∞`, and `η_N` also dominates the uniform `o(1)` error in `ψ(t)=t+o(t)` for `t≤log N`.

Then the estimate

$$
L_tH_t<p
$$

holds uniformly for all `t≤K_N` and all `p>N/K_N`. Indeed,

$$
\log(L_tH_t)=\psi(t)+O(\log\log t)=t+o(t)+O(\log\log t),
$$

while

$$
\log p\ge\log N-\log K_N
=
\log N-\log\log N+o(1).
$$

The choice of `η_N` absorbs the `o(t)` and `O(log log t)` terms.

Lemma 1 therefore excludes all multiples of primes `p>N/K_N`, and Lemma 2 gives

$$
N-|A|
\ge
\frac{N}{\log N}\left(\log K_N+\gamma-1+o(1)\right).
$$

Since `K_N=(1-o(1))log N`,

$$
\log K_N=\log\log N+o(1).
$$

Therefore

$$
M(N)\le
N-\frac{N}{\log N}\left(\log\log N+\gamma-1+o(1)\right).
$$

This is the cleanest human-verifiable asymptotic corollary of the Lean-checked finite lemma.

---

## 7. Optional second-order near-full-layer refinement

This section is **not Lean-formalized**. It records a further human asymptotic refinement suggested by a first-moment count of near-full `p`-adic layers.

Let `1<β<1/log 2` and `0<δ<1/2` satisfy

$$
\beta(\log 2+\mathcal H(\delta))<1,
$$

where

$$
\mathcal H(\delta)
=
-\delta\log\delta-(1-\delta)\log(1-\delta).
$$

The proposed refinement is

$$
M(N)\le
N-\frac{N}{\log N}
\left(
\log\log N+\gamma-1+\delta\log\beta+o(1)
\right).
$$

The extra term comes from primes with

$$
K_N<\left\lfloor\frac{N}{p}\right\rfloor\le B_N,
\qquad
B_N=\left\lfloor\beta\log N-2\beta\log\log N\right\rfloor.
$$

For such primes, a first-moment argument shows that for all but a negligible weighted set of primes, a `(1-δ)`-full `p`-layer is impossible inside a primitive support. Thus at least a `δ` proportion of each such layer must be missing.

The relevant counting input is the following.

### Lemma 3: near-full layers are impossible for almost all relevant primes

Let

$$
a=\log 2+\mathcal H(\delta),
\qquad
 a\beta<1.
$$

For each `t`, define the prime interval

$$
I_t(N)=\left(\frac{N}{t+1},\frac Nt\right].
$$

For a subset `S⊆{1,…,t}` and signs `ε_m∈{-1,1}`, define

$$
W_{t,S,\varepsilon}
=
\sum_{m\in S}\varepsilon_m\frac{L_t}{m}.
$$

Call a prime `p∈I_t(N)` bad if there exists `S⊆{1,…,t}` with `|S|≥(1-δ)t` and signs `ε_m∈{-1,1}` such that

$$
W_{t,S,\varepsilon}\ne0
\qquad\text{and}\qquad
p\mid W_{t,S,\varepsilon}.
$$

Then, in the range `t≤β log p`, the total weighted contribution of bad primes satisfies

$$
\sum_{\substack{p\ \mathrm{bad}\\ t=\lfloor N/p\rfloor}} t
=
o\left(\frac{N}{\log N}\right).
$$

### Proof sketch of Lemma 3

For fixed `t`, the number of near-full subsets `S` is at most

$$
\sum_{j\le\delta t}\binom tj
\le
\exp((\mathcal H(\delta)+o(1))t).
$$

For each such `S`, there are at most `2^t` sign choices. Hence the number of possible nonzero integers `W_{t,S,ε}` is at most

$$
\exp((\log2+\mathcal H(\delta)+o(1))t)
=
\exp((a+o(1))t).
$$

For fixed `t`, a fixed nonzero `W_{t,S,ε}` has at most one prime divisor in `I_t(N)` for large `N`: indeed,

$$
|W_{t,S,\varepsilon}|
\le
L_tH_t
=
\exp((1+o(1))t),
$$

while the product of two distinct primes in `I_t(N)` is at least

$$
\left(\frac{N}{t+1}\right)^2=N^{2-o(1)}.
$$

Since `t≤β log p` and `β<1/log2<2`, this product eventually exceeds `|W_{t,S,ε}|`. Therefore the number of bad primes in the `t`-th layer is at most `exp((a+o(1))t)`.

Summing over `t≤(β+o(1))log N`, the bad weighted contribution is at most

$$
\sum_{t\le(\beta+o(1))\log N}t\exp((a+o(1))t)
=
o\left(\frac{N}{\log N}\right),
$$

because `aβ<1`.

This proves the claimed first-moment estimate.

### Consequence for the upper bound

For good primes in the range `K_N<t≤B_N`, the `p`-layer of a primitive support cannot be `(1-δ)`-full. Thus at least `δt+O(1)` multiples of `p` are missing.

The relevant layers are disjoint because an integer `n≤N` cannot have two prime factors both exceeding `N/B_N`.

The first-stage exclusion contributes

$$
\frac{N}{\log N}\left(\log\log N+\gamma-1+o(1)\right),
$$

and the second-stage near-full exclusion contributes

$$
\delta
\sum_{N/B_N<p\le N/K_N}\left\lfloor\frac Np\right\rfloor
=
\delta\frac{N}{\log N}\left(\log\beta+o(1)\right).
$$

Combining the two stages gives

$$
M(N)\le
N-\frac{N}{\log N}
\left(
\log\log N+\gamma-1+\delta\log\beta+o(1)
\right).
$$

For example, taking `δ=0.04` and `β=1.16`,

$$
\beta(\log2+\mathcal H(\delta))\approx0.9988<1,
$$

and

$$
\delta\log\beta\approx0.00594.
$$

This improves only the `N/log N`-level constant, not the leading term.

---

## 8. Verification status

The best status split is:

1. **Lean-verified finite theorem.**  
   `Erdos319.erdos319_top_layer_exclusion` is formalized in Lean 4.

2. **Human-verifiable asymptotic corollary.**  
   The bound
   $$
   M(N)\le N-(1+o(1))\frac{N\log\log N}{\log N}
   $$
   follows from the Lean lemma plus standard analytic number theory.

3. **Sharper human-verifiable corollary.**  
   With a moving cutoff,
   $$
   M(N)\le
   N-\frac{N}{\log N}\left(\log\log N+\gamma-1+o(1)\right).
   $$

4. **Not yet Lean-formalized.**  
   The second-order refinement
   $$
   M(N)\le
   N-\frac{N}{\log N}
   \left(\log\log N+\gamma-1+\delta\log\beta+o(1)\right)
   $$
   depends on the additional near-full-layer first-moment argument in Section 7.

Again, none of the above is claimed as a solution to Erdős Problem #319.
