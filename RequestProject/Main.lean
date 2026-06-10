import Mathlib

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace Erdos319

/-- Official same-`δ` signed-zero condition:
`∑_{n ∈ A} δ n / n = 0` (as a rational). -/
def SignedZero (A : Finset ℕ) (δ : ℕ → ℤ) : Prop :=
  ∑ n ∈ A, (δ n : ℚ) / (n : ℚ) = 0

/-- Official primitivity: `A` is a signed-zero set, and no nonempty *proper* subset
`B ⊂ A` is itself a signed-zero set (using the same `δ`). -/
def DeltaPrimitive (A : Finset ℕ) (δ : ℕ → ℤ) : Prop :=
  SignedZero A δ ∧ ∀ B : Finset ℕ, B ⊂ A → B.Nonempty → ¬ SignedZero B δ

/-- `L t = lcm(1, …, t)`. -/
def Lfun (t : ℕ) : ℕ := (Finset.Icc 1 t).lcm id

/-- `H t = ∑_{m=1}^t 1/m`. -/
def Hfun (t : ℕ) : ℚ := ∑ m ∈ Finset.Icc 1 t, (1 : ℚ) / (m : ℚ)

/-- The cleared-denominator integer associated to the top layer:
`w = ∑_{m : p·m ∈ A, 1 ≤ m ≤ t} δ(p·m) · (L t / m)`. -/
noncomputable def topW (p t : ℕ) (A : Finset ℕ) (δ : ℕ → ℤ) : ℤ :=
  ∑ m ∈ (Finset.Icc 1 t).filter (fun m => p * m ∈ A),
    δ (p * m) * ((Lfun t / m : ℕ) : ℤ)

/-- Every `m ∈ {1, …, t}` divides `L t`. -/
lemma dvd_Lfun {t m : ℕ} (hm : m ∈ Finset.Icc 1 t) : m ∣ Lfun t := by
  exact Finset.dvd_lcm hm

/-- `L t > 0`. -/
lemma Lfun_pos (t : ℕ) : 0 < Lfun t := by
  exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) )

/-- The signed sum over the top layer equals `w / (p · L t)`, where `t = N / p`. -/
lemma signedZero_T_eq_topW
    {p N : ℕ} (hp : p.Prime) {A : Finset ℕ} {δ : ℕ → ℤ}
    (hA : A ⊆ Finset.Icc 1 N) :
    ∑ n ∈ (A.filter (fun n => p ∣ n)), (δ n : ℚ) / (n : ℚ)
      = (topW p (N / p) A δ : ℚ) / ((p : ℚ) * (Lfun (N / p) : ℚ)) := by
  -- `T = A.filter (p ∣ ·)` is in bijection with
  -- `M := (Finset.Icc 1 (N / p)).filter (p * · ∈ A)` via `n ↦ n / p` (inverse `m ↦ p * m`).
  have h_bij : Finset.filter (fun n => p ∣ n) A = Finset.image (fun m => p * m) ((Finset.Icc 1 (N / p)).filter (fun m => p * m ∈ A)) := by
    ext n; simp [Finset.mem_image];
    constructor;
    · rintro ⟨ hn, hpn ⟩;
      exact ⟨ n / p, ⟨ ⟨ Nat.div_pos ( Nat.le_of_dvd ( Finset.mem_Icc.mp ( hA hn ) |>.1 ) hpn ) hp.pos, Nat.div_le_div_right ( Finset.mem_Icc.mp ( hA hn ) |>.2 ) ⟩, by rwa [ Nat.mul_div_cancel' hpn ] ⟩, by rw [ Nat.mul_div_cancel' hpn ] ⟩;
    · aesop;
  simp_all +decide;
  rw [ Finset.sum_image ] <;> norm_num [ mul_comm p, topW ];
  · rw [ Finset.sum_div _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ Int.cast_div ] <;> norm_num ; ring_nf;
    · rw [ mul_inv_cancel_right₀ ( Nat.cast_ne_zero.mpr <| ne_of_gt <| Lfun_pos _ ) ];
    · exact_mod_cast dvd_Lfun ( Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ⟩ );
    · linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) ];
  · exact fun x hx y hy hxy => mul_right_cancel₀ hp.ne_zero hxy

/-- The cleared integer `w` is bounded in absolute value by `L t · H t`. -/
lemma topW_abs_le
    {p t : ℕ} {A : Finset ℕ} {δ : ℕ → ℤ}
    (hδ : ∀ n ∈ A, δ n = 1 ∨ δ n = -1) :
    |(topW p t A δ : ℚ)| ≤ (Lfun t : ℚ) * Hfun t := by
  set M := (Finset.Icc 1 t).filter (fun m => p * m ∈ A) with hM;
  have h_topW_sum : abs ((topW p t A δ : ℚ)) ≤ ∑ m ∈ M, (Lfun t : ℚ) / (m : ℚ) := by
    have h_topW_sum : abs ((topW p t A δ : ℚ)) = abs (∑ m ∈ M, (δ (p * m) : ℚ) * ((Lfun t : ℚ) / (m : ℚ))) := by
      unfold topW; norm_num;
      exact congr_arg _ ( Finset.sum_congr rfl fun x hx => by rw [ Int.cast_div ( mod_cast dvd_Lfun ( Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) ], by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) ] ⟩ ) ) ( by aesop ) ] ; push_cast; ring );
    rw [h_topW_sum];
    exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun x hx => by rcases hδ ( p * x ) ( Finset.mem_filter.mp hx |>.2 ) with h | h <;> rw [ h ] <;> norm_num [ abs_mul, abs_div, abs_of_nonneg, div_nonneg, Nat.cast_nonneg ] );
  refine le_trans h_topW_sum ?_;
  norm_num [ div_eq_mul_inv, Finset.mul_sum _ _ _, Hfun ];
  exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => by positivity;

/-- The prime `p` divides the cleared integer `w` (where `t = N / p`). -/
lemma p_dvd_topW
    {p N : ℕ} (hp : p.Prime) {A : Finset ℕ} {δ : ℕ → ℤ}
    (hA : A ⊆ Finset.Icc 1 N)
    (hS : SignedZero A δ) :
    (p : ℤ) ∣ topW p (N / p) A δ := by
  -- Split `A` into the multiples of `p` (`T`) and the rest (`R`); the global sum is `0`.
  set t := N / p
  set T := A.filter (fun n => p ∣ n)
  set R := A.filter (fun n => ¬ p ∣ n)
  have h_sum_zero : (∑ n ∈ T, ((δ n) : ℚ) / n) + (∑ n ∈ R, ((δ n) : ℚ) / n) = 0 := by
    rw [ Finset.sum_filter_add_sum_filter_not ] ; aesop;
  -- `K = ∏_{n ∈ R} n` is positive and coprime to `p`; every `n ∈ R` divides `K`.
  set K := ∏ n ∈ R, n
  have hK_pos : 0 < K := by
    exact Finset.prod_pos fun x hx => Finset.mem_Icc.mp ( hA ( Finset.mem_filter.mp hx |>.1 ) ) |>.1
  have hK_ne_zero : K ≠ 0 := by
    positivity
  have hK_div : ∀ n ∈ R, n ∣ K := by
    exact fun n hn => Finset.dvd_prod_of_mem _ hn;
  -- Clear denominators of the `R`-sum: `∑_{n ∈ R} δ n / n = r / K` for an integer `r`.
  set r := ∑ n ∈ R, δ n * ((K / n : ℕ) : ℤ)
  have h_sum_R : (∑ n ∈ R, ((δ n) : ℚ) / n) = (r : ℚ) / K := by
    simp +zetaDelta at *;
    rw [ Finset.sum_div _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ Int.cast_div ] <;> norm_num;
    · rw [ eq_div_iff ( Finset.prod_ne_zero_iff.mpr fun y hy => Nat.cast_ne_zero.mpr <| ne_of_gt <| hK_pos y ( Finset.mem_filter.mp hy |>.1 ) <| Finset.mem_filter.mp hy |>.2 ) ] ; ring;
    · exact Finset.dvd_prod_of_mem _ hx;
    · linarith [ hK_pos x ( Finset.filter_subset _ _ hx ) ( Finset.mem_filter.mp hx |>.2 ) ];
  -- Cross-multiply and pass to an integer identity `topW · K = -p · L t · r`.
  have h_cross_mul : (topW p t A δ : ℚ) * K = -(p : ℚ) * (Lfun t : ℚ) * r := by
    have h_cross_mul : (topW p t A δ : ℚ) / ((p : ℚ) * (Lfun t : ℚ)) = -(r : ℚ) / K := by
      convert eq_neg_of_add_eq_zero_left h_sum_zero using 1;
      · convert signedZero_T_eq_topW hp hA |> Eq.symm using 1;
      · rw [ h_sum_R, neg_div ];
    rw [ div_eq_div_iff ] at h_cross_mul <;> norm_cast at * <;> simp_all +decide [ Nat.Prime.ne_zero ];
    · ring;
    · exact Nat.ne_of_gt <| Lfun_pos _;
  have h_int_eq : (topW p t A δ : ℤ) * K = -(p : ℤ) * (Lfun t : ℤ) * r := by
    exact_mod_cast h_cross_mul;
  -- `p ∣ topW · K` and `p ∤ K`, so `p ∣ topW`.
  exact Or.resolve_right ( Int.Prime.dvd_mul' hp <| h_int_eq.symm ▸ dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( dvd_neg.mpr <| dvd_refl _ ) _ ) _ ) ( by norm_cast; exact fun h => absurd ( hp.dvd_iff_not_coprime.mp h ) ( by exact fun h' => h' <| Nat.Coprime.prod_right fun x hx => hp.coprime_iff_not_dvd.mpr <| by aesop ) )

/-- The heart of the argument: the "top layer" `T = A.filter (p ∣ ·)` is itself a
signed-zero set. -/
lemma signedZero_filter_p
    {p N : ℕ} (hp : p.Prime) {A : Finset ℕ} {δ : ℕ → ℤ}
    (hA : A ⊆ Finset.Icc 1 N)
    (hδ : ∀ n ∈ A, δ n = 1 ∨ δ n = -1)
    (hbound : (Lfun (N / p) : ℚ) * Hfun (N / p) < (p : ℚ))
    (hS : SignedZero A δ) :
    SignedZero (A.filter (fun n => p ∣ n)) δ := by
  -- `w = 0` because `p ∣ w` and `|w| < p`.
  have hdvd : (p : ℤ) ∣ topW p (N / p) A δ := p_dvd_topW hp hA hS
  have hbd : |(topW p (N / p) A δ : ℚ)| ≤ (Lfun (N / p) : ℚ) * Hfun (N / p) := topW_abs_le hδ
  have hlt : |(topW p (N / p) A δ : ℚ)| < (p : ℚ) := lt_of_le_of_lt hbd hbound
  have habs : |topW p (N / p) A δ| < (p : ℤ) := by
    have : (|topW p (N / p) A δ| : ℚ) < (p : ℚ) := by
      rw [← Int.cast_abs]; exact_mod_cast hlt
    exact_mod_cast this
  have hzero : topW p (N / p) A δ = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  unfold SignedZero
  rw [signedZero_T_eq_topW hp hA, hzero]
  simp only [Int.cast_zero, zero_div]

/-- If every element of `A ⊆ {1,…,N}` is a multiple of `p`, then `A.card ≤ N / p`. -/
lemma card_le_t_of_all_dvd
    {p N : ℕ} (hp : p.Prime) {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N)
    (hdvd : ∀ n ∈ A, p ∣ n) :
    A.card ≤ N / p := by
  -- The multiples of `p` in `{1,…,N}` are `{p·1, …, p·⌊N/p⌋}`.
  have h_subset : A ⊆ Finset.image (fun k => k * p) (Finset.Icc 1 (N / p)) := by
    intro n hn; specialize hdvd n hn; rcases hdvd with ⟨ k, rfl ⟩ ; exact Finset.mem_image.mpr ⟨ k, Finset.mem_Icc.mpr ⟨ by nlinarith [ Finset.mem_Icc.mp ( hA hn ) ], by nlinarith [ Finset.mem_Icc.mp ( hA hn ), Nat.div_add_mod N p, Nat.mod_lt N hp.pos ] ⟩, by ring ⟩ ;
  exact le_trans ( Finset.card_le_card h_subset ) ( Finset.card_image_le.trans ( by simp ) )

/-- **Erdős 319 finite top-layer exclusion lemma.**
Let `p` be prime, `t = N / p`, `A ⊆ {1, …, N}`, and `δ : ℕ → ℤ` with `δ = ±1` on `A`.
If `A` is `δ`-primitive, `t < A.card`, `N < p * p`, and `L t · H t < p`, then no
element of `A` is divisible by `p`.

Remark: the hypothesis `N < p * p` is included because it was part of the requested
statement, but the proof below does not actually use it — the conclusion already
follows from primitivity, `t < A.card`, and the bound `L t · H t < p`. (The role of
`N < p * p` is only to make the bound hypothesis attainable: it forces `t < p`, so
that `L t` is coprime to `p` and `L t · H t < p` can hold.) -/
theorem erdos319_top_layer_exclusion
    {p N : ℕ} (hp : p.Prime) {A : Finset ℕ} {δ : ℕ → ℤ}
    (hA : A ⊆ Finset.Icc 1 N)
    (hδ : ∀ n ∈ A, δ n = 1 ∨ δ n = -1)
    (hprim : DeltaPrimitive A δ)
    (hcard : N / p < A.card)
    (_hNpp : N < p * p)
    (hbound : (Lfun (N / p) : ℚ) * Hfun (N / p) < (p : ℚ)) :
    ∀ n ∈ A, ¬ p ∣ n := by
  intro n hn hpn
  -- the top layer
  set T : Finset ℕ := A.filter (fun n => p ∣ n) with hT
  have hTsub : T ⊆ A := Finset.filter_subset _ _
  have hTne : T.Nonempty := ⟨n, by rw [hT]; exact Finset.mem_filter.mpr ⟨hn, hpn⟩⟩
  have hsz : SignedZero T δ := signedZero_filter_p hp hA hδ hbound hprim.1
  -- primitivity forces T = A
  have hTeq : T = A := by
    by_contra hne
    exact hprim.2 T (Finset.ssubset_iff_subset_ne.mpr ⟨hTsub, hne⟩) hTne hsz
  -- so all of A is divisible by p
  have hdvd : ∀ m ∈ A, p ∣ m := by
    intro m hm
    have : m ∈ T := by rw [hTeq]; exact hm
    exact (Finset.mem_filter.mp this).2
  have := card_le_t_of_all_dvd hp hA hdvd
  omega

end Erdos319
