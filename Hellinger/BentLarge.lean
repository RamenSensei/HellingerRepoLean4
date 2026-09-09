import Hellinger.Flatness
import Hellinger.BentEstimates
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Analytic estimates for bent functions in higher dimensions

This module proves continuous real estimates, to be connected to the actual
Fourier and BSC moment identities. Hypotheses must state upstream moment or
channel facts, never the desired Hellinger inequality itself.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.BentLarge

/-- The first derivative of the actual Hellinger square-root function. -/
theorem root_hasDerivAt (x : ℝ) (hx : x ^ 2 < 1) :
    HasDerivAt root (-x / root x) x := by
  have hp : 0 < 1 - x ^ 2 := by linarith
  have hn : Real.sqrt (1 - x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have h := ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).sqrt
    (ne_of_gt hp)
  convert h using 1
  · rfl
  · unfold root
    dsimp
    field_simp
    ring

/-- The second derivative, with the nonzero denominator justified by `x² < 1`. -/
theorem root_derivative_hasDerivAt (x : ℝ) (hx : x ^ 2 < 1) :
    HasDerivAt (fun y => -y / root y) (-1 / root x ^ 3) x := by
  have hp : 0 < 1 - x ^ 2 := by linarith
  have hn : root x ≠ 0 := by exact ne_of_gt (Real.sqrt_pos.2 hp)
  have hs : root x ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (le_of_lt hp)
  have h : HasDerivAt (fun y : ℝ => -y / root y)
      ((-1 * root x - (-x) * (-x / root x)) / root x ^ 2) x :=
    (hasDerivAt_id x).neg.div (root_hasDerivAt x hx) hn
  apply h.congr_deriv
  field_simp [hn]
  nlinarith only [hs]

/-- Adding the sharp quadratic curvature correction gives a convex function
on a compact subinterval of `(-1,1)`. -/
theorem root_quadratic_convex (M : ℝ) (hM₀ : 0 ≤ M) (hM₁ : M < 1) :
    ConvexOn ℝ (Set.Icc (-M) M)
      (fun x => root x + (1 / (2 * root M ^ 3)) * x ^ 2) := by
  have hm : M ^ 2 < 1 := by nlinarith
  have hp : 0 < root M := Real.sqrt_pos.2 (by linarith)
  have bound (x : ℝ) (hx : x ∈ Set.Icc (-M) M) : x ^ 2 ≤ M ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hx.2) (show 0 ≤ M + x by linarith [hx.1])
    nlinarith only [hh]
  let L : ℝ := 1 / root M ^ 3
  have d₁ (x : ℝ) (hx : x ∈ interior (Set.Icc (-M) M)) :
      HasDerivAt (fun x => root x + (1 / (2 * root M ^ 3)) * x ^ 2)
        (-x / root x + L * x) x := by
    have hb := bound x (interior_subset hx)
    have h := (root_hasDerivAt x (lt_of_le_of_lt hb hm)).add
      (((hasDerivAt_id x).pow 2).const_mul (1 / (2 * root M ^ 3)))
    apply h.congr_deriv
    dsimp [L]
    ring
  have d₂ (x : ℝ) (hx : x ∈ interior (Set.Icc (-M) M)) :
      HasDerivAt (fun x => -x / root x + L * x) (-1 / root x ^ 3 + L) x := by
    have hb := bound x (interior_subset hx)
    exact (root_derivative_hasDerivAt x (lt_of_le_of_lt hb hm)).add
      (by simpa using ((hasDerivAt_id x).const_mul L))
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (-M) M)
    (f' := fun x => -x / root x + L * x)
    (f'' := fun x => -1 / root x ^ 3 + L)
  · have hr : Continuous root := Real.continuous_sqrt.comp
        (continuous_const.sub (continuous_id.pow 2))
    exact (hr.add ((continuous_id.pow 2).const_mul _)).continuousOn
  · exact fun x hx => (d₁ x hx).hasDerivWithinAt
  · exact fun x hx => (d₂ x hx).hasDerivWithinAt
  · intro x hx
    have hb := bound x (interior_subset hx)
    have hr : root M ≤ root x := Real.sqrt_le_sqrt (by linarith)
    have hpow : root M ^ 3 ≤ root x ^ 3 := pow_le_pow_left₀ (le_of_lt hp) hr 3
    have hi := one_div_le_one_div_of_le (show 0 < root M ^ 3 by positivity) hpow
    dsimp [L]
    simp only [neg_div]
    linarith only [hi]

/-- The Hellinger Jensen gap is bounded by variance times the curvature bound.
The mean is the actual mean of the supplied posterior values. -/
theorem weighted_curvature_bound {ι : Type*} [Fintype ι]
    (w u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (M : ℝ) (hM₀ : 0 ≤ M) (hM₁ : M < 1)
    (hu : ∀ i, u i ∈ Set.Icc (-M) M) :
    root (∑ i, w i * u i) - ∑ i, w i * root (u i) ≤
      ((∑ i, w i * (u i) ^ 2) - (∑ i, w i * u i) ^ 2) /
        (2 * root M ^ 3) := by
  have hj := (root_quadratic_convex M hM₀ hM₁).map_sum_le
    (t := Finset.univ) (w := w) (p := u)
    (fun i _ => hw i) (by simpa using hsum) (fun i _ => hu i)
  simp only [smul_eq_mul] at hj
  have hid : (∑ i, w i * (root (u i) + (1 / (2 * root M ^ 3)) * (u i) ^ 2)) =
      (∑ i, w i * root (u i)) + (1 / (2 * root M ^ 3)) *
        ∑ i, w i * (u i) ^ 2 := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid] at hj
  simp only [div_eq_mul_inv, one_mul] at hj ⊢
  nlinarith only [hj]

/-- The variance coefficient decreases from dimension four onwards. -/
theorem dimension_variance_coefficient (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) * (109 / 200 : ℝ) ^ (n - 1) / 2 ≤ 109 ^ 3 / 4000000 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : 1 ≤ n := by omega
    have hpow : (109 / 200 : ℝ) ^ n =
        (109 / 200 : ℝ) ^ (n - 1) * (109 / 200 : ℝ) := by
      rw [← pow_succ, Nat.sub_add_cancel hnpos]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    rw [hpow]
    have hcoef : ((n : ℝ) + 1) * (109 / 200) ≤ n := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoef
      (show 0 ≤ (109 / 200 : ℝ) ^ (n - 1) by positivity)
    nlinarith only [hmul, ih]

/-- Exact bent variance is quadratically small, uniformly in every `n ≥ 4`. -/
theorem high_noise_variance (n : ℕ) (hn : 4 ≤ n) (ρ : ℝ)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 3 / 10) :
    ((2 : ℝ) ^ n)⁻¹ * ((1 + ρ ^ 2) ^ n - 1) ≤
      (109 ^ 3 / 4000000 : ℝ) * ρ ^ 2 := by
  have hρsq : ρ ^ 2 ≤ 9 / 100 := by nlinarith
  have hbase : (1 + ρ ^ 2) / 2 ≤ 109 / 200 := by linarith
  have ha : 0 ≤ (1 + ρ ^ 2) / 2 := by positivity
  have hge : (1 / 2 : ℝ) ≤ (1 + ρ ^ 2) / 2 := by nlinarith [sq_nonneg ρ]
  have hd := abs_pow_sub_pow_le (a := (1 + ρ ^ 2) / 2) (b := (1 / 2 : ℝ)) (n := n)
  rw [abs_of_nonneg ha, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    max_eq_left hge, abs_of_nonneg (sub_nonneg.mpr hge)] at hd
  have hp := pow_le_pow_left₀ ha hbase (n - 1)
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ ((1 + ρ ^ 2) / 2 - 1 / 2) * (n : ℝ) by positivity)
  have hdim := dimension_variance_coefficient n hn
  have hv := mul_le_mul_of_nonneg_right hdim (sq_nonneg ρ)
  have hdiff := (le_abs_self (((1 + ρ ^ 2) / 2) ^ n - (1 / 2 : ℝ) ^ n)).trans hd
  have heq : ((2 : ℝ) ^ n)⁻¹ * ((1 + ρ ^ 2) ^ n - 1) =
      ((1 + ρ ^ 2) / 2) ^ n - (1 / 2 : ℝ) ^ n := by
    rw [div_pow, div_pow, one_pow]
    simp only [div_eq_mul_inv]
    ring
  rw [heq]
  nlinarith only [hdiff, hm, hv]

/-- Flatness controls the actual posterior on the whole high-noise interval. -/
theorem high_noise_posterior_bound {n : ℕ} (hn : 4 ≤ n)
    {f : Fourier.Cube n → ℝ} (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρ₁ : ρ ≤ 3 / 10)
    (x : Fourier.Cube n) :
    |(cubeBSC n ρ hρ).apply f x| ≤ (169 / 200 : ℝ) ^ 2 := by
  have hbase₀ : 0 ≤ (1 + ρ) ^ 2 / 2 := by positivity
  have hbase₁ : (1 + ρ) ^ 2 / 2 ≤ 169 / 200 := by nlinarith [hρ.1]
  have heq : (Flatness.amplitude n * (1 + ρ) ^ n) ^ 2 =
      ((1 + ρ) ^ 2 / 2) ^ n := by
    rw [mul_pow, Flatness.amplitude_sq, div_pow, div_eq_mul_inv]
    rw [← pow_mul, ← pow_mul]
    ring
  have hpow := (pow_le_pow_left₀ hbase₀ hbase₁ n).trans
    (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 169 / 200)
      (by norm_num : (169 / 200 : ℝ) ≤ 1) hn)
  rw [← heq] at hpow
  have hA : Flatness.amplitude n * (1 + ρ) ^ n ≤ (169 / 200 : ℝ) ^ 2 := by
    nlinarith only [hpow]
  exact (Flatness.noise_abs_le hb ρ hρ x).trans hA

/-- Uniform Jensen curvature bound for a finite nonempty probability space. -/
theorem mean_curvature_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (u : ι → ℝ) (M : ℝ) (hM₀ : 0 ≤ M) (hM₁ : M < 1)
    (hu : ∀ i, u i ∈ Set.Icc (-M) M) :
    objective u ≤ (mean (fun i => (u i) ^ 2) - (mean u) ^ 2) /
      (2 * root M ^ 3) := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := weighted_curvature_bound (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) u
    (by intro; positivity) (by simp [hcard]) M hM₀ hM₁ hu
  simpa only [objective, mean, ← Finset.mul_sum] using h

/-- The rational curvature constant is strictly below the denominator. -/
theorem high_noise_constant_lt :
    (109 ^ 3 / 4000000 : ℝ) < root ((169 / 200 : ℝ) ^ 2) ^ 3 := by
  have hs : root ((169 / 200 : ℝ) ^ 2) ^ 2 = 1 - (169 / 200 : ℝ) ^ 4 := by
    unfold root
    rw [Real.sq_sqrt (by norm_num)]
    ring
  have h₀ : 0 ≤ root ((169 / 200 : ℝ) ^ 2) ^ 3 := by unfold root; positivity
  have hh : (root ((169 / 200 : ℝ) ^ 2) ^ 3) ^ 2 =
      (1 - (169 / 200 : ℝ) ^ 4) ^ 3 := by rw [← pow_mul, mul_comm 3 2, pow_mul, hs]
  have h := BentEstimates.high_noise_curvature_constant
  rw [← hh] at h
  nlinarith only [h, h₀]

/-- High-noise theorem connected to the actual BSC, mean and flat Walsh spectrum. -/
theorem bent_high_noise_quadratic_bound {n : ℕ} (hn : 4 ≤ n)
    (f : Fourier.Cube n → ℝ) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρ₁ : ρ ≤ 3 / 10) :
    objective ((cubeBSC n ρ hρ).apply f) ≤ ρ ^ 2 / 2 := by
  let M : ℝ := (169 / 200) ^ 2
  let u := (cubeBSC n ρ hρ).apply f
  have hu : ∀ x, u x ∈ Set.Icc (-M) M := by
    intro x
    exact abs_le.mp (high_noise_posterior_bound hn hb ρ hρ hρ₁ x)
  have hc := mean_curvature_bound u M (by norm_num [M]) (by norm_num [M]) hu
  have hvar : mean (fun x => (u x) ^ 2) - (mean u) ^ 2 =
      ((2 : ℝ) ^ n)⁻¹ * ((1 + ρ ^ 2) ^ n - 1) := by
    rw [Flatness.noise_second_moment hb ρ hρ, Flatness.noisy_mean_sq hb ρ hρ]
    ring
  rw [hvar] at hc
  have hv := high_noise_variance n hn ρ hρ.1 hρ₁
  have hroot : 0 < root M := by unfold root M; apply Real.sqrt_pos.2; norm_num
  have hden : 0 < 2 * root M ^ 3 := by positivity
  have hcv := div_le_div_of_nonneg_right hv (le_of_lt hden)
  have hconst : (109 ^ 3 / 4000000 : ℝ) ≤ root M ^ 3 := le_of_lt high_noise_constant_lt
  have hcoeff : (109 ^ 3 / 4000000 : ℝ) * ρ ^ 2 / (2 * root M ^ 3) ≤ ρ ^ 2 / 2 := by
    apply (div_le_iff₀ hden).2
    have hmul := mul_le_mul_of_nonneg_right hconst (sq_nonneg ρ)
    nlinarith only [hmul]
  exact hc.trans (hcv.trans hcoeff)

/-- High noise, including the independent endpoint. -/
theorem bent_high_noise_hellinger {n : ℕ} (hn : 4 ≤ n)
    (f : Fourier.Cube n → ℝ) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρ₁ : ρ ≤ 3 / 10) :
    objective ((cubeBSC n ρ hρ).apply f) ≤ 1 - Real.sqrt (1 - ρ ^ 2) := by
  have h := bent_high_noise_quadratic_bound hn f hb ρ hρ hρ₁
  have hrad : 0 ≤ 1 - ρ ^ 2 := by nlinarith [hρ.1, hρ.2]
  have hs := Real.sq_sqrt hrad
  have hs₀ := Real.sqrt_nonneg (1 - ρ ^ 2)
  nlinarith [sq_nonneg (1 - Real.sqrt (1 - ρ ^ 2))]

/-- Strict high-noise inequality for every positive correlation. -/
theorem bent_high_noise_hellinger_strict {n : ℕ} (hn : 4 ≤ n)
    (f : Fourier.Cube n → ℝ) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρ₁ : ρ ≤ 3 / 10) (hρpos : 0 < ρ) :
    objective ((cubeBSC n ρ hρ).apply f) < 1 - Real.sqrt (1 - ρ ^ 2) := by
  have h := bent_high_noise_quadratic_bound hn f hb ρ hρ hρ₁
  have hrad : 0 ≤ 1 - ρ ^ 2 := by nlinarith [hρ.1, hρ.2]
  have hs := Real.sq_sqrt hrad
  have hs₀ := Real.sqrt_nonneg (1 - ρ ^ 2)
  have hs₁ : Real.sqrt (1 - ρ ^ 2) < 1 := by nlinarith [sq_pos_of_pos hρpos]
  have hp := sq_pos_of_pos (sub_pos.mpr hs₁)
  nlinarith only [h, hs, hp]

/-- Rational comparison used in the low-`c` part of the large-dimension interval. -/
theorem exp_neg_seventeen_twentyseven_lt :
    Real.exp (-(17 : ℝ) / 27) < 27 / 50 := by
  have h := Real.sum_le_exp_of_nonneg (show 0 ≤ (17 : ℝ) / 27 by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  rw [show (-(17 : ℝ) / 27) = -(17 / 27) by ring, Real.exp_neg]
  rw [inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos _)).2
  linarith

/-- A continuous certificate on the entire compact part of the middle interval.
The identity is in the Bernstein basis; every coefficient is positive. -/
theorem middle_six_polynomial (c : ℝ) (hc₀ : 23 / 50 ≤ c) (hc₁ : c ≤ 24 / 25) :
    (1 - c ^ 2 / 2) ^ 6 ≤ 1 - c - 1 / 100 := by
  have hu : 0 ≤ 2 * c - 23 / 25 := by linarith
  have hv : 0 ≤ 48 / 25 - 2 * c := by linarith
  have hcert : 1 - c - (1 - c ^ 2 / 2) ^ 6 - 1 / 100 =
    (293434608731602449679 / 15625000000000000000000 : ℝ) * (2 * c - 23 / 25) ^ 0 * (48 / 25 - 2 * c) ^ 12 +
    (251129447602744616189 / 488281250000000000000 : ℝ) * (2 * c - 23 / 25) ^ 1 * (48 / 25 - 2 * c) ^ 11 +
    (4237726818503820246779 / 976562500000000000000 : ℝ) * (2 * c - 23 / 25) ^ 2 * (48 / 25 - 2 * c) ^ 10 +
    (230239365838264238171 / 12207031250000000000 : ℝ) * (2 * c - 23 / 25) ^ 3 * (48 / 25 - 2 * c) ^ 9 +
    (2448356727329412268989 / 48828125000000000000 : ℝ) * (2 * c - 23 / 25) ^ 4 * (48 / 25 - 2 * c) ^ 8 +
    (336082710720389505633 / 3814697265625000000 : ℝ) * (2 * c - 23 / 25) ^ 5 * (48 / 25 - 2 * c) ^ 7 +
    (808924405129274562077 / 7629394531250000000 : ℝ) * (2 * c - 23 / 25) ^ 6 * (48 / 25 - 2 * c) ^ 6 +
    (42088389610722174351 / 476837158203125000 : ℝ) * (2 * c - 23 / 25) ^ 7 * (48 / 25 - 2 * c) ^ 5 +
    (38290088185633115901 / 762939453125000000 : ℝ) * (2 * c - 23 / 25) ^ 8 * (48 / 25 - 2 * c) ^ 4 +
    (222920542238415629 / 11920928955078125 : ℝ) * (2 * c - 23 / 25) ^ 9 * (48 / 25 - 2 * c) ^ 3 +
    (990913347086786599 / 238418579101562500 : ℝ) * (2 * c - 23 / 25) ^ 10 * (48 / 25 - 2 * c) ^ 2 +
    (51716948253250459 / 119209289550781250 : ℝ) * (2 * c - 23 / 25) ^ 11 * (48 / 25 - 2 * c) ^ 1 +
    (1293342884250839 / 238418579101562500 : ℝ) * (2 * c - 23 / 25) ^ 12 * (48 / 25 - 2 * c) ^ 0 := by ring
  have hpos : 0 ≤
    (293434608731602449679 / 15625000000000000000000 : ℝ) * (2 * c - 23 / 25) ^ 0 * (48 / 25 - 2 * c) ^ 12 +
    (251129447602744616189 / 488281250000000000000 : ℝ) * (2 * c - 23 / 25) ^ 1 * (48 / 25 - 2 * c) ^ 11 +
    (4237726818503820246779 / 976562500000000000000 : ℝ) * (2 * c - 23 / 25) ^ 2 * (48 / 25 - 2 * c) ^ 10 +
    (230239365838264238171 / 12207031250000000000 : ℝ) * (2 * c - 23 / 25) ^ 3 * (48 / 25 - 2 * c) ^ 9 +
    (2448356727329412268989 / 48828125000000000000 : ℝ) * (2 * c - 23 / 25) ^ 4 * (48 / 25 - 2 * c) ^ 8 +
    (336082710720389505633 / 3814697265625000000 : ℝ) * (2 * c - 23 / 25) ^ 5 * (48 / 25 - 2 * c) ^ 7 +
    (808924405129274562077 / 7629394531250000000 : ℝ) * (2 * c - 23 / 25) ^ 6 * (48 / 25 - 2 * c) ^ 6 +
    (42088389610722174351 / 476837158203125000 : ℝ) * (2 * c - 23 / 25) ^ 7 * (48 / 25 - 2 * c) ^ 5 +
    (38290088185633115901 / 762939453125000000 : ℝ) * (2 * c - 23 / 25) ^ 8 * (48 / 25 - 2 * c) ^ 4 +
    (222920542238415629 / 11920928955078125 : ℝ) * (2 * c - 23 / 25) ^ 9 * (48 / 25 - 2 * c) ^ 3 +
    (990913347086786599 / 238418579101562500 : ℝ) * (2 * c - 23 / 25) ^ 10 * (48 / 25 - 2 * c) ^ 2 +
    (51716948253250459 / 119209289550781250 : ℝ) * (2 * c - 23 / 25) ^ 11 * (48 / 25 - 2 * c) ^ 1 +
    (1293342884250839 / 238418579101562500 : ℝ) * (2 * c - 23 / 25) ^ 12 * (48 / 25 - 2 * c) ^ 0 := by positivity
  linarith only [hcert, hpos]

/-- The scalar second-moment estimate throughout the full middle-noise range. -/
theorem middle_scalar (n : ℕ) (hn : 6 ≤ n) (c : ℝ)
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 24 / 25)
    (hscale : 17 / 27 ≤ (n : ℝ) * c ^ 2 / 2) :
    (1 - c ^ 2 / 2) ^ n ≤ 1 - c := by
  have hb₀ : 0 ≤ 1 - c ^ 2 / 2 := by nlinarith
  have hb₁ : 1 - c ^ 2 / 2 ≤ 1 := by nlinarith [sq_nonneg c]
  by_cases hc : c ≤ 23 / 50
  · have he : 1 - c ^ 2 / 2 ≤ Real.exp (-(c ^ 2 / 2)) := by
      simpa only [neg_add_rev, sub_eq_add_neg, add_comm] using
        Real.add_one_le_exp (-(c ^ 2 / 2))
    have hp := pow_le_pow_left₀ hb₀ he n
    rw [← Real.exp_nat_mul] at hp
    have hexp : Real.exp ((n : ℝ) * -(c ^ 2 / 2)) ≤ Real.exp (-(17 : ℝ) / 27) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hscale]
    linarith only [hp.trans hexp, exp_neg_seventeen_twentyseven_lt, hc]
  · have hp := pow_le_pow_of_le_one hb₀ hb₁ hn
    have hq := middle_six_polynomial c (le_of_not_ge hc) hc₁
    linarith only [hp, hq]

/-- Conversion of the original dimension-dependent interval to the scalar range. -/
theorem middle_noise_second_moment (n : ℕ) (hn : 6 ≤ n) (ρ : ℝ)
    (hρ₀ : 3 / 10 ≤ ρ) (hρ₁ : ρ ≤ 1 - 2 / (3 * (n : ℝ))) :
    ((1 + ρ ^ 2) / 2) ^ n ≤ 1 - Real.sqrt (1 - ρ ^ 2) := by
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hdiv : 0 < 2 / (3 * (n : ℝ)) := by positivity
  have hρnonneg : 0 ≤ ρ := by linarith
  have hρle : ρ ≤ 1 := by linarith
  have hrad : 0 ≤ 1 - ρ ^ 2 := by nlinarith
  have hs := Real.sq_sqrt hrad
  have hs0 := Real.sqrt_nonneg (1 - ρ ^ 2)
  have hs1 : Real.sqrt (1 - ρ ^ 2) ≤ 24 / 25 := by nlinarith
  have hm : ρ * (3 * (n : ℝ)) ≤ 3 * (n : ℝ) - 2 := by
    have h := (le_div_iff₀ (show 0 < 3 * (n : ℝ) by positivity)).1
      (show ρ ≤ (3 * (n : ℝ) - 2) / (3 * (n : ℝ)) by
        convert hρ₁ using 1
        field_simp)
    exact h
  have hendpoint : (17 : ℝ) / 27 ≤ (n : ℝ) * (1 - ρ ^ 2) / 2 := by
    have hprod := mul_nonneg
      (show 0 ≤ 3 * (n : ℝ) - 2 - 3 * (n : ℝ) * ρ by nlinarith only [hm])
      (show 0 ≤ 3 * (n : ℝ) - 2 + 3 * (n : ℝ) * ρ by
        have hmul := mul_nonneg (le_of_lt hnpos) hρnonneg
        nlinarith only [hnR, hmul])
    have hN := mul_nonneg (show 0 ≤ (n : ℝ) - 6 by linarith) (show 0 ≤ (n : ℝ) by positivity)
    nlinarith only [hprod, hN, hnR]
  have h := middle_scalar n hn (Real.sqrt (1 - ρ ^ 2)) hs0 hs1
    (by rw [hs]; exact hendpoint)
  convert h using 1
  rw [hs]
  ring

/-- A simple lower bound for the actual posterior average. -/
theorem mean_root_lower {ι : Type*} [Fintype ι] [Nonempty ι]
    (u : ι → ℝ) (hu : ∀ i, u i ∈ Set.Icc (-1 : ℝ) 1) :
    1 - mean (fun i => (u i) ^ 2) ≤ mean (fun i => root (u i)) := by
  have hp (i : ι) : 1 - (u i) ^ 2 ≤ root (u i) := by
    have hs : (u i) ^ 2 ≤ 1 := by nlinarith [(hu i).1, (hu i).2]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (u i), mul_nonneg (sq_nonneg (u i)) (sub_nonneg.mpr hs)]
  have h := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hp i))
    (show 0 ≤ (Fintype.card ι : ℝ)⁻¹ by positivity)
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa [mean, Finset.sum_sub_distrib, mul_sub, hcard] using h

/-- Middle-noise Hellinger theorem for the genuine cube BSC and bent spectrum. -/
theorem bent_middle_hellinger {n : ℕ} (hn : 6 ≤ n)
    (f : Fourier.Cube n → ℝ) (hf : ∀ x, f x = 1 ∨ f x = -1)
    (hb : Flatness.IsBent f) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hρ₀ : 3 / 10 ≤ ρ) (hρ₁ : ρ ≤ 1 - 2 / (3 * (n : ℝ))) :
    objective ((cubeBSC n ρ hρ).apply f) ≤ 1 - Real.sqrt (1 - ρ ^ 2) := by
  let u := (cubeBSC n ρ hρ).apply f
  have hu : ∀ x, u x ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x
    apply UniformChannel.apply_mem_Icc
    intro y
    rcases hf y with h | h <;> rw [h] <;> constructor <;> norm_num
  have hl := mean_root_lower u hu
  have hQ := Flatness.noise_second_moment hb ρ hρ
  have hQ' : mean (fun x => (u x) ^ 2) = ((1 + ρ ^ 2) / 2) ^ n := by
    rw [hQ, div_pow, div_eq_mul_inv]
    ring
  rw [hQ'] at hl
  have hm := middle_noise_second_moment n hn ρ hρ₀ hρ₁
  have hroot : root (mean u) ≤ 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith [sq_nonneg (mean u)]
  change root (mean u) - mean (fun x => root (u x)) ≤ _
  linarith only [hl, hm, hroot]

/-- The nonzero bent mean makes the middle-noise inequality strict. -/
theorem bent_middle_hellinger_strict {n : ℕ} (hn : 6 ≤ n)
    (f : Fourier.Cube n → ℝ) (hf : ∀ x, f x = 1 ∨ f x = -1)
    (hb : Flatness.IsBent f) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hρ₀ : 3 / 10 ≤ ρ) (hρ₁ : ρ ≤ 1 - 2 / (3 * (n : ℝ))) :
    objective ((cubeBSC n ρ hρ).apply f) < 1 - Real.sqrt (1 - ρ ^ 2) := by
  let u := (cubeBSC n ρ hρ).apply f
  have hu : ∀ x, u x ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x
    apply UniformChannel.apply_mem_Icc
    intro y
    rcases hf y with h | h <;> rw [h] <;> constructor <;> norm_num
  have hl := mean_root_lower u hu
  have hQ' : mean (fun x => (u x) ^ 2) = ((1 + ρ ^ 2) / 2) ^ n := by
    rw [Flatness.noise_second_moment hb ρ hρ, div_pow, div_eq_mul_inv]
    ring
  rw [hQ'] at hl
  have hm := middle_noise_second_moment n hn ρ hρ₀ hρ₁
  have hroot : root (mean u) < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
    have hbias := Flatness.noisy_mean_sq hb ρ hρ
    have hp : 0 < ((2 : ℝ) ^ n)⁻¹ := by positivity
    change (mean u) ^ 2 = _ at hbias
    linarith only [hbias, hp]
  change root (mean u) - mean (fun x => root (u x)) < _
  linarith only [hl, hm, hroot]

end Hellinger.BentLarge
