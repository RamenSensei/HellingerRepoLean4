import Hellinger.Fourier

/-!
# Flat Walsh spectra on the actual Boolean cube

Flatness is a condition on the normalized Walsh transform, not on supplied
moments. The mean, exact noisy second moment, and posterior bound are derived
here for arbitrary dimension. Boolean-valuedness is separate from flatness.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.Flatness

open Hellinger.Fourier

def IsBent {n : ℕ} (f : Cube n → ℝ) : Prop :=
  ∀ s, walsh f s ^ 2 = ((2 : ℝ) ^ n)⁻¹

def amplitude (n : ℕ) : ℝ := Real.sqrt (((2 : ℝ) ^ n)⁻¹)

theorem amplitude_nonneg (n : ℕ) : 0 ≤ amplitude n := Real.sqrt_nonneg _

theorem amplitude_sq (n : ℕ) : amplitude n ^ 2 = ((2 : ℝ) ^ n)⁻¹ :=
  Real.sq_sqrt (by positivity)

theorem isBent_iff_abs {n : ℕ} (f : Cube n → ℝ) :
    IsBent f ↔ ∀ s, |walsh f s| = amplitude n := by
  constructor
  · intro hb s
    rw [← Real.sqrt_sq_eq_abs, hb s]
    rfl
  · intro h s
    have hs := congrArg (fun r : ℝ => r ^ 2) (h s)
    simpa only [sq_abs, amplitude_sq] using hs

theorem mean_sq {n : ℕ} {f : Cube n → ℝ} (hb : IsBent f) :
    mean f ^ 2 = ((2 : ℝ) ^ n)⁻¹ := by
  simpa only [walsh_zero] using hb (fun _ => false)

theorem noisy_mean_sq {n : ℕ} {f : Cube n → ℝ} (hb : IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean ((cubeBSC n ρ hρ).apply f) ^ 2 = ((2 : ℝ) ^ n)⁻¹ := by
  rw [UniformChannel.mean_apply]
  exact mean_sq hb

/-- The exact second moment is derived from actual Fourier flatness. -/
theorem noise_second_moment {n : ℕ} {f : Cube n → ℝ} (hb : IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun x => ((cubeBSC n ρ hρ).apply f x) ^ 2) =
      ((2 : ℝ) ^ n)⁻¹ * (1 + ρ ^ 2) ^ n := by
  rw [Fourier.noise_second_moment]
  unfold IsBent at hb
  simp only [hb, pow_mul]
  rw [← Finset.sum_mul, sum_pow_degree]
  ring

/-- The actual noisy posterior is bounded by the flat coefficient amplitude
times the exact degree generating polynomial. -/
theorem noise_abs_le {n : ℕ} {f : Cube n → ℝ} (hb : IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : Cube n) :
    |(cubeBSC n ρ hρ).apply f x| ≤ amplitude n * (1 + ρ) ^ n := by
  rw [noise_expansion]
  calc
    |∑ s, (ρ ^ degree s * walsh f s) * phase s x| ≤
        ∑ s, |(ρ ^ degree s * walsh f s) * phase s x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s : Cube n, ρ ^ degree s * amplitude n := by
      simp only [abs_mul, abs_pow, abs_of_nonneg hρ.1,
        (isBent_iff_abs f).mp hb, phase_abs, mul_one]
    _ = amplitude n * (1 + ρ) ^ n := by
      rw [← Finset.sum_mul, sum_pow_degree]
      ring

/-- Every nonzero translation has zero autocorrelation, derived from flatness. -/
theorem autocorrelation_eq {n : ℕ} {f : Cube n → ℝ} (hb : IsBent f) (v : Cube n) :
    autocorrelation f v = if v = (fun _ => false) then 1 else 0 := by
  rw [autocorrelation_formula]
  unfold IsBent at hb
  simp only [hb]
  rw [← Finset.mul_sum, sum_phase]
  split_ifs <;> simp

theorem autocorrelation_zero {n : ℕ} {f : Cube n → ℝ} (hb : IsBent f)
    (v : Cube n) (hv : v ≠ (fun _ => false)) : autocorrelation f v = 0 := by
  rw [autocorrelation_eq hb, if_neg hv]

def sensitivityIndicator {n : ℕ} (f : Cube n → ℝ) (i : Fin n) (x : Cube n) : ℝ :=
  (1 - f x * f (translate (unit i) x)) / 2

def sensitivity {n : ℕ} (f : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ i, sensitivityIndicator f i x

theorem sensitivityIndicator_zero_or_one {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = -1 ∨ f x = 1) (i : Fin n) (x : Cube n) :
    sensitivityIndicator f i x = 0 ∨ sensitivityIndicator f i x = 1 := by
  rcases hf x with h | h <;> rcases hf (translate (unit i) x) with ht | ht <;>
    norm_num [sensitivityIndicator, h, ht]

theorem sensitivityIndicator_sq {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = -1 ∨ f x = 1) (i : Fin n) (x : Cube n) :
    sensitivityIndicator f i x ^ 2 = sensitivityIndicator f i x := by
  rcases sensitivityIndicator_zero_or_one hf i x with h | h <;> simp [h]

theorem sensitivityIndicator_mean {n : ℕ} {f : Cube n → ℝ}
    (hb : IsBent f) (i : Fin n) : mean (sensitivityIndicator f i) = 1 / 2 := by
  unfold sensitivityIndicator
  simp only [div_eq_mul_inv]
  rw [mean_mul_const, mean_sub, mean_const]
  change (1 - autocorrelation f (unit i)) * (2 : ℝ)⁻¹ = 1 * (2 : ℝ)⁻¹
  rw [autocorrelation_zero hb (unit i) (unit_ne_zero i)]
  norm_num

theorem sensitivity_mean {n : ℕ} {f : Cube n → ℝ} (hb : IsBent f) :
    mean (sensitivity f) = (n : ℝ) / 2 := by
  unfold sensitivity
  rw [mean_sum]
  simp [sensitivityIndicator_mean hb]
  ring

theorem sensitivityIndicator_pair_mean {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : IsBent f)
    (i j : Fin n) (hij : i ≠ j) :
    mean (fun x => sensitivityIndicator f i x * sensitivityIndicator f j x) = 1 / 4 := by
  have he (x : Cube n) :
      sensitivityIndicator f i x * sensitivityIndicator f j x =
        (1 - f x * f (translate (unit i) x) -
          f x * f (translate (unit j) x) +
          f (translate (unit i) x) * f (translate (unit j) x)) / 4 := by
    have hs : f x ^ 2 = 1 := by rcases hf x with h | h <;> simp [h]
    calc
      sensitivityIndicator f i x * sensitivityIndicator f j x =
          (1 - f x * f (translate (unit i) x) -
            f x * f (translate (unit j) x) +
            f x ^ 2 * (f (translate (unit i) x) * f (translate (unit j) x))) / 4 := by
        unfold sensitivityIndicator
        ring
      _ = _ := by rw [hs, one_mul]
  simp only [he, div_eq_mul_inv]
  rw [mean_mul_const, mean_add, mean_sub, mean_sub, mean_const,
    mean_translated_product]
  change (1 - autocorrelation f (unit i) - autocorrelation f (unit j) +
    autocorrelation f (translate (unit j) (unit i))) * (4 : ℝ)⁻¹ = 1 * (4 : ℝ)⁻¹
  rw [autocorrelation_zero hb (unit i) (unit_ne_zero i),
    autocorrelation_zero hb (unit j) (unit_ne_zero j),
    autocorrelation_zero hb _ (unit_pair_ne_zero i j hij)]
  norm_num

theorem sensitivityIndicator_eq_ite {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = -1 ∨ f x = 1) (i : Fin n) (x : Cube n) :
    sensitivityIndicator f i x =
      if f (Function.update x i (!(x i))) ≠ f x then 1 else 0 := by
  rw [← translate_unit]
  rcases hf x with h | h <;> rcases hf (translate (unit i) x) with ht | ht <;>
    norm_num [sensitivityIndicator, h, ht]

/-- The sensitivity used here is exactly the number of changed outputs on
one-coordinate flips, as in the manuscript. -/
theorem sensitivity_eq_card {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = -1 ∨ f x = 1) (x : Cube n) :
    sensitivity f x =
      ((Finset.univ.filter
        (fun i => f (Function.update x i (!(x i))) ≠ f x)).card : ℝ) := by
  unfold sensitivity
  simp_rw [sensitivityIndicator_eq_ite hf]
  rw [← Finset.sum_filter]
  simp

theorem sensitivity_nonneg {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = -1 ∨ f x = 1) (x : Cube n) : 0 ≤ sensitivity f x := by
  rw [sensitivity_eq_card hf]
  positivity

theorem sensitivity_second_moment {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : IsBent f) :
    mean (fun x => sensitivity f x ^ 2) = (n : ℝ) * (n + 1) / 4 := by
  have hm (i j : Fin n) :
      mean (fun x => sensitivityIndicator f i x * sensitivityIndicator f j x) =
        if i = j then 1 / 2 else 1 / 4 := by
    by_cases hij : i = j
    · subst j
      simp only [← pow_two, sensitivityIndicator_sq hf, if_true]
      exact sensitivityIndicator_mean hb i
    · rw [if_neg hij]
      exact sensitivityIndicator_pair_mean hf hb i j hij
  have hrow (i : Fin n) :
      (∑ j : Fin n, if i = j then (1 : ℝ) / 2 else 1 / 4) = ((n : ℝ) + 1) / 4 := by
    have he (j : Fin n) :
        (if i = j then (1 : ℝ) / 2 else 1 / 4) =
          1 / 4 + if j = i then 1 / 4 else 0 := by
      by_cases hij : i = j
      · subst j
        norm_num
      · simp [hij, Ne.symm hij]
    simp_rw [he]
    simp [Finset.sum_add_distrib]
    ring
  calc
    mean (fun x => sensitivity f x ^ 2) =
        ∑ i, ∑ j, mean (fun x => sensitivityIndicator f i x * sensitivityIndicator f j x) := by
      unfold sensitivity
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum, mean_sum]
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ j : Fin n, if i = j then (1 : ℝ) / 2 else 1 / 4 := by
      simp only [hm]
    _ = (n : ℝ) * (n + 1) / 4 := by
      simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The moment interpolation used for the square-root sensitivity bound,
proved by two finite Cauchy-Schwarz inequalities. -/
theorem mean_sqrt_interpolation {Ω : Type*} [Fintype Ω] (s : Ω → ℝ)
    (hs : ∀ x, 0 ≤ s x) :
    mean s ^ 3 ≤ mean (fun x => Real.sqrt (s x)) ^ 2 * mean (fun x => s x ^ 2) := by
  have h₁ := mean_sq_le_mean_mul s (fun x => Real.sqrt (s x))
    (fun x => s x * Real.sqrt (s x))
    (fun x => Real.sqrt_nonneg _) (fun x => mul_nonneg (hs x) (Real.sqrt_nonneg _))
    (fun x => by
      have hr := Real.sq_sqrt (hs x)
      nlinarith)
  have h₂ := mean_sq_le_mean_mul (fun x => s x * Real.sqrt (s x)) s
    (fun x => s x ^ 2) hs (fun x => sq_nonneg _)
    (fun x => by rw [mul_pow, Real.sq_sqrt (hs x)]; ring)
  have hA := mean_nonneg s hs
  have hB := mean_nonneg (fun x => Real.sqrt (s x)) (fun x => Real.sqrt_nonneg _)
  by_cases hzero : mean s = 0
  · rw [hzero]
    simpa only [zero_pow (by decide : 3 ≠ 0)] using
      mul_nonneg (sq_nonneg (mean (fun x => Real.sqrt (s x))))
        (mean_nonneg (fun x => s x ^ 2) (fun x => sq_nonneg _))
  · have hpos : 0 < mean s := lt_of_le_of_ne hA (Ne.symm hzero)
    have h₁sq := mul_self_le_mul_self (sq_nonneg (mean s)) h₁
    have h₂mul := mul_le_mul_of_nonneg_left h₂
      (sq_nonneg (mean (fun x => Real.sqrt (s x))))
    apply le_of_mul_le_mul_left (a := mean s) _ hpos
    nlinarith

theorem sensitivity_sqrt_mean_lower {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : IsBent f) :
    (n : ℝ) / Real.sqrt (2 * (n + 1)) ≤
      mean (fun x => Real.sqrt (sensitivity f x)) := by
  have hi := mean_sqrt_interpolation (sensitivity f) (sensitivity_nonneg hf)
  rw [sensitivity_mean hb, sensitivity_second_moment hf hb] at hi
  have hB : 0 ≤ mean (fun x => Real.sqrt (sensitivity f x)) :=
    mean_nonneg _ (fun _ => Real.sqrt_nonneg _)
  have hd : 0 < Real.sqrt (2 * ((n : ℝ) + 1)) := Real.sqrt_pos.2 (by positivity)
  have hd2 := Real.sq_sqrt (show 0 ≤ 2 * ((n : ℝ) + 1) by positivity)
  by_cases hn : n = 0
  · subst n
    simpa using hB
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hs : (n : ℝ) ^ 2 ≤
        mean (fun x => Real.sqrt (sensitivity f x)) ^ 2 * (2 * (n + 1)) := by
      apply le_of_mul_le_mul_left (a := (n : ℝ)) _ hnpos
      nlinarith [hi]
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg hB hd.le]

#print axioms mean_sq
#print axioms noise_second_moment
#print axioms noise_abs_le
#print axioms autocorrelation_eq
#print axioms sensitivity_mean
#print axioms sensitivity_second_moment
#print axioms sensitivity_sqrt_mean_lower

end Hellinger.Flatness
