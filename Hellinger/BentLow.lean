import Hellinger.BentLarge

/-! The low-noise bound from actual no-flip and single-coordinate-flip events. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.BentLow
open Fourier

def neighbor {n : ℕ} (x : Cube n) (i : Fin n) : Cube n :=
  Function.update x i (!(x i))

theorem neighbor_injective {n : ℕ} (x : Cube n) : Function.Injective (neighbor x) := by
  intro i j h
  by_contra hij
  have he := congrFun h i
  have hji : i ≠ j := hij
  simp only [neighbor, Function.update_self, Function.update_of_ne hji] at he
  cases hx : x i <;> simp [hx] at he

theorem cube_weight_self (n : ℕ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (x : Cube n) : (cubeBSC n ρ hρ).weight x x = ((1 + ρ) / 2) ^ n := by
  simp [cubeBSC, UniformChannel.product, bsc, div_pow]

theorem cube_weight_neighbor {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (x : Cube n) (i : Fin n) :
    (cubeBSC n ρ hρ).weight x (neighbor x i) =
      ((1 - ρ) / 2) * ((1 + ρ) / 2) ^ (n - 1) := by
  classical
  change (∏ j, (bsc ρ hρ).weight (x j) (neighbor x i j)) = _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have hne : x i ≠ !(x i) := by cases x i <;> decide
  simp only [neighbor, Function.update_self, bsc, if_neg hne]
  congr 1
  calc
    (∏ j ∈ Finset.univ.erase i, (bsc ρ hρ).weight (x j) (Function.update x i (!(x i)) j)) =
        ∏ _j ∈ Finset.univ.erase i, ((1 + ρ) / 2) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji := (Finset.mem_erase.mp hj).1
      simp [Function.update_of_ne hji, bsc]
    _ = _ := by simp [div_pow]

def disagreement {n : ℕ} (f : Cube n → ℝ) (x y : Cube n) : ℝ :=
  (1 - f x * f y) / 2

theorem disagreement_nonneg {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = -1 ∨ f x = 1) (x y : Cube n) : 0 ≤ disagreement f x y := by
  rcases hf x with h | h <;> rcases hf y with hy | hy <;>
    norm_num [disagreement, h, hy]

theorem agreement_nonneg {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = -1 ∨ f x = 1) (x y : Cube n) : 0 ≤ 1 - disagreement f x y := by
  rcases hf x with h | h <;> rcases hf y with hy | hy <;>
    norm_num [disagreement, h, hy]

def mismatchProbability {n : ℕ} (f : Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : Cube n) : ℝ :=
  ∑ y, (cubeBSC n ρ hρ).weight x y * disagreement f x y

theorem mismatch_formula {n : ℕ} (f : Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : Cube n) :
    mismatchProbability f ρ hρ x = (1 - f x * (cubeBSC n ρ hρ).apply f x) / 2 := by
  unfold mismatchProbability disagreement UniformChannel.apply
  simp only [← mul_div_assoc, mul_sub, mul_one, ← Finset.sum_div, Finset.sum_sub_distrib]
  rw [UniformChannel.row_sum]
  congr 1
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem mismatch_lower {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : Cube n) :
    ((1 - ρ) / 2) * ((1 + ρ) / 2) ^ (n - 1) * Flatness.sensitivity f x ≤
      mismatchProbability f ρ hρ x := by
  classical
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (Finset.univ.image (neighbor x)))
    (f := fun y => (cubeBSC n ρ hρ).weight x y * disagreement f x y)
    (fun y _ _ => mul_nonneg ((cubeBSC n ρ hρ).nonneg x y) (disagreement_nonneg hf x y))
  rw [Finset.sum_image] at hsum
  · simp_rw [cube_weight_neighbor] at hsum
    have hindicator (i : Fin n) : disagreement f x (neighbor x i) = Flatness.sensitivityIndicator f i x := by
      rw [Flatness.sensitivityIndicator, translate_unit]
      rfl
    simp_rw [hindicator] at hsum
    rw [← Finset.mul_sum] at hsum
    exact hsum
  · exact fun i _ j _ h => neighbor_injective x h

theorem agreement_lower {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : Cube n) :
    ((1 + ρ) / 2) ^ n ≤ 1 - mismatchProbability f ρ hρ x := by
  have hsum := Finset.single_le_sum
    (f := fun y => (cubeBSC n ρ hρ).weight x y * (1 - disagreement f x y))
    (fun y (_ : y ∈ Finset.univ) =>
      mul_nonneg ((cubeBSC n ρ hρ).nonneg x y) (agreement_nonneg hf x y))
    (Finset.mem_univ x)
  have hself : disagreement f x x = 0 := by
    rcases hf x with h | h <;> norm_num [disagreement, h]
  simp only [hself, sub_zero, mul_one, cube_weight_self] at hsum
  have hid : (∑ y, (cubeBSC n ρ hρ).weight x y * (1 - disagreement f x y)) =
      1 - mismatchProbability f ρ hρ x := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, UniformChannel.row_sum, mismatchProbability]
  rw [hid] at hsum
  exact hsum

/-- Pointwise root bound from the two genuine channel events. -/
theorem posterior_root_lower {n : ℕ} (hn : 1 ≤ n) {f : Cube n → ℝ}
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : Cube n) :
    root ρ * ((1 + ρ) / 2) ^ (n - 1) * Real.sqrt (Flatness.sensitivity f x) ≤
      root ((cubeBSC n ρ hρ).apply f x) := by
  let p := mismatchProbability f ρ hρ x
  let a := (1 - ρ) / 2
  let b := (1 + ρ) / 2
  have ha : 0 ≤ a := by dsimp [a]; linarith [hρ.2]
  have hb : 0 ≤ b := by dsimp [b]; linarith [hρ.1]
  have hs : 0 ≤ Flatness.sensitivity f x := Flatness.sensitivity_nonneg hf x
  have hp : a * b ^ (n - 1) * Flatness.sensitivity f x ≤ p := mismatch_lower hf ρ hρ x
  have hq : b ^ n ≤ 1 - p := agreement_lower hf ρ hρ x
  have hp₀ : 0 ≤ p := le_trans (by positivity) hp
  have hq₀ : 0 ≤ 1 - p := le_trans (pow_nonneg hb _) hq
  have hprod := mul_le_mul hp hq (pow_nonneg hb _) hp₀
  have heq : 1 - ((cubeBSC n ρ hρ).apply f x) ^ 2 = 4 * p * (1 - p) := by
    have he := mismatch_formula f ρ hρ x
    change p = _ at he
    rw [he]
    rcases hf x with h | h <;> rw [h] <;> ring
  have hc : root ρ ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by nlinarith [hρ.1, hρ.2])
  have hsqrt := Real.sq_sqrt hs
  have hpow : b ^ n = b ^ (n - 1) * b := by rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [hpow] at hprod
  apply Real.le_sqrt_of_sq_le
  change (root ρ * b ^ (n - 1) * Real.sqrt (Flatness.sensitivity f x)) ^ 2 ≤ _
  rw [mul_pow, mul_pow, hc, hsqrt, heq]
  have hab : 1 - ρ ^ 2 = 4 * a * b := by dsimp [a, b]; ring
  rw [hab]
  nlinarith only [hprod]

/-- Averaging gives the full low-noise event bound, with no event assumption. -/
theorem posterior_root_mean_lower {n : ℕ} (hn : 1 ≤ n) {f : Cube n → ℝ}
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    root ρ * ((1 + ρ) / 2) ^ (n - 1) *
      mean (fun x => Real.sqrt (Flatness.sensitivity f x)) ≤
        mean (fun x => root ((cubeBSC n ρ hρ).apply f x)) := by
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => posterior_root_lower hn hf ρ hρ x)
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ (Fintype.card (Cube n) : ℝ)⁻¹ by positivity)
  simp only [← Finset.mul_sum] at hm
  unfold mean
  nlinarith only [hm]

/-- Bernoulli's inequality controls the no-flip factor over the whole range. -/
theorem low_noise_power_lower (n : ℕ) (hn : 1 ≤ n) (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hlo : 1 - 2 / (3 * (n : ℝ)) ≤ ρ) :
    (2 / 3 : ℝ) ≤ ((1 + ρ) / 2) ^ (n - 1) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hmul : (n : ℝ) * ((1 - ρ) / 2) ≤ 1 / 3 := by
    have hd : (1 - ρ) ≤ 2 / (3 * (n : ℝ)) := by linarith only [hlo]
    have hh := (le_div_iff₀ (show 0 < 3 * (n : ℝ) by positivity)).1 hd
    nlinarith only [hh]
  have hpow := one_add_mul_sub_le_pow
    (show (-1 : ℝ) ≤ (1 + ρ) / 2 by linarith [hρ.1]) (n - 1)
  rw [Nat.cast_sub hn] at hpow
  norm_num only [Nat.cast_one] at hpow
  nlinarith only [hpow, hmul, hρ.2]

/-- The sensitivity factor is already at least one from dimension six onward. -/
theorem low_noise_dimension_factor (n : ℕ) (hn : 6 ≤ n) :
    1 ≤ (2 / 3 : ℝ) * ((n : ℝ) / Real.sqrt (2 * ((n : ℝ) + 1))) := by
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < Real.sqrt (2 * ((n : ℝ) + 1)) := Real.sqrt_pos.2 (by linarith)
  have hs := Real.sq_sqrt (show 0 ≤ 2 * ((n : ℝ) + 1) by linarith)
  have hnn := mul_nonneg (show 0 ≤ (n : ℝ) - 6 by linarith) (show 0 ≤ (n : ℝ) by linarith)
  have hh : Real.sqrt (2 * ((n : ℝ) + 1)) ≤ 2 * (n : ℝ) / 3 := by
    nlinarith only [hs, hnn, hnR, le_of_lt hp]
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hp).2
  nlinarith only [hh]

/-- Actual low-noise posterior-root lower bound for every bent Boolean function. -/
theorem bent_low_noise_root_mean {n : ℕ} (hn : 6 ≤ n)
    {f : Cube n → ℝ} (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hlo : 1 - 2 / (3 * (n : ℝ)) ≤ ρ) :
    root ρ ≤ mean (fun x => root ((cubeBSC n ρ hρ).apply f x)) := by
  have hn₁ : 1 ≤ n := by omega
  have hevent := posterior_root_mean_lower hn₁ hf ρ hρ
  have hpower := low_noise_power_lower n hn₁ ρ hρ hlo
  have hsens := Flatness.sensitivity_sqrt_mean_lower hf hb
  have hdim := low_noise_dimension_factor n hn
  have hfactor := mul_le_mul hpower hsens
    (show 0 ≤ (n : ℝ) / Real.sqrt (2 * ((n : ℝ) + 1)) by positivity)
    (show 0 ≤ ((1 + ρ) / 2) ^ (n - 1) by
      apply pow_nonneg
      linarith [hρ.1])
  have hc : 0 ≤ root ρ := Real.sqrt_nonneg _
  have hprod := mul_le_mul_of_nonneg_left (hdim.trans hfactor) hc
  nlinarith only [hprod, hevent]

/-- Low-noise strict Hellinger bound, including the noiseless endpoint. -/
theorem bent_low_noise_hellinger_strict {n : ℕ} (hn : 6 ≤ n)
    {f : Cube n → ℝ} (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hlo : 1 - 2 / (3 * (n : ℝ)) ≤ ρ) :
    objective ((cubeBSC n ρ hρ).apply f) < 1 - root ρ := by
  have hR := bent_low_noise_root_mean hn hf hb ρ hρ hlo
  have hroot : root (mean ((cubeBSC n ρ hρ).apply f)) < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
    have hbias := Flatness.noisy_mean_sq hb ρ hρ
    have hp : 0 < ((2 : ℝ) ^ n)⁻¹ := by positivity
    linarith only [hbias, hp]
  unfold objective
  linarith only [hR, hroot]

/-- Full-noise theorem for every bent Boolean function of dimension at least six. -/
theorem bent_large_hellinger {n : ℕ} (hn : 6 ≤ n)
    {f : Cube n → ℝ} (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC n ρ hρ).apply f) ≤ 1 - root ρ ∧
      (0 < ρ → objective ((cubeBSC n ρ hρ).apply f) < 1 - root ρ) := by
  by_cases hhi : ρ ≤ 3 / 10
  · constructor
    · exact BentLarge.bent_high_noise_hellinger (by omega) f hb ρ hρ hhi
    · exact fun hpos => BentLarge.bent_high_noise_hellinger_strict (by omega) f hb ρ hρ hhi hpos
  · by_cases hlo : 1 - 2 / (3 * (n : ℝ)) ≤ ρ
    · have h := bent_low_noise_hellinger_strict hn hf hb ρ hρ hlo
      exact ⟨le_of_lt h, fun _ => h⟩
    · have h := BentLarge.bent_middle_hellinger_strict hn f
        (fun x => (hf x).symm) hb ρ hρ (le_of_not_ge hhi) (le_of_not_ge hlo)
      exact ⟨le_of_lt h, fun _ => h⟩

#print axioms posterior_root_mean_lower
#print axioms bent_large_hellinger
end Hellinger.BentLow
