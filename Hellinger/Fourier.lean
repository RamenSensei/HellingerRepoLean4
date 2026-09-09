import Hellinger.BooleanNoise
import Hellinger.Rigidity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp

/-!
# The normalized Walsh transform on the actual Boolean cube

All sums are over every point of Fin n → Bool. Orthogonality, inversion,
Parseval, and noise identities are proved from the finite product definitions.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.Fourier

abbrev Cube (n : ℕ) := Fin n → Bool

def support {n : ℕ} (s : Cube n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => s i = true)

def degree {n : ℕ} (s : Cube n) : ℕ := (support s).card

def phase {n : ℕ} (s x : Cube n) : ℝ :=
  ∏ i, boolSign (s i && x i)

def walsh {n : ℕ} (f : Cube n → ℝ) (s : Cube n) : ℝ :=
  mean (fun x => f x * phase s x)

theorem cube_card (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by simp [Cube]

theorem phase_symm {n : ℕ} (s x : Cube n) : phase s x = phase x s := by
  simp only [phase, Bool.and_comm]

theorem phase_sq {n : ℕ} (s x : Cube n) : phase s x ^ 2 = 1 := by
  simp only [phase, ← Finset.prod_pow, boolSign_sq, Finset.prod_const_one]

theorem phase_character {n : ℕ} (s x : Cube n) :
    phase s x = character n (support s) x := by
  apply Finset.prod_congr rfl
  intro i hi
  cases h : s i <;> simp [support, h, boolSign]

theorem coordinate_orthogonality (a b : Bool) :
    (∑ x : Bool, boolSign (a && x) * boolSign (b && x)) =
      if a = b then (2 : ℝ) else 0 := by
  cases a <;> cases b <;> norm_num [boolSign]

theorem sum_phase_mul {n : ℕ} (s t : Cube n) :
    (∑ x, phase s x * phase t x) =
      if s = t then (2 : ℝ) ^ n else 0 := by
  simp only [phase, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    boolSign (s i && b) * boolSign (t i && b))]
  simp_rw [coordinate_orthogonality]
  by_cases h : s = t
  · subst t
    simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, s i ≠ t i := by
      by_contra! heq
      exact h (funext heq)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem orthogonality {n : ℕ} (s t : Cube n) :
    mean (fun x => phase s x * phase t x) = if s = t then 1 else 0 := by
  rw [mean, cube_card, sum_phase_mul]
  split_ifs <;> simp

theorem walsh_zero {n : ℕ} (f : Cube n → ℝ) :
    walsh f (fun _ => false) = mean f := by
  simp [walsh, phase, boolSign]

theorem inversion {n : ℕ} (f : Cube n → ℝ) (x : Cube n) :
    f x = ∑ s, walsh f s * phase s x := by
  have hexpand : (∑ s, walsh f s * phase s x) =
      (Fintype.card (Cube n) : ℝ)⁻¹ *
        ∑ y, f y * (∑ s, phase s y * phase s x) := by
    unfold walsh mean
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro s hs
    ring
  have hk (y : Cube n) :
      (∑ s, phase s y * phase s x) =
        if y = x then (2 : ℝ) ^ n else 0 := by
    simpa only [phase_symm] using sum_phase_mul y x
  rw [hexpand]
  simp only [hk]
  simp [mul_left_comm]

theorem mean_mul_expansion {n : ℕ} (f : Cube n → ℝ) (a : Cube n → ℝ) :
    mean (fun x => f x * (∑ s, a s * phase s x)) =
      ∑ s, a s * walsh f s := by
  unfold walsh mean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Parseval for every real function on every finite Boolean cube. -/
theorem parseval {n : ℕ} (f : Cube n → ℝ) :
    mean (fun x => f x ^ 2) = ∑ s, walsh f s ^ 2 := by
  calc
    mean (fun x => f x ^ 2) =
        mean (fun x => f x * (∑ s, walsh f s * phase s x)) := by
      congr 1
      funext x
      rw [← inversion f x, pow_two]
    _ = ∑ s, walsh f s * walsh f s := mean_mul_expansion f (walsh f)
    _ = ∑ s, walsh f s ^ 2 := by simp only [pow_two]

theorem walsh_phase {n : ℕ} (s t : Cube n) :
    walsh (phase s) t = if s = t then 1 else 0 := orthogonality s t

theorem walsh_expansion {n : ℕ} (a : Cube n → ℝ) (s : Cube n) :
    walsh (fun x => ∑ t, a t * phase t x) s = a s := by
  unfold walsh
  simp only [mul_comm (∑ t, a t * phase t _) (phase s _)]
  rw [mean_mul_expansion]
  simp [walsh_phase]

theorem noise_phase {n : ℕ} (s : Cube n)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : Cube n) :
    (cubeBSC n ρ hρ).apply (phase s) x = ρ ^ degree s * phase s x := by
  have hp : phase s = character n (support s) := funext (phase_character s)
  rw [hp]
  exact character_eigenfunction n (support s) ρ hρ x

/-- The actual product BSC has the Walsh multiplier rho to the frequency degree. -/
theorem noise_expansion {n : ℕ} (f : Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : Cube n) :
    (cubeBSC n ρ hρ).apply f x =
      ∑ s, (ρ ^ degree s * walsh f s) * phase s x := by
  have hf : f = fun y => ∑ s, walsh f s * phase s y := by
    funext y
    exact inversion f y
  calc
    (cubeBSC n ρ hρ).apply f x =
        (cubeBSC n ρ hρ).apply (fun y => ∑ s, walsh f s * phase s y) x := by
      exact congrArg (fun g => (cubeBSC n ρ hρ).apply g x) hf
    _ = ∑ s, walsh f s * (cubeBSC n ρ hρ).apply (phase s) x := by
      unfold UniformChannel.apply
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = ∑ s, (ρ ^ degree s * walsh f s) * phase s x := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [noise_phase]
      ring

theorem walsh_noise {n : ℕ} (f : Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (s : Cube n) :
    walsh ((cubeBSC n ρ hρ).apply f) s = ρ ^ degree s * walsh f s := by
  have hn : (cubeBSC n ρ hρ).apply f =
      fun x => ∑ t, (ρ ^ degree t * walsh f t) * phase t x := by
    funext x
    exact noise_expansion f ρ hρ x
  rw [hn, walsh_expansion]

theorem noise_second_moment {n : ℕ} (f : Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun x => ((cubeBSC n ρ hρ).apply f x) ^ 2) =
      ∑ s, ρ ^ (2 * degree s) * walsh f s ^ 2 := by
  rw [parseval]
  simp only [walsh_noise, mul_pow, ← pow_mul, Nat.mul_comm]

theorem boolean_parseval {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) :
    (∑ s, walsh f s ^ 2) = 1 := by
  rw [← parseval]
  have hs : (fun x => f x ^ 2) = fun _ => (1 : ℝ) := by
    funext x
    rcases hf x with h | h <;> simp [h]
  rw [hs, mean_const]

theorem phase_abs {n : ℕ} (s x : Cube n) : |phase s x| = 1 := by
  rw [← Real.sqrt_sq_eq_abs, phase_sq]
  norm_num

theorem pow_degree {n : ℕ} (t : ℝ) (s : Cube n) :
    t ^ degree s = ∏ i, if s i = true then t else 1 := by
  rw [← Finset.prod_filter]
  simp [degree, support]

theorem sum_pow_degree (n : ℕ) (t : ℝ) :
    (∑ s : Cube n, t ^ degree s) = (1 + t) ^ n := by
  simp_rw [pow_degree]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bool) =>
    if b = true then t else (1 : ℝ))]
  simp [add_comm]

def translate {n : ℕ} (v x : Cube n) : Cube n :=
  fun i => Bool.xor (x i) (v i)

theorem translate_involutive {n : ℕ} (v : Cube n) :
    Function.Involutive (translate v) := by
  intro x
  funext i
  cases hxi : x i <;> cases hvi : v i <;> simp [translate, hxi, hvi]

def translationEquiv {n : ℕ} (v : Cube n) : Cube n ≃ Cube n :=
  (translate_involutive v).toPerm

theorem translate_twice {n : ℕ} (v x : Cube n) :
    translate v (translate v x) = x := translate_involutive v x

theorem mean_translate {n : ℕ} (f : Cube n → ℝ) (v : Cube n) :
    mean (fun x => f (translate v x)) = mean f := by
  unfold mean
  rw [show (∑ x, f (translate v x)) = ∑ x, f x from (translationEquiv v).sum_comp f]

theorem coordinate_phase_translate (s x v : Bool) :
    boolSign (s && Bool.xor x v) =
      boolSign (s && x) * boolSign (s && v) := by
  cases s <;> cases x <;> cases v <;> norm_num [boolSign]

theorem phase_translate {n : ℕ} (s v x : Cube n) :
    phase s (translate v x) = phase s x * phase s v := by
  simp only [phase, translate, coordinate_phase_translate, Finset.prod_mul_distrib]

def autocorrelation {n : ℕ} (f : Cube n → ℝ) (v : Cube n) : ℝ :=
  mean (fun x => f x * f (translate v x))

/-- The autocorrelation formula follows from actual Fourier inversion. -/
theorem autocorrelation_formula {n : ℕ} (f : Cube n → ℝ) (v : Cube n) :
    autocorrelation f v = ∑ s, walsh f s ^ 2 * phase s v := by
  have he (x : Cube n) : f (translate v x) =
      ∑ s, (walsh f s * phase s v) * phase s x := by
    rw [inversion f (translate v x)]
    apply Finset.sum_congr rfl
    intro s hs
    rw [phase_translate]
    ring
  unfold autocorrelation
  simp_rw [he]
  rw [mean_mul_expansion]
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem phase_zero {n : ℕ} (x : Cube n) : phase (fun _ => false) x = 1 := by
  simp [phase, boolSign]

theorem sum_phase {n : ℕ} (v : Cube n) :
    (∑ s : Cube n, phase s v) =
      if v = (fun _ => false) then (2 : ℝ) ^ n else 0 := by
  have h := sum_phase_mul v (fun _ => false)
  simp only [phase_zero, mul_one] at h
  simpa only [phase_symm] using h

theorem mean_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g := by
  simp [mean, Finset.sum_add_distrib, mul_add]

theorem mean_sub {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g := by
  simp [mean, Finset.sum_sub_distrib, mul_sub]

theorem mean_mul_const {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (c : ℝ) :
    mean (fun x => f x * c) = mean f * c := by
  simp [mean, Finset.sum_mul, mul_assoc]

theorem mean_const_mul {Ω : Type*} [Fintype Ω] (c : ℝ) (f : Ω → ℝ) :
    mean (fun x => c * f x) = c * mean f := by
  simp [mean, Finset.mul_sum, mul_left_comm]

theorem mean_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι] (f : ι → Ω → ℝ) :
    mean (fun x => ∑ i, f i x) = ∑ i, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.mul_sum]

theorem mean_nonneg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f := by
  unfold mean
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun x _ => hf x))

theorem mean_le_mean {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ)
    (hfg : ∀ x, f x ≤ g x) : mean f ≤ mean g := by
  unfold mean
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun x _ => hfg x)) (by positivity)

/-- A normalized finite Cauchy-Schwarz inequality with an explicit pointwise
factorization, useful without fractional real powers. -/
theorem mean_sq_le_mean_mul {Ω : Type*} [Fintype Ω] (r f g : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (he : ∀ x, r x ^ 2 = f x * g x) :
    mean r ^ 2 ≤ mean f * mean g := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun x _ => hf x) (fun x _ => hg x) (fun x _ => (he x).le)
  have hc := mul_le_mul_of_nonneg_left h (sq_nonneg ((Fintype.card Ω : ℝ)⁻¹))
  unfold mean
  simpa only [mul_pow, pow_two, mul_assoc, mul_left_comm] using hc

def unit {n : ℕ} (i : Fin n) : Cube n :=
  fun j => if j = i then true else false

theorem unit_ne_zero {n : ℕ} (i : Fin n) : unit i ≠ (fun _ => false) := by
  intro h
  have hi := congrFun h i
  simp [unit] at hi

theorem translate_comp {n : ℕ} (u v x : Cube n) :
    translate u (translate v x) = translate (translate u v) x := by
  funext i
  cases hxi : x i <;> cases hui : u i <;> cases hvi : v i <;>
    simp [translate, hxi, hui, hvi]

theorem translate_unit {n : ℕ} (i : Fin n) (x : Cube n) :
    translate (unit i) x = Function.update x i (!(x i)) := by
  funext j
  by_cases h : j = i
  · subst j
    cases hxi : x i <;> simp [translate, unit, hxi]
  · simp [translate, unit, h]

theorem unit_pair_ne_zero {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    translate (unit j) (unit i) ≠ (fun _ => false) := by
  intro h
  have hi := congrFun h i
  simp [translate, unit, hij] at hi

theorem mean_translated_product {n : ℕ} (f : Cube n → ℝ) (u v : Cube n) :
    mean (fun x => f (translate u x) * f (translate v x)) =
      autocorrelation f (translate v u) := by
  have h := mean_translate
    (fun x => f (translate u x) * f (translate v x)) u
  simp only [translate_twice, translate_comp] at h
  exact h.symm

#print axioms inversion
#print axioms parseval
#print axioms walsh_noise
#print axioms noise_second_moment

end Hellinger.Fourier
