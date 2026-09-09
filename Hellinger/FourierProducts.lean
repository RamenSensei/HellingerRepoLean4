import Hellinger.Flatness

/-! Product and duality identities for the actual normalized Walsh transform. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Hellinger.FourierProducts
open Fourier

theorem walsh_involution {n : ℕ} (f : Cube n → ℝ) (x : Cube n) :
    walsh (walsh f) x = ((2 : ℝ) ^ n)⁻¹ * f x := by
  change mean (fun s => walsh f s * phase x s) = _
  calc
    mean (fun s => walsh f s * phase x s) =
        ((2 : ℝ) ^ n)⁻¹ * ∑ s, walsh f s * phase s x := by
      simp only [mean, cube_card, Nat.cast_pow, Nat.cast_ofNat]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      rw [phase_symm x s]
    _ = ((2 : ℝ) ^ n)⁻¹ * f x := by rw [← inversion f x]

theorem phase_product {n : ℕ} (s a x : Cube n) :
    phase s x * phase a x = phase (translate s a) x := by
  rw [phase_symm (translate s a) x, phase_translate, phase_symm x a, phase_symm x s]
  ring

theorem walsh_modulate {n : ℕ} (g : Cube n → ℝ) (s a : Cube n) :
    walsh (fun x => g x * phase s x) a = walsh g (translate s a) := by
  unfold walsh
  congr 1
  funext x
  rw [mul_assoc, phase_product]

theorem walsh_mul {n : ℕ} (f g : Cube n → ℝ) (s : Cube n) :
    walsh (fun x => f x * g x) s =
      ∑ a, walsh f a * walsh g (translate s a) := by
  have hi (x : Cube n) : f x * g x * phase s x =
      (g x * phase s x) * (∑ a, walsh f a * phase a x) := by
    rw [← inversion f x]
    ring
  unfold walsh
  simp_rw [hi]
  rw [mean_mul_expansion]
  simp_rw [walsh_modulate]
  rfl

theorem noise_fourth_moment {n : ℕ} (f : Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun x => ((cubeBSC n ρ hρ).apply f x) ^ 4) =
      ∑ s, (∑ a, (ρ ^ degree a * walsh f a) *
        (ρ ^ degree (translate s a) * walsh f (translate s a))) ^ 2 := by
  have h := parseval (fun x => ((cubeBSC n ρ hρ).apply f x) ^ 2)
  simp only [← pow_mul, Nat.reduceMul] at h
  rw [h]
  congr 1
  funext s
  rw [show (fun x => ((cubeBSC n ρ hρ).apply f x) ^ 2) =
      (fun x => (cubeBSC n ρ hρ).apply f x * (cubeBSC n ρ hρ).apply f x) by funext; ring,
    walsh_mul]
  simp_rw [walsh_noise]

#print axioms walsh_involution
#print axioms walsh_mul
#print axioms noise_fourth_moment
end Hellinger.FourierProducts
