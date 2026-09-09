import Hellinger.FiniteInformation
import Hellinger.LinearQuotient

/-! The single coordinate change supplied by the linear-quotient theorem
simultaneously compares every convex posterior functional and actual
KL-defined Boolean-output mutual information, at every noise parameter. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set

namespace Hellinger.QuotientInformation
open F2Model ChannelSections FiniteInformation

/-- Actual negative binary entropy in bits is convex as a function of the
posterior sign bias, including both endpoints. -/
theorem neg_binary_entropy_convex : ConvexOn ℝ (Icc (-1 : ℝ) 1)
    (fun t => -PaperSpecs.binaryEntropyBits ((1 - t) / 2)) := by
  have hc : ConcaveOn ℝ (Icc (-1 : ℝ) 1) (fun t => Real.binEntropy ((1 - t) / 2)) := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hx' : (1 - x) / 2 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
    have hy' : (1 - y) / 2 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hy.1, hy.2]
    have hh := Real.strictConcave_binEntropy.concaveOn.2 hx' hy' ha hb hab
    simp only [smul_eq_mul] at hh ⊢
    have he : (1 - (a * x + b * y)) / 2 = a * ((1 - x) / 2) + b * ((1 - y) / 2) := by
      nlinarith
    rw [he]
    exact hh
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := hc.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  have hd := div_le_div_of_nonneg_right hh (le_of_lt EntropyTransfer.log_two_pos)
  simp only [add_div, mul_div_assoc] at hd
  unfold PaperSpecs.binaryEntropyBits
  nlinarith

/-- Exact transfer from the additive F₂ BSC to the probability model on the
Boolean cube. The displayed quantity is actual KL mutual information. -/
theorem bscMutualInformation_bits (n : ℕ) (g : Cube n → ℝ)
    (hg : ∀ x, g x = -1 ∨ g x = 1) (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    bscMutualInformation (g ∘ bitsEquiv (Fin n)) ρ hρ =
      PaperSpecs.binaryEntropyBits ((1 - mean g) / 2) -
        mean (fun y => PaperSpecs.binaryEntropyBits ((1 - (noise (Fin n) ρ hρ).apply g y) / 2)) := by
  rw [bscMutualInformation_eq_posteriorInformation (g ∘ bitsEquiv (Fin n))
    (fun x => hg _) ρ hρ]
  unfold PaperSpecs.posteriorInformation
  rw [mean_comp_equiv]
  congr 1
  rw [← mean_comp_equiv (bitsEquiv (Fin n))
    (fun y => PaperSpecs.binaryEntropyBits ((1 - (noise (Fin n) ρ hρ).apply g y) / 2))]
  congr 1
  funext x
  rw [Function.comp_apply, noise_apply_bits]
  rfl

/-- A single invertible output-coordinate map, chosen before the noise and
convex test function, provides both the complete convex comparison and the
actual mutual-information comparison. -/
theorem linear_quotient_information (n k : ℕ) (L : Cube n →ₗ[F2] Cube k)
    (hL : Function.Surjective L) (g : Cube k → ℝ)
    (hg : ∀ x, g x = -1 ∨ g x = 1) :
    ∃ M : Cube k ≃ₗ[F2] Cube k,
      mean (g ∘ M) = mean (g ∘ L) ∧
      (∀ (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1)
        (Ψ : ℝ → ℝ), ConvexOn ℝ (Icc (-1 : ℝ) 1) Ψ →
        mean (fun y => Ψ ((noise (Fin n) ρ hρ).apply (g ∘ L) y)) ≤
          mean (fun y => Ψ ((noise (Fin k) ρ hρ).apply (g ∘ M) y))) ∧
      ∀ (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1),
        bscMutualInformation ((g ∘ L) ∘ bitsEquiv (Fin n)) ρ hρ ≤
          bscMutualInformation ((g ∘ M) ∘ bitsEquiv (Fin k)) ρ hρ := by
  have hgc : ∀ x, g x ∈ Icc (-1 : ℝ) 1 := by
    intro x
    rcases hg x with h | h <;> rw [h] <;> norm_num
  obtain ⟨M, hm, hc⟩ := LinearQuotient.linear_quotient_comparison n k L hL g hgc
  refine ⟨M, hm, hc, ?_⟩
  intro ρ hρ
  rw [bscMutualInformation_bits n (g ∘ L) (fun x => hg _) ρ hρ,
    bscMutualInformation_bits k (g ∘ M) (fun x => hg _) ρ hρ, hm]
  have hh := hc ρ hρ (fun t => -PaperSpecs.binaryEntropyBits ((1 - t) / 2))
    neg_binary_entropy_convex
  rw [mean_neg, mean_neg] at hh
  linarith

end Hellinger.QuotientInformation
