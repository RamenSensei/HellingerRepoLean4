import Hellinger.ProbabilityContracts
import Hellinger.FlatnessConsequences
import Hellinger.BentLowExact
import Hellinger.OddDual
import Hellinger.SpectralContracts

/-! Full types for the manuscript's function-class theorems. Information is
the KL mutual information of the actual BSC joint law. Noise endpoints,
nonzero biases, every dimension, and both equality directions are retained. -/

set_option autoImplicit false
noncomputable section

namespace Hellinger.FunctionContracts
open PaperSpecs FiniteInformation

theorem translation (n : ℕ) (f : Cube n → ℝ) (hf : IsBoolean f)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hs : SignReversing f S)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean f = 0 ∧ root ρ ≤ posteriorRootMean f ρ hρ ∧
    HellingerBound f ρ hρ ∧
    bscMutualInformation f ρ hρ ≤ 1 - binaryEntropyBits ((1 - ρ) / 2) ∧
    (0 < ρ → ρ < 1 →
      (objective ((cubeBSC n ρ hρ).apply f) = 1 - root ρ ↔ SignedDictatorOn f S) ∧
      (bscMutualInformation f ρ hρ = 1 - binaryEntropyBits ((1 - ρ) / 2) ↔
        SignedDictatorOn f S)) := by
  obtain ⟨hm, hR, hH⟩ := ChannelSections.translation_hellinger n f hf S hS hs ρ hρ
  obtain ⟨hI, heI⟩ := ProbabilityContracts.translation_information n f hf S hS hs ρ hρ
  refine ⟨hm, hR, hH, hI, ?_⟩
  intro hp hl
  refine ⟨?_, heI hp hl⟩
  have heR := TranslationEquality.translation_equality n f hf S hS hs ρ hρ hp hl
  have hobj : objective ((cubeBSC n ρ hρ).apply f) = 1 - posteriorRootMean f ρ hρ := by
    simp only [objective, UniformChannel.mean_apply, hm, posteriorRootMean]
    norm_num [root]
  rw [hobj]
  have he : (1 - posteriorRootMean f ρ hρ = 1 - root ρ) ↔
      posteriorRootMean f ρ hρ = root ρ := by constructor <;> intro h <;> linarith
  exact he.trans heR

theorem flat_spectra_and_quadratic_phases :
    (∀ (n : ℕ), 0 < n → ∀ (f : Cube n → ℝ), IsBoolean f → Flatness.IsBent f →
      ∀ (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1),
        HellingerBound f ρ hρ ∧
        bscMutualInformation f ρ hρ ≤ 1 - binaryEntropyBits ((1 - ρ) / 2) ∧
        (0 < ρ → objective ((cubeBSC n ρ hρ).apply f) < 1 - root ρ)) ∧
    (∀ (n : ℕ), 0 < n → ∀ (f : Cube n → ℝ), IsQuadratic f →
      ∀ (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1),
        HellingerBound f ρ hρ ∧
        bscMutualInformation f ρ hρ ≤ 1 - binaryEntropyBits ((1 - ρ) / 2) ∧
        (0 < ρ → ρ < 1 →
          (objective ((cubeBSC n ρ hρ).apply f) = 1 - root ρ ↔ SignedDictatorOn f Finset.univ) ∧
          (bscMutualInformation f ρ hρ = 1 - binaryEntropyBits ((1 - ρ) / 2) ↔
            SignedDictatorOn f Finset.univ))) := by
  constructor
  · intro n hn f hf hb ρ hρ
    obtain ⟨hH, hstrict⟩ := AllBent.paper_bent_hellinger n hn f hf hb ρ hρ
    exact ⟨hH, (ProbabilityContracts.bent_information n hn f hf hb ρ hρ).1, hstrict⟩
  · intro n hn f hq ρ hρ
    obtain ⟨hH, heH⟩ := AllQuadratic.paper_quadratic_hellinger n hn f hq ρ hρ
    obtain ⟨hI, heI⟩ := ProbabilityContracts.quadratic_information n hn f hq ρ hρ
    exact ⟨hH, hI, fun hp hl => ⟨heH hp hl, heI hp hl⟩⟩

theorem flat_amplitude (n : ℕ) : Flatness.amplitude n = (2 : ℝ) ^ (-(n : ℝ) / 2) := by
  rw [Flatness.amplitude, Real.sqrt_eq_rpow, ← Real.rpow_natCast (2 : ℝ) n,
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem bent_definition_equivalence (n : ℕ) (f : Cube n → ℝ) :
    Flatness.IsBent f ↔ ∀ s, |Fourier.walsh f s| = (2 : ℝ) ^ (-(n : ℝ) / 2) := by
  rw [Flatness.isBent_iff_abs, flat_amplitude]

theorem consequences_of_flatness (n : ℕ) (_hn : 0 < n) (f : Cube n → ℝ)
    (hf : IsBoolean f) (hb : Flatness.IsBent f) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    Even n ∧ mean f ^ 2 = ((2 : ℝ) ^ n)⁻¹ ∧
    mean (fun x => ((cubeBSC n ρ hρ).apply f x) ^ 2) = ((2 : ℝ) ^ n)⁻¹ * (1 + ρ ^ 2) ^ n ∧
    (∀ x, |(cubeBSC n ρ hρ).apply f x| ≤ (2 : ℝ) ^ (-(n : ℝ) / 2) * (1 + ρ) ^ n) ∧
    (∀ x, Flatness.sensitivity f x =
      ((Finset.univ.filter (fun i => f (Function.update x i (!(x i))) ≠ f x)).card : ℝ)) ∧
    mean (Flatness.sensitivity f) = (n : ℝ) / 2 ∧
    mean (fun x => Flatness.sensitivity f x ^ 2) = (n : ℝ) * (n + 1) / 4 ∧
    (n : ℝ) / Real.sqrt (2 * (n + 1)) ≤ mean (fun x => Real.sqrt (Flatness.sensitivity f x)) := by
  refine ⟨Flatness.dimension_even hf hb, Flatness.mean_sq hb,
    Flatness.noise_second_moment hb ρ hρ, ?_, Flatness.sensitivity_eq_card hf,
    Flatness.sensitivity_mean hb, Flatness.sensitivity_second_moment hf hb,
    Flatness.sensitivity_sqrt_mean_lower hf hb⟩
  intro x
  rw [← flat_amplitude]
  exact Flatness.noise_abs_le hb ρ hρ x

theorem odd_real_dual (n : ℕ) (h : Cube n → ℝ)
    (ho : ∀ x, h (antipode n x) = -h x) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    root ρ ≤ mean (fun x => Real.sqrt (1 + h x ^ 2)) -
      mean (fun x => |(cubeBSC n ρ hρ).apply h x|) ∧
    (0 < ρ → ρ < 1 →
      (mean (fun x => Real.sqrt (1 + h x ^ 2)) -
        mean (fun x => |(cubeBSC n ρ hρ).apply h x|) = root ρ ↔
        ∃ i : Fin n, ∃ negative : Bool,
          h = fun x => (ρ / root ρ) * (if negative then -boolSign (x i) else boolSign (x i)))) := by
  exact ⟨OddDual.odd_dual_bound_all n h ho ρ hρ,
    fun hp hl => OddDual.odd_dual_equality_iff_all n h ho ρ hρ hp hl⟩

theorem bent_high_noise (n : ℕ) (hn : 4 ≤ n) (f : Cube n → ℝ)
    (_hf : IsBoolean f) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hhigh : ρ ≤ 3 / 10) :
    HellingerBound f ρ hρ ∧ (0 < ρ → objective ((cubeBSC n ρ hρ).apply f) < 1 - root ρ) := by
  exact ⟨BentLarge.bent_high_noise_hellinger hn f hb ρ hρ hhigh,
    fun hp => BentLarge.bent_high_noise_hellinger_strict hn f hb ρ hρ hhigh hp⟩

theorem bent_large_dimension (n : ℕ) (hn : 6 ≤ n) (f : Cube n → ℝ)
    (hf : IsBoolean f) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    HellingerBound f ρ hρ ∧ (0 < ρ → objective ((cubeBSC n ρ hρ).apply f) < 1 - root ρ) :=
  BentLow.bent_large_hellinger hn hf hb ρ hρ

theorem four_point_completion (n : ℕ) (f : Cube n → ℝ)
    (hf : IsBoolean f) (hmean : mean f = 0) (x y : Cube n)
    (hyx : y ≠ x) (hyax : y ≠ antipode n x)
    (hfx : f x = 1) (hfax : f (antipode n x) = 1)
    (hfy : f y = -1) (hfay : f (antipode n y) = -1)
    (hother : ∀ z, z ≠ x → z ≠ antipode n x → z ≠ y → z ≠ antipode n y →
      f (antipode n z) = -f z)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (∃ g : Cube n → ℝ,
      (g = FourPoint.plusCompletion f x y ∨ g = FourPoint.minusCompletion f x y) ∧
      IsBoolean g ∧ (∀ z, g (antipode n z) = -g z) ∧
      (∀ z, z ≠ x → z ≠ antipode n x → z ≠ y → z ≠ antipode n y → g z = f z) ∧
      objective ((cubeBSC n ρ hρ).apply f) ≤ objective ((cubeBSC n ρ hρ).apply g)) ∧
    HellingerBound f ρ hρ ∧
    bscMutualInformation f ρ hρ ≤ 1 - binaryEntropyBits ((1 - ρ) / 2) := by
  exact ⟨FourPoint.four_point_completion n f hf hmean x y hyx hyax hfx hfax hfy hfay hother ρ hρ,
    ProbabilityContracts.four_point_information n f hf hmean x y hyx hyax hfx hfax hfy hfay hother ρ hρ⟩

end Hellinger.FunctionContracts
