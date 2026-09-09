import Hellinger.FiniteInformation
import Hellinger.TranslationInformation
import Hellinger.ClassInformation
import Hellinger.FourPoint

/-! The manuscript information theorems for genuine KL mutual information of
Boolean outputs of uniform-input product binary symmetric channels. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.ProbabilityContracts
open PaperSpecs FiniteInformation

/-- The biased entropy transfer stated for the actual BSC probability model. -/
theorem entropy_transfer {n : ℕ} (f : Cube n → ℝ) (hf : IsBoolean f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hH : HellingerBound f ρ hρ) :
    bscMutualInformation f ρ hρ ≤ 1 - binaryEntropyBits ((1 - ρ) / 2) :=
  bscMutualInformation_le_of_hellinger f hf ρ hρ hH

/-- The information bound for every nonempty sign-reversing translation, with
exactly the signed dictators on the reversed coordinate set as interior-noise
maximizers. -/
theorem translation_information (n : ℕ) (f : Cube n → ℝ) (hf : IsBoolean f)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hs : SignReversing f S)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    bscMutualInformation f ρ hρ ≤ 1 - binaryEntropyBits ((1 - ρ) / 2) ∧
      (0 < ρ → ρ < 1 →
        (bscMutualInformation f ρ hρ = 1 - binaryEntropyBits ((1 - ρ) / 2) ↔
          SignedDictatorOn f S)) := by
  rw [bscMutualInformation_eq_posteriorInformation f hf]
  exact TranslationInformation.translation_information n f hf S hS hs ρ hρ

/-- Every positive-dimensional bent Boolean function has strictly smaller
information than a dictator whenever the channel has positive correlation. -/
theorem bent_information (n : ℕ) (hn : 0 < n) (f : Cube n → ℝ)
    (hf : IsBoolean f) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    bscMutualInformation f ρ hρ ≤ 1 - binaryEntropyBits ((1 - ρ) / 2) ∧
      (0 < ρ → bscMutualInformation f ρ hρ < 1 - binaryEntropyBits ((1 - ρ) / 2)) := by
  rw [bscMutualInformation_eq_posteriorInformation f hf]
  exact ClassInformation.bent_information n hn f hf hb ρ hρ

/-- All positive-dimensional quadratic Boolean phases satisfy the information
bound, and their interior-noise maximizers are exactly the signed dictators. -/
theorem quadratic_information (n : ℕ) (hn : 0 < n) (f : Cube n → ℝ)
    (hq : IsQuadratic f) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    bscMutualInformation f ρ hρ ≤ 1 - binaryEntropyBits ((1 - ρ) / 2) ∧
      (0 < ρ → ρ < 1 →
        (bscMutualInformation f ρ hρ = 1 - binaryEntropyBits ((1 - ρ) / 2) ↔
          SignedDictatorOn f Finset.univ)) := by
  rw [bscMutualInformation_eq_posteriorInformation f (ClassInformation.quadratic_isBoolean hq)]
  exact ClassInformation.quadratic_information n hn f hq ρ hρ

theorem strict_entropy_transfer {n : ℕ} (f : Cube n → ℝ) (hf : IsBoolean f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hH : objective ((cubeBSC n ρ hρ).apply f) < 1 - root ρ) :
    bscMutualInformation f ρ hρ < 1 - binaryEntropyBits ((1 - ρ) / 2) := by
  rw [bscMutualInformation_eq_posteriorInformation f hf]
  exact EntropyTransfer.strict_hellinger_implies_strict_ck f hf ρ hρ hH

theorem information_equality_implies_hellinger_equality {n : ℕ} (f : Cube n → ℝ)
    (hf : IsBoolean f) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hH : HellingerBound f ρ hρ)
    (hI : bscMutualInformation f ρ hρ = 1 - binaryEntropyBits ((1 - ρ) / 2)) :
    objective ((cubeBSC n ρ hρ).apply f) = 1 - root ρ := by
  rw [bscMutualInformation_eq_posteriorInformation f hf] at hI
  exact EntropyTransfer.ck_equality_implies_hellinger_equality f hf ρ hρ hH hI

theorem signed_dictator_information (n : ℕ) (i : Fin n) (negative : Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    bscMutualInformation
      (fun x : Cube n => if negative then -boolSign (x i) else boolSign (x i)) ρ hρ =
        1 - binaryEntropyBits ((1 - ρ) / 2) := by
  have hf : IsBoolean
      (fun x : Cube n => if negative then -boolSign (x i) else boolSign (x i)) := by
    intro x
    cases negative <;> cases hx : x i <;> norm_num [boolSign, hx]
  rw [bscMutualInformation_eq_posteriorInformation _ hf]
  exact EntropyTransfer.signed_dictator_information n i negative ρ hρ

/-- The exceptional-four-point class also satisfies the bound for actual
Boolean-output mutual information. -/
theorem four_point_information (n : ℕ) (f : Cube n → ℝ)
    (hf : IsBoolean f) (hmean : mean f = 0) (x y : Cube n)
    (hyx : y ≠ x) (hyax : y ≠ antipode n x)
    (hfx : f x = 1) (hfax : f (antipode n x) = 1)
    (hfy : f y = -1) (hfay : f (antipode n y) = -1)
    (hother : ∀ z, z ≠ x → z ≠ antipode n x → z ≠ y → z ≠ antipode n y →
      f (antipode n z) = -f z)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    HellingerBound f ρ hρ ∧
      bscMutualInformation f ρ hρ ≤ 1 - binaryEntropyBits ((1 - ρ) / 2) := by
  rw [bscMutualInformation_eq_posteriorInformation f hf]
  exact FourPoint.four_point_bounds n f hf hmean x y hyx hyax hfx hfax hfy hfay hother ρ hρ

/-- The zero-dimensional quotient channel is the identity on its singleton
input space. -/
theorem zero_dimension_noise (f : Cube 0 → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : (cubeBSC 0 ρ hρ).apply f = f := by
  funext y
  calc
    _ = ∑ x : Cube 0, (cubeBSC 0 ρ hρ).weight y x * f y := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Subsingleton.elim x y]
    _ = f y := by rw [← Finset.sum_mul, UniformChannel.row_sum, one_mul]

theorem zero_dimension_objective (f : Cube 0 → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : objective ((cubeBSC 0 ρ hρ).apply f) = 0 := by
  rw [zero_dimension_noise]
  have hc : f = fun _ => f default := by
    funext x
    exact congrArg f (Subsingleton.elim x default)
  rw [hc]
  simp only [objective, mean_const, sub_self]

theorem zero_dimension_information (f : Cube 0 → ℝ) (hf : IsBoolean f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : bscMutualInformation f ρ hρ = 0 := by
  rw [bscMutualInformation_eq_posteriorInformation f hf]
  unfold posteriorInformation
  rw [zero_dimension_noise]
  have hc : f = fun _ => f default := by
    funext x
    exact congrArg f (Subsingleton.elim x default)
  rw [hc]
  simp only [mean_const, sub_self]

theorem zero_dimension_strict_hellinger (f : Cube 0 → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hp : 0 < ρ) :
    objective ((cubeBSC 0 ρ hρ).apply f) < 1 - root ρ := by
  rw [zero_dimension_objective]
  have hr : root ρ < 1 := (Real.sqrt_lt' zero_lt_one).mpr (by nlinarith)
  linarith

end Hellinger.ProbabilityContracts
