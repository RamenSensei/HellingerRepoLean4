import Hellinger.ChannelSections
import Hellinger.TranslationNoise
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Exact identification of the Boolean BSC with additive noise over F₂.
All coordinate changes below retain their transformed noise law. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.F2Model

abbrev F2 := ZMod 2
abbrev Cube (n : ℕ) := Fin n → F2

set_option backward.isDefEq.respectTransparency false in
def bitEquiv : Bool ≃ F2 where
  toFun := PaperSpecs.bit
  invFun z := decide (z = 1)
  left_inv b := by cases b <;> norm_num [PaperSpecs.bit]
  right_inv z := by fin_cases z <;> norm_num [PaperSpecs.bit]

@[simp] theorem bitEquiv_false : bitEquiv false = 0 := rfl
@[simp] theorem bitEquiv_true : bitEquiv true = 1 := rfl

def bitsEquiv (ι : Type*) : (ι → Bool) ≃ (ι → F2) :=
  Equiv.arrowCongr (Equiv.refl ι) bitEquiv

@[simp] theorem bitsEquiv_apply {ι : Type*} (x : ι → Bool) (i : ι) :
    bitsEquiv ι x i = bitEquiv (x i) := rfl

@[simp] theorem bitsEquiv_symm_apply {ι : Type*} (x : ι → F2) (i : ι) :
    (bitsEquiv ι).symm x i = bitEquiv.symm (x i) := rfl

def sign (z : F2) : ℝ := if z = 0 then 1 else -1

@[simp] theorem sign_bit (b : Bool) : sign (bitEquiv b) = boolSign b := by
  cases b <;> norm_num [sign, boolSign]

theorem sign_add (a b : F2) : sign (a + b) = sign a * sign b := by
  obtain ⟨a, rfl⟩ := bitEquiv.surjective a
  obtain ⟨b, rfl⟩ := bitEquiv.surjective b
  cases a <;> cases b <;> norm_num [sign, show (1 : F2) + 1 = 0 from rfl]

def transportedChannel {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (e : Ω ≃ Λ) (K : UniformChannel Ω) : UniformChannel Λ where
  weight x y := K.weight (e.symm x) (e.symm y)
  nonneg x y := K.nonneg _ _
  row_sum x := by rw [e.symm.sum_comp]; exact K.row_sum _
  column_sum y := by
    rw [e.symm.sum_comp (fun x => K.weight x (e.symm y))]
    exact K.column_sum _

theorem transportedChannel_apply {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (e : Ω ≃ Λ) (K : UniformChannel Ω) (f : Λ → ℝ) (x : Ω) :
    (transportedChannel e K).apply f (e x) = K.apply (f ∘ e) x := by
  simp only [UniformChannel.apply, transportedChannel, Equiv.symm_apply_apply,
    Function.comp_apply]
  rw [← e.sum_comp (fun y => K.weight x (e.symm y) * f y)]
  simp only [Equiv.symm_apply_apply]

def oneStep (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : UniformChannel F2 :=
  transportedChannel bitEquiv (bsc ρ hρ)

theorem oneStep_weight (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x y : F2) :
    (oneStep ρ hρ).weight x y = if x = y then (1 + ρ) / 2 else (1 - ρ) / 2 := by
  simp [oneStep, transportedChannel, bsc]

def noise (ι : Type*) [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : UniformChannel (ι → F2) :=
  UniformChannel.product (fun _ : ι => oneStep ρ hρ)

theorem noise_weight_bits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x y : ι → Bool) :
    (noise ι ρ hρ).weight (bitsEquiv ι x) (bitsEquiv ι y) =
      (ChannelSections.indexedBSC ι ρ hρ).weight x y := by
  simp [noise, UniformChannel.product, oneStep, transportedChannel,
    ChannelSections.indexedBSC]

theorem noise_apply_bits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f : (ι → F2) → ℝ) (x : ι → Bool) :
    (noise ι ρ hρ).apply f (bitsEquiv ι x) =
      (ChannelSections.indexedBSC ι ρ hρ).apply (f ∘ bitsEquiv ι) x := by
  unfold UniformChannel.apply
  rw [← (bitsEquiv ι).sum_comp
    (fun y => (noise ι ρ hρ).weight (bitsEquiv ι x) y * f y)]
  simp only [noise_weight_bits, Function.comp_apply]

def errorMass {ι : Type*} [Fintype ι] (ρ : ℝ) (e : ι → F2) : ℝ :=
  ∏ i, if e i = 0 then (1 + ρ) / 2 else (1 - ρ) / 2

theorem add_eq_zero_iff (x y : F2) : x + y = 0 ↔ x = y := by
  rw [add_eq_zero_iff_eq_neg, ZMod.neg_eq_self_mod_two]

theorem noise_weight_additive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x y : ι → F2) :
    (noise ι ρ hρ).weight x y = errorMass ρ (x + y) := by
  simp only [noise, UniformChannel.product, oneStep_weight, errorMass, Pi.add_apply,
    add_eq_zero_iff]

theorem errorMass_nonneg {ι : Type*} [Fintype ι] (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (e : ι → F2) : 0 ≤ errorMass ρ e := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith [hρ.1, hρ.2]

theorem errorMass_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : (∑ e : ι → F2, errorMass ρ e) = 1 := by
  have h := (noise ι ρ hρ).row_sum 0
  simp only [noise_weight_additive, zero_add] at h
  exact h

theorem noise_apply_additive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f : (ι → F2) → ℝ) (y : ι → F2) :
    (noise ι ρ hρ).apply f y = ∑ e, errorMass ρ e * f (y + e) := by
  unfold UniformChannel.apply
  rw [← Equiv.sum_comp (Equiv.addLeft y)
    (fun x => (noise ι ρ hρ).weight y x * f x)]
  simp only [Equiv.coe_addLeft, noise_weight_additive]
  have hyy : y + y = 0 := by
    ext i
    exact (add_eq_zero_iff (y i) (y i)).mpr rfl
  simp only [← add_assoc, hyy, zero_add]

end Hellinger.F2Model
