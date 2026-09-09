import Hellinger.BooleanNoise
import Hellinger.BentEstimates
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# A concrete two-bit Hellinger theorem

This module connects the actual finite product BSC to the posterior formula
proved analytically in `BentEstimates`. No moment or posterior-formula
hypothesis is imposed on the final canonical theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.TwoBitCase

open Hellinger.BentEstimates

/-- The phase `(-1)^(x₀x₁)` with additive bits represented by `Bool`. -/
def canonical (x : Fin 2 → Bool) : ℝ := boolSign (x 0 && x 1)

/-- Exact expansion of a sum over the four points of the two-bit cube. -/
theorem sum_two_bits (f : (Fin 2 → Bool) → ℝ) :
    (∑ x, f x) = f ![false, false] + f ![false, true] +
      f ![true, false] + f ![true, true] := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp f]
  simp [Fintype.sum_prod_type, finTwoArrowEquiv]
  ring

theorem canonical_mean : mean canonical = (1 : ℝ) / 2 := by
  norm_num [mean, sum_two_bits, canonical, boolSign]

theorem canonical_posterior_ff (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (cubeBSC 2 ρ hρ).apply canonical ![false, false] = (1 + 2 * ρ - ρ ^ 2) / 2 := by
  simp [UniformChannel.apply, sum_two_bits, cubeBSC, UniformChannel.product,
    Fin.prod_univ_two, bsc, canonical, boolSign]
  ring

theorem canonical_posterior_ft (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (cubeBSC 2 ρ hρ).apply canonical ![false, true] = (1 + ρ ^ 2) / 2 := by
  simp [UniformChannel.apply, sum_two_bits, cubeBSC, UniformChannel.product,
    Fin.prod_univ_two, bsc, canonical, boolSign]
  ring

theorem canonical_posterior_tf (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (cubeBSC 2 ρ hρ).apply canonical ![true, false] = (1 + ρ ^ 2) / 2 := by
  simp [UniformChannel.apply, sum_two_bits, cubeBSC, UniformChannel.product,
    Fin.prod_univ_two, bsc, canonical, boolSign]
  ring

theorem canonical_posterior_tt (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (cubeBSC 2 ρ hρ).apply canonical ![true, true] = (1 - 2 * ρ - ρ ^ 2) / 2 := by
  simp [UniformChannel.apply, sum_two_bits, cubeBSC, UniformChannel.product,
    Fin.prod_univ_two, bsc, canonical, boolSign]
  ring

/-- The true BSC posterior average is exactly the four-value analytic expression. -/
theorem canonical_posterior_root_mean (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun y => root ((cubeBSC 2 ρ hρ).apply canonical y)) = twoNoiseR ρ := by
  simp only [mean, sum_two_bits, canonical_posterior_ff, canonical_posterior_ft,
    canonical_posterior_tf, canonical_posterior_tt]
  norm_num [root, twoNoiseR]
  ring

/-- The bias term for the canonical function. -/
theorem canonical_root_mean : root (mean canonical) = Real.sqrt 3 / 2 := by
  rw [canonical_mean]
  unfold root
  have harg : (1 : ℝ) - (1 / 2) ^ 2 = 3 / 4 := by norm_num
  rw [harg, Real.sqrt_div' _ (show 0 ≤ (4 : ℝ) by norm_num)]
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs4]

/-- The true biased Hellinger objective under the two-fold BSC. -/
theorem canonical_objective (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC 2 ρ hρ).apply canonical) = Real.sqrt 3 / 2 - twoNoiseR ρ := by
  unfold objective
  rw [UniformChannel.mean_apply, canonical_root_mean, canonical_posterior_root_mean]

/-- A full-noise Hellinger theorem for an actual nonlinear Boolean function,
with no moment estimates or posterior formula assumed. -/
theorem canonical_hellinger (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC 2 ρ hρ).apply canonical) ≤ 1 - root ρ := by
  rw [canonical_objective]
  have hgap := twoNoiseR_gap_bound ρ hρ.1 hρ.2
  have hpos : 0 ≤ (4 + Real.sqrt (2 : ℝ) - 3 * Real.sqrt 3) / 4 * ρ ^ 2 :=
    mul_nonneg (le_of_lt two_gap_coefficient_pos) (sq_nonneg _)
  unfold root
  linarith

/-- Strictness for the canonical nonlinear Boolean function at every `ρ > 0`. -/
theorem canonical_hellinger_strict (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hρpos : 0 < ρ) :
    objective ((cubeBSC 2 ρ hρ).apply canonical) < 1 - root ρ := by
  rw [canonical_objective]
  exact twoNoiseR_hellinger_strict ρ hρpos hρ.2

/-- The Boolean function negative at one specified vertex and positive elsewhere. -/
def pointPhase (p : Bool × Bool) (x : Fin 2 → Bool) : ℝ :=
  if x 0 = p.1 ∧ x 1 = p.2 then -1 else 1

theorem pointPhase_mean (p : Bool × Bool) : mean (pointPhase p) = (1 : ℝ) / 2 := by
  rcases p with ⟨p₀, p₁⟩
  cases p₀ <;> cases p₁ <;> norm_num [mean, sum_two_bits, pointPhase]

/-- All four posterior values, simultaneously for each of the four negative-vertex choices. -/
theorem pointPhase_posterior (p : Bool × Bool) (y₀ y₁ : Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (cubeBSC 2 ρ hρ).apply (pointPhase p) ![y₀, y₁] =
      if y₀ = p.1 then
        (if y₁ = p.2 then (1 - 2 * ρ - ρ ^ 2) / 2 else (1 + ρ ^ 2) / 2)
      else
        (if y₁ = p.2 then (1 + ρ ^ 2) / 2 else (1 + 2 * ρ - ρ ^ 2) / 2) := by
  rcases p with ⟨p₀, p₁⟩
  cases p₀ <;> cases p₁ <;> cases y₀ <;> cases y₁ <;>
    simp [UniformChannel.apply, sum_two_bits, cubeBSC, UniformChannel.product,
      Fin.prod_univ_two, bsc, pointPhase] <;> ring

theorem pointPhase_posterior_root_mean (p : Bool × Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun y => root ((cubeBSC 2 ρ hρ).apply (pointPhase p) y)) = twoNoiseR ρ := by
  simp only [mean, sum_two_bits, pointPhase_posterior]
  rcases p with ⟨p₀, p₁⟩
  cases p₀ <;> cases p₁ <;> norm_num [root, twoNoiseR] <;> ring

theorem pointPhase_objective (p : Bool × Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC 2 ρ hρ).apply (pointPhase p)) = Real.sqrt 3 / 2 - twoNoiseR ρ := by
  unfold objective
  rw [UniformChannel.mean_apply, pointPhase_mean, pointPhase_posterior_root_mean]
  have hr : root ((1 : ℝ) / 2) = Real.sqrt 3 / 2 := by
    simpa only [canonical_mean] using canonical_root_mean
  rw [hr]

/-- Output complementation leaves the biased Hellinger objective unchanged. -/
theorem objective_apply_neg {Ω : Type*} [Fintype Ω]
    (K : UniformChannel Ω) (f : Ω → ℝ) :
    objective (K.apply (fun x => -f x)) = objective (K.apply f) := by
  have hk : K.apply (fun x => -f x) = fun x => -K.apply f x := by
    funext x
    simp [UniformChannel.apply, Finset.sum_neg_distrib]
  rw [hk]
  have hm : mean (fun x => -K.apply f x) = -mean (K.apply f) := by
    simp [mean, Finset.sum_neg_distrib]
  unfold objective
  rw [hm, root_neg]
  congr 1
  apply congrArg mean
  funext x
  exact root_neg _

/-- The eight truth tables obtained from four single-minus functions and their complements. -/
def eightPhase (p : Bool × Bool) (complement : Bool) (x : Fin 2 → Bool) : ℝ :=
  boolSign complement * pointPhase p x

theorem eightPhase_boolean (p : Bool × Bool) (complement : Bool) (x : Fin 2 → Bool) :
    eightPhase p complement x = -1 ∨ eightPhase p complement x = 1 := by
  cases complement <;> by_cases h : x 0 = p.1 ∧ x 1 = p.2 <;>
    simp [eightPhase, boolSign, pointPhase, h]

/-- Exact objective for every function in the eight-truth-table family. -/
theorem eightPhase_objective (p : Bool × Bool) (complement : Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC 2 ρ hρ).apply (eightPhase p complement)) =
      Real.sqrt 3 / 2 - twoNoiseR ρ := by
  cases complement
  · have hf : eightPhase p false = pointPhase p := by funext x; simp [eightPhase, boolSign]
    rw [hf]
    exact pointPhase_objective p ρ hρ
  · have hf : eightPhase p true = fun x => -pointPhase p x := by
      funext x; simp [eightPhase, boolSign]
    rw [hf]
    exact (objective_apply_neg (cubeBSC 2 ρ hρ) (pointPhase p)).trans (pointPhase_objective p ρ hρ)

/-- Full-noise Hellinger inequality for all eight explicit two-bit truth tables. -/
theorem eightPhase_hellinger (p : Bool × Bool) (complement : Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC 2 ρ hρ).apply (eightPhase p complement)) ≤ 1 - root ρ := by
  rw [eightPhase_objective, ← canonical_objective ρ hρ]
  exact canonical_hellinger ρ hρ

/-- Strictness for all eight truth tables at every positive correlation. -/
theorem eightPhase_hellinger_strict (p : Bool × Bool) (complement : Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) :
    objective ((cubeBSC 2 ρ hρ).apply (eightPhase p complement)) < 1 - root ρ := by
  rw [eightPhase_objective, ← canonical_objective ρ hρ]
  exact canonical_hellinger_strict ρ hρ hρpos

/-- Normalized Walsh transform on the two-bit cube; the four frequencies are
indexed by `Bool × Bool`, and the dot product uses Boolean XOR. -/
def normalizedWalsh (f : (Fin 2 → Bool) → ℝ) (s : Bool × Bool) : ℝ :=
  mean (fun x => f x * boolSign (Bool.xor (s.1 && x 0) (s.2 && x 1)))

/-- The standard flat-Walsh definition of a two-bit bent real-valued phase.
Boolean-valuedness is a separate hypothesis in the final classification theorem. -/
def IsBent2 (f : (Fin 2 → Bool) → ℝ) : Prop :=
  ∀ s : Bool × Bool, normalizedWalsh f s ^ 2 = 1 / 4

theorem normalizedWalsh_zero (f : (Fin 2 → Bool) → ℝ) :
    normalizedWalsh f (false, false) = mean f := by
  simp [normalizedWalsh, boolSign, mean]

/-- Every member of the eight-table family is indeed bent by the flat-Walsh definition. -/
theorem eightPhase_isBent2 (p : Bool × Bool) (complement : Bool) : IsBent2 (eightPhase p complement) := by
  intro s
  rcases p with ⟨p₀, p₁⟩
  rcases s with ⟨s₀, s₁⟩
  cases p₀ <;> cases p₁ <;> cases complement <;> cases s₀ <;> cases s₁ <;>
    norm_num [normalizedWalsh, mean, sum_two_bits, eightPhase, pointPhase, boolSign]

theorem two_bits_ext {f g : (Fin 2 → Bool) → ℝ}
    (hff : f ![false, false] = g ![false, false])
    (hft : f ![false, true] = g ![false, true])
    (htf : f ![true, false] = g ![true, false])
    (htt : f ![true, true] = g ![true, true]) : f = g := by
  funext x
  have hx : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  cases h₀ : x 0 <;> cases h₁ : x 1
  · simpa only [h₀, h₁] using hff
  · simpa only [h₀, h₁] using hft
  · simpa only [h₀, h₁] using htf
  · simpa only [h₀, h₁] using htt

/-- Boolean-valuedness and squared mean `1/4` already force one of the eight tables.
The proof is a kernel-checked exhaustion of the sixteen Boolean truth tables. -/
theorem classify_of_mean_sq (f : (Fin 2 → Bool) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hm : mean f ^ 2 = 1 / 4) :
    ∃ p : Bool × Bool, ∃ complement : Bool, f = eightPhase p complement := by
  rcases hf ![false, false] with hff | hff <;>
    rcases hf ![false, true] with hft | hft <;>
    rcases hf ![true, false] with htf | htf <;>
    rcases hf ![true, true] with htt | htt
  all_goals norm_num [mean, sum_two_bits, hff, hft, htf, htt] at hm
  all_goals
    solve
    | refine ⟨(false, false), false, ?_⟩
      apply two_bits_ext <;> simp [eightPhase, pointPhase, boolSign, hff, hft, htf, htt]
    | refine ⟨(false, false), true, ?_⟩
      apply two_bits_ext <;> simp [eightPhase, pointPhase, boolSign, hff, hft, htf, htt]
    | refine ⟨(false, true), false, ?_⟩
      apply two_bits_ext <;> simp [eightPhase, pointPhase, boolSign, hff, hft, htf, htt]
    | refine ⟨(false, true), true, ?_⟩
      apply two_bits_ext <;> simp [eightPhase, pointPhase, boolSign, hff, hft, htf, htt]
    | refine ⟨(true, false), false, ?_⟩
      apply two_bits_ext <;> simp [eightPhase, pointPhase, boolSign, hff, hft, htf, htt]
    | refine ⟨(true, false), true, ?_⟩
      apply two_bits_ext <;> simp [eightPhase, pointPhase, boolSign, hff, hft, htf, htt]
    | refine ⟨(true, true), false, ?_⟩
      apply two_bits_ext <;> simp [eightPhase, pointPhase, boolSign, hff, hft, htf, htt]
    | refine ⟨(true, true), true, ?_⟩
      apply two_bits_ext <;> simp [eightPhase, pointPhase, boolSign, hff, hft, htf, htt]

/-- Complete two-variable bent classification, starting from Boolean and Walsh conditions. -/
theorem classify_bent2 (f : (Fin 2 → Bool) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : IsBent2 f) :
    ∃ p : Bool × Bool, ∃ complement : Bool, f = eightPhase p complement := by
  apply classify_of_mean_sq f hf
  simpa only [normalizedWalsh_zero] using hb (false, false)

/-- Full-noise Hellinger theorem for every two-variable bent Boolean function,
under the actual finite product BSC, with no moment or classification hypothesis. -/
theorem bent2_hellinger (f : (Fin 2 → Bool) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : IsBent2 f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC 2 ρ hρ).apply f) ≤ 1 - root ρ := by
  obtain ⟨p, complement, rfl⟩ := classify_bent2 f hf hb
  exact eightPhase_hellinger p complement ρ hρ

/-- Strictness for every two-variable bent Boolean function when `ρ > 0`. -/
theorem bent2_hellinger_strict (f : (Fin 2 → Bool) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : IsBent2 f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) :
    objective ((cubeBSC 2 ρ hρ).apply f) < 1 - root ρ := by
  obtain ⟨p, complement, rfl⟩ := classify_bent2 f hf hb
  exact eightPhase_hellinger_strict p complement ρ hρ hρpos

#print axioms canonical_posterior_root_mean
#print axioms canonical_hellinger
#print axioms canonical_hellinger_strict
#print axioms eightPhase_hellinger
#print axioms eightPhase_hellinger_strict
#print axioms classify_bent2
#print axioms bent2_hellinger
#print axioms bent2_hellinger_strict

end Hellinger.TwoBitCase
