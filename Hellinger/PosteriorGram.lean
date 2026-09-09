import Hellinger.PosteriorState
import Hellinger.FourierRigidity
import Hellinger.TraceEquality

/-!
# Actual posterior components and neighboring Gram identities

All vectors are constructed from the finite BSC kernel and the Boolean output.
Strict posterior bounds and edge inner products are derived directly.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Matrix

namespace Hellinger.PosteriorGram

open Hellinger.Fourier Hellinger.PosteriorState

def plusVector {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (K : UniformChannel Ω)
    (y : Ω) : Ω → ℝ :=
  fun x => if f x = 1 then posteriorVector K y x else 0

def minusVector {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (K : UniformChannel Ω)
    (y : Ω) : Ω → ℝ :=
  fun x => if f x = 1 then 0 else posteriorVector K y x

theorem boolean_has_both_signs {Ω : Type*} (f : Ω → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hnonconstant : ∃ x z, f x ≠ f z) :
    (∃ x, f x = 1) ∧ ∃ x, f x = -1 := by
  obtain ⟨x, z, hxz⟩ := hnonconstant
  rcases hf x with hx | hx <;> rcases hf z with hz | hz
  · exact False.elim (hxz (hx.trans hz.symm))
  · exact ⟨⟨z, hz⟩, ⟨x, hx⟩⟩
  · exact ⟨⟨x, hx⟩, ⟨z, hz⟩⟩
  · exact False.elim (hxz (hx.trans hz.symm))

theorem bsc_weight_pos (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1)
    (y x : Bool) : 0 < (bsc ρ hρ).weight y x := by
  change 0 < if y = x then (1 + ρ) / 2 else (1 - ρ) / 2
  split_ifs <;> linarith [hρ.1]

theorem cube_weight_pos (n : ℕ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hρlt : ρ < 1) (y x : Cube n) : 0 < (cubeBSC n ρ hρ).weight y x := by
  change 0 < ∏ i : Fin n, (bsc ρ hρ).weight (y i) (x i)
  exact Finset.prod_pos (fun i _ => bsc_weight_pos ρ hρ hρlt (y i) (x i))

theorem apply_strict_bounds {Ω : Type*} [Fintype Ω]
    (K : UniformChannel Ω) (hK : ∀ y x, 0 < K.weight y x) (f : Ω → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hnonconstant : ∃ x z, f x ≠ f z) (y : Ω) :
    -1 < K.apply f y ∧ K.apply f y < 1 := by
  obtain ⟨⟨xp, hxp⟩, ⟨xm, hxm⟩⟩ := boolean_has_both_signs f hf hnonconstant
  have hb (x : Ω) : -1 ≤ f x ∧ f x ≤ 1 := by
    rcases hf x with h | h <;> norm_num [h]
  constructor
  · calc
      -1 = ∑ x, K.weight y x * (-1) := by rw [← Finset.sum_mul, K.row_sum]; ring
      _ < K.apply f y := by
        apply Finset.sum_lt_sum
        · intro x hx
          exact mul_le_mul_of_nonneg_left (hb x).1 (hK y x).le
        · refine ⟨xp, Finset.mem_univ _, ?_⟩
          rw [hxp]
          linarith [hK y xp]
  · calc
      K.apply f y < ∑ x, K.weight y x * 1 := by
        apply Finset.sum_lt_sum
        · intro x hx
          exact mul_le_mul_of_nonneg_left (hb x).2 (hK y x).le
        · refine ⟨xm, Finset.mem_univ _, ?_⟩
          rw [hxm]
          linarith [hK y xm]
      _ = 1 := by simp only [mul_one, K.row_sum]

theorem posterior_strict_bounds {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hnonconstant : ∃ x z, f x ≠ f z)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1) (y : Cube n) :
    -1 < (cubeBSC n ρ hρ).apply f y ∧ (cubeBSC n ρ hρ).apply f y < 1 :=
  apply_strict_bounds (cubeBSC n ρ hρ) (cube_weight_pos n ρ hρ hρlt)
    f hf hnonconstant y

theorem plus_norm_sq {Ω : Type*} [Fintype Ω] (f : Ω → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (K : UniformChannel Ω) (y : Ω) :
    plusVector f K y ⬝ᵥ plusVector f K y = (1 + K.apply f y) / 2 := by
  have he (x : Ω) : plusVector f K y x * plusVector f K y x =
      (K.weight y x + K.weight y x * f x) / 2 := by
    rcases hf x with h | h
    · norm_num [plusVector, h]
    · simp only [plusVector, h, if_true, posteriorVector, Real.mul_self_sqrt (K.nonneg y x)]
      ring
  unfold dotProduct
  simp only [he]
  rw [← Finset.sum_div, Finset.sum_add_distrib, K.row_sum]
  rfl

theorem minus_norm_sq {Ω : Type*} [Fintype Ω] (f : Ω → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (K : UniformChannel Ω) (y : Ω) :
    minusVector f K y ⬝ᵥ minusVector f K y = (1 - K.apply f y) / 2 := by
  have he (x : Ω) : minusVector f K y x * minusVector f K y x =
      (K.weight y x - K.weight y x * f x) / 2 := by
    rcases hf x with h | h
    · norm_num [minusVector, h, posteriorVector, Real.mul_self_sqrt (K.nonneg y x)]
    · simp only [minusVector, h, if_true]
      ring
  unfold dotProduct
  simp only [he]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, K.row_sum]
  rfl

theorem component_orthogonal {Ω : Type*} [Fintype Ω]
    (f : Ω → ℝ) (K : UniformChannel Ω) (y z : Ω) :
    plusVector f K y ⬝ᵥ minusVector f K z = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  by_cases h : f x = 1 <;> simp [plusVector, minusVector, h]

theorem bsc_flip_sum (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (y x : Bool) :
    (bsc ρ hρ).weight y x + (bsc ρ hρ).weight (!y) x = 1 := by
  cases y <;> cases x <;> simp [bsc] <;> ring

theorem bsc_flip_sqrt_product (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (y x : Bool) :
    Real.sqrt ((bsc ρ hρ).weight y x) *
      Real.sqrt ((bsc ρ hρ).weight (!y) x) = root ρ / 2 := by
  cases y <;> cases x <;> simpa [bsc, mul_comm] using bsc_sqrt_cross ρ hρ

theorem cube_weight_split {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (y x : Cube n) (i : Fin n) :
    (cubeBSC n ρ hρ).weight y x =
      (bsc ρ hρ).weight (y i) (x i) *
        ∏ j ∈ Finset.univ.erase i, (bsc ρ hρ).weight (y j) (x j) := by
  exact (Finset.mul_prod_erase Finset.univ
    (fun j => (bsc ρ hρ).weight (y j) (x j)) (Finset.mem_univ i)).symm

theorem cube_weight_neighbor_sum {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (y x : Cube n) (i : Fin n) :
    (cubeBSC n ρ hρ).weight y x +
      (cubeBSC n ρ hρ).weight (Function.update y i (!(y i))) x =
        ∏ j ∈ Finset.univ.erase i, (bsc ρ hρ).weight (y j) (x j) := by
  rw [cube_weight_split ρ hρ y x i,
    cube_weight_split ρ hρ (Function.update y i (!(y i))) x i]
  simp only [Function.update_self]
  have he :
      (∏ j ∈ Finset.univ.erase i,
        (bsc ρ hρ).weight ((Function.update y i (!(y i))) j) (x j)) =
      ∏ j ∈ Finset.univ.erase i, (bsc ρ hρ).weight (y j) (x j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he, ← add_mul, bsc_flip_sum, one_mul]

/-- The pointwise neighboring posterior-vector identity, before restricting
to either Boolean output fiber. -/
theorem posterior_neighbor_product {n : ℕ} (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (y x : Cube n) (i : Fin n) :
    posteriorVector (cubeBSC n ρ hρ) y x *
      posteriorVector (cubeBSC n ρ hρ) (Function.update y i (!(y i))) x =
      root ρ / 2 * ((cubeBSC n ρ hρ).weight y x +
        (cubeBSC n ρ hρ).weight (Function.update y i (!(y i))) x) := by
  rw [cube_weight_neighbor_sum]
  simp only [cube_posterior_product, ← Finset.prod_mul_distrib]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => Real.sqrt ((bsc ρ hρ).weight (y j) (x j)) *
      Real.sqrt ((bsc ρ hρ).weight ((Function.update y i (!(y i))) j) (x j)))
    (Finset.mem_univ i)]
  simp only [Function.update_self, bsc_flip_sqrt_product]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1,
    Real.mul_self_sqrt ((bsc ρ hρ).nonneg (y j) (x j))]

/-- The positive-output posterior component has the manuscript's exact
neighboring inner product. -/
theorem plus_neighbor_inner {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (y : Cube n) (i : Fin n) :
    plusVector f (cubeBSC n ρ hρ) y ⬝ᵥ
      plusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) =
      root ρ / 2 * (1 + ((cubeBSC n ρ hρ).apply f y +
        (cubeBSC n ρ hρ).apply f (Function.update y i (!(y i)))) / 2) := by
  have he (x : Cube n) :
      plusVector f (cubeBSC n ρ hρ) y x *
        plusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) x =
      root ρ / 2 *
        (plusVector f (cubeBSC n ρ hρ) y x * plusVector f (cubeBSC n ρ hρ) y x +
          plusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) x *
            plusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) x) := by
    by_cases h : f x = 1
    · simp only [plusVector, h, if_true]
      rw [posterior_neighbor_product]
      simp only [posteriorVector, Real.mul_self_sqrt ((cubeBSC n ρ hρ).nonneg _ _)]
    · simp [plusVector, h]
  unfold dotProduct
  simp only [he, ← Finset.mul_sum, Finset.sum_add_distrib]
  change root ρ / 2 * (plusVector f (cubeBSC n ρ hρ) y ⬝ᵥ
      plusVector f (cubeBSC n ρ hρ) y +
      plusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) ⬝ᵥ
        plusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i)))) = _
  rw [plus_norm_sq f hf, plus_norm_sq f hf]
  ring

theorem minus_neighbor_inner {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (y : Cube n) (i : Fin n) :
    minusVector f (cubeBSC n ρ hρ) y ⬝ᵥ
      minusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) =
      root ρ / 2 * (1 - ((cubeBSC n ρ hρ).apply f y +
        (cubeBSC n ρ hρ).apply f (Function.update y i (!(y i)))) / 2) := by
  have he (x : Cube n) :
      minusVector f (cubeBSC n ρ hρ) y x *
        minusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) x =
      root ρ / 2 *
        (minusVector f (cubeBSC n ρ hρ) y x * minusVector f (cubeBSC n ρ hρ) y x +
          minusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) x *
            minusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) x) := by
    by_cases h : f x = 1
    · simp [minusVector, h]
    · simp only [minusVector, h, if_false]
      rw [posterior_neighbor_product]
      simp only [posteriorVector, Real.mul_self_sqrt ((cubeBSC n ρ hρ).nonneg _ _)]
  unfold dotProduct
  simp only [he, ← Finset.mul_sum, Finset.sum_add_distrib]
  change root ρ / 2 * (minusVector f (cubeBSC n ρ hρ) y ⬝ᵥ
      minusVector f (cubeBSC n ρ hρ) y +
      minusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) ⬝ᵥ
        minusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i)))) = _
  rw [minus_norm_sq f hf, minus_norm_sq f hf]
  ring

theorem sqrt_half_product (a b : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (a / 2) * Real.sqrt (b / 2) = Real.sqrt (a * b) / 2 := by
  rw [← Real.sqrt_mul (div_nonneg ha (by norm_num))]
  rw [show a / 2 * (b / 2) = (a * b) / 4 by ring]
  rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem root_eq_two_component_norms {Ω : Type*} [Fintype Ω]
    (f : Ω → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) (K : UniformChannel Ω) (y : Ω) :
    root (K.apply f y) =
      2 * Real.sqrt (plusVector f K y ⬝ᵥ plusVector f K y) *
        Real.sqrt (minusVector f K y ⬝ᵥ minusVector f K y) := by
  have hb := K.apply_mem_Icc f (fun x => by
    rcases hf x with h | h <;> norm_num [h]) y
  rw [plus_norm_sq f hf, minus_norm_sq f hf, mul_assoc, sqrt_half_product _ _
    (by linarith [hb.1])]
  rw [show (1 + K.apply f y) * (1 - K.apply f y) = 1 - K.apply f y ^ 2 by ring]
  unfold root
  ring

theorem pureDifference_components {Ω : Type*} [Fintype Ω]
    (f : Ω → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) (K : UniformChannel Ω) (y : Ω) :
    MatrixLifting.pureDifference (posteriorVector K y)
      (reflectedVector f (posteriorVector K y)) =
      (2 : ℝ) • (Matrix.vecMulVec (plusVector f K y) (minusVector f K y) +
        Matrix.vecMulVec (minusVector f K y) (plusVector f K y)) := by
  ext x z
  rcases hf x with hx | hx <;> rcases hf z with hz | hz <;>
    norm_num [MatrixLifting.pureDifference, reflectedVector, plusVector, minusVector,
      Matrix.vecMulVec_apply, hx, hz] <;> ring

theorem average_component_cross {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (f : Ω → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) (K : UniformChannel Ω) :
    averageProjection K - reflection f * averageProjection K * reflection f =
      (2 : ℝ) • ∑ y, (Fintype.card Ω : ℝ)⁻¹ •
        (Matrix.vecMulVec (plusVector f K y) (minusVector f K y) +
          Matrix.vecMulVec (minusVector f K y) (plusVector f K y)) := by
  rw [average_difference]
  simp only [pureDifference_components f hf, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  exact smul_comm _ _ _

theorem weighted_component_roots {Ω : Type*} [Fintype Ω]
    (f : Ω → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) (K : UniformChannel Ω) :
    (2 : ℝ) * ∑ y, (Fintype.card Ω : ℝ)⁻¹ *
        Real.sqrt (plusVector f K y ⬝ᵥ plusVector f K y) *
        Real.sqrt (minusVector f K y ⬝ᵥ minusVector f K y) =
      mean (fun y => root (K.apply f y)) := by
  unfold mean
  simp only [root_eq_two_component_norms f hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- Equality in actual posterior lifting gives precisely the cross-ensemble
trace equality required by the abstract equality theorem. -/
theorem cross_equality_of_lifting_equality {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (f : Ω → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) (K : UniformChannel Ω)
    (heq : TraceNorm.traceNorm
      (averageProjection K - reflection f * averageProjection K * reflection f) / 2 =
        mean (fun y => root (K.apply f y))) :
    TraceNorm.traceNorm
      (∑ y, (Fintype.card Ω : ℝ)⁻¹ •
        (Matrix.vecMulVec (plusVector f K y) (minusVector f K y) +
          Matrix.vecMulVec (minusVector f K y) (plusVector f K y))) =
      2 * ∑ y, (Fintype.card Ω : ℝ)⁻¹ *
        Real.sqrt (plusVector f K y ⬝ᵥ plusVector f K y) *
        Real.sqrt (minusVector f K y ⬝ᵥ minusVector f K y) := by
  rw [average_component_cross f hf, TraceNorm.traceNorm_smul] at heq
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at heq
  rw [weighted_component_roots f hf]
  linarith

theorem component_norms_pos {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hnonconstant : ∃ x z, f x ≠ f z)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1) (y : Cube n) :
    0 < plusVector f (cubeBSC n ρ hρ) y ⬝ᵥ plusVector f (cubeBSC n ρ hρ) y ∧
      0 < minusVector f (cubeBSC n ρ hρ) y ⬝ᵥ minusVector f (cubeBSC n ρ hρ) y := by
  rw [plus_norm_sq f hf, minus_norm_sq f hf]
  have h := posterior_strict_bounds f hf hnonconstant ρ hρ hρlt y
  constructor <;> linarith

theorem normalized_gram_of_component_equality (p q c : ℝ)
    (hp : -1 < p ∧ p < 1) (hq : -1 < q ∧ q < 1) (hc : 0 < c)
    (h :
      (c / 2 * (1 + (p + q) / 2)) /
          (Real.sqrt ((1 + p) / 2) * Real.sqrt ((1 + q) / 2)) =
        (c / 2 * (1 - (p + q) / 2)) /
          (Real.sqrt ((1 - p) / 2) * Real.sqrt ((1 - q) / 2))) :
    (1 + (p + q) / 2) / Real.sqrt ((1 + p) * (1 + q)) =
      (1 - (p + q) / 2) / Real.sqrt ((1 - p) * (1 - q)) := by
  have hplus : Real.sqrt ((1 + p) * (1 + q)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos (by linarith [hp.1]) (by linarith [hq.1])))
  have hminus : Real.sqrt ((1 - p) * (1 - q)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos (by linarith [hp.2]) (by linarith [hq.2])))
  rw [sqrt_half_product _ _ (by linarith [hp.1]),
    sqrt_half_product _ _ (by linarith [hp.2])] at h
  have hleft :
      (c / 2 * (1 + (p + q) / 2)) / (Real.sqrt ((1 + p) * (1 + q)) / 2) =
      c * ((1 + (p + q) / 2) / Real.sqrt ((1 + p) * (1 + q))) := by
    field_simp
  have hright :
      (c / 2 * (1 - (p + q) / 2)) / (Real.sqrt ((1 - p) * (1 - q)) / 2) =
      c * ((1 - (p + q) / 2) / Real.sqrt ((1 - p) * (1 - q))) := by
    field_simp
  rw [hleft, hright] at h
  exact mul_left_cancel₀ (ne_of_gt hc) h

/-- The actual posterior has constant absolute value once equality of its
normalized positive/negative component Gram matrices has been established.
The equality-of-Gram premise is discharged by the abstract trace-equality module. -/
theorem posterior_abs_constant_of_component_gram {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hnonconstant : ∃ x z, f x ≠ f z)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1)
    (hgram : ∀ y z : Cube n,
      (plusVector f (cubeBSC n ρ hρ) y ⬝ᵥ plusVector f (cubeBSC n ρ hρ) z) /
        (Real.sqrt (plusVector f (cubeBSC n ρ hρ) y ⬝ᵥ plusVector f (cubeBSC n ρ hρ) y) *
          Real.sqrt (plusVector f (cubeBSC n ρ hρ) z ⬝ᵥ plusVector f (cubeBSC n ρ hρ) z)) =
      (minusVector f (cubeBSC n ρ hρ) y ⬝ᵥ minusVector f (cubeBSC n ρ hρ) z) /
        (Real.sqrt (minusVector f (cubeBSC n ρ hρ) y ⬝ᵥ minusVector f (cubeBSC n ρ hρ) y) *
          Real.sqrt (minusVector f (cubeBSC n ρ hρ) z ⬝ᵥ minusVector f (cubeBSC n ρ hρ) z))) :
    ∀ y z, |(cubeBSC n ρ hρ).apply f y| = |(cubeBSC n ρ hρ).apply f z| := by
  have hb := posterior_strict_bounds f hf hnonconstant ρ hρ hρlt
  apply Rigidity.abs_constant_of_normalized_edge_gram ((cubeBSC n ρ hρ).apply f) hb
  intro y i
  have hg := hgram y (Function.update y i (!(y i)))
  rw [plus_neighbor_inner f hf, minus_neighbor_inner f hf] at hg
  simp only [plus_norm_sq f hf, minus_norm_sq f hf] at hg
  have hc : 0 < root ρ := by
    unfold root
    apply Real.sqrt_pos.2
    nlinarith [hρ.1]
  have hh := normalized_gram_of_component_equality _ _ _ (hb y) (hb _) hc hg
  simpa only [add_comm, mul_comm] using hh

theorem balanced_boolean_nonconstant {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hm : mean f = 0) :
    ∃ x z, f x ≠ f z := by
  by_contra! h
  let x₀ : Cube n := fun _ => false
  have hc : f = fun _ => f x₀ := funext (fun x => h x x₀)
  have hmean : mean f = f x₀ := calc
    mean f = mean (fun _ : Cube n => f x₀) := congrArg mean hc
    _ = f x₀ := mean_const _
  have hz : f x₀ = 0 := hmean.symm.trans hm
  rcases hf x₀ with hs | hs <;> linarith

/-- Once the actual posterior has constant absolute value, equality in the
Hellinger objective forces its actual second moment to be rho squared. -/
theorem noise_second_moment_of_abs_constant_and_objective_eq {n : ℕ}
    (f : Cube n → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) (hm : mean f = 0)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (habs : ∀ y z, |(cubeBSC n ρ hρ).apply f y| = |(cubeBSC n ρ hρ).apply f z|)
    (hobj : objective ((cubeBSC n ρ hρ).apply f) = 1 - root ρ) :
    mean (fun x => ((cubeBSC n ρ hρ).apply f x) ^ 2) = ρ ^ 2 := by
  let x₀ : Cube n := fun _ => false
  have hsq (x : Cube n) :
      (cubeBSC n ρ hρ).apply f x ^ 2 = (cubeBSC n ρ hρ).apply f x₀ ^ 2 := by
    have h := congrArg (fun r : ℝ => r ^ 2) (habs x x₀)
    rw [_root_.sq_abs ((cubeBSC n ρ hρ).apply f x),
      _root_.sq_abs ((cubeBSC n ρ hρ).apply f x₀)] at h
    exact h
  have hroot (x : Cube n) :
      root ((cubeBSC n ρ hρ).apply f x) = root ((cubeBSC n ρ hρ).apply f x₀) := by
    unfold root
    rw [hsq x]
  have hmroot :
      mean (fun x => root ((cubeBSC n ρ hρ).apply f x)) =
        root ((cubeBSC n ρ hρ).apply f x₀) := by
    simp only [hroot, mean_const]
  unfold objective at hobj
  rw [UniformChannel.mean_apply, hm, hmroot] at hobj
  have hr0 : root (0 : ℝ) = 1 := by norm_num [root]
  rw [hr0] at hobj
  have hr : root ((cubeBSC n ρ hρ).apply f x₀) = root ρ := by linarith
  have hb := (cubeBSC n ρ hρ).apply_mem_Icc f
    (fun x => by rcases hf x with h | h <;> norm_num [h]) x₀
  have hp : 0 ≤ 1 - (cubeBSC n ρ hρ).apply f x₀ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (show 0 ≤ 1 + (cubeBSC n ρ hρ).apply f x₀ by linarith [hb.1])]
  have hρsq : 0 ≤ 1 - ρ ^ 2 := by nlinarith [hρ.1, hρ.2]
  have hp2 : root ((cubeBSC n ρ hρ).apply f x₀) ^ 2 =
      1 - (cubeBSC n ρ hρ).apply f x₀ ^ 2 := Real.sq_sqrt hp
  have hρ2 : root ρ ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt hρsq
  rw [hr] at hp2
  have heq : (cubeBSC n ρ hρ).apply f x₀ ^ 2 = ρ ^ 2 := by linarith
  simp only [hsq, heq, mean_const]

/-- Equality in actual BSC lifting forces constant absolute posterior.
The trace-equality theorem constructs the common contraction and proves the
Gram identity; no contraction or Gram condition is an input here. -/
theorem posterior_abs_constant_of_lifting_equality {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hnonconstant : ∃ x z, f x ≠ f z)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1)
    (heq : TraceNorm.traceNorm
      (averageProjection (cubeBSC n ρ hρ) -
        reflection f * averageProjection (cubeBSC n ρ hρ) * reflection f) / 2 =
        mean (fun y => root ((cubeBSC n ρ hρ).apply f y))) :
    ∀ y z, |(cubeBSC n ρ hρ).apply f y| = |(cubeBSC n ρ hρ).apply f z| := by
  apply posterior_abs_constant_of_component_gram f hf hnonconstant ρ hρ hρlt
  have hnorm := component_norms_pos f hf hnonconstant ρ hρ hρlt
  have hcross := cross_equality_of_lifting_equality f hf (cubeBSC n ρ hρ) heq
  intro y z
  exact TraceEquality.weighted_cross_trace_equality_gram
    (fun _ : Cube n => (Fintype.card (Cube n) : ℝ)⁻¹)
    (plusVector f (cubeBSC n ρ hρ)) (minusVector f (cubeBSC n ρ hρ))
    (fun _ => by positivity) (fun y => (hnorm y).1) (fun y => (hnorm y).2)
    hcross y z

theorem bsc_posterior_abs_constant_of_lifting_equality {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hnonconstant : ∃ x z, f x ≠ f z)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1)
    (heq : TraceNorm.traceNorm
      (ProductState.state n (root ρ) -
        reflection f * ProductState.state n (root ρ) * reflection f) / 2 =
        mean (fun y => root ((cubeBSC n ρ hρ).apply f y))) :
    ∀ y z, |(cubeBSC n ρ hρ).apply f y| = |(cubeBSC n ρ hρ).apply f z| := by
  apply posterior_abs_constant_of_lifting_equality f hf hnonconstant ρ hρ hρlt
  simpa only [cube_averageProjection] using heq

/-- The actual lifting and Hellinger equalities imply the full Boolean
signed-dictator classification. Every Fourier and Gram step is discharged. -/
theorem signed_dictator_of_lifting_and_objective_equality {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hm : mean f = 0)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hlift : TraceNorm.traceNorm
      (ProductState.state n (root ρ) -
        reflection f * ProductState.state n (root ρ) * reflection f) / 2 =
        mean (fun y => root ((cubeBSC n ρ hρ).apply f y)))
    (hobj : objective ((cubeBSC n ρ hρ).apply f) = 1 - root ρ) :
    ∃ i : Fin n, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
      ∀ x, f x = a * boolSign (x i) := by
  have habs := bsc_posterior_abs_constant_of_lifting_equality f hf
    (balanced_boolean_nonconstant f hf hm) ρ hρ hρlt hlift
  exact Fourier.signed_dictator_of_noise_equality f hf hm ρ hρ hρpos hρlt
    (noise_second_moment_of_abs_constant_and_objective_eq f hf hm ρ hρ habs hobj)

/-- A signed dictator that reverses sign under a specified input translation
must use a coordinate in that translation's actual support. -/
theorem signed_dictator_coordinate_in_support {n : ℕ} (f : Cube n → ℝ)
    (i : Fin n) (a : ℝ) (ha : a = 1 ∨ a = -1)
    (hform : ∀ x, f x = a * boolSign (x i)) (v : Cube n)
    (hv : ∀ x, f (translate v x) = -f x) : i ∈ support v := by
  have h := hv (fun _ => false)
  rw [hform, hform] at h
  cases hvi : v i
  · simp [translate, hvi, boolSign] at h
    rcases ha with ha | ha <;> linarith
  · simp [support, hvi]

#print axioms posterior_strict_bounds
#print axioms plus_norm_sq
#print axioms minus_norm_sq
#print axioms plus_neighbor_inner
#print axioms minus_neighbor_inner
#print axioms posterior_abs_constant_of_component_gram
#print axioms noise_second_moment_of_abs_constant_and_objective_eq
#print axioms bsc_posterior_abs_constant_of_lifting_equality
#print axioms signed_dictator_of_lifting_and_objective_equality

end Hellinger.PosteriorGram
