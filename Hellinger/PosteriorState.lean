import Hellinger.ProductState
import Hellinger.MatrixLifting

/-! The actual square-root posterior ensemble and its product-state average.
The normalization, inner product, and average density matrix are proved from
the finite BSC kernel, rather than supplied as ensemble hypotheses. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Matrix

namespace Hellinger.PosteriorState

open Hellinger.TraceNorm Hellinger.MatrixLifting

variable {Ω : Type*} [Fintype Ω]

def posteriorVector (K : UniformChannel Ω) (y : Ω) : Ω → ℝ :=
  fun x => Real.sqrt (K.weight y x)

def reflectedVector (f v : Ω → ℝ) : Ω → ℝ := fun x => f x * v x

def reflection [DecidableEq Ω] (f : Ω → ℝ) : Matrix Ω Ω ℝ := Matrix.diagonal f

theorem posteriorVector_unit (K : UniformChannel Ω) (y : Ω) :
    posteriorVector K y ⬝ᵥ posteriorVector K y = 1 := by
  unfold posteriorVector dotProduct
  simp_rw [Real.mul_self_sqrt (K.nonneg y _)]
  exact K.row_sum y

theorem reflectedVector_unit (K : UniformChannel Ω) (f : Ω → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (y : Ω) :
    reflectedVector f (posteriorVector K y) ⬝ᵥ
      reflectedVector f (posteriorVector K y) = 1 := by
  calc
    _ = posteriorVector K y ⬝ᵥ posteriorVector K y := by
      apply Finset.sum_congr rfl
      intro x _
      rcases hf x with hx | hx <;> simp [reflectedVector, hx]
    _ = 1 := posteriorVector_unit K y

theorem posterior_inner (K : UniformChannel Ω) (f : Ω → ℝ) (y : Ω) :
    posteriorVector K y ⬝ᵥ reflectedVector f (posteriorVector K y) = K.apply f y := by
  unfold dotProduct UniformChannel.apply
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = f x * (Real.sqrt (K.weight y x) * Real.sqrt (K.weight y x)) := by
      unfold posteriorVector reflectedVector
      ring
    _ = K.weight y x * f x := by
      rw [Real.mul_self_sqrt (K.nonneg y x)]
      ring

variable [DecidableEq Ω]

theorem reflected_projection (f v : Ω → ℝ) :
    Matrix.vecMulVec (reflectedVector f v) (reflectedVector f v) =
      reflection f * Matrix.vecMulVec v v * reflection f := by
  ext x z
  rw [reflection, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.vecMulVec_apply, reflectedVector]
  ring

def averageProjection (K : UniformChannel Ω) : Matrix Ω Ω ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ • ∑ y, Matrix.vecMulVec (posteriorVector K y) (posteriorVector K y)

theorem average_difference (K : UniformChannel Ω) (f : Ω → ℝ) :
    averageProjection K - reflection f * averageProjection K * reflection f =
      ∑ y, (Fintype.card Ω : ℝ)⁻¹ •
        pureDifference (posteriorVector K y) (reflectedVector f (posteriorVector K y)) := by
  simp only [averageProjection, pureDifference, reflected_projection, Finset.smul_sum,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub,
    Finset.sum_sub_distrib]

/-- Square-root lifting for a concrete finite uniform-measure-preserving channel. -/
theorem uniform_channel_lifting (K : UniformChannel Ω) (f : Ω → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) :
    traceNorm (averageProjection K - reflection f * averageProjection K * reflection f) / 2 ≤
      mean (fun y => root (K.apply f y)) := by
  rw [average_difference]
  have h := traceNorm_weighted_pureDifference_le
    (fun _ : Ω => (Fintype.card Ω : ℝ)⁻¹)
    (posteriorVector K) (fun y => reflectedVector f (posteriorVector K y))
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (posteriorVector_unit K) (reflectedVector_unit K f hf)
  simp only [posterior_inner] at h
  have hs : (∑ y, (Fintype.card Ω : ℝ)⁻¹ *
      (2 * Real.sqrt (1 - K.apply f y ^ 2))) =
      2 * mean (fun y => root (K.apply f y)) := by
    unfold mean root
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hs] at h
  linarith

theorem bsc_sqrt_cross (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt ((1 + ρ) / 2) * Real.sqrt ((1 - ρ) / 2) = root ρ / 2 := by
  have hp : 0 ≤ (1 + ρ) / 2 := by linarith [hρ.1]
  rw [← Real.sqrt_mul hp]
  have heq : ((1 + ρ) / 2) * ((1 - ρ) / 2) = (1 - ρ ^ 2) / 4 := by ring
  rw [heq, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num [root]

theorem bsc_projection_sum (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x z : Bool) :
    (∑ y : Bool, Real.sqrt ((bsc ρ hρ).weight y x) *
      Real.sqrt ((bsc ρ hρ).weight y z)) = if x = z then 1 else root ρ := by
  have hp : 0 ≤ (1 + ρ) / 2 := by linarith [hρ.1]
  have hm : 0 ≤ (1 - ρ) / 2 := by linarith [hρ.2]
  have hc := bsc_sqrt_cross ρ hρ
  cases x <;> cases z <;> rw [Fintype.sum_bool]
  · change Real.sqrt ((1 - ρ) / 2) * Real.sqrt ((1 - ρ) / 2) +
      Real.sqrt ((1 + ρ) / 2) * Real.sqrt ((1 + ρ) / 2) = 1
    rw [Real.mul_self_sqrt hm, Real.mul_self_sqrt hp]
    ring
  · change Real.sqrt ((1 - ρ) / 2) * Real.sqrt ((1 + ρ) / 2) +
      Real.sqrt ((1 + ρ) / 2) * Real.sqrt ((1 - ρ) / 2) = root ρ
    nlinarith [hc]
  · change Real.sqrt ((1 + ρ) / 2) * Real.sqrt ((1 - ρ) / 2) +
      Real.sqrt ((1 - ρ) / 2) * Real.sqrt ((1 + ρ) / 2) = root ρ
    nlinarith [hc]
  · change Real.sqrt ((1 + ρ) / 2) * Real.sqrt ((1 + ρ) / 2) +
      Real.sqrt ((1 - ρ) / 2) * Real.sqrt ((1 - ρ) / 2) = 1
    rw [Real.mul_self_sqrt hp, Real.mul_self_sqrt hm]
    ring

theorem cube_posterior_product (n : ℕ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (y x : ProductState.Cube n) :
    posteriorVector (cubeBSC n ρ hρ) y x =
      ∏ i, Real.sqrt ((bsc ρ hρ).weight (y i) (x i)) := by
  unfold posteriorVector cubeBSC UniformChannel.product
  exact Real.sqrt_prod Finset.univ (fun i _ => (bsc ρ hρ).nonneg (y i) (x i))

/-- The actual average posterior projection is the concrete product density matrix. -/
theorem cube_averageProjection (n : ℕ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    averageProjection (cubeBSC n ρ hρ) = ProductState.state n (root ρ) := by
  ext x z
  simp only [averageProjection, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]
  change (Fintype.card (ProductState.Cube n) : ℝ)⁻¹ *
    (∑ y, posteriorVector (cubeBSC n ρ hρ) y x * posteriorVector (cubeBSC n ρ hρ) y z) = _
  simp_rw [cube_posterior_product, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (y : Bool) =>
    Real.sqrt ((bsc ρ hρ).weight y (x i)) * Real.sqrt ((bsc ρ hρ).weight y (z i)))]
  simp_rw [bsc_projection_sum]
  simp only [ProductState.state, ProductState.oneQubit, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp [ProductState.Cube, div_eq_mul_inv, mul_comm]

/-- The manuscript's BSC square-root lifting, with no ensemble or matrix-spectrum premises. -/
theorem bsc_lifting (n : ℕ) (f : ProductState.Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    traceNorm (ProductState.state n (root ρ) -
      reflection f * ProductState.state n (root ρ) * reflection f) / 2 ≤
      mean (fun y => root ((cubeBSC n ρ hρ).apply f y)) := by
  simpa only [cube_averageProjection] using uniform_channel_lifting (cubeBSC n ρ hρ) f hf

end Hellinger.PosteriorState
