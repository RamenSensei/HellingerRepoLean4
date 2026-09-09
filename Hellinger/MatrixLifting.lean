import Hellinger.TraceNorm

/-! Concrete real pure-state matrix identities for the square-root lifting.
All state assumptions are explicit Euclidean normalization identities. -/

set_option autoImplicit false
open scoped BigOperators MatrixOrder
open Matrix

namespace Hellinger.MatrixLifting

open Hellinger.TraceNorm

variable {ι : Type*} [Fintype ι]

/-- The difference of two real rank-one state matrices. -/
def pureDifference (v w : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.vecMulVec v v - Matrix.vecMulVec w w

theorem outer_mul (u v w z : ι → ℝ) :
    Matrix.vecMulVec u v * Matrix.vecMulVec w z = (v ⬝ᵥ w) • Matrix.vecMulVec u z := by
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]

theorem pureDifference_isHermitian (v w : ι → ℝ) : (pureDifference v w).IsHermitian := by
  have hv : (Matrix.vecMulVec v v).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star v
  have hw : (Matrix.vecMulVec w w).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star w
  exact hv.isHermitian.sub hw.isHermitian

theorem pureDifference_square (v w : ι → ℝ) (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 1) :
    pureDifference v w * pureDifference v w =
      Matrix.vecMulVec v v + Matrix.vecMulVec w w -
        (v ⬝ᵥ w) • Matrix.vecMulVec v w - (v ⬝ᵥ w) • Matrix.vecMulVec w v := by
  unfold pureDifference
  rw [sub_mul, mul_sub, mul_sub]
  simp only [outer_mul, hv, hw, one_smul, dotProduct_comm w v]
  abel

theorem pureDifference_cube (v w : ι → ℝ) (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 1) :
    pureDifference v w * pureDifference v w * pureDifference v w =
      (1 - (v ⬝ᵥ w) ^ 2) • pureDifference v w := by
  rw [pureDifference_square v w hv hw]
  unfold pureDifference
  simp only [sub_mul, add_mul, mul_sub, smul_mul_assoc, outer_mul,
    hv, hw, dotProduct_comm w v, one_smul, smul_smul]
  module

theorem pureDifference_square_trace (v w : ι → ℝ)
    (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 1) :
    (pureDifference v w * pureDifference v w).trace = 2 * (1 - (v ⬝ᵥ w) ^ 2) := by
  rw [pureDifference_square v w hv hw]
  simp only [trace_sub, trace_add, trace_smul, trace_vecMulVec, hv, hw,
    dotProduct_comm w v, smul_eq_mul]
  ring

theorem pureDifference_square_posSemidef (v w : ι → ℝ) :
    (pureDifference v w * pureDifference v w).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (pureDifference v w)
  rwa [(pureDifference_isHermitian v w).eq] at h

theorem one_sub_inner_sq_nonneg (v w : ι → ℝ)
    (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 1) : 0 ≤ 1 - (v ⬝ᵥ w) ^ 2 := by
  have h := (pureDifference_square_posSemidef v w).trace_nonneg
  rw [pureDifference_square_trace v w hv hw] at h
  linarith

variable [DecidableEq ι]

/-- The exact trace norm of the difference of two real pure states, including
coincident states and opposite representatives of the same state. -/
theorem traceNorm_pureDifference (v w : ι → ℝ)
    (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 1) :
    traceNorm (pureDifference v w) = 2 * Real.sqrt (1 - (v ⬝ᵥ w) ^ 2) := by
  let H := pureDifference v w
  let t := 1 - (v ⬝ᵥ w) ^ 2
  have ht : 0 ≤ t := one_sub_inner_sq_nonneg v w hv hw
  have hH : H.IsHermitian := pureDifference_isHermitian v w
  have hH₂ : (H * H).PosSemidef := pureDifference_square_posSemidef v w
  have htr : (H * H).trace = 2 * t := pureDifference_square_trace v w hv hw
  change traceNorm H = 2 * Real.sqrt t
  by_cases htzero : t = 0
  · have hsqzero : H * H = 0 := hH₂.trace_eq_zero_iff.mp (by rw [htr, htzero, mul_zero])
    have hzero : H = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp (hH.eq.symm ▸ hsqzero)
    simp [hzero, htzero]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
    have hspos : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
    have hsne : Real.sqrt t ≠ 0 := ne_of_gt hspos
    have hssq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
    have hfour : (H * H) * (H * H) = t • (H * H) := by
      rw [← mul_assoc, pureDifference_cube v w hv hw, smul_mul_assoc]
    have hcoefficient : (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ * t = 1 := by
      field_simp
      nlinarith
    have habs : CFC.abs H = (Real.sqrt t)⁻¹ • (H * H) := by
      change CFC.sqrt (star H * H) = _
      apply CFC.sqrt_unique
      · rw [smul_mul_assoc, mul_smul_comm, smul_smul, hfour, smul_smul,
          hcoefficient, one_smul]
        exact congrArg (fun X => X * H) hH.eq.symm
      · exact (hH₂.smul (inv_nonneg.mpr hspos.le)).nonneg
    rw [traceNorm, habs, trace_smul, htr, smul_eq_mul]
    field_simp
    nlinarith

/-- A finite weighted pure-state lifting bound.  The state vectors and their
normalizations are concrete inputs; the norm inequality is proved, not assumed. -/
theorem traceNorm_weighted_pureDifference_le {α : Type*} [Fintype α]
    (p : α → ℝ) (v w : α → ι → ℝ) (hp : ∀ y, 0 ≤ p y)
    (hv : ∀ y, v y ⬝ᵥ v y = 1) (hw : ∀ y, w y ⬝ᵥ w y = 1) :
    traceNorm (∑ y, p y • pureDifference (v y) (w y)) ≤
      ∑ y, p y * (2 * Real.sqrt (1 - (v y ⬝ᵥ w y) ^ 2)) := by
  calc
    _ ≤ ∑ y, traceNorm (p y • pureDifference (v y) (w y)) :=
      traceNorm_sum_le Finset.univ _ (fun y _ =>
        (pureDifference_isHermitian (v y) (w y)).smul (.of_nonneg (hp y)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [traceNorm_smul, abs_of_nonneg (hp y), traceNorm_pureDifference _ _ (hv y) (hw y)]

end Hellinger.MatrixLifting
