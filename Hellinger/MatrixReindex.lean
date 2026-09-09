import Hellinger.TraceNorm

set_option autoImplicit false
open scoped BigOperators MatrixOrder
open Matrix

namespace Hellinger.TraceNorm

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem abs_submatrix_equiv (A : Matrix ι ι ℝ) (e : κ ≃ ι) :
    CFC.abs (A.submatrix e e) = (CFC.abs A).submatrix e e := by
  apply CFC.sqrt_unique
  · rw [Matrix.submatrix_mul_equiv, CFC.abs_mul_abs]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv]
  · exact ((CFC.abs_nonneg A).posSemidef.submatrix e).nonneg

omit [DecidableEq ι] [DecidableEq κ] in
theorem trace_submatrix_equiv (A : Matrix ι ι ℝ) (e : κ ≃ ι) :
    (A.submatrix e e).trace = A.trace := by
  exact e.sum_comp (fun i => A i i)

theorem traceNorm_submatrix_equiv (A : Matrix ι ι ℝ) (e : κ ≃ ι) :
    traceNorm (A.submatrix e e) = traceNorm A := by
  rw [traceNorm, abs_submatrix_equiv, trace_submatrix_equiv]
  rfl

end Hellinger.TraceNorm
