import Hellinger.ComplexSpectral

/-! The real matrices used by the Boolean-cube construction are embedded into
the complex matrices appearing in the manuscript. The positive square root,
absolute value, and unnormalized Schatten 1 norm are all preserved. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace Hellinger.Complexification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def complexify : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix

@[simp] theorem complexify_apply (A : Matrix ι ι ℝ) (i j : ι) :
    complexify A i j = (A i j : ℂ) := rfl

@[simp] theorem complexify_conjTranspose (A : Matrix ι ι ℝ) :
    (complexify A).conjTranspose = complexify A.transpose := by
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem complexify_isHermitian {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (complexify A).IsHermitian := by
  change (complexify A).conjTranspose = complexify A
  rw [complexify_conjTranspose]
  exact congrArg complexify (by simpa only [conjTranspose_eq_transpose_of_trivial] using hA.eq)

theorem complexify_posSemidef {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (complexify A).PosSemidef := by
  have hs : (CFC.sqrt A).transpose = CFC.sqrt A := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq
  have h := Matrix.posSemidef_conjTranspose_mul_self (complexify (CFC.sqrt A))
  rw [complexify_conjTranspose, ← map_mul, hs, CFC.sqrt_mul_sqrt_self A hA.nonneg] at h
  exact h

theorem sqrt_complexify {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    CFC.sqrt (complexify A) = complexify (CFC.sqrt A) := by
  apply CFC.sqrt_unique
  · rw [← map_mul, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact (complexify_posSemidef (CFC.sqrt_nonneg A).posSemidef).nonneg

theorem abs_complexify (A : Matrix ι ι ℝ) :
    CFC.abs (complexify A) = complexify (CFC.abs A) := by
  change CFC.sqrt ((complexify A).conjTranspose * complexify A) = _
  have hp : (A.transpose * A).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self A
  rw [complexify_conjTranspose, ← map_mul,
    sqrt_complexify hp]
  rfl

theorem trace_complexify (A : Matrix ι ι ℝ) : (complexify A).trace = (A.trace : ℂ) := by
  simp [Matrix.trace, Matrix.diag, ← Complex.ofReal_sum]

theorem realTrace_complexify (A : Matrix ι ι ℝ) :
    ComplexSpectral.realTrace (complexify A) = A.trace := by
  rw [ComplexSpectral.realTrace, trace_complexify, Complex.ofReal_re]

/-- Equality of the actual complex and real Schatten 1 norms under the
canonical real-to-complex embedding, for every real square matrix. -/
theorem traceNorm_complexify (A : Matrix ι ι ℝ) :
    ComplexSpectral.traceNorm (complexify A) = TraceNorm.traceNorm A := by
  rw [ComplexSpectral.traceNorm, abs_complexify, realTrace_complexify]
  rfl

theorem traceNorm_reflection_difference (K F : Matrix ι ι ℝ) :
    ComplexSpectral.traceNorm (complexify K - complexify F * complexify K * complexify F) =
      TraceNorm.traceNorm (K - F * K * F) := by
  rw [← map_mul, ← map_mul, ← map_sub, traceNorm_complexify]

end Hellinger.Complexification
