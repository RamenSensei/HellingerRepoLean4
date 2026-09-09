import Hellinger.ReflectionCounterexample

/-! The computational-basis cut norm. Rectangular trace norm is defined by
the positive square root of the actual rectangular Gram matrix. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators MatrixOrder
open Matrix

namespace Hellinger.CutNorm
open TraceNorm ProductState

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def rectangularTraceNorm (A : Matrix ι κ ℝ) : ℝ :=
  (CFC.sqrt (A.transpose * A)).trace

omit [DecidableEq ι] [DecidableEq κ] in
theorem gram_posSemidef (A : Matrix ι κ ℝ) : (A.transpose * A).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self A

omit [DecidableEq ι] [DecidableEq κ] in
theorem cogram_posSemidef (A : Matrix ι κ ℝ) : (A * A.transpose).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose A

theorem sqrt_eq_real_cfc {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    CFC.sqrt A = cfc Real.sqrt A := by
  rw [CFC.sqrt_eq_real_sqrt A hA.nonneg, cfcₙ_eq_cfc]

theorem traceNorm_transpose (A : Matrix ι ι ℝ) : traceNorm A.transpose = traceNorm A := by
  have h₁ := (cogram_posSemidef A).isHermitian
  have h₂ := (gram_posSemidef A).isHermitian
  have he := (h₁.eigenvalues_eq_eigenvalues_iff h₂).mpr
    (Matrix.charpoly_mul_comm A A.transpose)
  rw [traceNorm_eq_trace_sqrt, traceNorm_eq_trace_sqrt, Matrix.transpose_transpose,
    sqrt_eq_real_cfc (cogram_posSemidef A),
    sqrt_eq_real_cfc (gram_posSemidef A),
    trace_cfc h₁, trace_cfc h₂, he]

theorem traceNorm_offDiagonal (A : Matrix ι ι ℝ) :
    traceNorm (Matrix.fromBlocks 0 A A.transpose 0) = 2 * traceNorm A := by
  rw [traceNorm_eq_trace_sqrt]
  simp only [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_transpose,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
  rw [sqrt_blockDiagonal (cogram_posSemidef A)
    (gram_posSemidef A), TraceNorm.trace_blockDiagonal]
  have ht := traceNorm_eq_trace_sqrt A.transpose
  rw [Matrix.transpose_transpose] at ht
  rw [← ht, ← traceNorm_eq_trace_sqrt A]
  rw [traceNorm_transpose]
  ring

theorem sqrt_submatrix_equiv {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (e : κ ≃ ι) :
    CFC.sqrt (A.submatrix e e) = (CFC.sqrt A).submatrix e e := by
  apply CFC.sqrt_unique
  · rw [Matrix.submatrix_mul_equiv, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact ((CFC.sqrt_nonneg A).posSemidef.submatrix e).nonneg

theorem rectangularTraceNorm_columns (A : Matrix ι κ ℝ) (e : ι ≃ κ) :
    rectangularTraceNorm A = traceNorm (A.submatrix id e) := by
  rw [traceNorm_eq_trace_sqrt]
  have hmul : (A.submatrix id e).transpose * A.submatrix id e =
      (A.transpose * A).submatrix e e := by
    ext i j
    rfl
  rw [hmul, sqrt_submatrix_equiv (gram_posSemidef A),
    trace_submatrix_equiv]
  rfl

attribute [local instance] Classical.propDecidable

abbrev Positive (f : ι → ℝ) := {x // f x = 1}
abbrev Negative (f : ι → ℝ) := {x // f x ≠ 1}

omit [Fintype ι] [DecidableEq ι] in
theorem value_negative (f : ι → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1)
    (x : Negative f) : f x = -1 := (hf x).resolve_right x.property

omit [DecidableEq ι] in
theorem balanced_cards [Nonempty ι] (f : ι → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hm : mean f = 0) :
    Fintype.card (Positive f) = Fintype.card (Negative f) := by
  have hs : ∑ x, f x = 0 := by
    simpa only [mean, mul_eq_zero, inv_eq_zero, Nat.cast_eq_zero,
      Fintype.card_ne_zero, false_or] using hm
  have h := Fintype.sum_subtype_add_sum_subtype (fun x => f x = 1) f
  have hp (x : Positive f) : f x = 1 := x.property
  simp only [hp, value_negative f hf, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, mul_neg, hs, add_neg_eq_zero] at h
  exact_mod_cast h

def cutMatrix (K : Matrix ι ι ℝ) (f : ι → ℝ) : Matrix (Positive f) (Negative f) ℝ :=
  fun x y => K x y

def cutEquiv (f : ι → ℝ) (e : Positive f ≃ Negative f) :
    Positive f ⊕ Positive f ≃ ι :=
  (Equiv.sumCongr (Equiv.refl _) e).trans (Equiv.sumCompl (fun x => f x = 1))

theorem cut_blocks (K : Matrix ι ι ℝ) (hK : K.IsHermitian)
    (f : ι → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1)
    (e : Positive f ≃ Negative f) :
    (K - Matrix.diagonal f * K * Matrix.diagonal f).submatrix (cutEquiv f e) (cutEquiv f e) =
      (2 : ℝ) • Matrix.fromBlocks 0 ((cutMatrix K f).submatrix id e)
        ((cutMatrix K f).submatrix id e).transpose 0 := by
  have hp (x : Positive f) : f x = 1 := x.property
  have hn (x : Positive f) : f (e x) = -1 := value_negative f hf (e x)
  have hsym (i j : ι) : K i j = K j i := by
    have h := congrArg (fun M : Matrix ι ι ℝ => M j i) hK
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.submatrix_apply, cutEquiv, Matrix.mul_diagonal,
      Matrix.diagonal_mul, hp, hn, cutMatrix, hsym] <;> ring

theorem cut_trace_identity [Nonempty ι] (K : Matrix ι ι ℝ) (hK : K.IsHermitian)
    (f : ι → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) (hm : mean f = 0) :
    traceNorm (K - Matrix.diagonal f * K * Matrix.diagonal f) / 2 =
      2 * rectangularTraceNorm (cutMatrix K f) := by
  let e : Positive f ≃ Negative f := Fintype.equivOfCardEq (balanced_cards f hf hm)
  rw [← traceNorm_submatrix_equiv _ (cutEquiv f e), cut_blocks K hK f hf e,
    traceNorm_smul, traceNorm_offDiagonal,
    rectangularTraceNorm_columns (cutMatrix K f) e]
  norm_num

theorem product_state_cut_identity (n : ℕ) (c : ℝ) (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hm : mean f = 0) :
    traceNorm (state n c - Matrix.diagonal f * state n c * Matrix.diagonal f) / 2 =
      2 * rectangularTraceNorm
        (fun (x : Positive f) (z : Negative f) => c ^ hammingDistance n x z / (2 : ℝ) ^ n) := by
  have h := cut_trace_identity (state n c) (state_isHermitian n c) f hf hm
  have hcut : cutMatrix (state n c) f =
      (fun (x : Positive f) (z : Negative f) =>
        c ^ hammingDistance n x z / (2 : ℝ) ^ n) := by
    funext x z
    exact state_entry n c x z
  rw [hcut] at h
  exact h

end Hellinger.CutNorm
