import Hellinger.TraceNorm
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-! General complex Hermitian spectral inequalities. All matrix norms in this
file use `Matrix.Norms.L2Operator`; the Schatten 1 norm is defined separately
as the real trace of the positive square root of `Aᴴ * A`. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Unitary WithLp

namespace Hellinger.ComplexSpectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realTrace (A : Matrix ι ι ℂ) : ℝ := A.trace.re

def traceNorm (A : Matrix ι ι ℂ) : ℝ := realTrace (CFC.abs A)

theorem traceNorm_eq_trace_sqrt (A : Matrix ι ι ℂ) :
    traceNorm A = (CFC.sqrt (A.conjTranspose * A)).trace.re := rfl

omit [DecidableEq ι] in
@[simp] theorem realTrace_add (A B : Matrix ι ι ℂ) :
    realTrace (A + B) = realTrace A + realTrace B := by simp [realTrace]

omit [DecidableEq ι] in
@[simp] theorem realTrace_sub (A B : Matrix ι ι ℂ) :
    realTrace (A - B) = realTrace A - realTrace B := by simp [realTrace]

omit [DecidableEq ι] in
@[simp] theorem realTrace_neg (A : Matrix ι ι ℂ) : realTrace (-A) = -realTrace A := by
  simp [realTrace]

omit [DecidableEq ι] in
@[simp] theorem realTrace_smul (r : ℝ) (A : Matrix ι ι ℂ) :
    realTrace (r • A) = r * realTrace A := by simp [realTrace]

omit [DecidableEq ι] in
theorem realTrace_mul_comm (A B : Matrix ι ι ℂ) : realTrace (A * B) = realTrace (B * A) := by
  rw [realTrace, realTrace, trace_mul_comm]

theorem realTrace_conjugate (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    realTrace (conjStarAlgAut ℂ _ U A) = realTrace A := by
  simp only [realTrace, conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self, one_mul]

theorem realTrace_cfc {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    realTrace (cfc f A) = ∑ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, realTrace_conjugate]
  simp [realTrace, trace_diagonal]

theorem traceNorm_eq_sum_abs_eigenvalues {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    traceNorm A = ∑ i, |hA.eigenvalues i| := by
  rw [traceNorm, CFC.abs_eq_cfc_norm A hA, realTrace_cfc hA]
  simp [Real.norm_eq_abs]

omit [DecidableEq ι] in
theorem realTrace_nonneg {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : 0 ≤ realTrace A := by
  exact (Complex.nonneg_iff.mp hA.trace_nonneg).1

theorem traceNorm_nonneg (A : Matrix ι ι ℂ) : 0 ≤ traceNorm A :=
  realTrace_nonneg (CFC.abs_nonneg A).posSemidef

theorem norm_conjugate (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    ‖conjStarAlgAut ℂ _ U A‖ = ‖A‖ := by
  rw [conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

theorem norm_entry_le (Q : Matrix ι ι ℂ) (i j : ι) : ‖Q i j‖ ≤ ‖Q‖ := by
  let e : EuclideanSpace ℂ ι := PiLp.single 2 j 1
  have h := Matrix.l2_opNorm_mulVec Q e
  have he : ‖e‖ = 1 := by simp [e]
  have hc := PiLp.norm_apply_le (toLp 2 (Q *ᵥ ofLp e)) i
  have hei : (Q *ᵥ ofLp e) i = Q i j := by simp [e, mulVec, dotProduct]
  rw [he, mul_one] at h
  change ‖(Q *ᵥ ofLp e) i‖ ≤ ‖toLp 2 (Q *ᵥ ofLp e)‖ at hc
  rw [hei] at hc
  exact hc.trans h

theorem realTrace_mul_le_traceNorm {A Q : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hQ : ‖Q‖ ≤ 1) : realTrace (Q * A) ≤ traceNorm A := by
  rw [← realTrace_conjugate (star hA.eigenvectorUnitary) (Q * A), map_mul,
    hA.conjStarAlgAut_star_eigenvectorUnitary, traceNorm_eq_sum_abs_eigenvalues hA]
  simp only [realTrace, trace, diag_apply, mul_diagonal, Function.comp_apply, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  change (_ * (hA.eigenvalues i : ℂ)).re ≤ |hA.eigenvalues i|
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hb : |(conjStarAlgAut ℂ _ (star hA.eigenvectorUnitary) Q i i).re| ≤ 1 := by
    exact (Complex.abs_re_le_norm _).trans ((norm_entry_le _ i i).trans (by rwa [norm_conjugate]))
  calc
    _ ≤ |(conjStarAlgAut ℂ _ (star hA.eigenvectorUnitary) Q i i).re * hA.eigenvalues i| :=
      le_abs_self _
    _ = |(conjStarAlgAut ℂ _ (star hA.eigenvectorUnitary) Q i i).re| * |hA.eigenvalues i| :=
      abs_mul _ _
    _ ≤ 1 * |hA.eigenvalues i| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    _ = _ := one_mul _

def signWitness (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := cfc TraceNorm.scalarSign A

theorem signWitness_isHermitian (A : Matrix ι ι ℂ) : (signWitness A).IsHermitian :=
  IsSelfAdjoint.cfc

theorem signWitness_norm_le (A : Matrix ι ι ℂ) : ‖signWitness A‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro x _
  rw [Real.norm_eq_abs]
  exact abs_le.mpr (TraceNorm.scalarSign_bounds x)

theorem signWitness_attains {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    realTrace (signWitness A * A) = traceNorm A := by
  rw [signWitness, hA.cfc_eq, Matrix.IsHermitian.cfc]
  calc
    _ = realTrace (conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (diagonal (fun i => (TraceNorm.scalarSign (hA.eigenvalues i) : ℂ))) *
      conjStarAlgAut ℂ _ hA.eigenvectorUnitary
        (diagonal (RCLike.ofReal ∘ hA.eigenvalues))) := by
          congr 1
          exact congrArg (fun X => _ * X) hA.spectral_theorem
    _ = _ := by
      rw [← map_mul, realTrace_conjugate, diagonal_mul_diagonal,
        traceNorm_eq_sum_abs_eigenvalues hA]
      simp [realTrace, trace_diagonal, ← Complex.ofReal_mul, TraceNorm.scalarSign_mul]

theorem reflection_conjugate_twice {F : Matrix ι ι ℂ} (hF : F * F = 1)
    (A : Matrix ι ι ℂ) : F * (F * A * F) * F = A := by
  calc
    _ = (F * F) * A * (F * F) := by noncomm_ring
    _ = _ := by rw [hF, one_mul, mul_one]

omit [DecidableEq ι] in
theorem reflection_conjugate_isHermitian {F A : Matrix ι ι ℂ}
    (hF : F.IsHermitian) (hA : A.IsHermitian) : (F * A * F).IsHermitian := by
  change (F * A * F).conjTranspose = _
  simp only [conjTranspose_mul, hF.eq, hA.eq, mul_assoc]

theorem norm_reflection_conjugate {F : Matrix ι ι ℂ}
    (hF : F.IsHermitian) (hFsq : F * F = 1) (A : Matrix ι ι ℂ) :
    ‖F * A * F‖ = ‖A‖ := by
  let U : Matrix.unitaryGroup ι ℂ := ⟨F, Matrix.mem_unitaryGroup_iff.mpr (by
    simpa only [Matrix.star_eq_conjTranspose, hF.eq] using hFsq)⟩
  have hc : conjStarAlgAut ℂ _ U A = F * A * F := by
    change F * A * F.conjTranspose = F * A * F
    rw [hF.eq]
  rw [← hc, norm_conjugate]

omit [DecidableEq ι] in
theorem realTrace_reflection_move (F A B : Matrix ι ι ℂ) :
    realTrace (F * A * F * B) = realTrace (A * (F * B * F)) := by
  calc
    _ = realTrace (F * (A * F * B)) := by congr 1; noncomm_ring
    _ = realTrace ((A * F * B) * F) := realTrace_mul_comm _ _
    _ = _ := by congr 1; noncomm_ring

omit [DecidableEq ι] in
theorem anticommuting_trace_identity {F Q : Matrix ι ι ℂ}
    (hQ : F * Q * F = -Q) (K : Matrix ι ι ℂ) :
    realTrace (Q * (K - F * K * F)) = 2 * realTrace (K * Q) := by
  have hm : realTrace (Q * (F * K * F)) = -realTrace (Q * K) := by
    rw [← realTrace_reflection_move, hQ, neg_mul, realTrace_neg]
  rw [mul_sub, realTrace_sub, hm, realTrace_mul_comm Q K]
  ring

theorem exists_anticommuting_trace_witness {K F : Matrix ι ι ℂ}
    (hK : K.IsHermitian) (hF : F.IsHermitian) (hFsq : F * F = 1) :
    ∃ Q : Matrix ι ι ℂ, Q.IsHermitian ∧ ‖Q‖ ≤ 1 ∧ F * Q * F = -Q ∧
      realTrace (K * Q) = traceNorm (K - F * K * F) / 2 := by
  let H := K - F * K * F
  have hH : H.IsHermitian := hK.sub (reflection_conjugate_isHermitian hF hK)
  let S := signWitness H
  let Q := (1 / 2 : ℝ) • (S - F * S * F)
  have hQH : Q.IsHermitian := ((signWitness_isHermitian H).sub
    (reflection_conjugate_isHermitian hF (signWitness_isHermitian H))).smul
      (IsSelfAdjoint.of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num))
  have hQ : ‖Q‖ ≤ 1 := by
    have hs : ‖S‖ ≤ 1 := signWitness_norm_le H
    have h := norm_sub_le S (F * S * F)
    rw [norm_reflection_conjugate hF hFsq] at h
    simp only [Q, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have ha : F * Q * F = -Q := by
    dsimp only [Q]
    simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul]
    rw [reflection_conjugate_twice hFsq]
    module
  refine ⟨Q, hQH, hQ, ha, ?_⟩
  have hHanti : F * H * F = -H := by
    dsimp only [H]
    simp only [mul_sub, sub_mul]
    rw [reflection_conjugate_twice hFsq]
    abel
  have hSH : realTrace (S * H) = traceNorm H := signWitness_attains hH
  have hQH : realTrace (Q * H) = traceNorm H := by
    dsimp only [Q]
    rw [smul_mul_assoc, realTrace_smul, sub_mul, realTrace_sub, realTrace_reflection_move,
      hHanti, mul_neg, realTrace_neg, hSH]
    ring
  have hi := anticommuting_trace_identity ha K
  change realTrace (Q * H) = 2 * realTrace (K * Q) at hi
  change realTrace (K * Q) = traceNorm H / 2
  linarith

/-- Exact maximum for arbitrary complex Hermitian matrices, including every
density matrix. No real-coordinate restriction appears in this statement. -/
theorem anticommuting_trace_maximum {K F : Matrix ι ι ℂ}
    (hK : K.IsHermitian) (hF : F.IsHermitian) (hFsq : F * F = 1) :
    IsGreatest {t : ℝ | ∃ Q : Matrix ι ι ℂ,
      Q.IsHermitian ∧ ‖Q‖ ≤ 1 ∧ F * Q * F = -Q ∧ t = realTrace (K * Q)}
      (traceNorm (K - F * K * F) / 2) := by
  constructor
  · obtain ⟨Q, hQH, hn, ha, ht⟩ := exists_anticommuting_trace_witness hK hF hFsq
    exact ⟨Q, hQH, hn, ha, ht.symm⟩
  · rintro t ⟨Q, _, hn, ha, rfl⟩
    have h := realTrace_mul_le_traceNorm (hK.sub (reflection_conjugate_isHermitian hF hK)) hn
    rw [anticommuting_trace_identity ha] at h
    linarith

open scoped InnerProductSpace

omit [DecidableEq ι] in
theorem norm_toLp_sq (v : ι → ℂ) : ‖toLp 2 v‖ ^ 2 = (star v ⬝ᵥ v).re := by
  simpa only [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, RCLike.re_to_complex] using
    (norm_sq_eq_re_inner (𝕜 := ℂ) (toLp 2 v))

omit [DecidableEq ι] in
theorem hermitian_norm_mulVec_sq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (v : ι → ℂ) :
    ‖toLp 2 (A *ᵥ v)‖ ^ 2 = (star v ⬝ᵥ (A * A) *ᵥ v).re := by
  have hs : star v ᵥ* A = star (A *ᵥ v) := by
    rw [star_mulVec, hA.eq]
  rw [← mulVec_mulVec, dotProduct_mulVec (star v) A (A *ᵥ v), hs, norm_toLp_sq]

theorem reflection_anticommutes {F Q : Matrix ι ι ℂ}
    (hFsq : F * F = 1) (ha : F * Q * F = -Q) : F * Q = -(Q * F) := by
  have h := congrArg (fun A => A * F) ha
  simpa only [mul_assoc, hFsq, mul_one, neg_mul] using h

/-- Complex-vector uncertainty relation with the Euclidean unit-vector
normalization and the genuine matrix operator norm. -/
theorem anticommuting_uncertainty {F Q : Matrix ι ι ℂ}
    (hF : F.IsHermitian) (hFsq : F * F = 1) (hQ : Q.IsHermitian) (hn : ‖Q‖ ≤ 1)
    (ha : F * Q * F = -Q) (ψ : ι → ℂ) (hψ : ‖toLp 2 ψ‖ = 1) :
    (star ψ ⬝ᵥ F *ᵥ ψ).re ^ 2 + (star ψ ⬝ᵥ Q *ᵥ ψ).re ^ 2 ≤ 1 := by
  let a := (star ψ ⬝ᵥ F *ᵥ ψ).re
  let b := (star ψ ⬝ᵥ Q *ᵥ ψ).re
  let A := a • F + b • Q
  have hAH : A.IsHermitian := (hF.smul (isSelfAdjoint_iff.mpr (star_trivial a))).add
    (hQ.smul (isSelfAdjoint_iff.mpr (star_trivial b)))
  have hA2 : A * A = a ^ 2 • (1 : Matrix ι ι ℂ) + b ^ 2 • (Q * Q) := by
    simp only [A, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      hFsq, reflection_anticommutes hFsq ha]
    module
  have hself : (star ψ ⬝ᵥ ψ).re = 1 := by rw [← norm_toLp_sq, hψ, one_pow]
  have hQψ : ‖toLp 2 (Q *ᵥ ψ)‖ ≤ 1 := by
    have h := Matrix.l2_opNorm_mulVec Q (toLp 2 ψ)
    rw [hψ, mul_one] at h
    exact h.trans hn
  have hQQ : (star ψ ⬝ᵥ (Q * Q) *ᵥ ψ).re ≤ 1 := by
    rw [← hermitian_norm_mulVec_sq hQ]
    nlinarith [norm_nonneg (toLp 2 (Q *ᵥ ψ))]
  have hAψ : ‖toLp 2 (A *ᵥ ψ)‖ ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rw [hermitian_norm_mulVec_sq hAH, hA2]
    simp only [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
      Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul, hself, mul_one]
    nlinarith [sq_nonneg b]
  have hinner : (star ψ ⬝ᵥ A *ᵥ ψ).re = a ^ 2 + b ^ 2 := by
    simp only [A, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
      Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul]
    change a * a + b * b = _
    ring
  have hcs := re_inner_le_norm (𝕜 := ℂ) (toLp 2 ψ) (toLp 2 (A *ᵥ ψ))
  simp only [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, RCLike.re_to_complex, hψ, one_mul] at hcs
  rw [hinner] at hcs
  have hnonneg : 0 ≤ a ^ 2 + b ^ 2 := add_nonneg (sq_nonneg a) (sq_nonneg b)
  have hsq : (a ^ 2 + b ^ 2) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    nlinarith [norm_nonneg (toLp 2 (A *ᵥ ψ))]
  change a ^ 2 + b ^ 2 ≤ 1
  nlinarith

theorem operator_norm_eq (A : Matrix ι ι ℂ) :
    ‖A‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A‖ := rfl

omit [DecidableEq ι] in
theorem realTrace_hermitian_product {K Q : Matrix ι ι ℂ}
    (hK : K.IsHermitian) (hQ : Q.IsHermitian) :
    (realTrace (K * Q) : ℂ) = (K * Q).trace := by
  apply Complex.conj_eq_iff_re.mp
  change star (K * Q).trace = (K * Q).trace
  rw [← trace_conjTranspose, conjTranspose_mul, hQ.eq, hK.eq, trace_mul_comm]

end Hellinger.ComplexSpectral
