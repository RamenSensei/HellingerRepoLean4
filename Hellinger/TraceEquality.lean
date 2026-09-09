import Hellinger.EigenvalueOrder
import Hellinger.MatrixLifting

/-! Equality in finite trace-norm averaging.  The common witness is constructed
from the spectral sign matrix; no contraction or Gram equality is assumed. -/

set_option autoImplicit false
open scoped BigOperators MatrixOrder InnerProductSpace
open Matrix Unitary WithLp

namespace Hellinger.TraceEquality

open Hellinger.TraceNorm

variable {ι : Type*} [Fintype ι]

noncomputable def vectorNorm (v : ι → ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v)

theorem dot_self_nonneg (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v := by
  simpa only [star_trivial] using dotProduct_star_self_nonneg v

theorem vectorNorm_nonneg (v : ι → ℝ) : 0 ≤ vectorNorm v := Real.sqrt_nonneg _

theorem vectorNorm_sq (v : ι → ℝ) : vectorNorm v ^ 2 = v ⬝ᵥ v :=
  Real.sq_sqrt (dot_self_nonneg v)

theorem vectorNorm_pos {v : ι → ℝ} (hv : 0 < v ⬝ᵥ v) : 0 < vectorNorm v :=
  Real.sqrt_pos.mpr hv

theorem vectorNorm_eq_norm (v : ι → ℝ) : vectorNorm v = ‖toLp 2 v‖ := by
  simpa only [vectorNorm, EuclideanSpace.inner_toLp_toLp, star_trivial] using
    (norm_eq_sqrt_real_inner (toLp 2 v)).symm

theorem dot_le_vectorNorm_mul (u v : ι → ℝ) : u ⬝ᵥ v ≤ vectorNorm u * vectorNorm v := by
  rw [vectorNorm_eq_norm, vectorNorm_eq_norm]
  simpa only [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm] using
    real_inner_le_norm (toLp 2 u) (toLp 2 v)

noncomputable def normalizedVector (v : ι → ℝ) : ι → ℝ := (vectorNorm v)⁻¹ • v

theorem normalizedVector_self {v : ι → ℝ} (hv : 0 < v ⬝ᵥ v) :
    normalizedVector v ⬝ᵥ normalizedVector v = 1 := by
  have hs := vectorNorm_sq v
  have hn := ne_of_gt (vectorNorm_pos hv)
  simp only [normalizedVector, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp
  nlinarith

theorem normalizedVector_dot (u v : ι → ℝ) :
    normalizedVector u ⬝ᵥ normalizedVector v =
      (u ⬝ᵥ v) / (vectorNorm u * vectorNorm v) := by
  simp only [normalizedVector, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem dot_mulVec_comm {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian) (u v : ι → ℝ) :
    u ⬝ᵥ Q *ᵥ v = v ⬝ᵥ Q *ᵥ u := by
  have hQt : Q.transpose = Q := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hQ.eq
  simpa only [hQt] using Matrix.dotProduct_transpose_mulVec Q u v

variable [DecidableEq ι]

omit [Fintype ι] in
theorem orderContraction_isHermitian {Q : Matrix ι ι ℝ} (hQ : OrderContraction Q) :
    Q.IsHermitian := by
  have h := Matrix.isHermitian_one.sub hQ.1.isHermitian
  simpa only [sub_sub_cancel] using h

theorem signWitness_isHermitian {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (signWitness hA).IsHermitian :=
  isHermitian_conjugate (Matrix.isHermitian_diagonal _) hA.eigenvectorUnitary

/-- Every spectral value of an order contraction lies in `[-1,1]`. -/
theorem orderContraction_eigenvalue_abs_le {Q : Matrix ι ι ℝ}
    (hQ : OrderContraction Q) (i : ι) :
    |(orderContraction_isHermitian hQ).eigenvalues i| ≤ 1 := by
  let hH := orderContraction_isHermitian hQ
  have h := hQ.conjugate (star hH.eigenvectorUnitary)
  rw [hH.conjStarAlgAut_star_eigenvectorUnitary] at h
  simpa only [diagonal_apply_eq, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq] using
    h.diagonal_abs_le i

/-- The order contraction is also a contraction on Euclidean vectors. -/
theorem orderContraction_square_posSemidef {Q : Matrix ι ι ℝ}
    (hQ : OrderContraction Q) : (1 - Q * Q).PosSemidef := by
  let hH := orderContraction_isHermitian hQ
  let D := Matrix.diagonal hH.eigenvalues
  have hspec : Q = conjStarAlgAut ℝ _ hH.eigenvectorUnitary D := by
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using hH.spectral_theorem
  have hdiag : (Matrix.diagonal (fun i => 1 - hH.eigenvalues i ^ 2)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr (orderContraction_eigenvalue_abs_le hQ i))
  have hD : 1 - D * D = Matrix.diagonal (fun i => 1 - hH.eigenvalues i ^ 2) := by
    rw [show (1 : Matrix ι ι ℝ) = Matrix.diagonal (fun _ => 1) from diagonal_one.symm]
    simp only [D, diagonal_mul_diagonal, diagonal_sub, pow_two]
  have hid : 1 - Q * Q = conjStarAlgAut ℝ _ hH.eigenvectorUnitary (1 - D * D) := by
    rw [map_sub, map_one, map_mul, ← hspec]
  rw [hid, hD]
  exact posSemidef_conjugate _ hdiag

theorem orderContraction_dot_sq_le {Q : Matrix ι ι ℝ} (hQ : OrderContraction Q)
    (v : ι → ℝ) : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) ≤ v ⬝ᵥ v := by
  have h := (orderContraction_square_posSemidef hQ).dotProduct_mulVec_nonneg v
  simp only [star_trivial, Matrix.sub_mulVec, one_mulVec, dotProduct_sub,
    ← mulVec_mulVec] at h
  rw [dot_mulVec_comm (orderContraction_isHermitian hQ)] at h
  exact sub_nonneg.mp h

theorem orderContraction_vectorNorm_le {Q : Matrix ι ι ℝ} (hQ : OrderContraction Q)
    (v : ι → ℝ) : vectorNorm (Q *ᵥ v) ≤ vectorNorm v :=
  Real.sqrt_le_sqrt (orderContraction_dot_sq_le hQ v)

/-- The contraction bound uses the genuine Euclidean operator norm. -/
theorem orderContraction_operatorNorm_le {Q : Matrix ι ι ℝ} (hQ : OrderContraction Q) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) Q‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖toLp 2 (Q *ᵥ ofLp x)‖ ≤ 1 * ‖x‖
  simpa only [one_mul, vectorNorm_eq_norm, toLp_ofLp] using
    orderContraction_vectorNorm_le hQ (ofLp x)

theorem operatorNorm_quadratic_abs_le {Q : Matrix ι ι ℝ}
    (hQ : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) Q‖ ≤ 1) (v : ι → ℝ) :
    |v ⬝ᵥ Q *ᵥ v| ≤ v ⬝ᵥ v := by
  have hn : vectorNorm (Q *ᵥ v) ≤ vectorNorm v := by
    simpa only [vectorNorm_eq_norm, Matrix.toEuclideanCLM_toLp, one_mul] using
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) Q).le_of_opNorm_le hQ (toLp 2 v)
  have hcs : |v ⬝ᵥ Q *ᵥ v| ≤ vectorNorm v * vectorNorm (Q *ᵥ v) := by
    rw [vectorNorm_eq_norm, vectorNorm_eq_norm]
    simpa only [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm] using
      abs_real_inner_le_norm (toLp 2 v) (toLp 2 (Q *ᵥ v))
  have hs := vectorNorm_sq v
  nlinarith [vectorNorm_nonneg v]

theorem orderContraction_iff_operatorNorm {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian) :
    OrderContraction Q ↔ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) Q‖ ≤ 1 := by
  constructor
  · exact orderContraction_operatorNorm_le
  · intro hn
    constructor
    · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_one.sub hQ)
      intro v
      have h := (abs_le.mp (operatorNorm_quadratic_abs_le hn v)).2
      simpa only [star_trivial, sub_mulVec, one_mulVec, dotProduct_sub] using sub_nonneg.mpr h
    · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_one.add hQ)
      intro v
      have h := (abs_le.mp (operatorNorm_quadratic_abs_le hn v)).1
      simp only [star_trivial, add_mulVec, one_mulVec, dotProduct_add]
      linarith

theorem orderContraction_pair_le {Q : Matrix ι ι ℝ} (hQ : OrderContraction Q)
    (u v : ι → ℝ) : u ⬝ᵥ (Q *ᵥ v) ≤ vectorNorm u * vectorNorm v :=
  (dot_le_vectorNorm_mul u _).trans
    (mul_le_mul_of_nonneg_left (orderContraction_vectorNorm_le hQ v) (vectorNorm_nonneg u))

theorem unit_pair_equality_maps {Q : Matrix ι ι ℝ} (hQ : OrderContraction Q)
    (u v : ι → ℝ) (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (heq : u ⬝ᵥ Q *ᵥ v = 1) : Q *ᵥ v = u := by
  have hb := orderContraction_dot_sq_le hQ v
  rw [hv] at hb
  have hn := dot_self_nonneg (Q *ᵥ v - u)
  have hc : Q *ᵥ v ⬝ᵥ u = 1 := by rw [dotProduct_comm]; exact heq
  have hz : (Q *ᵥ v - u) ⬝ᵥ (Q *ᵥ v - u) = 0 := by
    simp only [sub_dotProduct, dotProduct_sub, hu, heq, hc] at hn ⊢
    linarith
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hz)

theorem pair_equality_maps_normalized {Q : Matrix ι ι ℝ} (hQ : OrderContraction Q)
    (u v : ι → ℝ) (hu : 0 < u ⬝ᵥ u) (hv : 0 < v ⬝ᵥ v)
    (heq : u ⬝ᵥ Q *ᵥ v = vectorNorm u * vectorNorm v) :
    Q *ᵥ normalizedVector v = normalizedVector u ∧
      Q *ᵥ normalizedVector u = normalizedVector v := by
  have hnu := ne_of_gt (vectorNorm_pos hu)
  have hnv := ne_of_gt (vectorNorm_pos hv)
  have hpair : normalizedVector u ⬝ᵥ Q *ᵥ normalizedVector v = 1 := by
    simp only [normalizedVector, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, heq]
    field_simp
  constructor
  · exact unit_pair_equality_maps hQ _ _ (normalizedVector_self hu) (normalizedVector_self hv) hpair
  · apply unit_pair_equality_maps hQ _ _ (normalizedVector_self hv) (normalizedVector_self hu)
    rw [dot_mulVec_comm (orderContraction_isHermitian hQ)]
    exact hpair

theorem common_pair_equality_gram {α : Type*} {Q : Matrix ι ι ℝ}
    (hQ : OrderContraction Q) (u v : α → ι → ℝ)
    (hu : ∀ y, 0 < u y ⬝ᵥ u y) (hv : ∀ y, 0 < v y ⬝ᵥ v y)
    (heq : ∀ y, u y ⬝ᵥ Q *ᵥ v y = vectorNorm (u y) * vectorNorm (v y)) (y z : α) :
    (u y ⬝ᵥ u z) / (vectorNorm (u y) * vectorNorm (u z)) =
      (v y ⬝ᵥ v z) / (vectorNorm (v y) * vectorNorm (v z)) := by
  rw [← normalizedVector_dot, ← normalizedVector_dot]
  have hy := pair_equality_maps_normalized hQ (u y) (v y) (hu y) (hv y) (heq y)
  have hz := pair_equality_maps_normalized hQ (u z) (v z) (hu z) (hv z) (heq z)
  calc
    _ = normalizedVector (u z) ⬝ᵥ Q *ᵥ normalizedVector (v y) := by
      rw [hy.1, dotProduct_comm]
    _ = normalizedVector (v y) ⬝ᵥ Q *ᵥ normalizedVector (u z) :=
      dot_mulVec_comm (orderContraction_isHermitian hQ) _ _
    _ = _ := by rw [hz.2]

omit [Fintype ι] [DecidableEq ι] in
theorem cross_isHermitian (u v : ι → ℝ) :
    (vecMulVec u v + vecMulVec v u).IsHermitian := by
  change (vecMulVec u v + vecMulVec v u).conjTranspose = _
  simp only [conjTranspose_eq_transpose_of_trivial, transpose_add, transpose_vecMulVec]
  exact add_comm _ _

theorem trace_mul_cross {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian) (u v : ι → ℝ) :
    (Q * (vecMulVec u v + vecMulVec v u)).trace = 2 * (u ⬝ᵥ Q *ᵥ v) := by
  rw [mul_add, trace_add, mul_vecMulVec, mul_vecMulVec, trace_vecMulVec, trace_vecMulVec]
  rw [dotProduct_comm (Q *ᵥ u), dotProduct_comm (Q *ᵥ v), dot_mulVec_comm hQ v u]
  ring

/-- Equality for a positively weighted sum of symmetric cross matrices forces
the normalized Gram matrices of the two vector families to coincide. The
common contraction is the spectral sign of the actual weighted sum. -/
theorem weighted_cross_trace_equality_gram {α : Type*} [Fintype α]
    (p : α → ℝ) (u v : α → ι → ℝ) (hp : ∀ y, 0 < p y)
    (hu : ∀ y, 0 < u y ⬝ᵥ u y) (hv : ∀ y, 0 < v y ⬝ᵥ v y)
    (heq : traceNorm (∑ y, p y • (vecMulVec (u y) (v y) + vecMulVec (v y) (u y))) =
      2 * ∑ y, p y * vectorNorm (u y) * vectorNorm (v y)) (y z : α) :
    (u y ⬝ᵥ u z) / (vectorNorm (u y) * vectorNorm (u z)) =
      (v y ⬝ᵥ v z) / (vectorNorm (v y) * vectorNorm (v z)) := by
  classical
  let H := ∑ y, p y • (vecMulVec (u y) (v y) + vecMulVec (v y) (u y))
  have hH : H.IsHermitian := isSelfAdjoint_sum _ fun y _ =>
    (cross_isHermitian (u y) (v y)).smul (IsSelfAdjoint.of_nonneg (hp y).le)
  let Q := signWitness hH
  have hQ : OrderContraction Q := signWitness_orderContraction hH
  have hQH : Q.IsHermitian := signWitness_isHermitian hH
  have ht : (Q * H).trace = 2 * ∑ y, p y * (u y ⬝ᵥ Q *ᵥ v y) := by
    simp only [H, Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul,
      trace_mul_cross hQH, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hs : (∑ y, p y * (u y ⬝ᵥ Q *ᵥ v y)) =
      ∑ y, p y * vectorNorm (u y) * vectorNorm (v y) := by
    have hw := signWitness_attains hH
    change (Q * H).trace = traceNorm H at hw
    rw [ht, heq] at hw
    linarith
  have hnonneg : ∀ y, 0 ≤ p y * vectorNorm (u y) * vectorNorm (v y) -
      p y * (u y ⬝ᵥ Q *ᵥ v y) := by
    intro y
    have hb := mul_le_mul_of_nonneg_left (orderContraction_pair_le hQ (u y) (v y)) (hp y).le
    nlinarith
  have hzero : ∑ y, (p y * vectorNorm (u y) * vectorNorm (v y) -
      p y * (u y ⬝ᵥ Q *ᵥ v y)) = 0 := by rw [Finset.sum_sub_distrib, hs, sub_self]
  have heach := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hnonneg y)).mp hzero
  apply common_pair_equality_gram hQ u v hu hv _ y z
  intro a
  have ha := heach a (Finset.mem_univ a)
  have hpa := hp a
  nlinarith

theorem reflection_conjugate_twice {F : Matrix ι ι ℝ} (hF : F * F = 1)
    (A : Matrix ι ι ℝ) : F * (F * A * F) * F = A := by
  calc
    _ = (F * F) * A * (F * F) := by noncomm_ring
    _ = _ := by rw [hF, one_mul, mul_one]

omit [DecidableEq ι] in
theorem reflection_conjugate_isHermitian {F A : Matrix ι ι ℝ}
    (hF : F.IsHermitian) (hA : A.IsHermitian) : (F * A * F).IsHermitian := by
  change (F * A * F).conjTranspose = _
  simp only [conjTranspose_mul, hF.eq, hA.eq, mul_assoc]

theorem orderContraction_reflection_conjugate {F Q : Matrix ι ι ℝ}
    (hF : F.IsHermitian) (hFsq : F * F = 1) (hQ : OrderContraction Q) :
    OrderContraction (F * Q * F) := by
  constructor
  · have h := hQ.1.mul_mul_conjTranspose_same F
    simpa only [hF.eq, mul_sub, sub_mul, mul_one, hFsq] using h
  · have h := hQ.2.mul_mul_conjTranspose_same F
    simpa only [hF.eq, mul_add, add_mul, mul_one, hFsq] using h

omit [Fintype ι] in
theorem orderContraction_half_sub {Q R : Matrix ι ι ℝ}
    (hQ : OrderContraction Q) (hR : OrderContraction R) :
    OrderContraction ((1 / 2 : ℝ) • (Q - R)) := by
  constructor
  · have h := (hQ.1.add hR.2).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    convert h using 1; module
  · have h := (hQ.2.add hR.1).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    convert h using 1; module

omit [DecidableEq ι] in
theorem trace_reflection_move (F A B : Matrix ι ι ℝ) :
    (F * A * F * B).trace = (A * (F * B * F)).trace := by
  calc
    _ = (F * (A * F * B)).trace := by congr 1; noncomm_ring
    _ = ((A * F * B) * F).trace := trace_mul_comm _ _
    _ = _ := by congr 1; noncomm_ring

omit [DecidableEq ι] in
theorem anticommuting_trace_identity {F Q : Matrix ι ι ℝ}
    (hQ : F * Q * F = -Q) (K : Matrix ι ι ℝ) :
    (Q * (K - F * K * F)).trace = 2 * (K * Q).trace := by
  have hm : (Q * (F * K * F)).trace = -(Q * K).trace := by
    rw [← trace_reflection_move, hQ, neg_mul, trace_neg]
  rw [mul_sub, trace_sub, hm, trace_mul_comm Q K]
  ring

/-- The anticommuting trace witness exists for every real symmetric `K` and
reflection `F`; density normalization and positivity of `K` are unnecessary. -/
theorem exists_anticommuting_trace_witness {K F : Matrix ι ι ℝ}
    (hK : K.IsHermitian) (hF : F.IsHermitian) (hFsq : F * F = 1) :
    ∃ Q : Matrix ι ι ℝ, Q.IsHermitian ∧ OrderContraction Q ∧ F * Q * F = -Q ∧
      (K * Q).trace = traceNorm (K - F * K * F) / 2 := by
  let H := K - F * K * F
  have hH : H.IsHermitian := hK.sub (reflection_conjugate_isHermitian hF hK)
  let S := signWitness hH
  have hS : OrderContraction S := signWitness_orderContraction hH
  let Q := (1 / 2 : ℝ) • (S - F * S * F)
  have hQ : OrderContraction Q := orderContraction_half_sub hS
    (orderContraction_reflection_conjugate hF hFsq hS)
  have ha : F * Q * F = -Q := by
    dsimp only [Q]
    simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul]
    rw [reflection_conjugate_twice hFsq]
    module
  refine ⟨Q, orderContraction_isHermitian hQ, hQ, ha, ?_⟩
  have hHanti : F * H * F = -H := by
    dsimp only [H]
    simp only [mul_sub, sub_mul]
    rw [reflection_conjugate_twice hFsq]
    abel
  have hSH : (S * H).trace = traceNorm H := signWitness_attains hH
  have hQH : (Q * H).trace = traceNorm H := by
    dsimp only [Q]
    rw [smul_mul_assoc, trace_smul, sub_mul, trace_sub, trace_reflection_move,
      hHanti, mul_neg, trace_neg, hSH]
    simp only [smul_eq_mul]
    ring
  have hi := anticommuting_trace_identity ha K
  change (Q * H).trace = 2 * (K * Q).trace at hi
  change (K * Q).trace = traceNorm H / 2
  linarith

theorem anticommuting_trace_le {K F Q : Matrix ι ι ℝ}
    (hK : K.IsHermitian) (hF : F.IsHermitian) (hQ : OrderContraction Q)
    (ha : F * Q * F = -Q) :
    (K * Q).trace ≤ traceNorm (K - F * K * F) / 2 := by
  have h := trace_mul_le_traceNorm
    (hK.sub (reflection_conjugate_isHermitian hF hK)) hQ
  rw [anticommuting_trace_identity ha] at h
  linarith

theorem reflection_anticommutes {F Q : Matrix ι ι ℝ}
    (hFsq : F * F = 1) (ha : F * Q * F = -Q) : F * Q = -(Q * F) := by
  have h := congrArg (fun A => A * F) ha
  simpa only [mul_assoc, hFsq, mul_one, neg_mul] using h

/-- The real finite-dimensional uncertainty relation for a reflection and an
anticommuting order contraction, with a genuinely normalized input vector. -/
theorem anticommuting_uncertainty {F Q : Matrix ι ι ℝ}
    (hF : F.IsHermitian) (hFsq : F * F = 1) (hQ : OrderContraction Q)
    (ha : F * Q * F = -Q) (ψ : ι → ℝ) (hψ : ψ ⬝ᵥ ψ = 1) :
    (ψ ⬝ᵥ F *ᵥ ψ) ^ 2 + (ψ ⬝ᵥ Q *ᵥ ψ) ^ 2 ≤ 1 := by
  let a := ψ ⬝ᵥ F *ᵥ ψ
  let b := ψ ⬝ᵥ Q *ᵥ ψ
  let A := a • F + b • Q
  have hAH : A.IsHermitian := (hF.smul (isSelfAdjoint_iff.mpr (star_trivial a))).add
    ((orderContraction_isHermitian hQ).smul (isSelfAdjoint_iff.mpr (star_trivial b)))
  have hA2 : A * A = a ^ 2 • (1 : Matrix ι ι ℝ) + b ^ 2 • (Q * Q) := by
    simp only [A, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      hFsq, reflection_anticommutes hFsq ha]
    module
  have hQQ : ψ ⬝ᵥ (Q * Q) *ᵥ ψ ≤ 1 := by
    rw [← mulVec_mulVec, dot_mulVec_comm (orderContraction_isHermitian hQ)]
    simpa only [hψ] using orderContraction_dot_sq_le hQ ψ
  have hAψ : (A *ᵥ ψ) ⬝ᵥ (A *ᵥ ψ) ≤ a ^ 2 + b ^ 2 := by
    rw [← dot_mulVec_comm hAH ψ, mulVec_mulVec, hA2]
    simp only [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul, hψ, mul_one]
    nlinarith [sq_nonneg b]
  have hinner : ψ ⬝ᵥ A *ᵥ ψ = a ^ 2 + b ^ 2 := by
    simp only [A, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
    change a * a + b * b = _
    ring
  have hcs := dot_le_vectorNorm_mul ψ (A *ᵥ ψ)
  have hnorm : vectorNorm ψ = 1 := by simp [vectorNorm, hψ]
  rw [hinner, hnorm, one_mul] at hcs
  have hnorm2 := vectorNorm_sq (A *ᵥ ψ)
  have hnonneg : 0 ≤ a ^ 2 + b ^ 2 := add_nonneg (sq_nonneg a) (sq_nonneg b)
  have hsq : (a ^ 2 + b ^ 2) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    nlinarith [vectorNorm_nonneg (A *ᵥ ψ)]
  change a ^ 2 + b ^ 2 ≤ 1
  nlinarith

/-- Exact real-matrix version of the manuscript maximum, using the Euclidean
continuous-linear-map operator norm rather than a matrix entrywise norm. -/
theorem anticommuting_trace_maximum {K F : Matrix ι ι ℝ}
    (hK : K.IsHermitian) (hF : F.IsHermitian) (hFsq : F * F = 1) :
    IsGreatest {t : ℝ | ∃ Q : Matrix ι ι ℝ, Q.IsHermitian ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) Q‖ ≤ 1 ∧ F * Q * F = -Q ∧
      t = (K * Q).trace} (traceNorm (K - F * K * F) / 2) := by
  constructor
  · obtain ⟨Q, hQH, hQ, ha, ht⟩ := exists_anticommuting_trace_witness hK hF hFsq
    exact ⟨Q, hQH, orderContraction_operatorNorm_le hQ, ha, ht.symm⟩
  · rintro t ⟨Q, hQH, hn, ha, rfl⟩
    exact anticommuting_trace_le hK hF ((orderContraction_iff_operatorNorm hQH).mpr hn) ha

theorem anticommuting_uncertainty_operatorNorm {F Q : Matrix ι ι ℝ}
    (hF : F.IsHermitian) (hFsq : F * F = 1) (hQ : Q.IsHermitian)
    (hn : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) Q‖ ≤ 1)
    (ha : F * Q * F = -Q) (ψ : ι → ℝ) (hψ : ψ ⬝ᵥ ψ = 1) :
    (ψ ⬝ᵥ F *ᵥ ψ) ^ 2 + (ψ ⬝ᵥ Q *ᵥ ψ) ^ 2 ≤ 1 :=
  anticommuting_uncertainty hF hFsq ((orderContraction_iff_operatorNorm hQ).mpr hn) ha ψ hψ

end Hellinger.TraceEquality
