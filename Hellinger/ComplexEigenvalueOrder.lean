import Hellinger.ComplexSpectral

/-! Ordered eigenvalue monotonicity and Mirsky comparison over the actual
complex field, using complex dimensions in the min--max argument. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Unitary

namespace Hellinger.ComplexSpectral

section SpectralOrder

open scoped InnerProductSpace
open WithLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {d : ℕ}

omit [FiniteDimensional ℂ E] in
theorem norm_sq_eq_sum_repr_norm_sq (b : OrthonormalBasis (Fin d) ℂ E) (x : E) :
    ‖x‖ ^ 2 = ∑ j, ‖b.repr x j‖ ^ 2 := by
  simpa only [b.repr_apply_apply] using
    (b.sum_sq_norm_inner_right x).symm

theorem inner_apply_eq_sum_eigenvalues {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hd : Module.finrank ℂ E = d) (x : E) :
    (inner ℂ x (T x)).re = ∑ j, hT.eigenvalues hd j * ‖(hT.eigenvectorBasis hd).repr x j‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis hd).repr.inner_map_map x (T x)]
  simp only [PiLp.inner_apply, hT.eigenvectorBasis_apply_self_apply hd, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (inner ℂ ((hT.eigenvectorBasis hd).repr x j)
    ((hT.eigenvalues hd j : ℂ) • ((hT.eigenvectorBasis hd).repr x j))).re = _
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem eigenvalue_mul_norm_sq_le_inner {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hd : Module.finrank ℂ E = d) (k : Fin d) (x : E)
    (hx : ∀ j : Fin d, k < j → (hT.eigenvectorBasis hd).repr x j = 0) :
    hT.eigenvalues hd k * ‖x‖ ^ 2 ≤ (inner ℂ x (T x)).re := by
  rw [inner_apply_eq_sum_eigenvalues hT hd,
    norm_sq_eq_sum_repr_norm_sq (hT.eigenvectorBasis hd), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : k < j
  · simp [hx j hj]
  · exact mul_le_mul_of_nonneg_right
      (hT.eigenvalues_antitone hd (le_of_not_gt hj)) (sq_nonneg _)

theorem inner_le_eigenvalue_mul_norm_sq {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hd : Module.finrank ℂ E = d) (k : Fin d) (x : E)
    (hx : ∀ j : Fin d, j < k → (hT.eigenvectorBasis hd).repr x j = 0) :
    (inner ℂ x (T x)).re ≤ hT.eigenvalues hd k * ‖x‖ ^ 2 := by
  rw [inner_apply_eq_sum_eigenvalues hT hd,
    norm_sq_eq_sum_repr_norm_sq (hT.eigenvectorBasis hd), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j < k
  · simp [hx j hj]
  · exact mul_le_mul_of_nonneg_right
      (hT.eigenvalues_antitone hd (le_of_not_gt hj)) (sq_nonneg _)

/-- Extend the first `k` coordinates by zero. -/
noncomputable def initialCoordinates (d k : ℕ) :
    (Fin k → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) where
  toFun c := toLp 2 (fun j => if h : j.val < k then c ⟨j.val, h⟩ else 0)
  map_add' c e := by
    apply PiLp.ext
    intro j
    by_cases h : j.val < k <;> simp [h]
  map_smul' r c := by
    apply PiLp.ext
    intro j
    by_cases h : j.val < k <;> simp [h]

theorem initialCoordinates_injective {d k : ℕ} (hk : k ≤ d) :
    Function.Injective (initialCoordinates d k) := by
  intro c e h
  funext j
  have hj := congrArg (fun x : EuclideanSpace ℂ (Fin d) => x ⟨j.val, lt_of_lt_of_le j.isLt hk⟩) h
  simpa [initialCoordinates, j.isLt] using hj

/-- Restrict to the first `k` coordinates. -/
noncomputable def firstCoordinates (d k : ℕ) (hk : k ≤ d) :
    EuclideanSpace ℂ (Fin d) →ₗ[ℂ] (Fin k → ℂ) where
  toFun x j := x ⟨j.val, lt_of_lt_of_le j.isLt hk⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional ℂ E] in
/-- The first `k+1` vectors of one orthonormal basis have a nonzero linear
combination orthogonal to the first `k` vectors of any other basis. -/
theorem exists_initial_final_vector (b c : OrthonormalBasis (Fin d) ℂ E) (k : Fin d) :
    ∃ x : E, x ≠ 0 ∧
      (∀ j : Fin d, k < j → b.repr x j = 0) ∧
      (∀ j : Fin d, j < k → c.repr x j = 0) := by
  let emb : (Fin (k.val + 1) → ℂ) →ₗ[ℂ] E :=
    b.repr.symm.toLinearEquiv.toLinearMap.comp (initialCoordinates d (k.val + 1))
  let L : (Fin (k.val + 1) → ℂ) →ₗ[ℂ] (Fin k.val → ℂ) :=
    (firstCoordinates d k.val k.isLt.le).comp (c.repr.toLinearEquiv.toLinearMap.comp emb)
  have hdim : Module.finrank ℂ (Fin k.val → ℂ) <
      Module.finrank ℂ (Fin (k.val + 1) → ℂ) := by simp
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hdim)
  have hLa : L a = 0 := LinearMap.mem_ker.mp ha
  have hemb : Function.Injective emb :=
    b.repr.symm.injective.comp (initialCoordinates_injective (Nat.succ_le_of_lt k.isLt))
  refine ⟨emb a, ?_, ?_, ?_⟩
  · intro hz
    apply ha0
    exact hemb (by simpa using hz)
  · intro j hj
    change b.repr (b.repr.symm (initialCoordinates d (k.val + 1) a)) j = 0
    rw [LinearIsometryEquiv.apply_symm_apply]
    have hnot : ¬j.val < k.val + 1 := by
      have : k.val < j.val := hj
      omega
    change (if h : j.val < k.val + 1 then a ⟨j.val, h⟩ else 0) = 0
    exact dif_neg hnot
  · intro j hj
    have h := congrFun hLa ⟨j.val, hj⟩
    change c.repr (emb a) j = 0 at h
    exact h

/-- Ordered eigenvalues are monotone under quadratic-form order. -/
theorem symmetric_eigenvalues_mono {T S : E →ₗ[ℂ] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : Module.finrank ℂ E = d)
    (hTS : ∀ x : E, (inner ℂ x (T x)).re ≤ (inner ℂ x (S x)).re) (k : Fin d) :
    hT.eigenvalues hd k ≤ hS.eigenvalues hd k := by
  obtain ⟨x, hx, hxt, hxs⟩ :=
    exists_initial_final_vector (hT.eigenvectorBasis hd) (hS.eigenvectorBasis hd) k
  have h : hT.eigenvalues hd k * ‖x‖ ^ 2 ≤ hS.eigenvalues hd k * ‖x‖ ^ 2 :=
    (eigenvalue_mul_norm_sq_le_inner hT hd k x hxt).trans
      ((hTS x).trans (inner_le_eigenvalue_mul_norm_sq hS hd k x hxs))
  exact _root_.le_of_mul_le_mul_right h (sq_pos_of_pos (norm_pos_iff.mpr hx))

end SpectralOrder

section MatrixOrder

open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_eigenvalues_mono {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A ≤ B)
    (k : Fin (Fintype.card ι)) : hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  apply symmetric_eigenvalues_mono
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB) finrank_euclideanSpace
  intro x
  have h := (Matrix.le_iff.mp hAB).re_dotProduct_nonneg (WithLp.ofLp x)
  rw [Matrix.sub_mulVec, dotProduct_sub, map_sub] at h
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, RCLike.re_to_complex, dotProduct_comm] using sub_nonneg.mp h

theorem realTrace_eq_sum_eigenvalues₀ {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    realTrace A = ∑ j : Fin (Fintype.card ι), hA.eigenvalues₀ j := by
  unfold realTrace
  rw [hA.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re]
  let e : ι ≃ Fin (Fintype.card ι) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm
  simpa only [Matrix.IsHermitian.eigenvalues] using e.sum_comp hA.eigenvalues₀

theorem sum_positive_eigenvalue_differences_le {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ j, max (hA.eigenvalues₀ j - hB.eigenvalues₀ j) 0) ≤ realTrace ((A - B)⁺) := by
  let C := B + (A - B)⁺
  have hP : ((A - B)⁺).PosSemidef := (CFC.posPart_nonneg (A - B)).posSemidef
  have hC : C.IsHermitian := hB.add hP.isHermitian
  have hBC : B ≤ C := by
    change (B + (A - B)⁺ - B).PosSemidef
    simpa only [add_sub_cancel_left] using hP
  have hAC : A ≤ C := by
    have horder : A - B ≤ (A - B)⁺ := CFC.le_posPart (hA.sub hB)
    change (B + (A - B)⁺ - A).PosSemidef
    have hid : B + (A - B)⁺ - A = (A - B)⁺ - (A - B) := by abel
    rw [hid]
    exact Matrix.le_iff.mp horder
  calc
    _ ≤ ∑ j, (hC.eigenvalues₀ j - hB.eigenvalues₀ j) := by
      apply Finset.sum_le_sum
      intro j _
      exact max_le (sub_le_sub_right (matrix_eigenvalues_mono hA hC hAC j) _)
        (sub_nonneg.mpr (matrix_eigenvalues_mono hB hC hBC j))
    _ = realTrace C - realTrace B := by
      rw [Finset.sum_sub_distrib, ← realTrace_eq_sum_eigenvalues₀ hC,
        ← realTrace_eq_sum_eigenvalues₀ hB]
    _ = _ := by simp [C]

/-- Mirsky's trace-norm comparison for arbitrary complex Hermitian matrices,
with sorted eigenvalues and every multiplicity included. -/
theorem ordered_eigenvalue_distance_le_traceNorm {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j|) ≤ traceNorm (A - B) := by
  have hpos := sum_positive_eigenvalue_differences_le hA hB
  have hneg := sum_positive_eigenvalue_differences_le hB hA
  rw [show B - A = -(A - B) by abel, CFC.posPart_neg] at hneg
  calc
    _ = (∑ j, max (hA.eigenvalues₀ j - hB.eigenvalues₀ j) 0) +
        ∑ j, max (hB.eigenvalues₀ j - hA.eigenvalues₀ j) 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simpa only [_root_.posPart_def, _root_.negPart_def, neg_sub] using
        (_root_.posPart_add_negPart (hA.eigenvalues₀ j - hB.eigenvalues₀ j)).symm
    _ ≤ realTrace ((A - B)⁺) + realTrace ((A - B)⁻) := add_le_add hpos hneg
    _ = traceNorm (A - B) := by
      rw [← realTrace_add, CFC.posPart_add_negPart (A - B) (hA.sub hB)]
      rfl

theorem isHermitian_conjugate {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (U : Matrix.unitaryGroup ι ℂ) : (conjStarAlgAut ℂ _ U A).IsHermitian := by
  simpa only [conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
    Matrix.isHermitian_mul_mul_conjTranspose (U : Matrix ι ι ℂ) hA

theorem eigenvalues₀_conjugate {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (U : Matrix.unitaryGroup ι ℂ) :
    (isHermitian_conjugate hA U).eigenvalues₀ = hA.eigenvalues₀ := by
  have hchar : (conjStarAlgAut ℂ _ U A).charpoly = A.charpoly := by
    rw [conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← mul_assoc, coe_star_mul_self, one_mul]
  rw [← List.ofFn_inj, ← (isHermitian_conjugate hA U).sort_roots_charpoly_eq_eigenvalues₀,
    ← hA.sort_roots_charpoly_eq_eigenvalues₀, hchar]

theorem ordered_eigenvalue_distance_le_traceNorm_conjugate {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (U : Matrix.unitaryGroup ι ℂ) :
    (∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j|) ≤
      traceNorm (A - conjStarAlgAut ℂ _ U B) := by
  have h := ordered_eigenvalue_distance_le_traceNorm hA (isHermitian_conjugate hB U)
  rwa [eigenvalues₀_conjugate hB U] at h

end MatrixOrder

end Hellinger.ComplexSpectral
