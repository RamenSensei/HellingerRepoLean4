import Hellinger.TraceNorm

/-! Loewner monotonicity of ordered eigenvalues and the trace-norm comparison. -/

set_option autoImplicit false
open scoped BigOperators MatrixOrder
open Matrix Unitary

namespace Hellinger.TraceNorm

section SpectralOrder

open scoped InnerProductSpace
open WithLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {d : ℕ}

omit [FiniteDimensional ℝ E] in
theorem norm_sq_eq_sum_repr_sq (b : OrthonormalBasis (Fin d) ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ j, (b.repr x j) ^ 2 := by
  simpa only [b.repr_apply_apply, Real.norm_eq_abs, sq_abs] using
    (b.sum_sq_norm_inner_right x).symm

theorem inner_apply_eq_sum_eigenvalues {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hd : Module.finrank ℝ E = d) (x : E) :
    ⟪x, T x⟫_ℝ = ∑ j, hT.eigenvalues hd j * ((hT.eigenvectorBasis hd).repr x j) ^ 2 := by
  rw [← (hT.eigenvectorBasis hd).repr.inner_map_map x (T x)]
  simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    hT.eigenvectorBasis_apply_self_apply hd]
  apply Finset.sum_congr rfl
  intro j _
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

theorem eigenvalue_mul_norm_sq_le_inner {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hd : Module.finrank ℝ E = d) (k : Fin d) (x : E)
    (hx : ∀ j : Fin d, k < j → (hT.eigenvectorBasis hd).repr x j = 0) :
    hT.eigenvalues hd k * ‖x‖ ^ 2 ≤ ⟪x, T x⟫_ℝ := by
  rw [inner_apply_eq_sum_eigenvalues hT hd,
    norm_sq_eq_sum_repr_sq (hT.eigenvectorBasis hd), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : k < j
  · simp [hx j hj]
  · exact mul_le_mul_of_nonneg_right
      (hT.eigenvalues_antitone hd (le_of_not_gt hj)) (sq_nonneg _)

theorem inner_le_eigenvalue_mul_norm_sq {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hd : Module.finrank ℝ E = d) (k : Fin d) (x : E)
    (hx : ∀ j : Fin d, j < k → (hT.eigenvectorBasis hd).repr x j = 0) :
    ⟪x, T x⟫_ℝ ≤ hT.eigenvalues hd k * ‖x‖ ^ 2 := by
  rw [inner_apply_eq_sum_eigenvalues hT hd,
    norm_sq_eq_sum_repr_sq (hT.eigenvectorBasis hd), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j < k
  · simp [hx j hj]
  · exact mul_le_mul_of_nonneg_right
      (hT.eigenvalues_antitone hd (le_of_not_gt hj)) (sq_nonneg _)

/-- Extend the first `k` coordinates by zero. -/
noncomputable def initialCoordinates (d k : ℕ) :
    (Fin k → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
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
  have hj := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x ⟨j.val, lt_of_lt_of_le j.isLt hk⟩) h
  simpa [initialCoordinates, j.isLt] using hj

/-- Restrict to the first `k` coordinates. -/
noncomputable def firstCoordinates (d k : ℕ) (hk : k ≤ d) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (Fin k → ℝ) where
  toFun x j := x ⟨j.val, lt_of_lt_of_le j.isLt hk⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional ℝ E] in
/-- The first `k+1` vectors of one orthonormal basis have a nonzero linear
combination orthogonal to the first `k` vectors of any other basis. -/
theorem exists_initial_final_vector (b c : OrthonormalBasis (Fin d) ℝ E) (k : Fin d) :
    ∃ x : E, x ≠ 0 ∧
      (∀ j : Fin d, k < j → b.repr x j = 0) ∧
      (∀ j : Fin d, j < k → c.repr x j = 0) := by
  let emb : (Fin (k.val + 1) → ℝ) →ₗ[ℝ] E :=
    b.repr.symm.toLinearEquiv.toLinearMap.comp (initialCoordinates d (k.val + 1))
  let L : (Fin (k.val + 1) → ℝ) →ₗ[ℝ] (Fin k.val → ℝ) :=
    (firstCoordinates d k.val k.isLt.le).comp (c.repr.toLinearEquiv.toLinearMap.comp emb)
  have hdim : Module.finrank ℝ (Fin k.val → ℝ) <
      Module.finrank ℝ (Fin (k.val + 1) → ℝ) := by simp
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
theorem symmetric_eigenvalues_mono {T S : E →ₗ[ℝ] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : Module.finrank ℝ E = d)
    (hTS : ∀ x : E, ⟪x, T x⟫_ℝ ≤ ⟪x, S x⟫_ℝ) (k : Fin d) :
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

/-- Loewner order implies pointwise order of the decreasing eigenvalue lists.
The min--max step is proved above using a dimension argument. -/
theorem matrix_eigenvalues_mono {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A ≤ B)
    (k : Fin (Fintype.card ι)) : hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  apply symmetric_eigenvalues_mono
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB) finrank_euclideanSpace
  intro x
  have h := (Matrix.le_iff.mp hAB).dotProduct_mulVec_nonneg (WithLp.ofLp x)
  rw [Matrix.sub_mulVec, dotProduct_sub] at h
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, dotProduct_comm] using sub_nonneg.mp h

theorem trace_eq_sum_eigenvalues₀ {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    A.trace = ∑ j : Fin (Fintype.card ι), hA.eigenvalues₀ j := by
  rw [hA.trace_eq_sum_eigenvalues]
  let e : ι ≃ Fin (Fintype.card ι) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm
  simpa only [Matrix.IsHermitian.eigenvalues, RCLike.ofReal_real_eq_id, id_eq] using
    e.sum_comp hA.eigenvalues₀

/-- The positive deviations of the ordered eigenvalues are bounded by the
trace of the actual positive part of the matrix difference. -/
theorem sum_positive_eigenvalue_differences_le {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ j, max (hA.eigenvalues₀ j - hB.eigenvalues₀ j) 0) ≤ ((A - B)⁺).trace := by
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
    _ = C.trace - B.trace := by
      rw [Finset.sum_sub_distrib, ← trace_eq_sum_eigenvalues₀ hC, ← trace_eq_sum_eigenvalues₀ hB]
    _ = _ := by simp [C, trace_add]

/-- Mirsky's trace-norm comparison, with ordered eigenvalues and all
multiplicities.  No simple-spectrum or eigenvalue-monotonicity hypothesis is
needed: the latter is proved from Loewner order above. -/
theorem ordered_eigenvalue_distance_le_traceNorm {A B : Matrix ι ι ℝ}
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
    _ ≤ ((A - B)⁺).trace + ((A - B)⁻).trace := add_le_add hpos hneg
    _ = traceNorm (A - B) := by
      rw [← trace_add, CFC.posPart_add_negPart (A - B) (hA.sub hB)]
      rfl

theorem isHermitian_conjugate {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (U : Matrix.unitaryGroup ι ℝ) : (conjStarAlgAut ℝ _ U A).IsHermitian := by
  simpa only [conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
    Matrix.isHermitian_mul_mul_conjTranspose (U : Matrix ι ι ℝ) hA

theorem eigenvalues₀_conjugate {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (U : Matrix.unitaryGroup ι ℝ) :
    (isHermitian_conjugate hA U).eigenvalues₀ = hA.eigenvalues₀ := by
  have hchar : (conjStarAlgAut ℝ _ U A).charpoly = A.charpoly := by
    rw [conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← mul_assoc,
      coe_star_mul_self, one_mul]
  rw [← List.ofFn_inj, ← (isHermitian_conjugate hA U).sort_roots_charpoly_eq_eigenvalues₀,
    ← hA.sort_roots_charpoly_eq_eigenvalues₀, hchar]

/-- The unitary-conjugation form used by the antipodal block argument. -/
theorem ordered_eigenvalue_distance_le_traceNorm_conjugate {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (U : Matrix.unitaryGroup ι ℝ) :
    (∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j|) ≤
      traceNorm (A - conjStarAlgAut ℝ _ U B) := by
  have h := ordered_eigenvalue_distance_le_traceNorm hA (isHermitian_conjugate hB U)
  rwa [eigenvalues₀_conjugate hB U] at h

/-- A decreasing diagonal is already the decreasing eigenvalue list.  The
cast only identifies `card (Fin N)` with `N`. -/
theorem eigenvalues₀_diagonal_of_antitone {N : ℕ} (a : Fin N → ℝ) (ha : Antitone a) :
    (Matrix.isHermitian_diagonal a).eigenvalues₀ =
      fun j => a (Fin.cast (Fintype.card_fin N) j) := by
  have hroots : (Matrix.diagonal a).charpoly.roots = (List.ofFn a : Multiset ℝ) := by
    rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hsorted : ((Matrix.diagonal a).charpoly.roots.map RCLike.re).sort (· ≥ ·) =
      List.ofFn a := by
    rw [hroots]
    simp only [Multiset.map_coe, List.map_ofFn, Function.comp_def, RCLike.re_to_real,
      Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact ha.sortedGE_ofFn
  apply List.ofFn_inj.mp
  calc
    _ = ((Matrix.diagonal a).charpoly.roots.map RCLike.re).sort (· ≥ ·) :=
      (Matrix.isHermitian_diagonal a).sort_roots_charpoly_eq_eigenvalues₀.symm
    _ = List.ofFn a := hsorted
    _ = _ := List.ofFn_congr (Fintype.card_fin N).symm a

/-- Direct diagonal-list form, with the spectral identification proved here. -/
theorem sorted_diagonal_distance_le_traceNorm {N : ℕ} (a b : Fin N → ℝ)
    (ha : Antitone a) (hb : Antitone b) (U : Matrix.unitaryGroup (Fin N) ℝ) :
    (∑ j, |a j - b j|) ≤ traceNorm
      (Matrix.diagonal a - conjStarAlgAut ℝ _ U (Matrix.diagonal b)) := by
  have h := ordered_eigenvalue_distance_le_traceNorm_conjugate
    (Matrix.isHermitian_diagonal a) (Matrix.isHermitian_diagonal b) U
  rw [eigenvalues₀_diagonal_of_antitone a ha, eigenvalues₀_diagonal_of_antitone b hb] at h
  let e : Fin (Fintype.card (Fin N)) ≃ Fin N :=
    ⟨Fin.cast (Fintype.card_fin N), Fin.cast (Fintype.card_fin N).symm,
      (by intro j; simp), (by intro j; simp)⟩
  have hsum := e.sum_comp (fun j => |a j - b j|)
  exact hsum ▸ h

end MatrixOrder

end Hellinger.TraceNorm

#print axioms Hellinger.TraceNorm.matrix_eigenvalues_mono
#print axioms Hellinger.TraceNorm.ordered_eigenvalue_distance_le_traceNorm
#print axioms Hellinger.TraceNorm.ordered_eigenvalue_distance_le_traceNorm_conjugate
