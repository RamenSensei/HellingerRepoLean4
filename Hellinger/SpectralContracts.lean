import Hellinger.ProductStateProperties
import Hellinger.Complexification
import Hellinger.ComplexEigenvalueOrder
import Hellinger.PosteriorGram
import Hellinger.CutNorm
import Hellinger.PaperSpecs

/-! Manuscript-facing spectral contracts. Each theorem repeats the full
mathematical assertion at its concrete objects; the proofs supply every
intermediate ensemble, spectrum, and matrix-norm fact. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace Hellinger.SpectralContracts
open ProductState ParityBlocks

theorem square_root_lifting (n : ℕ) (f : Cube n → ℝ) (hf : PaperSpecs.IsBoolean f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    ComplexSpectral.traceNorm
      (Complexification.complexify (state n (root ρ)) -
        Complexification.complexify (Matrix.diagonal f) *
        Complexification.complexify (state n (root ρ)) *
        Complexification.complexify (Matrix.diagonal f)) / 2 ≤
      PaperSpecs.posteriorRootMean f ρ hρ := by
  rw [Complexification.traceNorm_reflection_difference]
  exact PosteriorState.bsc_lifting n f hf ρ hρ

theorem product_state_formula (n : ℕ) (c : ℝ) :
    state n c = ((2 : ℝ) ^ n)⁻¹ • (List.ofFn (fun i : Fin n =>
      1 + c • SpinState.spin n i)).prod ∧
    (∀ x z, state n c x z = c ^ hammingDistance n x z / (2 : ℝ) ^ n) := by
  exact ⟨SpinState.state_ordered_product n c, state_entry n c⟩

theorem anticommuting_witnesses (d : ℕ) (K F : Matrix (Fin d) (Fin d) ℂ)
    (hK : K.PosSemidef) (_htrace : K.trace = 1)
    (hF : F.IsHermitian) (hF2 : F * F = 1) :
    IsGreatest {t : ℝ | ∃ Q : Matrix (Fin d) (Fin d) ℂ,
      Q.IsHermitian ∧ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) Q‖ ≤ 1 ∧
      F * Q * F = -Q ∧ t = (K * Q).trace.re}
      (ComplexSpectral.traceNorm (K - F * K * F) / 2) ∧
    (∀ Q : Matrix (Fin d) (Fin d) ℂ, Q.IsHermitian →
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) Q‖ ≤ 1 → F * Q * F = -Q →
      ∀ ψ : Fin d → ℂ, ‖WithLp.toLp 2 ψ‖ = 1 →
        (star ψ ⬝ᵥ F *ᵥ ψ).re ^ 2 + (star ψ ⬝ᵥ Q *ᵥ ψ).re ^ 2 ≤ 1) := by
  exact ⟨ComplexSpectral.anticommuting_trace_maximum hK.isHermitian hF hF2,
    fun Q hQ hnorm ha ψ hψ =>
      ComplexSpectral.anticommuting_uncertainty hF hF2 hQ hnorm ha ψ hψ⟩

def evenRestriction (n : ℕ) (c : ℝ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ :=
  (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary (n + 1)) (state (n + 1) c)).submatrix
    (fun i => (evenEquiv n i).val) (fun i => (evenEquiv n i).val)

def oddRestriction (n : ℕ) (c : ℝ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ :=
  (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary (n + 1)) (state (n + 1) c)).submatrix
    (fun i => (oddEquiv n i).val) (fun i => (oddEquiv n i).val)

theorem evenRestriction_diagonal (n : ℕ) (c : ℝ) :
    evenRestriction n c = Matrix.diagonal (evenEigenvalue n c) := by
  ext i j
  have h := congrArg (fun M : Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n))
      (Fin (2 ^ n) ⊕ Fin (2 ^ n)) ℝ => M (Sum.inl i) (Sum.inl j))
    (state_diagonal_blocks n c)
  simpa only [evenRestriction, transformed_state, Matrix.submatrix_apply,
    blockEquiv_inl, Matrix.fromBlocks_apply₁₁] using h

theorem oddRestriction_diagonal (n : ℕ) (c : ℝ) :
    oddRestriction n c = Matrix.diagonal (oddEigenvalue n c) := by
  ext i j
  have h := congrArg (fun M : Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n))
      (Fin (2 ^ n) ⊕ Fin (2 ^ n)) ℝ => M (Sum.inr i) (Sum.inr j))
    (state_diagonal_blocks n c)
  simpa only [oddRestriction, transformed_state, Matrix.submatrix_apply,
    blockEquiv_inr, Matrix.fromBlocks_apply₂₂] using h

/-- The decreasing eigenvalues of the actual two parity restrictions. -/
theorem exact_parity_spectrum_distance (n : ℕ) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    ∃ hA : (evenRestriction n c).IsHermitian,
    ∃ hB : (oddRestriction n c).IsHermitian,
      (∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j|) = c := by
  rw [evenRestriction_diagonal, oddRestriction_diagonal]
  refine ⟨Matrix.isHermitian_diagonal _, Matrix.isHermitian_diagonal _, ?_⟩
  rw [TraceNorm.eigenvalues₀_diagonal_of_antitone _ (evenEigenvalue_antitone n c hc),
    TraceNorm.eigenvalues₀_diagonal_of_antitone _ (oddEigenvalue_antitone n c hc)]
  calc
    _ = ∑ j : Fin (2 ^ n), |evenEigenvalue n c j - oddEigenvalue n c j| :=
      (finCongr (Fintype.card_fin (2 ^ n))).sum_comp _
    _ = c := actual_parity_spectra_l1 n c hc

theorem trace_equality (n : ℕ) (f : Cube n → ℝ) (hf : PaperSpecs.IsBoolean f)
    (hnonconstant : ∃ x z, f x ≠ f z) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (_hρpos : 0 < ρ) (hρlt : ρ < 1)
    (heq : PaperSpecs.posteriorRootMean f ρ hρ =
      TraceNorm.traceNorm (state n (root ρ) -
        Matrix.diagonal f * state n (root ρ) * Matrix.diagonal f) / 2) :
    ∀ y z, |(cubeBSC n ρ hρ).apply f y| = |(cubeBSC n ρ hρ).apply f z| := by
  exact PosteriorGram.bsc_posterior_abs_constant_of_lifting_equality
    f hf hnonconstant ρ hρ hρlt heq.symm

theorem ordered_matrix_comparison (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j|) ≤
      ComplexSpectral.traceNorm (A - B) :=
  ComplexSpectral.ordered_eigenvalue_distance_le_traceNorm hA hB

theorem gibbs_representation (n : ℕ) (c : ℝ) (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ β : ℝ, 0 < β ∧ c = Real.tanh β ∧
      state n c = ((2 * Real.cosh β) ^ n)⁻¹ •
        NormedSpace.exp (β • ∑ i : Fin n, SpinState.spin n i) :=
  SpinState.exists_positive_gibbs_parameter n c hc

theorem three_qubit_counterexample (c : ℝ) (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ P : Matrix (Cube 3) (Cube 3) ℂ,
      P.IsHermitian ∧ P * P = 1 ∧
      (∀ s, (Complexification.complexify (hadamard 3) * P *
        Complexification.complexify (hadamard 3)) s s = 0) ∧
      ComplexSpectral.traceNorm (Complexification.complexify (state 3 c) -
        P * Complexification.complexify (state 3 c) * P) / 2 = c * (1 + c ^ 2) / 2 ∧
      c * (1 + c ^ 2) / 2 < c ∧
      (∀ f : Cube 3 → ℝ, P ≠ Complexification.complexify (Matrix.diagonal f)) := by
  obtain ⟨P, hP, hP2, hdiag, hnorm, hlt, hnot⟩ :=
    ReflectionCounterexample.reflection_counterexample c hc
  refine ⟨Complexification.complexify P, Complexification.complexify_isHermitian hP,
    ?_, ?_, ?_, hlt, ?_⟩
  · rw [← map_mul, hP2, map_one]
  · intro s
    rw [← map_mul, ← map_mul]
    have h := hdiag s
    simp only [Unitary.conjStarAlgAut_apply, hadamardUnitary_coe,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      hadamard_transpose] at h
    simp only [Complexification.complexify_apply, h, Complex.ofReal_zero]
  · rw [Complexification.traceNorm_reflection_difference, hnorm]
  · intro f h
    apply hnot f
    ext x z
    have he := congrArg (fun M : Matrix (Cube 3) (Cube 3) ℂ => M x z) h
    exact Complex.ofReal_injective he

end Hellinger.SpectralContracts
