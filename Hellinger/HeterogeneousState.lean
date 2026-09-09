import Hellinger.ParityBlocks

/-! Heterogeneous product states and contraction under diagonal dephasing. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix

namespace Hellinger.HeterogeneousState

open Hellinger.Fourier Hellinger.PosteriorState Hellinger.TraceNorm
open Hellinger.ProductState (oneQubit oneQubit_symmetric)

def state (n : ℕ) (z : Fin n → ℝ) : Matrix (Cube n) (Cube n) ℝ :=
  fun x y => ∏ i, oneQubit (z i) (x i) (y i)

theorem state_isHermitian (n : ℕ) (z : Fin n → ℝ) : (state n z).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, star_trivial, state]
  exact Finset.prod_congr rfl (fun i _ => oneQubit_symmetric (z i) (y i) (x i))

theorem state_const (n : ℕ) (c : ℝ) : state n (fun _ => c) = ProductState.state n c := rfl

def phaseMatrix {n : ℕ} (s : Cube n) : Matrix (Cube n) (Cube n) ℝ :=
  Matrix.diagonal (phase s)

theorem phaseMatrix_star {n : ℕ} (s : Cube n) : star (phaseMatrix s) = phaseMatrix s := by
  exact Matrix.isHermitian_diagonal (phase s)

theorem phaseMatrix_sq {n : ℕ} (s : Cube n) : phaseMatrix s * phaseMatrix s = 1 := by
  rw [phaseMatrix, Matrix.diagonal_mul_diagonal]
  have hs : (fun x => phase s x * phase s x) = (fun _ => (1 : ℝ)) := by
    funext x
    simpa only [pow_two] using phase_sq s x
  rw [hs, Matrix.diagonal_one]

def phaseUnitary {n : ℕ} (s : Cube n) : Matrix.unitaryGroup (Cube n) ℝ :=
  ⟨phaseMatrix s, Matrix.mem_unitaryGroup_iff.mpr (by rw [phaseMatrix_star, phaseMatrix_sq])⟩

def phaseConjugate {n : ℕ} (s : Cube n) (A : Matrix (Cube n) (Cube n) ℝ) :
    Matrix (Cube n) (Cube n) ℝ := phaseMatrix s * A * phaseMatrix s

theorem phaseConjugate_entry {n : ℕ} (s : Cube n) (A : Matrix (Cube n) (Cube n) ℝ)
    (x y : Cube n) : phaseConjugate s A x y = phase s x * A x y * phase s y := by
  simp only [phaseConjugate, phaseMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem phaseConjugate_eq {n : ℕ} (s : Cube n) (A : Matrix (Cube n) (Cube n) ℝ) :
    phaseConjugate s A = Unitary.conjStarAlgAut ℝ _ (phaseUnitary s) A := by
  simp only [Unitary.conjStarAlgAut_apply, phaseUnitary, phaseMatrix_star]
  rfl

theorem phaseConjugate_isHermitian {n : ℕ} (s : Cube n)
    {A : Matrix (Cube n) (Cube n) ℝ} (hA : A.IsHermitian) :
    (phaseConjugate s A).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, star_trivial, phaseConjugate_entry]
  have ha := congrFun (congrFun hA.eq x) y
  change A y x = A x y at ha
  rw [ha]
  ring

def mixingChannel (n : ℕ) (η : Fin n → ℝ) (hη : ∀ i, η i ∈ Set.Icc (0 : ℝ) 1) :
    UniformChannel (Cube n) := UniformChannel.product (fun i => bsc (η i) (hη i))

def mixtureWeight (n : ℕ) (η : Fin n → ℝ) (hη : ∀ i, η i ∈ Set.Icc (0 : ℝ) 1)
    (s : Cube n) : ℝ := (mixingChannel n η hη).weight (fun _ => false) s

def dephase (n : ℕ) (η : Fin n → ℝ) (hη : ∀ i, η i ∈ Set.Icc (0 : ℝ) 1)
    (A : Matrix (Cube n) (Cube n) ℝ) : Matrix (Cube n) (Cube n) ℝ :=
  ∑ s, mixtureWeight n η hη s • phaseConjugate s A

theorem dephase_traceNorm_le (n : ℕ) (η : Fin n → ℝ) (hη : ∀ i, η i ∈ Set.Icc (0 : ℝ) 1)
    (A : Matrix (Cube n) (Cube n) ℝ) (hA : A.IsHermitian) :
    traceNorm (dephase n η hη A) ≤ traceNorm A := by
  have hp (s : Cube n) : 0 ≤ mixtureWeight n η hη s := (mixingChannel n η hη).nonneg _ _
  have hs : ∑ s, mixtureWeight n η hη s = 1 := (mixingChannel n η hη).row_sum _
  calc
    _ ≤ ∑ s, traceNorm (mixtureWeight n η hη s • phaseConjugate s A) :=
      traceNorm_sum_le Finset.univ _ (fun s _ =>
        (phaseConjugate_isHermitian s hA).smul (IsSelfAdjoint.of_nonneg (hp s)))
    _ = ∑ s, mixtureWeight n η hη s * traceNorm A := by
      apply Finset.sum_congr rfl
      intro s _
      rw [traceNorm_smul, abs_of_nonneg (hp s), phaseConjugate_eq, traceNorm_conjugate]
    _ = traceNorm A := by rw [← Finset.sum_mul, hs, one_mul]

theorem bool_mixture_phase (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1) (x y : Bool) :
    (∑ s : Bool, (bsc η hη).weight false s * boolSign (s && x) * boolSign (s && y)) =
      if x = y then 1 else η := by
  cases x <;> cases y <;> simp [bsc, boolSign] <;> ring

theorem mixture_phase (n : ℕ) (η : Fin n → ℝ) (hη : ∀ i, η i ∈ Set.Icc (0 : ℝ) 1)
    (x y : Cube n) :
    (∑ s, mixtureWeight n η hη s * phase s x * phase s y) =
      ∏ i, if x i = y i then 1 else η i := by
  calc
    _ = ∑ s : Cube n, ∏ i, (bsc (η i) (hη i)).weight false (s i) *
        boolSign (s i && x i) * boolSign (s i && y i) := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [mixtureWeight, mixingChannel, UniformChannel.product, phase,
        Finset.prod_mul_distrib]
    _ = ∏ i, ∑ s : Bool, (bsc (η i) (hη i)).weight false s *
        boolSign (s && x i) * boolSign (s && y i) :=
      (Fintype.prod_sum (fun (i : Fin n) (s : Bool) =>
        (bsc (η i) (hη i)).weight false s * boolSign (s && x i) * boolSign (s && y i))).symm
    _ = _ := by simp only [bool_mixture_phase]

theorem dephase_entry (n : ℕ) (η : Fin n → ℝ) (hη : ∀ i, η i ∈ Set.Icc (0 : ℝ) 1)
    (A : Matrix (Cube n) (Cube n) ℝ) (x y : Cube n) :
    dephase n η hη A x y = (∏ i, if x i = y i then 1 else η i) * A x y := by
  simp only [dephase, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, phaseConjugate_entry]
  rw [← mixture_phase n η hη x y, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem dephase_state (n : ℕ) (η : Fin n → ℝ) (hη : ∀ i, η i ∈ Set.Icc (0 : ℝ) 1)
    (z : Fin n → ℝ) : dephase n η hη (state n z) = state n (fun i => η i * z i) := by
  ext x y
  rw [dephase_entry]
  simp only [state, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hxy : x i = y i <;> simp [oneQubit, hxy]
  ring

theorem dephase_reflection (n : ℕ) (η : Fin n → ℝ) (hη : ∀ i, η i ∈ Set.Icc (0 : ℝ) 1)
    (f : Cube n → ℝ) (A : Matrix (Cube n) (Cube n) ℝ) :
    dephase n η hη (reflection f * A * reflection f) =
      reflection f * dephase n η hη A * reflection f := by
  ext x y
  simp only [dephase_entry, reflection, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

theorem dephase_sub (n : ℕ) (η : Fin n → ℝ) (hη : ∀ i, η i ∈ Set.Icc (0 : ℝ) 1)
    (A B : Matrix (Cube n) (Cube n) ℝ) :
    dephase n η hη (A - B) = dephase n η hη A - dephase n η hη B := by
  ext x y
  simp only [dephase_entry, Matrix.sub_apply, mul_sub]

theorem reflection_isHermitian {n : ℕ} (f : Cube n → ℝ)
    {A : Matrix (Cube n) (Cube n) ℝ} (hA : A.IsHermitian) :
    (reflection f * A * reflection f).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, star_trivial, reflection, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have ha := congrFun (congrFun hA.eq x) y
  change A y x = A x y at ha
  rw [ha]
  ring

theorem antipodal_trace_lower_bound (n : ℕ) (z : Fin (n + 1) → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hcz : ∀ i, c ≤ z i) (f : Cube (n + 1) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x) :
    c ≤ traceNorm (state (n + 1) z - reflection f * state (n + 1) z * reflection f) / 2 := by
  by_cases hc0 : c = 0
  · rw [hc0]
    exact div_nonneg (traceNorm_nonneg _) (by norm_num)
  have hcpos : 0 < c := lt_of_le_of_ne hc.1 (Ne.symm hc0)
  have hzpos (i : Fin (n + 1)) : 0 < z i := hcpos.trans_le (hcz i)
  let η : Fin (n + 1) → ℝ := fun i => c / z i
  have hη (i : Fin (n + 1)) : η i ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hc.1 (hz i).1, (div_le_one (hzpos i)).mpr (hcz i)⟩
  have hηz : (fun i => η i * z i) = (fun _ => c) := by
    funext i
    exact div_mul_cancel₀ c (ne_of_gt (hzpos i))
  have hmap : dephase (n + 1) η hη (state (n + 1) z) = ProductState.state (n + 1) c := by
    rw [dephase_state, hηz, state_const]
  have hcontract := dephase_traceNorm_le (n + 1) η hη
    (state (n + 1) z - reflection f * state (n + 1) z * reflection f)
    ((state_isHermitian _ _).sub (reflection_isHermitian f (state_isHermitian _ _)))
  rw [dephase_sub, dephase_reflection, hmap] at hcontract
  have hbase := ParityBlocks.antipodal_trace_lower_bound n c hc f hf hanti
  change c ≤ traceNorm (ProductState.state (n + 1) c -
    reflection f * ProductState.state (n + 1) c * reflection f) / 2 at hbase
  linarith

#print axioms dephase_traceNorm_le
#print axioms antipodal_trace_lower_bound

end Hellinger.HeterogeneousState
