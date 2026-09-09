import Hellinger.QuadraticRadical
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Actual polar matrices, inverse matrices, and Fourier duals of quadratic phases. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace Hellinger.QuadraticDual
open F2Model QuadraticRadical ChannelSections

def polarMatrix {n : ℕ} (Q : Form n) : Matrix (Fin n) (Fin n) F2 := LinearMap.BilinForm.toMatrix' Q.polarBilin

theorem polarMatrix_bilin {n : ℕ} (Q : Form n) (x y : Cube n) :
    x ⬝ᵥ polarMatrix Q *ᵥ y = Q.polarBilin x y := by
  rw [← Matrix.toBilin'_apply', polarMatrix, Matrix.toBilin'_toMatrix']

theorem polarMatrix_mulVec {n : ℕ} (Q : Form n) (y : Cube n) (i : Fin n) :
    (polarMatrix Q *ᵥ y) i = Q.polarBilin (Pi.single i 1) y := by
  rw [← polarMatrix_bilin, single_one_dotProduct]

theorem polarMatrix_symmetric {n : ℕ} (Q : Form n) : (polarMatrix Q).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, polarMatrix, LinearMap.BilinForm.toMatrix'_apply]
  exact QuadraticMap.polar_comm Q _ _

theorem polarMatrix_kernel {n : ℕ} (Q : Form n) (hQ : IsUnit (polarMatrix Q).det) :
    Q.polarBilin.ker = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  have hAv : polarMatrix Q *ᵥ v = 0 := by
    funext i
    rw [polarMatrix_mulVec]
    change QuadraticMap.polar Q (Pi.single i 1) v = 0
    rw [QuadraticMap.polar_comm]
    exact congrArg (fun l : Cube n →ₗ[F2] F2 => l (Pi.single i 1)) hv
  have h := congrArg (fun w => (polarMatrix Q)⁻¹ *ᵥ w) hAv
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hQ,
    Matrix.one_mulVec, Matrix.mulVec_zero] using h

/-- This is precisely the manuscript convention for the polar matrix, including
an arbitrary constant term in the quadratic polynomial. -/
theorem polarMatrix_characterization {n : ℕ} (a : F2) (Q : Form n) (x v : Cube n) :
    (a + Q (x + v)) + (a + Q x) + (a + Q v) + (a + Q 0) =
      x ⬝ᵥ polarMatrix Q *ᵥ v := by
  rw [polarMatrix_bilin]
  have h := QuadraticMap.map_add Q x v
  change Q (x + v) = Q x + Q v + Q.polarBilin x v at h
  rw [h, map_zero]
  ring_nf
  simp only [show (4 : F2) = 0 from rfl, show (2 : F2) = 0 from rfl, mul_zero, add_zero, zero_add]

def walsh {n : ℕ} (f : Cube n → ℝ) (s : Cube n) : ℝ :=
  mean (fun x => f x * sign (s ⬝ᵥ x))

theorem sign_sum {ι : Type*} (s : Finset ι) (z : ι → F2) :
    sign (∑ i ∈ s, z i) = ∏ i ∈ s, sign (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, sign_add, ih]

theorem sign_dot_bits {n : ℕ} (s x : Fourier.Cube n) :
    sign (bitsEquiv (Fin n) s ⬝ᵥ bitsEquiv (Fin n) x) = Fourier.phase s x := by
  have hs := sign_sum (Finset.univ : Finset (Fin n))
    (fun i => bitEquiv (s i) * bitEquiv (x i))
  change sign (∑ i, bitEquiv (s i) * bitEquiv (x i)) = _
  rw [hs]
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> cases x i <;> norm_num [boolSign]

theorem walsh_bits {n : ℕ} (f : Cube n → ℝ) (s : Fourier.Cube n) :
    walsh f (bitsEquiv (Fin n) s) = Fourier.walsh (f ∘ bitsEquiv (Fin n)) s := by
  unfold walsh
  rw [← mean_comp_equiv (bitsEquiv (Fin n))]
  simp only [Function.comp_def, sign_dot_bits, Fourier.walsh]

theorem phase_translation {n : ℕ} (a : F2) (Q : Form n) (x v : Cube n) :
    phase a Q (x + v) = phase a Q x * sign (Q v) * sign (Q.polarBilin x v) := by
  have h := QuadraticMap.map_add Q x v
  change Q (x + v) = Q x + Q v + Q.polarBilin x v at h
  simp only [phase, h, sign_add]
  ring

/-- Translating the genuine Fourier sum produces the inverse-polar quadratic dual. -/
theorem walsh_phase {n : ℕ} (a : F2) (Q : Form n)
    (hQ : IsUnit (polarMatrix Q).det) (s : Cube n) :
    walsh (phase a Q) s = walsh (phase a Q) 0 * sign (Q ((polarMatrix Q)⁻¹ *ᵥ s)) := by
  let v := (polarMatrix Q)⁻¹ *ᵥ s
  have hAv : polarMatrix Q *ᵥ v = s := by
    simp [v, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQ]
  have hpol (x : Cube n) : Q.polarBilin x v = s ⬝ᵥ x := by
    rw [← polarMatrix_bilin, hAv, dotProduct_comm]
  have hsign (x : Cube n) : phase a Q (x + v) * sign (Q v) =
      phase a Q x * sign (s ⬝ᵥ x) := by
    rw [phase_translation, hpol]
    calc
      _ = (phase a Q x * sign (s ⬝ᵥ x)) * sign (Q v) ^ 2 := by ring
      _ = _ := by rw [sign_sq, mul_one]
  have hm := mean_comp_equiv (Equiv.addRight v) (phase a Q)
  change mean (fun x => phase a Q (x + v)) = mean (phase a Q) at hm
  have hmean : mean (fun x => phase a Q (x + v) * sign (Q v)) =
      mean (phase a Q) * sign (Q v) := by rw [Fourier.mean_mul_const, hm]
  simp_rw [hsign] at hmean
  simpa [walsh, dotProduct, sign] using hmean

def dualForm {n : ℕ} (Q : Form n) : Form n := Q.comp ((polarMatrix Q)⁻¹).toLin'

theorem dualForm_polar {n : ℕ} (Q : Form n) (hQ : IsUnit (polarMatrix Q).det)
    (x y : Cube n) :
    (dualForm Q).polarBilin x y = x ⬝ᵥ (polarMatrix Q)⁻¹ *ᵥ y := by
  simp only [dualForm, QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply,
    Matrix.toLin'_apply]
  rw [← polarMatrix_bilin, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQ,
    Matrix.one_mulVec]
  rw [dotProduct_comm ((polarMatrix Q)⁻¹ *ᵥ x) y]
  have hs := Matrix.dotProduct_transpose_mulVec (polarMatrix Q)⁻¹ x y
  rw [(polarMatrix_symmetric Q).inv.eq] at hs
  exact hs.symm

theorem walsh_zero {n : ℕ} (f : Cube n → ℝ) : walsh f 0 = mean f := by
  simp [walsh, dotProduct]

theorem walsh_phase_zero_sq {n : ℕ} (a : F2) (Q : Form n)
    (hQ : IsUnit (polarMatrix Q).det) :
    walsh (phase a Q) 0 ^ 2 = ((2 : ℝ) ^ n)⁻¹ := by
  have h := Flatness.mean_sq (phase_bent a Q (polarMatrix_kernel Q hQ))
  rw [mean_comp_equiv] at h
  simpa [walsh_zero] using h

theorem walsh_phase_pair {n : ℕ} (a : F2) (Q : Form n)
    (hQ : IsUnit (polarMatrix Q).det) (x s : Cube n) :
    walsh (phase a Q) x * walsh (phase a Q) (x + s) =
      ((2 : ℝ) ^ n)⁻¹ * sign (dualForm Q s) *
        sign (x ⬝ᵥ (polarMatrix Q)⁻¹ *ᵥ s) := by
  have hd := phase_derivative (0 : F2) (dualForm Q) x s
  simp only [phase, zero_add, dualForm_polar Q hQ] at hd
  rw [walsh_phase a Q hQ x, walsh_phase a Q hQ (x + s)]
  change walsh (phase a Q) 0 * sign (dualForm Q x) *
    (walsh (phase a Q) 0 * sign (dualForm Q (x + s))) = _
  calc
    _ = walsh (phase a Q) 0 ^ 2 *
        (sign (dualForm Q x) * sign (dualForm Q (x + s))) := by ring
    _ = _ := by rw [walsh_phase_zero_sq a Q hQ, hd]; ring

def noiseWeight {n : ℕ} (ρ : ℝ) (x : Cube n) : ℝ :=
  ∏ i, if x i = 0 then 1 else ρ

theorem noiseWeight_bits {n : ℕ} (ρ : ℝ) (x : Fourier.Cube n) :
    noiseWeight ρ (bitsEquiv (Fin n) x) = ρ ^ Fourier.degree x := by
  rw [Fourier.pow_degree]
  apply Finset.prod_congr rfl
  intro i _
  have hb (b : Bool) : (if bitEquiv b = 0 then (1 : ℝ) else ρ) =
      (if b = true then ρ else 1) := by cases b <;> norm_num
  exact hb (x i)

theorem noise_fourth_moment {n : ℕ} (f : Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun x => ((cubeBSC n ρ hρ).apply (f ∘ bitsEquiv (Fin n)) x) ^ 4) =
      ∑ s : Cube n, (∑ x : Cube n, (noiseWeight ρ x * walsh f x) *
        (noiseWeight ρ (x + s) * walsh f (x + s))) ^ 2 := by
  rw [FourierProducts.noise_fourth_moment]
  rw [← (bitsEquiv (Fin n)).sum_comp (fun s : Cube n =>
    (∑ x : Cube n, (noiseWeight ρ x * walsh f x) *
      (noiseWeight ρ (x + s) * walsh f (x + s))) ^ 2)]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  rw [← (bitsEquiv (Fin n)).sum_comp (fun x : Cube n =>
    (noiseWeight ρ x * walsh f x) *
      (noiseWeight ρ (x + bitsEquiv (Fin n) s) * walsh f (x + bitsEquiv (Fin n) s)))]
  apply Finset.sum_congr rfl
  intro x _
  rw [← bitsEquiv_translate n x s]
  simp only [noiseWeight_bits, walsh_bits]
  have htrans : Fourier.translate s x = Fourier.translate x s := by
    funext i
    exact Bool.xor_comm _ _
  rw [htrans]

/-- Genuine fourth moment reduced to the inverse-polar character sum. -/
theorem phase_fourth_moment {n : ℕ} (a : F2) (Q : Form n)
    (hQ : IsUnit (polarMatrix Q).det) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun x => ((cubeBSC n ρ hρ).apply (phase a Q ∘ bitsEquiv (Fin n)) x) ^ 4) =
      ((2 : ℝ) ^ n)⁻¹ ^ 2 * ∑ s : Cube n,
        (∑ x : Cube n, noiseWeight ρ x * noiseWeight ρ (x + s) *
          sign (x ⬝ᵥ (polarMatrix Q)⁻¹ *ᵥ s)) ^ 2 := by
  rw [noise_fourth_moment]
  have hp (x s : Cube n) :
      (noiseWeight ρ x * walsh (phase a Q) x) *
        (noiseWeight ρ (x + s) * walsh (phase a Q) (x + s)) =
      (((2 : ℝ) ^ n)⁻¹ * sign (dualForm Q s)) *
        (noiseWeight ρ x * noiseWeight ρ (x + s) *
          sign (x ⬝ᵥ (polarMatrix Q)⁻¹ *ᵥ s)) := by
    calc
      _ = (noiseWeight ρ x * noiseWeight ρ (x + s)) *
        (walsh (phase a Q) x * walsh (phase a Q) (x + s)) := by ring
      _ = _ := by rw [walsh_phase_pair a Q hQ]; ring
  simp_rw [hp, ← Finset.mul_sum, mul_pow, sign_sq, mul_one]
  rw [Finset.mul_sum]

#print axioms walsh_phase
#print axioms phase_fourth_moment
end Hellinger.QuadraticDual
