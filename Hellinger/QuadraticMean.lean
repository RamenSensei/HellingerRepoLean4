import Hellinger.RankCharacterSum
import Hellinger.FlatnessConsequences

/-! Exact bias formulas and even polar rank for arbitrary quadratic Boolean phases. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace Hellinger.QuadraticMean
open F2Model QuadraticRadical QuadraticDual RankCharacterSum ChannelSections

theorem polar_kernel_iff {n : ℕ} (Q : Form n) (v : Cube n) :
    Q.polarBilin v = 0 ↔ polarMatrix Q *ᵥ v = 0 := by
  constructor
  · intro hv
    funext i
    rw [polarMatrix_mulVec]
    change QuadraticMap.polar Q (Pi.single i 1) v = 0
    rw [QuadraticMap.polar_comm]
    exact congrArg (fun l : Cube n →ₗ[F2] F2 => l (Pi.single i 1)) hv
  · intro hv
    apply LinearMap.ext
    intro x
    change QuadraticMap.polar Q v x = 0
    rw [QuadraticMap.polar_comm]
    change Q.polarBilin x v = 0
    rw [← polarMatrix_bilin, hv, dotProduct_zero]

theorem mean_character {n : ℕ} (v : Cube n) :
    mean (fun x => sign (x ⬝ᵥ v)) = if v = 0 then 1 else 0 := by
  rw [mean, sum_character]
  simp only [Cube, Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  split_ifs <;> simp

theorem phase_autocorrelation {n : ℕ} (a : F2) (Q : Form n) (v : Cube n) :
    mean (fun x => phase a Q x * phase a Q (x + v)) =
      if polarMatrix Q *ᵥ v = 0 then sign (Q v) else 0 := by
  simp_rw [phase_derivative, ← polarMatrix_bilin]
  rw [Fourier.mean_const_mul, mean_character]
  split_ifs <;> simp

theorem mean_square_autocorrelation {n : ℕ} (f : Cube n → ℝ) :
    mean f ^ 2 = mean (fun v => mean (fun x => f x * f (x + v))) := by
  have hm := mean_prod_swap (fun p : Cube n × Cube n => f p.1 * f (p.1 + p.2))
  rw [mean_prod] at hm
  have hi (x : Cube n) : mean (fun v => f x * f (x + v)) = f x * mean f := by
    rw [Fourier.mean_const_mul]
    exact congrArg (f x * ·) (mean_comp_equiv (Equiv.addLeft x) f)
  simp_rw [hi] at hm
  rw [Fourier.mean_mul_const] at hm
  simpa only [pow_two] using hm

/-- Exact kernel character-sum formula for the bias, with the constant phase
term cancelling as in the manuscript's `q(v)+q(0)`. -/
theorem mean_square_kernel_sum {n : ℕ} (a : F2) (Q : Form n) :
    mean (phase a Q) ^ 2 = ((2 : ℝ) ^ n)⁻¹ *
      ∑ v ∈ Finset.univ.filter (fun v : Cube n => polarMatrix Q *ᵥ v = 0), sign (Q v) := by
  rw [mean_square_autocorrelation]
  simp_rw [phase_autocorrelation]
  simp only [mean, Cube, Fintype.card_fun, ZMod.card, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, Finset.sum_filter]

theorem mean_zero_of_kernel_nonzero {n : ℕ} (a : F2) (Q : Form n)
    (h : ∃ v : Cube n, polarMatrix Q *ᵥ v = 0 ∧ Q v ≠ 0) : mean (phase a Q) = 0 := by
  obtain ⟨v, hv, hq⟩ := h
  have hq1 := eq_one_of_ne_zero (Q v) hq
  have ha (x : Cube n) : phase a Q (x + v) = -phase a Q x := by
    rw [phase_translation, ← polarMatrix_bilin, hv, dotProduct_zero, hq1]
    simp
  exact mean_eq_zero_of_sign_reversing (Equiv.addRight v) (phase a Q) ha

theorem mean_square_of_kernel_zero {n : ℕ} (a : F2) (Q : Form n)
    (h : ∀ v : Cube n, polarMatrix Q *ᵥ v = 0 → Q v = 0) :
    mean (phase a Q) ^ 2 = ((2 : ℝ) ^ (polarMatrix Q).rank)⁻¹ := by
  classical
  rw [mean_square_kernel_sum]
  have hs : (∑ v ∈ Finset.univ.filter (fun v : Cube n => polarMatrix Q *ᵥ v = 0), sign (Q v)) =
      (2 : ℝ) ^ (n - (polarMatrix Q).rank) := by
    rw [Finset.sum_congr rfl (fun v hv => show sign (Q v) = 1 by
      rw [h v (Finset.mem_filter.mp hv).2, sign_zero])]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    let : Fintype (polarMatrix Q).mulVecLin.ker := Fintype.ofFinite _
    have hc := kernel_card (polarMatrix Q)
    have hcard : Fintype.card (polarMatrix Q).mulVecLin.ker =
        (Finset.univ.filter (fun v : Cube n => polarMatrix Q *ᵥ v = 0)).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext x
      simp [LinearMap.mem_ker]
    rw [hcard] at hc
    norm_num only [Fintype.card_fin] at hc
    exact_mod_cast hc
  rw [hs]
  have hr : (polarMatrix Q).rank ≤ n := by simpa using (polarMatrix Q).rank_le_card_width
  have he : n = (n - (polarMatrix Q).rank) + (polarMatrix Q).rank := by omega
  have hepow := congrArg (fun k : ℕ => (2 : ℝ) ^ k) he
  rw [pow_add] at hepow
  rw [hepow, mul_inv]
  field_simp

/-- The two exhaustive bias branches, with the actual polar matrix rank. -/
theorem mean_square_branches {n : ℕ} (a : F2) (Q : Form n) :
    mean (phase a Q) ^ 2 =
      if ∃ v : Cube n, polarMatrix Q *ᵥ v = 0 ∧ Q v ≠ 0 then 0
      else ((2 : ℝ) ^ (polarMatrix Q).rank)⁻¹ := by
  split_ifs with h
  · rw [mean_zero_of_kernel_nonzero a Q h]
    norm_num
  · apply mean_square_of_kernel_zero
    intro v hv
    by_contra hq
    exact h ⟨v, hv, hq⟩

def linearForm {n : ℕ} (s : Cube n) : Form n := polynomial s (fun _ _ => 0)

@[simp] theorem linearForm_apply {n : ℕ} (s x : Cube n) : linearForm s x = s ⬝ᵥ x := by
  simp [linearForm, polynomial_apply, dotProduct]

theorem polarMatrix_add_linear {n : ℕ} (Q : Form n) (s : Cube n) :
    polarMatrix (Q + linearForm s) = polarMatrix Q := by
  ext i j
  simp only [polarMatrix, LinearMap.BilinForm.toMatrix'_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, _root_.add_apply,
    linearForm_apply, dotProduct_add]
  abel

theorem mean_add_linear {n : ℕ} (a : F2) (Q : Form n) (s : Cube n) :
    mean (phase a (Q + linearForm s)) = walsh (phase a Q) s := by
  unfold walsh
  congr 1
  funext x
  simp only [phase, _root_.add_apply, linearForm_apply, sign_add]
  ring

theorem exists_nonzero_walsh {n : ℕ} (a : F2) (Q : Form n) :
    ∃ s : Cube n, walsh (phase a Q) s ≠ 0 := by
  by_contra! h
  have hi := Fourier.inversion (phase a Q ∘ bitsEquiv (Fin n)) (fun _ => false)
  simp only [← walsh_bits, h, zero_mul, Finset.sum_const_zero, Function.comp_apply] at hi
  rcases phase_boolean a Q (bitsEquiv (Fin n) (fun _ => false)) with hp | hp <;>
    rw [hp] at hi <;> norm_num at hi

/-- Every polar matrix of a quadratic form over F₂ has even rank. The proof
uses a nonzero Walsh coefficient, the exact bias formula, and integer-square parity. -/
theorem polar_rank_even {n : ℕ} (Q : Form n) : Even (polarMatrix Q).rank := by
  obtain ⟨s, hs⟩ := exists_nonzero_walsh (0 : F2) Q
  let Q' := Q + linearForm s
  have hmean : mean (phase 0 Q') ≠ 0 := by
    rw [mean_add_linear]
    exact hs
  have hk : ∀ v : Cube n, polarMatrix Q' *ᵥ v = 0 → Q' v = 0 := by
    intro v hv
    by_contra hq
    exact hmean (mean_zero_of_kernel_nonzero 0 Q' ⟨v, hv, hq⟩)
  have hm := mean_square_of_kernel_zero 0 Q' hk
  rw [show polarMatrix Q' = polarMatrix Q from polarMatrix_add_linear Q s] at hm
  let z : Cube n → ℤ := fun x => if phase 0 Q' x = 1 then 1 else -1
  have hz (x : Cube n) : (z x : ℝ) = phase 0 Q' x := by
    rcases phase_boolean 0 Q' x with h | h <;> norm_num [z, h]
  have hsum : ((∑ x, z x : ℤ) : ℝ) = ∑ x, phase 0 Q' x := by
    rw [Int.cast_sum]
    simp only [hz]
  unfold mean at hm
  simp only [Cube, Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hm
  rw [← hsum] at hm
  have hr : (polarMatrix Q).rank ≤ n := by simpa using (polarMatrix Q).rank_le_card_width
  have hexp : 2 * n - (polarMatrix Q).rank + (polarMatrix Q).rank = n * 2 := by omega
  have hreal : ((∑ x, z x : ℤ) : ℝ) ^ 2 = (2 : ℝ) ^ (2 * n - (polarMatrix Q).rank) := by
    have hp : ((∑ x, z x : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ (polarMatrix Q).rank = (2 : ℝ) ^ (n * 2) := by
      field_simp at hm
      simpa only [← pow_mul] using hm
    apply mul_right_cancel₀ (show (2 : ℝ) ^ (polarMatrix Q).rank ≠ 0 by positivity)
    rw [hp, ← pow_add, hexp]
  have hint : (∑ x, z x : ℤ) ^ 2 = (2 : ℤ) ^ (2 * n - (polarMatrix Q).rank) := by
    exact_mod_cast hreal
  have hnat : (∑ x, z x : ℤ).natAbs ^ 2 = 2 ^ (2 * n - (polarMatrix Q).rank) := by
    simpa using congrArg Int.natAbs hint
  have hfactor := congrArg (fun k : ℕ => k.factorization 2) hnat
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.Prime.factorization_self Nat.prime_two] at hfactor
  exact ⟨n - (∑ x, z x : ℤ).natAbs.factorization 2, by omega⟩

#print axioms mean_square_kernel_sum
#print axioms mean_square_branches
#print axioms polar_rank_even
end Hellinger.QuadraticMean
