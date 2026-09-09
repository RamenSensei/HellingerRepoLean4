import Hellinger.QuadraticDual
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact coordinate and subset expansions of the quadratic fourth moment. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace Hellinger.RankMomentExpansion
open F2Model QuadraticRadical QuadraticDual

theorem sum_f2 (f : F2 → ℝ) : (∑ x, f x) = f 0 + f 1 := by
  rw [← bitEquiv.sum_comp]
  simp [add_comm]

def weightBit (ρ : ℝ) (b : F2) : ℝ := if b = 0 then 1 else ρ

theorem char_add {n : ℕ} (B : Matrix (Fin n) (Fin n) F2) (x y s : Cube n) :
    sign ((x + y) ⬝ᵥ B *ᵥ s) = sign (x ⬝ᵥ B *ᵥ s) * sign (y ⬝ᵥ B *ᵥ s) := by
  rw [add_dotProduct, sign_add]

theorem coordinate_four_weights (ρ : ℝ) (s d : F2) :
    (∑ x : F2, weightBit ρ x * weightBit ρ (x + s) *
      weightBit ρ (x + d) * weightBit ρ (x + d + s)) =
    2 * ρ ^ 2 + (1 - ρ ^ 2) ^ 2 * (if s = 0 ∧ d = 0 then 1 else 0) := by
  obtain ⟨a, rfl⟩ := bitEquiv.surjective s
  obtain ⟨b, rfl⟩ := bitEquiv.surjective d
  rw [sum_f2]
  cases a <;> cases b <;> norm_num [weightBit, show (1 : F2) + 1 = 0 from rfl] <;> ring

theorem four_weights_sum {n : ℕ} (ρ : ℝ) (s d : Cube n) :
    (∑ x : Cube n, noiseWeight ρ x * noiseWeight ρ (x + s) *
      noiseWeight ρ (x + d) * noiseWeight ρ (x + d + s)) =
    ∏ i, (2 * ρ ^ 2 + (1 - ρ ^ 2) ^ 2 * (if s i = 0 ∧ d i = 0 then 1 else 0)) := by
  simp only [noiseWeight, Pi.add_apply, ← Finset.prod_mul_distrib]
  change (∑ x : Cube n, ∏ i, weightBit ρ (x i) * weightBit ρ (x i + s i) *
    weightBit ρ (x i + d i) * weightBit ρ (x i + d i + s i)) = _
  rw [← Fintype.prod_sum (fun (i : Fin n) (x : F2) =>
    weightBit ρ x * weightBit ρ (x + s i) *
      weightBit ρ (x + d i) * weightBit ρ (x + d i + s i))]
  simp only [coordinate_four_weights]

/-- The square of a weighted character sum, with the noise parameter retained exactly. -/
theorem weighted_character_square {n : ℕ} (B : Matrix (Fin n) (Fin n) F2)
    (ρ : ℝ) (s : Cube n) :
    (∑ x : Cube n, noiseWeight ρ x * noiseWeight ρ (x + s) *
      sign (x ⬝ᵥ B *ᵥ s)) ^ 2 =
    ∑ d : Cube n, sign (d ⬝ᵥ B *ᵥ s) *
      ∏ i, (2 * ρ ^ 2 + (1 - ρ ^ 2) ^ 2 * (if s i = 0 ∧ d i = 0 then 1 else 0)) := by
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]
  have hterm (x : Cube n) :
      (∑ y : Cube n, (noiseWeight ρ x * noiseWeight ρ (x + s) * sign (x ⬝ᵥ B *ᵥ s)) *
        (noiseWeight ρ y * noiseWeight ρ (y + s) * sign (y ⬝ᵥ B *ᵥ s))) =
      ∑ d : Cube n, sign (d ⬝ᵥ B *ᵥ s) *
        (noiseWeight ρ x * noiseWeight ρ (x + s) *
          noiseWeight ρ (x + d) * noiseWeight ρ (x + d + s)) := by
    rw [← Equiv.sum_comp (Equiv.addLeft x) (fun y : Cube n =>
      (noiseWeight ρ x * noiseWeight ρ (x + s) * sign (x ⬝ᵥ B *ᵥ s)) *
        (noiseWeight ρ y * noiseWeight ρ (y + s) * sign (y ⬝ᵥ B *ᵥ s)))]
    apply Finset.sum_congr rfl
    intro d _
    simp only [Equiv.coe_addLeft, char_add]
    calc
      _ = sign (x ⬝ᵥ B *ᵥ s) ^ 2 * (sign (d ⬝ᵥ B *ᵥ s) *
        (noiseWeight ρ x * noiseWeight ρ (x + s) *
          noiseWeight ρ (x + d) * noiseWeight ρ (x + d + s))) := by ring
      _ = _ := by rw [sign_sq, one_mul]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.mul_sum, four_weights_sum]

/-- The actual posterior fourth moment before restricting to principal coordinate subspaces. -/
theorem phase_fourth_coordinate_expansion {n : ℕ} (a : F2) (Q : Form n)
    (hQ : IsUnit (polarMatrix Q).det) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun x => ((cubeBSC n ρ hρ).apply (phase a Q ∘ bitsEquiv (Fin n)) x) ^ 4) =
      ((2 : ℝ) ^ n)⁻¹ ^ 2 * ∑ s : Cube n, ∑ d : Cube n,
        sign (d ⬝ᵥ (polarMatrix Q)⁻¹ *ᵥ s) *
          ∏ i, (2 * ρ ^ 2 + (1 - ρ ^ 2) ^ 2 * (if s i = 0 ∧ d i = 0 then 1 else 0)) := by
  rw [phase_fourth_moment a Q hQ]
  simp_rw [weighted_character_square]

#print axioms phase_fourth_coordinate_expansion
end Hellinger.RankMomentExpansion
