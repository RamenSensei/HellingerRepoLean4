import Hellinger.Flatness
import Mathlib.Data.Nat.Factorization.Basic

/-! Arithmetic and translation consequences of actual Boolean Walsh flatness. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.Flatness

open Hellinger.Fourier

theorem dimension_even {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : IsBent f) : Even n := by
  let z : Cube n → ℤ := fun x => if f x = 1 then 1 else -1
  have hz (x : Cube n) : (z x : ℝ) = f x := by
    rcases hf x with h | h <;> norm_num [z, h]
  have hsum : ((∑ x, z x : ℤ) : ℝ) = ∑ x, f x := by
    rw [Int.cast_sum]
    simp only [hz]
  have hm := mean_sq hb
  unfold mean at hm
  rw [cube_card] at hm
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hm
  rw [← hsum] at hm
  have hreal : ((∑ x, z x : ℤ) : ℝ) ^ 2 = (2 : ℝ) ^ n := by
    field_simp at hm
    exact hm
  have hint : (∑ x, z x : ℤ) ^ 2 = (2 : ℤ) ^ n := by exact_mod_cast hreal
  have hnat : (∑ x, z x : ℤ).natAbs ^ 2 = 2 ^ n := by
    simpa using congrArg Int.natAbs hint
  have hfactor := congrArg (fun k : ℕ => k.factorization 2) hnat
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.Prime.factorization_self Nat.prime_two] at hfactor
  exact ⟨(∑ x, z x : ℤ).natAbs.factorization 2, by omega⟩

theorem no_sign_reversing_translation {n : ℕ} {f : Cube n → ℝ}
    (hb : IsBent f) (v : Cube n) :
    ¬ (∀ x, f (translate v x) = -f x) := by
  intro h
  have hm : mean f = 0 := mean_eq_zero_of_sign_reversing (translationEquiv v) f h
  have hs := mean_sq hb
  rw [hm, zero_pow (by decide : 2 ≠ 0)] at hs
  have hp : 0 < ((2 : ℝ) ^ n)⁻¹ := by positivity
  linarith

#print axioms dimension_even
#print axioms no_sign_reversing_translation

end Hellinger.Flatness
