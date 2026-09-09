import Hellinger.Fourier
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Ring.Parity

/-!
# Exact frequency multiplicities and parity block dimensions

The frequency support is an explicit equivalence with finite subsets.
All counts apply to arbitrary dimension.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.Fourier

def supportEquiv (n : ℕ) : Cube n ≃ Finset (Fin n) where
  toFun := support
  invFun S i := decide (i ∈ S)
  left_inv s := by
    funext i
    cases hi : s i <;> simp [support, hi]
  right_inv S := by
    ext i
    simp [support]

theorem degree_le {n : ℕ} (s : Cube n) : degree s ≤ n := by
  have h := Finset.card_le_card (Finset.filter_subset (fun i => s i = true) Finset.univ)
  simpa only [degree, support, Finset.card_univ, Fintype.card_fin] using h

theorem card_degree (n k : ℕ) :
    (Finset.univ.filter (fun s : Cube n => degree s = k)).card = n.choose k := by
  let e : {s : Cube n // degree s = k} ≃ {S : Finset (Fin n) // S.card = k} :=
    (supportEquiv n).subtypeEquiv (fun s => Iff.rfl)
  have he := Fintype.card_congr e
  simpa [Fintype.subtype_card] using he

theorem parity_card_eq (n : ℕ) :
    (Finset.univ.filter (fun s : Cube (n + 1) => Even (degree s))).card =
      (Finset.univ.filter (fun s : Cube (n + 1) => Odd (degree s))).card := by
  have hsum := sum_pow_degree (n + 1) (-1 : ℝ)
  simp only [neg_one_pow_eq_ite, add_neg_cancel, zero_pow (Nat.succ_ne_zero n)] at hsum
  rw [Finset.sum_ite] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg, Nat.not_even_iff_odd] at hsum
  have he :
      ((Finset.univ.filter (fun s : Cube (n + 1) => Even (degree s))).card : ℝ) =
      ((Finset.univ.filter (fun s : Cube (n + 1) => Odd (degree s))).card : ℝ) := by
    linarith
  exact_mod_cast he

theorem card_even_degree (n : ℕ) :
    (Finset.univ.filter (fun s : Cube (n + 1) => Even (degree s))).card = 2 ^ n := by
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Cube (n + 1)))) (fun s => Even (degree s))
  simp only [Nat.not_even_iff_odd, Finset.card_univ, cube_card] at hsum
  have he := parity_card_eq n
  have hp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by simp [pow_succ, Nat.mul_comm, two_mul]
  omega

theorem card_odd_degree (n : ℕ) :
    (Finset.univ.filter (fun s : Cube (n + 1) => Odd (degree s))).card = 2 ^ n := by
  rw [← parity_card_eq, card_even_degree]

#print axioms card_degree
#print axioms card_even_degree
#print axioms card_odd_degree

end Hellinger.Fourier
