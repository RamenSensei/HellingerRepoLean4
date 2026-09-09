import Hellinger.BentEstimates
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Convex.Deriv

/-! Exact polynomial identities and the global concavity assertion printed
in the small-dimensional appendix. This also checks the manuscript's own
analytic route, independently of the Bernstein positivity certificate. -/

set_option autoImplicit false
noncomputable section
open Polynomial

namespace Hellinger.PaperPolynomialIdentities
open BentEstimates

theorem bentH_square_form (t : ℝ) :
    bentH t = (1 - t) ^ 4 + 16 * t * (1 - t) ^ 2 + 16 * t ^ 2 := by
  unfold bentH
  ring

theorem bentP_expansion (t : ℝ) :
    512 * bentP t = -t ^ 8 - 24 * t ^ 7 - 124 * t ^ 6 + 216 * t ^ 5 -
      406 * t ^ 4 + 152 * t ^ 3 - 156 * t ^ 2 + 168 * t - 1 := by
  unfold bentP bentH
  ring

def paperPolynomial : Polynomial ℝ := C (1 / 512) *
  (-X ^ 8 - 24 * X ^ 7 - 124 * X ^ 6 + 216 * X ^ 5 -
    406 * X ^ 4 + 152 * X ^ 3 - 156 * X ^ 2 + 168 * X - 1)

theorem paperPolynomial_eval (t : ℝ) : paperPolynomial.eval t = bentP t := by
  simp only [paperPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_add, Polynomial.eval_one]
  rw [← bentP_expansion]
  ring

theorem bentP_second_derivative (t : ℝ) :
    -64 * deriv (deriv bentP) t = 7 * t ^ 6 + 126 * t ^ 5 +
      15 * t ^ 2 * (31 * t ^ 2 - 36 * t + 12) + 3 * (143 * t ^ 2 - 38 * t + 13) := by
  have hp : bentP = fun t => paperPolynomial.eval t := (funext paperPolynomial_eval).symm
  have hd : deriv bentP = fun t => paperPolynomial.derivative.eval t := by
    rw [hp]
    funext x
    exact paperPolynomial.deriv
  rw [hd, Polynomial.deriv]
  norm_num [paperPolynomial, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring

theorem bentP_second_derivative_neg (t : ℝ) (ht : 0 ≤ t) : deriv (deriv bentP) t < 0 := by
  have h₁ : 0 < 31 * t ^ 2 - 36 * t + 12 := by
    nlinarith [sq_nonneg (31 * t - 18)]
  have h₂ : 0 < 143 * t ^ 2 - 38 * t + 13 := by
    nlinarith [sq_nonneg (143 * t - 19)]
  have h₃ : 0 ≤ 7 * t ^ 6 + 126 * t ^ 5 +
      15 * t ^ 2 * (31 * t ^ 2 - 36 * t + 12) := by positivity
  have h := bentP_second_derivative t
  nlinarith

theorem bentP_strictConcave : StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) bentP := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ici 0)
  · unfold bentP bentH
    fun_prop
  · intro t ht
    change deriv (deriv bentP) t < 0
    exact bentP_second_derivative_neg t (Set.mem_Ici.mp (interior_subset ht))

theorem bentP_endpoints :
    bentP (1 / 16) = (38318572159 : ℝ) / 2199023255552 ∧
    bentP (7 / 10) = (1449589279 : ℝ) / 51200000000 := by
  norm_num [bentP, bentH]

theorem quadratic_discriminants :
    (-36 : ℝ) ^ 2 - 4 * 31 * 12 = -192 ∧
    (-38 : ℝ) ^ 2 - 4 * 143 * 13 = -5992 := by norm_num

end Hellinger.PaperPolynomialIdentities
