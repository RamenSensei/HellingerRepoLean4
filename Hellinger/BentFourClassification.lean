import Hellinger.BentFourStructure
import Hellinger.QuadraticRadical

/-! The actual small-dimensional classification, in the independent paper specification. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Hellinger.BentFourClassification
open Fourier BentFour F2Model QuadraticRadical

def signCode (r : ℝ) : F2 := if r = 1 then 0 else 1

theorem sign_signCode (r : ℝ) (hr : r ^ 2 = 1) : sign (signCode r) = r := by
  rcases sq_eq_one_iff.mp hr with h | h <;> rw [h] <;> norm_num [signCode]

def crossCoefficients (e : Fin 6 → ℝ) (i j : Fin 4) : F2 :=
  if i.val = 0 ∧ j.val = 1 then signCode (e 0) else
  if i.val = 0 ∧ j.val = 2 then signCode (e 1) else
  if i.val = 0 ∧ j.val = 3 then signCode (e 2) else
  if i.val = 1 ∧ j.val = 2 then signCode (e 3) else
  if i.val = 1 ∧ j.val = 3 then signCode (e 4) else
  if i.val = 2 ∧ j.val = 3 then signCode (e 5) else 0

set_option maxHeartbeats 2000000 in
theorem quadraticPhase_isQuadratic (c : ℝ) (l : Fin 4 → ℝ) (e : Fin 6 → ℝ)
    (hc : c ^ 2 = 1) (hl : ∀ i, l i ^ 2 = 1) (he : ∀ i, e i ^ 2 = 1) :
    PaperSpecs.IsQuadratic (quadraticPhase c l e) := by
  refine ⟨signCode c, (fun i => signCode (l i)), crossCoefficients e, ?_⟩
  intro x
  change quadraticPhase c l e x = sign (PaperSpecs.quadraticValue _ _ _ x)
  have hx : x = (fun i => if i.val = 0 then x 0 else if i.val = 1 then x 1
      else if i.val = 2 then x 2 else x 3) := by
    funext i
    fin_cases i <;> norm_num <;> rfl
  cases hx₀ : x 0 <;> cases hx₁ : x 1 <;> cases hx₂ : x 2 <;> cases hx₃ : x 3 <;>
    rw [hx₀, hx₁, hx₂, hx₃] at hx <;> rw [hx] <;>
    simp only [PaperSpecs.quadraticValue, Finset.sum_filter, Fin.sum_univ_succ, Fin.lt_def] <;>
    norm_num [quadraticPhase, crossCoefficients, PaperSpecs.bit, sign_add,
      sign_signCode c hc, fun i => sign_signCode (l i) (hl i),
      fun i => sign_signCode (e i) (he i)] <;>
    (try simp only [show (Fin.succ (2 : Fin 3)) = (3 : Fin 4) from rfl, eq_self, true_or]) <;> first | (left; first | trivial | ring) | ring

theorem bent_isQuadratic (f : Fourier.Cube 4 → ℝ) (hf : PaperSpecs.IsBoolean f)
    (hb : Flatness.IsBent f) : PaperSpecs.IsQuadratic f := by
  obtain ⟨hc, hl, he⟩ := BentFourStructure.coefficient_squares f hf
  rw [bent_quadratic_representation f hf hb]
  exact quadraticPhase_isQuadratic _ _ _ hc hl he

#print axioms quadraticPhase_isQuadratic
#print axioms bent_isQuadratic
end Hellinger.BentFourClassification
