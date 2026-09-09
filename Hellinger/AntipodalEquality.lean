import Hellinger.PosteriorGram
import Hellinger.ParityBlocks

/-! The actual antipodal Hellinger equality classification, with the trace,
posterior Gram, and Boolean Fourier implications all connected. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.AntipodalEquality

open Hellinger.Fourier Hellinger.PosteriorState Hellinger.PosteriorGram

theorem root_mean_equality_iff_signed_dictator (n : ℕ) (f : Cube (n + 1) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) (hρlt : ρ < 1) :
    mean (fun y => root ((cubeBSC (n + 1) ρ hρ).apply f y)) = root ρ ↔
      ∃ i : Fin (n + 1), ∃ negative : Bool,
        f = fun x => if negative then -boolSign (x i) else boolSign (x i) := by
  have hm := antipodal_mean_zero (n + 1) f hanti
  have hr0 : root (0 : ℝ) = 1 := by norm_num [root]
  constructor
  · intro heq
    have hc : root ρ ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg ρ])⟩
    have hlower := ParityBlocks.antipodal_trace_lower_bound n (root ρ) hc f hf hanti
    have hupper := bsc_lifting (n + 1) f hf ρ hρ
    have hlift : TraceNorm.traceNorm
        (ProductState.state (n + 1) (root ρ) -
          reflection f * ProductState.state (n + 1) (root ρ) * reflection f) / 2 =
        mean (fun y => root ((cubeBSC (n + 1) ρ hρ).apply f y)) := by
      change root ρ ≤ TraceNorm.traceNorm
        (ProductState.state (n + 1) (root ρ) -
          reflection f * ProductState.state (n + 1) (root ρ) * reflection f) / 2 at hlower
      linarith
    have hobj : objective ((cubeBSC (n + 1) ρ hρ).apply f) = 1 - root ρ := by
      unfold objective
      rw [UniformChannel.mean_apply, hm, heq, hr0]
    obtain ⟨i, a, ha, hform⟩ :=
      signed_dictator_of_lifting_and_objective_equality f hf hm ρ hρ hρpos hρlt hlift hobj
    rcases ha with ha | ha
    · refine ⟨i, false, ?_⟩
      funext x
      simp only [hform, ha, one_mul, Bool.false_eq_true, if_false]
    · refine ⟨i, true, ?_⟩
      funext x
      simp only [hform, ha, neg_one_mul, if_true]
  · rintro ⟨i, negative, hform⟩
    have hobj : objective ((cubeBSC (n + 1) ρ hρ).apply f) = 1 - root ρ := by
      rw [hform]
      exact bsc_signed_dictator_equality (n + 1) i negative ρ hρ
    unfold objective at hobj
    rw [UniformChannel.mean_apply, hm, hr0] at hobj
    linarith

theorem objective_equality_iff_signed_dictator (n : ℕ) (f : Cube (n + 1) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) (hρlt : ρ < 1) :
    objective ((cubeBSC (n + 1) ρ hρ).apply f) = 1 - root ρ ↔
      ∃ i : Fin (n + 1), ∃ negative : Bool,
        f = fun x => if negative then -boolSign (x i) else boolSign (x i) := by
  rw [← root_mean_equality_iff_signed_dictator n f hf hanti ρ hρ hρpos hρlt]
  unfold objective
  rw [UniformChannel.mean_apply, antipodal_mean_zero (n + 1) f hanti]
  have hr0 : root (0 : ℝ) = 1 := by norm_num [root]
  rw [hr0]
  constructor <;> intro h <;> linarith

#print axioms root_mean_equality_iff_signed_dictator
#print axioms objective_equality_iff_signed_dictator

end Hellinger.AntipodalEquality
