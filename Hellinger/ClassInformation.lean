import Hellinger.AllBent
import Hellinger.AllQuadratic
import Hellinger.EntropyTransfer

/-! The complete information bounds for flat Boolean spectra and quadratic
phases, with strictness and equality. Probability-model identification is
kept separate from this finite entropy calculation. -/

set_option autoImplicit false
noncomputable section

namespace Hellinger.ClassInformation

theorem quadratic_isBoolean {n : ℕ} {f : PaperSpecs.Cube n → ℝ}
    (hf : PaperSpecs.IsQuadratic f) : PaperSpecs.IsBoolean f := by
  obtain ⟨a, b, q, h⟩ := hf
  intro x
  rw [h x]
  split_ifs <;> simp

theorem bent_information : PaperSpecs.BentInformation := by
  intro n hn f hf hb ρ hρ
  obtain ⟨hH, hs⟩ := AllBent.paper_bent_hellinger n hn f hf hb ρ hρ
  exact ⟨EntropyTransfer.hellinger_implies_ck f hf ρ hρ hH,
    fun hp => EntropyTransfer.strict_hellinger_implies_strict_ck f hf ρ hρ (hs hp)⟩

theorem quadratic_information : PaperSpecs.QuadraticInformation := by
  intro n hn f hq ρ hρ
  have hf := quadratic_isBoolean hq
  obtain ⟨hH, heq⟩ := AllQuadratic.paper_quadratic_hellinger n hn f hq ρ hρ
  refine ⟨EntropyTransfer.hellinger_implies_ck f hf ρ hρ hH, ?_⟩
  intro hp hl
  constructor
  · intro hI
    exact (heq hp hl).mp
      (EntropyTransfer.ck_equality_implies_hellinger_equality f hf ρ hρ hH hI)
  · rintro ⟨i, _, negative, hform⟩
    rw [hform]
    exact EntropyTransfer.signed_dictator_information n i negative ρ hρ

end Hellinger.ClassInformation
