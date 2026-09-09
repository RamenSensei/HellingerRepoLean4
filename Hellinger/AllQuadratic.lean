import Hellinger.QuadraticRadical
import Hellinger.LinearQuotient
import Hellinger.AllBent
import Hellinger.TranslationEquality

/-! Complete all-dimensional quadratic-phase theorem for the actual Boolean BSC. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Hellinger.AllQuadratic
open F2Model QuadraticRadical ChannelSections

def support {n : ℕ} (v : Cube n) : Finset (Fin n) := Finset.univ.filter (fun i => v i = 1)

theorem support_nonempty {n : ℕ} (v : Cube n) (hv : v ≠ 0) : (support v).Nonempty := by
  by_contra h
  apply hv
  funext i
  by_contra hi
  have hi1 := eq_one_of_ne_zero (v i) hi
  exact h ⟨i, by simp [support, hi1]⟩

theorem bits_flip_support {n : ℕ} (v : Cube n) (x : PaperSpecs.Cube n) :
    bitsEquiv (Fin n) (PaperSpecs.flip (support v) x) = bitsEquiv (Fin n) x + v := by
  funext i
  obtain ⟨b, hb⟩ := bitEquiv.surjective (v i)
  simp only [bitsEquiv_apply, PaperSpecs.flip, support, Finset.mem_filter,
    Finset.mem_univ, true_and, Pi.add_apply, ← hb]
  cases x i <;> cases b <;> norm_num [show (1 : F2) + 1 = 0 from rfl]

theorem translation_phase_bound {n : ℕ} (a : F2) (Q : Form n) (v : Cube n)
    (hv : v ≠ 0) (hanti : ∀ x, phase a Q (x + v) = -phase a Q x)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    PaperSpecs.HellingerBound (phase a Q ∘ bitsEquiv (Fin n)) ρ hρ ∧
    (0 < ρ → ρ < 1 →
      (objective ((cubeBSC n ρ hρ).apply (phase a Q ∘ bitsEquiv (Fin n))) = 1 - root ρ ↔
        PaperSpecs.SignedDictatorOn (phase a Q ∘ bitsEquiv (Fin n)) Finset.univ)) := by
  let f := phase a Q ∘ bitsEquiv (Fin n)
  have hf : PaperSpecs.IsBoolean f := fun x => phase_boolean a Q _
  have hs : PaperSpecs.SignReversing f (support v) := by
    intro x
    change phase a Q (bitsEquiv (Fin n) (PaperSpecs.flip (support v) x)) = _
    rw [bits_flip_support]
    exact hanti _
  have ht := translation_hellinger n f hf (support v) (support_nonempty v hv) hs ρ hρ
  refine ⟨ht.2.2, ?_⟩
  intro hp hl
  constructor
  · intro heq
    have hr : PaperSpecs.posteriorRootMean f ρ hρ = root ρ := by
      unfold objective at heq
      rw [UniformChannel.mean_apply, ht.1] at heq
      have hz : root (0 : ℝ) = 1 := by norm_num [root]
      rw [hz] at heq
      exact sub_right_injective heq
    obtain ⟨i, _, negative, hf⟩ :=
      (TranslationEquality.translation_equality n f hf (support v)
        (support_nonempty v hv) hs ρ hρ hp hl).mp hr
    exact ⟨i, Finset.mem_univ i, negative, hf⟩
  · rintro ⟨i, _, negative, hf⟩
    rw [hf]
    exact bsc_signed_dictator_equality n i negative ρ hρ

theorem constant_objective {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (K : UniformChannel Ω) (c : ℝ) : objective (K.apply (fun _ => c)) = 0 := by
  have heq : K.apply (fun _ => c) = fun _ => c := by
    funext x
    simp only [UniformChannel.apply, ← Finset.sum_mul, K.row_sum, one_mul]
  simp only [heq, objective, mean_const, sub_self]

theorem root_le_one (ρ : ℝ) : root ρ ≤ 1 := by
  unfold root
  exact Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [sq_nonneg ρ]⟩

theorem root_lt_one (ρ : ℝ) (hp : 0 < ρ) : root ρ < 1 := by
  unfold root
  exact (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith [sq_pos_of_pos hp])

/-- The quotient case is strict at every positive correlation, including when
the reduced quotient has dimension zero and the phase is constant. -/
theorem quotient_phase_bound {n k : ℕ} (a : F2) (Q : Form n) (Q₀ : Form k)
    (L : Cube n →ₗ[F2] Cube k) (hL : Function.Surjective L)
    (hQ₀ : Q₀.polarBilin.ker = ⊥) (hf : phase a Q = phase a Q₀ ∘ L)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    PaperSpecs.HellingerBound (phase a Q ∘ bitsEquiv (Fin n)) ρ hρ ∧
    (0 < ρ → objective ((cubeBSC n ρ hρ).apply
      (phase a Q ∘ bitsEquiv (Fin n))) < 1 - root ρ) := by
  have hg : ∀ x, phase a Q₀ x ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x
    rcases phase_boolean a Q₀ x with hx | hx <;> simp [hx]
  obtain ⟨M, _, hcmp⟩ := LinearQuotient.linear_quotient_objective_comparison n k L hL
    (phase a Q₀) hg
  have hc := hcmp ρ hρ
  rw [← hf, noise_objective_bits, noise_objective_bits] at hc
  change objective ((cubeBSC n ρ hρ).apply (phase a Q ∘ bitsEquiv (Fin n))) ≤
    objective ((cubeBSC k ρ hρ).apply ((phase a Q₀ ∘ M) ∘ bitsEquiv (Fin k))) at hc
  by_cases hk : k = 0
  · subst k
    have hfun : ((phase a Q₀ ∘ M) ∘ bitsEquiv (Fin 0)) = fun _ => phase a Q₀ 0 := by
      funext x
      exact congrArg (phase a Q₀) (Subsingleton.elim _ _)
    rw [hfun, constant_objective] at hc
    exact ⟨hc.trans (by linarith [root_le_one ρ]), fun hp =>
      hc.trans_lt (by linarith [root_lt_one ρ hp])⟩
  · have hb := bent_linearEquiv k (phase a Q₀) (phase_boolean a Q₀)
      (phase_bent a Q₀ hQ₀) M
    have ht := AllBent.bent_hellinger k (Nat.pos_of_ne_zero hk)
      ((phase a Q₀ ∘ M) ∘ bitsEquiv (Fin k)) (fun x => phase_boolean a Q₀ _) hb ρ hρ
    exact ⟨hc.trans ht.1, fun hp => hc.trans_lt (ht.2 hp)⟩

theorem phase_hellinger {n : ℕ} (a : F2) (Q : Form n)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    PaperSpecs.HellingerBound (phase a Q ∘ bitsEquiv (Fin n)) ρ hρ ∧
    (0 < ρ → ρ < 1 →
      (objective ((cubeBSC n ρ hρ).apply (phase a Q ∘ bitsEquiv (Fin n))) = 1 - root ρ ↔
        PaperSpecs.SignedDictatorOn (phase a Q ∘ bitsEquiv (Fin n)) Finset.univ)) := by
  rcases radical_dichotomy a Q with ⟨v, hv, hanti⟩ | ⟨k, L, hL, Q₀, hQ₀, hf⟩
  · exact translation_phase_bound a Q v hv hanti ρ hρ
  · have h := quotient_phase_bound a Q Q₀ L hL hQ₀ hf ρ hρ
    refine ⟨h.1, fun hp _ => ?_⟩
    constructor
    · intro heq
      exact False.elim ((ne_of_lt (h.2 hp)) heq)
    · rintro ⟨i, _, negative, heq⟩
      rw [heq]
      exact bsc_signed_dictator_equality n i negative ρ hρ

/-- Exact inhabitant of the independent quadratic-function manuscript target. -/
theorem paper_quadratic_hellinger : PaperSpecs.QuadraticHellinger := by
  intro n _ f hquad ρ hρ
  obtain ⟨a, b, q, hq⟩ := hquad
  have hf : f = phase a (polynomial b q) ∘ bitsEquiv (Fin n) := by
    funext x
    exact (hq x).trans (polynomial_phase_bits a b q x).symm
  rw [hf]
  exact phase_hellinger a (polynomial b q) ρ hρ

#print axioms quotient_phase_bound
#print axioms paper_quadratic_hellinger
end Hellinger.AllQuadratic
