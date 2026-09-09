import Hellinger.F2Fourier
import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-! Characteristic-two radical decomposition of actual quadratic Boolean phases. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Hellinger.QuadraticRadical
open F2Model ChannelSections

abbrev Form (n : ℕ) := QuadraticMap F2 (Cube n) F2

def phase {n : ℕ} (a : F2) (Q : Form n) (x : Cube n) : ℝ := sign (a + Q x)

theorem sign_boolean (z : F2) : sign z = -1 ∨ sign z = 1 := by
  unfold sign
  split_ifs <;> simp

@[simp] theorem sign_zero : sign (0 : F2) = 1 := by norm_num [sign]
@[simp] theorem sign_one : sign (1 : F2) = -1 := by norm_num [sign]

theorem sign_sq (z : F2) : sign z ^ 2 = 1 := by
  rcases sign_boolean z with h | h <;> rw [h] <;> norm_num

theorem eq_one_of_ne_zero (z : F2) (hz : z ≠ 0) : z = 1 := by
  obtain ⟨b, rfl⟩ := bitEquiv.surjective z
  cases b <;> simp_all

theorem phase_boolean {n : ℕ} (a : F2) (Q : Form n) (x : Cube n) :
    phase a Q x = -1 ∨ phase a Q x = 1 := sign_boolean _

theorem phase_derivative {n : ℕ} (a : F2) (Q : Form n) (x v : Cube n) :
    phase a Q x * phase a Q (x + v) = sign (Q v) * sign (Q.polarBilin x v) := by
  have hq := QuadraticMap.map_add Q x v
  change Q (x + v) = Q x + Q v + Q.polarBilin x v at hq
  simp only [phase, hq, sign_add]
  have ha := sign_sq a
  have hx := sign_sq (Q x)
  calc
    _ = sign a ^ 2 * sign (Q x) ^ 2 * (sign (Q v) * sign (Q.polarBilin x v)) := by ring
    _ = _ := by rw [ha, hx]; ring

theorem character_mean_zero {n : ℕ} (L : Cube n →ₗ[F2] F2)
    (hL : L ≠ 0) : mean (fun x => sign (L x)) = 0 := by
  have hex : ∃ v, L v ≠ 0 := by
    by_contra h
    apply hL
    apply LinearMap.ext
    intro v
    by_contra hv
    exact h ⟨v, hv⟩
  obtain ⟨v, hv⟩ := hex
  have hv1 := eq_one_of_ne_zero (L v) hv
  have hm := mean_comp_equiv (Equiv.addLeft v) (fun x => sign (L x))
  have hfun : (fun x => sign (L x)) ∘ Equiv.addLeft v = fun x => -sign (L x) := by
    funext x
    simp [Function.comp_apply, map_add, sign_add, hv1]
  rw [hfun, mean_neg] at hm
  linarith

theorem phase_bent {n : ℕ} (a : F2) (Q : Form n)
    (hQ : Q.polarBilin.ker = ⊥) :
    Flatness.IsBent (phase a Q ∘ bitsEquiv (Fin n)) := by
  apply bent_of_autocorrelation n (phase a Q) (phase_boolean a Q)
  intro v hv
  have hL : Q.polarBilin v ≠ 0 := by
    intro h
    have hvk : v ∈ Q.polarBilin.ker := h
    rw [hQ, Submodule.mem_bot] at hvk
    exact hv hvk
  have hs (x : Cube n) : Q.polarBilin x v = Q.polarBilin v x :=
    QuadraticMap.polar_comm Q x v
  simp_rw [phase_derivative, hs]
  rw [Fourier.mean_const_mul, character_mean_zero _ hL, mul_zero]

def polynomial {n : ℕ} (b : Fin n → F2) (q : Fin n → Fin n → F2) : Form n :=
  ∑ i, b i • QuadraticMap.proj i i +
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), q i j • QuadraticMap.proj i j

theorem polynomial_apply {n : ℕ} (b : Fin n → F2) (q : Fin n → Fin n → F2)
    (x : Cube n) : polynomial b q x =
      (∑ i, b i * x i) + ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        q i j * x i * x j := by
  have hs (z : F2) : z * z = z := by
    obtain ⟨t, rfl⟩ := bitEquiv.surjective z
    cases t <;> norm_num
  simp [polynomial, QuadraticMap.proj_apply, hs, mul_assoc]

theorem polynomial_phase_bits {n : ℕ} (a : F2) (b : Fin n → F2)
    (q : Fin n → Fin n → F2) (x : PaperSpecs.Cube n) :
    phase a (polynomial b q) (bitsEquiv (Fin n) x) =
      if PaperSpecs.quadraticValue a b q x = 0 then 1 else -1 := by
  simp only [phase, polynomial_apply, bitsEquiv_apply, bitEquiv, sign,
    PaperSpecs.quadraticValue, ← add_assoc]
  rfl

/-- A quadratic phase either has a sign-reversing additive translation, or
factors through a quadratic form whose polar bilinear form has trivial kernel. -/
theorem radical_dichotomy {n : ℕ} (a : F2) (Q : Form n) :
    (∃ v : Cube n, v ≠ 0 ∧ ∀ x, phase a Q (x + v) = -phase a Q x) ∨
    ∃ (k : ℕ) (L : Cube n →ₗ[F2] Cube k), Function.Surjective L ∧
      ∃ Q₀ : Form k, Q₀.polarBilin.ker = ⊥ ∧ phase a Q = phase a Q₀ ∘ L := by
  let R := Q.polarBilin.ker
  by_cases h : ∃ v ∈ R, Q v ≠ 0
  · left
    obtain ⟨v, hv, hq⟩ := h
    refine ⟨v, ?_, ?_⟩
    · intro hz
      simp [hz] at hq
    · intro x
      have hpol : Q.polarBilin x v = 0 := by
        change QuadraticMap.polar Q x v = 0
        rw [QuadraticMap.polar_comm]
        exact congrArg (fun l : Cube n →ₗ[F2] F2 => l x) hv
      have hv1 := eq_one_of_ne_zero (Q v) hq
      have hadd := QuadraticMap.map_add Q x v
      change Q (x + v) = Q x + Q v + Q.polarBilin x v at hadd
      simp [phase, hadd, hpol, hv1, sign_add]
  · right
    have hR : R ≤ Q.radical := by
      intro v hv
      refine ⟨?_, hv⟩
      by_contra hq
      exact h ⟨v, hv, hq⟩
    let k := Module.finrank F2 (Cube n ⧸ R)
    let E : (Cube n ⧸ R) ≃ₗ[F2] Cube k := (Module.finBasis F2 (Cube n ⧸ R)).equivFun
    let L : Cube n →ₗ[F2] Cube k := E.toLinearMap.comp R.mkQ
    let Q₀ : Form k := (Q.lift R hR).comp E.symm.toLinearMap
    have hL : Function.Surjective L := E.surjective.comp R.mkQ_surjective
    refine ⟨k, L, hL, Q₀, ?_, ?_⟩
    · apply le_antisymm _ bot_le
      intro w hw
      change w = 0
      obtain ⟨v, rfl⟩ := hL w
      have hvR : v ∈ R := by
        change Q.polarBilin v = 0
        apply LinearMap.ext
        intro x
        have hp := congrArg (fun l : Cube k →ₗ[F2] F2 => l (L x)) hw
        change Q₀.polarBilin (L v) (L x) = 0 at hp
        simpa [Q₀, L, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
          QuadraticMap.comp_apply, ← Submodule.Quotient.mk_add] using hp
      change E (R.mkQ v) = 0
      rw [show R.mkQ v = 0 from (Submodule.Quotient.mk_eq_zero R).mpr hvR, E.map_zero]
    · funext x
      simp [phase, Q₀, L, QuadraticMap.comp_apply]

#print axioms radical_dichotomy
#print axioms phase_bent
end Hellinger.QuadraticRadical
