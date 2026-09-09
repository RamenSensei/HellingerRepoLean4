import Hellinger.BentLow
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Fin.Basic

/-! Four-dimensional bent functions: structural and exact moment proofs. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.BentFour
open Fourier

def fourBitsEquiv : Cube 4 ≃ Bool × Bool × Bool × Bool where
  toFun x := ⟨x 0, x 1, x 2, x 3⟩
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a, b, c, d⟩; rfl

theorem sum_four_bits {R : Type*} [AddCommMonoid R] (F : Cube 4 → R) :
    (∑ x, F x) =
      ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, F ![a, b, c, d] := by
  rw [← fourBitsEquiv.symm.sum_comp F]
  simp [Fintype.sum_prod_type, fourBitsEquiv]

theorem prod_four_bits {R : Type*} [CommMonoid R] (F : Cube 4 → R) :
    (∏ x, F x) =
      ∏ a : Bool, ∏ b : Bool, ∏ c : Bool, ∏ d : Bool, F ![a, b, c, d] := by
  rw [← fourBitsEquiv.symm.prod_comp F]
  simp [Fintype.prod_prod_type, fourBitsEquiv]

def face (i : Fin 4) (b : Bool) : Finset (Cube 4) := Finset.univ.filter (fun x => x i = b)

theorem face_card (i : Fin 4) (b : Bool) : (face i b).card = 8 := by
  have heq : (face i b).card = ∑ x : Cube 4, if x i = b then (1 : ℕ) else 0 := by
    simp [face, Finset.sum_boole]
  rw [heq, sum_four_bits]
  fin_cases i <;> cases b <;> norm_num

theorem phase_unit (i : Fin 4) (x : Cube 4) : phase (unit i) x = boolSign (x i) := by
  fin_cases i <;> simp [phase, Fin.prod_univ_succ, unit, boolSign]

theorem face_sum (f : Cube 4 → ℝ) (i : Fin 4) (b : Bool) :
    (∑ x ∈ face i b, f x) = 8 * (mean f + boolSign b * walsh f (unit i)) := by
  have hpoint (x : Cube 4) : (if x i = b then f x else 0) =
      (f x + boolSign b * (f x * phase (unit i) x)) / 2 := by
    rw [phase_unit]
    cases hx : x i <;> cases b <;> norm_num [hx, boolSign]
  rw [face, Finset.sum_filter]
  simp_rw [hpoint]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [mean, walsh, cube_card]
  norm_num
  ring

theorem flat_four_coefficient (f : Cube 4 → ℝ) (hb : Flatness.IsBent f) (s : Cube 4) :
    walsh f s = -1 / 4 ∨ walsh f s = 1 / 4 := by
  have h := hb s
  norm_num at h
  have hh : (walsh f s + 1 / 4) * (walsh f s - 1 / 4) = 0 := by nlinarith only [h]
  rcases mul_eq_zero.mp hh with h | h
  · left; linarith
  · right; linarith

theorem bent_face_sum (f : Cube 4 → ℝ) (hb : Flatness.IsBent f) (i : Fin 4) (b : Bool) :
    (∑ x ∈ face i b, f x) = -4 ∨ (∑ x ∈ face i b, f x) = 0 ∨
      (∑ x ∈ face i b, f x) = 4 := by
  rw [face_sum]
  have hm := flat_four_coefficient f hb (fun _ => false)
  rw [walsh_zero] at hm
  rcases hm with hm | hm <;> rcases flat_four_coefficient f hb (unit i) with hw | hw <;>
    cases b <;> norm_num [hm, hw, boolSign]

theorem boolean_product_of_eight_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ) (hf : ∀ x ∈ s, f x = -1 ∨ f x = 1) (hcard : s.card = 8)
    (hsum : (∑ x ∈ s, f x) = -4 ∨ (∑ x ∈ s, f x) = 0 ∨ (∑ x ∈ s, f x) = 4) :
    ∏ x ∈ s, f x = 1 := by
  let k := (s.filter (fun x => f x = -1)).card
  have hpoint (x : ι) (hx : x ∈ s) : f x = if f x = -1 then -1 else 1 := by
    rcases hf x hx with h | h <;> simp [h]
  have hsumval : (∑ x ∈ s, f x) = 8 - 2 * (k : ℝ) := by
    rw [Finset.sum_congr rfl hpoint]
    have heq : (∑ x ∈ s, if f x = -1 then (-1 : ℝ) else 1) =
        ∑ x ∈ s, (1 - 2 * (if f x = -1 then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> norm_num
    rw [heq, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [Finset.sum_boole, hcard, k]
  have hprod : (∏ x ∈ s, f x) = (-1 : ℝ) ^ k := by
    rw [Finset.prod_congr rfl hpoint, Finset.prod_ite]
    simp [k]
  have hk : k = 2 ∨ k = 4 ∨ k = 6 := by
    rcases hsum with h | h | h
    · right; right
      have hc : (k : ℝ) = 6 := by linarith
      exact_mod_cast hc
    · right; left
      have hc : (k : ℝ) = 4 := by linarith
      exact_mod_cast hc
    · left
      have hc : (k : ℝ) = 2 := by linarith
      exact_mod_cast hc
  rw [hprod]
  rcases hk with h | h | h <;> rw [h] <;> norm_num

theorem bent_face_product (f : Cube 4 → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hb : Flatness.IsBent f) (i : Fin 4) (b : Bool) :
    ∏ x ∈ face i b, f x = 1 :=
  boolean_product_of_eight_sum (face i b) f (fun x _ => hf x) (face_card i b)
    (bent_face_sum f hb i b)

/-- The six mixed terms are ordered `01,02,03,12,13,23`. -/
def quadraticPhase (c : ℝ) (l : Fin 4 → ℝ) (e : Fin 6 → ℝ) (x : Cube 4) : ℝ :=
  c * (if x 0 then l 0 else 1) * (if x 1 then l 1 else 1) *
    (if x 2 then l 2 else 1) * (if x 3 then l 3 else 1) *
    (if x 0 && x 1 then e 0 else 1) * (if x 0 && x 2 then e 1 else 1) *
    (if x 0 && x 3 then e 2 else 1) * (if x 1 && x 2 then e 3 else 1) *
    (if x 1 && x 3 then e 4 else 1) * (if x 2 && x 3 then e 5 else 1)

def constantTerm (f : Cube 4 → ℝ) : ℝ := f ![false, false, false, false]

def linearTerms (f : Cube 4 → ℝ) : Fin 4 → ℝ :=
  ![constantTerm f * f ![true, false, false, false],
    constantTerm f * f ![false, true, false, false],
    constantTerm f * f ![false, false, true, false],
    constantTerm f * f ![false, false, false, true]]

def mixedTerms (f : Cube 4 → ℝ) : Fin 6 → ℝ :=
  ![constantTerm f * f ![true, false, false, false] * f ![false, true, false, false] * f ![true, true, false, false],
    constantTerm f * f ![true, false, false, false] * f ![false, false, true, false] * f ![true, false, true, false],
    constantTerm f * f ![true, false, false, false] * f ![false, false, false, true] * f ![true, false, false, true],
    constantTerm f * f ![false, true, false, false] * f ![false, false, true, false] * f ![false, true, true, false],
    constantTerm f * f ![false, true, false, false] * f ![false, false, false, true] * f ![false, true, false, true],
    constantTerm f * f ![false, false, true, false] * f ![false, false, false, true] * f ![false, false, true, true]]

private theorem sign_eq_product (a P : ℝ) (ha : a ^ 2 = 1) (h : a * P = 1) : a = P := by
  calc
    a = a * (a * P) := by rw [h]; ring
    _ = a ^ 2 * P := by ring
    _ = P := by rw [ha, one_mul]

set_option maxHeartbeats 3000000 in
/-- Flatness forces all cubic face derivatives to vanish; these five face
identities reconstruct the entire truth table from its terms of degree at most two. -/
theorem bent_quadratic_representation (f : Cube 4 → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f) :
    f = quadraticPhase (constantTerm f) (linearTerms f) (mixedTerms f) := by
  have hs (x : Cube 4) : f x ^ 2 = 1 := by rcases hf x with h | h <;> norm_num [h]
  have hp2 (x : Cube 4) : f x ^ 2 = 1 := by simpa using pow_eq_pow_mod 2 (hs x)
  have hp3 (x : Cube 4) : f x ^ 3 = f x := by simpa using pow_eq_pow_mod 3 (hs x)
  have hp4 (x : Cube 4) : f x ^ 4 = 1 := by simpa using pow_eq_pow_mod 4 (hs x)
  have hp7 (x : Cube 4) : f x ^ 7 = f x := by simpa using pow_eq_pow_mod 7 (hs x)
  have hp11 (x : Cube 4) : f x ^ 11 = f x := by simpa using pow_eq_pow_mod 11 (hs x)

  have h7 : f ![false, true, true, true] = f ![false, false, false, false] * f ![false, false, false, true] * f ![false, false, true, false] * f ![false, false, true, true] * f ![false, true, false, false] * f ![false, true, false, true] * f ![false, true, true, false] := by
    apply sign_eq_product _ _ (hs _)
    have h := bent_face_product f hf hb 0 false
    simp [face, Finset.prod_filter, prod_four_bits] at h
    convert h using 1
    ring

  have h11 : f ![true, false, true, true] = f ![false, false, false, false] * f ![false, false, false, true] * f ![false, false, true, false] * f ![false, false, true, true] * f ![true, false, false, false] * f ![true, false, false, true] * f ![true, false, true, false] := by
    apply sign_eq_product _ _ (hs _)
    have h := bent_face_product f hf hb 1 false
    simp [face, Finset.prod_filter, prod_four_bits] at h
    convert h using 1
    ring

  have h13 : f ![true, true, false, true] = f ![false, false, false, false] * f ![false, false, false, true] * f ![false, true, false, false] * f ![false, true, false, true] * f ![true, false, false, false] * f ![true, false, false, true] * f ![true, true, false, false] := by
    apply sign_eq_product _ _ (hs _)
    have h := bent_face_product f hf hb 2 false
    simp [face, Finset.prod_filter, prod_four_bits] at h
    convert h using 1
    ring

  have h14 : f ![true, true, true, false] = f ![false, false, false, false] * f ![false, false, true, false] * f ![false, true, false, false] * f ![false, true, true, false] * f ![true, false, false, false] * f ![true, false, true, false] * f ![true, true, false, false] := by
    apply sign_eq_product _ _ (hs _)
    have h := bent_face_product f hf hb 3 false
    simp [face, Finset.prod_filter, prod_four_bits] at h
    convert h using 1
    ring

  have h15 : f ![true, true, true, true] = f ![true, false, false, false] * f ![true, false, false, true] * f ![true, false, true, false] * f ![true, false, true, true] * f ![true, true, false, false] * f ![true, true, false, true] * f ![true, true, true, false] := by
    apply sign_eq_product _ _ (hs _)
    have h := bent_face_product f hf hb 0 true
    simp [face, Finset.prod_filter, prod_four_bits] at h
    convert h using 1
    ring

  funext x
  have hx : x = ![x 0, x 1, x 2, x 3] := by funext i; fin_cases i <;> rfl
  cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;> cases h₃ : x 3 <;>
    rw [h₀, h₁, h₂, h₃] at hx <;> rw [hx] <;>
    dsimp [quadraticPhase, constantTerm, linearTerms, mixedTerms]
  all_goals
    norm_num
  all_goals
    try simp only [h15, h7, h11, h13, h14]
    try ring_nf
    try simp only [hp2, hp3, hp4, hp7, hp11, mul_one, one_mul]

def edgeAction (e : Fin 6 → ℝ) (s : Cube 4) : Fin 4 → ℝ :=
  ![(if s 1 then e 0 else 1) * (if s 2 then e 1 else 1) * (if s 3 then e 2 else 1),
    (if s 0 then e 0 else 1) * (if s 2 then e 3 else 1) * (if s 3 then e 4 else 1),
    (if s 0 then e 1 else 1) * (if s 1 then e 3 else 1) * (if s 3 then e 5 else 1),
    (if s 0 then e 2 else 1) * (if s 1 then e 4 else 1) * (if s 2 then e 5 else 1)]

def signCharacter (a : Fin 4 → ℝ) (x : Cube 4) : ℝ := ∏ i, if x i then a i else 1

set_option maxHeartbeats 10000000 in
/-- The exact polar identity, for arbitrary sign-valued coefficients. -/
theorem quadratic_polar (c : ℝ) (l : Fin 4 → ℝ) (e : Fin 6 → ℝ)
    (hc : c ^ 2 = 1) (hl : ∀ i, l i ^ 2 = 1) (he : ∀ i, e i ^ 2 = 1)
    (s x : Cube 4) :
    quadraticPhase c l e x * quadraticPhase c l e (translate s x) =
      c * quadraticPhase c l e s * signCharacter (edgeAction e s) x := by
  have hp3 (i : Fin 6) : e i ^ 3 = e i := by simpa using pow_eq_pow_mod 3 (he i)
  have hx : x = ![x 0, x 1, x 2, x 3] := by funext i; fin_cases i <;> rfl
  have hs : s = ![s 0, s 1, s 2, s 3] := by funext i; fin_cases i <;> rfl
  cases hx₀ : x 0 <;> cases hx₁ : x 1 <;> cases hx₂ : x 2 <;> cases hx₃ : x 3 <;>
    cases hs₀ : s 0 <;> cases hs₁ : s 1 <;> cases hs₂ : s 2 <;> cases hs₃ : s 3 <;>
    rw [hx₀, hx₁, hx₂, hx₃] at hx <;> rw [hs₀, hs₁, hs₂, hs₃] at hs <;>
    rw [hx, hs] <;>
    simp only [signCharacter, Fin.prod_univ_succ] <;>
    dsimp [quadraticPhase, translate, edgeAction] <;>
    ring_nf <;> simp only [hc, hl, he, hp3, mul_one, one_mul]

theorem quadraticPhase_sq (c : ℝ) (l : Fin 4 → ℝ) (e : Fin 6 → ℝ)
    (hc : c ^ 2 = 1) (hl : ∀ i, l i ^ 2 = 1) (he : ∀ i, e i ^ 2 = 1) (x : Cube 4) :
    quadraticPhase c l e x ^ 2 = 1 := by
  simp only [quadraticPhase, mul_pow, ite_pow, hc, hl, he, one_pow, ite_self, mul_one]

theorem signCharacter_sum (a : Fin 4 → ℝ) :
    (∑ x : Cube 4, signCharacter a x) = ∏ i, (1 + a i) := by
  unfold signCharacter
  rw [← Fintype.prod_sum (fun (i : Fin 4) (b : Bool) => if b then a i else (1 : ℝ))]
  simp [add_comm]

def noiseDerivativeSum (e : Fin 6 → ℝ) (ρ : ℝ) (s : Cube 4) : ℝ :=
  ∏ i, if s i then ρ * (1 + edgeAction e s i) else 1 + ρ ^ 2 * edgeAction e s i

theorem weighted_character_sum (a : Fin 4 → ℝ) (ρ : ℝ) (s : Cube 4) :
    (∑ x : Cube 4, ρ ^ (degree x + degree (translate s x)) * signCharacter a x) =
      ∏ i, if s i then ρ * (1 + a i) else 1 + ρ ^ 2 * a i := by
  simp only [pow_add, pow_degree, signCharacter]
  simp_rw [← Finset.prod_mul_distrib]
  change (∑ x : Cube 4, ∏ i, ((if x i = true then ρ else 1) *
    (if Bool.xor (x i) (s i) = true then ρ else 1) * (if x i then a i else 1))) = _
  rw [← Fintype.prod_sum (fun (i : Fin 4) (b : Bool) =>
    (if b = true then ρ else 1) * (if Bool.xor b (s i) = true then ρ else 1) *
      (if b then a i else 1))]
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> simp <;> ring

theorem quadratic_weighted_derivative (c : ℝ) (l : Fin 4 → ℝ) (e : Fin 6 → ℝ)
    (hc : c ^ 2 = 1) (hl : ∀ i, l i ^ 2 = 1) (he : ∀ i, e i ^ 2 = 1)
    (ρ : ℝ) (s : Cube 4) :
    (∑ x : Cube 4, ρ ^ (degree x + degree (translate s x)) *
      (quadraticPhase c l e x * quadraticPhase c l e (translate s x))) ^ 2 =
        noiseDerivativeSum e ρ s ^ 2 := by
  simp_rw [quadratic_polar c l e hc hl he]
  have heq : (∑ x : Cube 4, ρ ^ (degree x + degree (translate s x)) *
      (c * quadraticPhase c l e s * signCharacter (edgeAction e s) x)) =
      (c * quadraticPhase c l e s) *
        (∑ x : Cube 4, ρ ^ (degree x + degree (translate s x)) * signCharacter (edgeAction e s) x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq, mul_pow, mul_pow, hc, quadraticPhase_sq c l e hc hl he, one_mul, one_mul,
    weighted_character_sum]
  rfl

/-- Nondegeneracy in the exact four-coordinate sign matrix representation. -/
def EdgeNondegenerate (e : Fin 6 → ℝ) : Prop :=
  ∀ s : Cube 4, s ≠ (fun _ => false) → ∏ i, (1 + edgeAction e s i) = 0

theorem quadratic_bent_nondegenerate (c : ℝ) (l : Fin 4 → ℝ) (e : Fin 6 → ℝ)
    (hc : c ^ 2 = 1) (hl : ∀ i, l i ^ 2 = 1) (he : ∀ i, e i ^ 2 = 1)
    (hb : Flatness.IsBent (quadraticPhase c l e)) : EdgeNondegenerate e := by
  intro s hs
  have h := Flatness.autocorrelation_zero hb s hs
  unfold autocorrelation mean at h
  simp_rw [quadratic_polar c l e hc hl he] at h
  rw [← Finset.mul_sum, signCharacter_sum, cube_card] at h
  norm_num at h
  have hc₀ : c ≠ 0 := by intro hzero; rw [hzero] at hc; norm_num at hc
  have hq₀ : quadraticPhase c l e s ≠ 0 := by
    have hq := quadraticPhase_sq c l e hc hl he s
    intro hzero
    rw [hzero] at hq
    norm_num at hq
  simpa only [hc₀, hq₀, false_or] using h

#print axioms bent_quadratic_representation
#print axioms quadratic_polar
end Hellinger.BentFour
