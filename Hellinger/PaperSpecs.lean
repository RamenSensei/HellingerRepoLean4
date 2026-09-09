import Hellinger.Flatness
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.ZMod.Basic

/-! Independent target statements for the principal manuscript claims.
These are proposition definitions, not proofs. A completion theorem must inhabit
the entire stated proposition without extra analytic or spectral hypotheses. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.PaperSpecs

abbrev Cube (n : ℕ) := Fin n → Bool

def IsBoolean {n : ℕ} (f : Cube n → ℝ) : Prop := ∀ x, f x = -1 ∨ f x = 1

def flip {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : Cube n :=
  fun i => if i ∈ S then !(x i) else x i

def SignReversing {n : ℕ} (f : Cube n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ x, f (flip S x) = -f x

def SignedDictatorOn {n : ℕ} (f : Cube n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∃ i ∈ S, ∃ negative : Bool,
    f = fun x => if negative then -boolSign (x i) else boolSign (x i)

def posteriorRootMean {n : ℕ} (f : Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : ℝ :=
  mean (fun y => root ((cubeBSC n ρ hρ).apply f y))

def HellingerBound {n : ℕ} (f : Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : Prop :=
  objective ((cubeBSC n ρ hρ).apply f) ≤ 1 - root ρ

/-- Binary entropy in bits; mathlib's binEntropy itself uses natural logarithms. -/
def binaryEntropyBits (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

/-- The exact finite-posterior expression for Boolean output mutual information.
Its identification with measure-theoretic mutual information is a separate
model-equivalence obligation, not supplied by this definition. -/
def posteriorInformation {n : ℕ} (f : Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : ℝ :=
  binaryEntropyBits ((1 - mean f) / 2) -
    mean (fun y => binaryEntropyBits ((1 - (cubeBSC n ρ hρ).apply f y) / 2))

def CKBound {n : ℕ} (f : Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : Prop :=
  posteriorInformation f ρ hρ ≤ 1 - binaryEntropyBits ((1 - ρ) / 2)

def TranslationHellinger : Prop :=
  ∀ (n : ℕ) (f : Cube n → ℝ), IsBoolean f →
  ∀ (S : Finset (Fin n)), S.Nonempty → SignReversing f S →
  ∀ (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1),
    mean f = 0 ∧ root ρ ≤ posteriorRootMean f ρ hρ ∧ HellingerBound f ρ hρ

def TranslationEquality : Prop :=
  ∀ (n : ℕ) (f : Cube n → ℝ), IsBoolean f →
  ∀ (S : Finset (Fin n)), S.Nonempty → SignReversing f S →
  ∀ (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1), 0 < ρ → ρ < 1 →
    (posteriorRootMean f ρ hρ = root ρ ↔ SignedDictatorOn f S)

def TranslationInformation : Prop :=
  ∀ (n : ℕ) (f : Cube n → ℝ), IsBoolean f →
  ∀ (S : Finset (Fin n)), S.Nonempty → SignReversing f S →
  ∀ (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1), CKBound f ρ hρ ∧
    (0 < ρ → ρ < 1 →
      (posteriorInformation f ρ hρ = 1 - binaryEntropyBits ((1 - ρ) / 2) ↔
        SignedDictatorOn f S))

def BentHellinger : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (f : Cube n → ℝ), IsBoolean f → Flatness.IsBent f →
  ∀ (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1), HellingerBound f ρ hρ ∧
    (0 < ρ → objective ((cubeBSC n ρ hρ).apply f) < 1 - root ρ)

def bit (b : Bool) : ZMod 2 := if b then 1 else 0

def quadraticValue {n : ℕ} (a : ZMod 2) (b : Fin n → ZMod 2)
    (q : Fin n → Fin n → ZMod 2) (x : Cube n) : ZMod 2 :=
  a + ∑ i, b i * bit (x i) +
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), q i j * bit (x i) * bit (x j)

def IsQuadratic {n : ℕ} (f : Cube n → ℝ) : Prop :=
  ∃ a b q, ∀ x, f x = if quadraticValue a b q x = 0 then 1 else -1

def QuadraticHellinger : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (f : Cube n → ℝ), IsQuadratic f →
  ∀ (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1), HellingerBound f ρ hρ ∧
    (0 < ρ → ρ < 1 →
      (objective ((cubeBSC n ρ hρ).apply f) = 1 - root ρ ↔
        SignedDictatorOn f Finset.univ))

def EntropyTransfer : Prop :=
  ∀ (n : ℕ) (f : Cube n → ℝ), IsBoolean f →
  ∀ (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1), HellingerBound f ρ hρ → CKBound f ρ hρ

def BentInformation : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (f : Cube n → ℝ), IsBoolean f → Flatness.IsBent f →
  ∀ (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1), CKBound f ρ hρ ∧
    (0 < ρ → posteriorInformation f ρ hρ < 1 - binaryEntropyBits ((1 - ρ) / 2))

def QuadraticInformation : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (f : Cube n → ℝ), IsQuadratic f →
  ∀ (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1), CKBound f ρ hρ ∧
    (0 < ρ → ρ < 1 →
      (posteriorInformation f ρ hρ = 1 - binaryEntropyBits ((1 - ρ) / 2) ↔
        SignedDictatorOn f Finset.univ))

end Hellinger.PaperSpecs
