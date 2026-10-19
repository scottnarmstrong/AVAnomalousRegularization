-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVenhance.Statements.Roots.UnitCube
public import AVenhance.Statements.Roots.IsZ2Periodic
public import Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Topology.Separation.CompletelyRegular

/-! Ordered weak jets and their ambient Hilbert product. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization
open scoped ENNReal

namespace AVRegularity.Sobolev

/-- An ordered derivative word of length `j` in `d` spatial directions. -/
abbrev DerivativeWord (d j : ℕ) := Fin j → Fin d

/-- All ordered derivative words in dimension `d` through order `K`. -/
abbrev JetIndex (d K : ℕ) := Σ j : Fin (K + 1), DerivativeWord d j.val

/-- The raw representative of every derivative in dimension `d` through order `K`. -/
abbrev RawJet (d K : ℕ) (E : Type*) := JetIndex d K → Vec d → E

/-- Two-dimensional specialization of `DerivativeWord`. -/
abbrev DerivativeWord2 (j : ℕ) := DerivativeWord 2 j

/-- Two-dimensional specialization of `JetIndex`. -/
abbrev JetIndex2 (K : ℕ) := JetIndex 2 K

/-- Two-dimensional specialization of `RawJet`. -/
abbrev RawJet2 (K : ℕ) (E : Type*) := RawJet 2 K E

/-- The index of the value component in dimension `d`. -/
def valueIndex (d K : ℕ) : JetIndex d K := ⟨0, Fin.elim0⟩

/-- The index of a derivative one order below the top order in dimension `d`. -/
def lowerIndex {d K : ℕ} (j : Fin K) (w : DerivativeWord d j.val) : JetIndex d K :=
  ⟨⟨j.val, Nat.lt_succ_of_lt j.isLt⟩, w⟩

/-- Append the next coordinate to an ordered derivative word in dimension `d`. -/
def nextIndex {d K : ℕ} (j : Fin K) (w : DerivativeWord d j.val) (i : Fin d) : JetIndex d K :=
  ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.snoc w i⟩

/-- Two-dimensional index of the value component. -/
def valueIndex2 (K : ℕ) : JetIndex2 K := valueIndex 2 K

/-- Two-dimensional index of a derivative below the top order. -/
def lowerIndex2 {K : ℕ} (j : Fin K) (w : DerivativeWord2 j.val) : JetIndex2 K :=
  lowerIndex j w

/-- Two-dimensional index obtained by appending a coordinate. -/
def nextIndex2 {K : ℕ} (j : Fin K) (w : DerivativeWord2 j.val) (i : Fin 2) : JetIndex2 K :=
  nextIndex j w i

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every raw jet component belongs to `L²` on `U`. -/
def JetMemL2On (U : Set (Vec 2)) {K : ℕ} (D : RawJet2 K E) : Prop :=
  ∀ a, MemLp (D a) 2 (volume.restrict U)

/-- Ordered weak derivative identities, tested against every value vector. -/
def HasOrderedWeakJetOn (U : Set (Vec 2)) {K : ℕ} (D : RawJet2 K E) : Prop :=
  ∀ (j : Fin K) (w : DerivativeWord2 j.val) (i : Fin 2) (e : E),
    HasWeakPartialDerivOn U i
      (fun x => inner ℝ e (D (lowerIndex2 j w) x))
      (fun x => inner ℝ e (D (nextIndex2 j w i) x))

/-- Periodic ordered weak jets use global weak identities and cell `L²` data. -/
def HasPeriodicOrderedWeakJet {K : ℕ} (D : RawJet2 K E) : Prop :=
  (∀ a, AVenhance.IsZ2Periodic (D a)) ∧
    JetMemL2On AVenhance.unitCube D ∧ HasOrderedWeakJetOn Set.univ D

/-- A raw weak Sobolev witness on an open subset of `Vec 2`. -/
structure PlaneHkFunction (U : Set (Vec 2)) (K : ℕ) (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  jet : RawJet2 K E
  memL2 : JetMemL2On U jet
  hasWeakJet : HasOrderedWeakJetOn U jet

/-- A raw periodic weak Sobolev witness on the two-dimensional unit torus. -/
structure TorusHkFunction (K : ℕ) (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  jet : RawJet2 K E
  hasPeriodicWeakJet : HasPeriodicOrderedWeakJet jet

/-- One derivative component as an `L²` class for an arbitrary measure. -/
abbrev ComponentL2 (μ : Measure (Vec 2)) (E : Type*) [NormedAddCommGroup E]
    [MeasurableSpace E] := Lp E 2 μ

/-- The finite Hilbert product of all ordered `L²` derivatives through order `K`. -/
abbrev JetL2 (μ : Measure (Vec 2)) (K : ℕ) (E : Type*) [NormedAddCommGroup E]
    [MeasurableSpace E] := PiLp 2 (fun _ : JetIndex2 K => ComponentL2 μ E)

/-- A smooth compactly supported scalar test function supported in `U`. -/
structure WeakTest (U : Set (Vec 2)) where
  toFun : Vec 2 → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  compact : HasCompactSupport toFun
  support_subset : tsupport toFun ⊆ U

namespace WeakTest

/-- The coordinate derivative of a weak test function. -/
def coordDeriv {U : Set (Vec 2)} (φ : WeakTest U) (i : Fin 2) : Vec 2 → ℝ :=
  fun x => (fderiv ℝ φ.toFun x) (basisVec i)

/-- A weak test function belongs to `L²` on its support domain. -/
theorem memL2 {U : Set (Vec 2)} (φ : WeakTest U) :
    MemLp φ.toFun 2 (volume.restrict U) :=
  (φ.smooth.continuous.memLp_of_hasCompactSupport φ.compact).restrict U

/-- A coordinate derivative of a weak test function belongs to `L²`. -/
theorem coordDeriv_memL2 {U : Set (Vec 2)} (φ : WeakTest U) (i : Fin 2) :
    MemLp (φ.coordDeriv i) 2 (volume.restrict U) := by
  have hcont : Continuous (φ.coordDeriv i) :=
    (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  exact (hcont.memLp_of_hasCompactSupport
    (φ.compact.fderiv_apply (𝕜 := ℝ) (basisVec i))).restrict U

end WeakTest

end AVRegularity.Sobolev
