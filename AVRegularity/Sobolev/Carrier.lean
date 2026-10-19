-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Constraints

/-! Closed Hilbert subspaces defined by the weak-derivative constraints. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization
open scoped ENNReal

namespace AVRegularity.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The closed graph of ordered weak jets on `U`. -/
def planeHkGraph (U : Set (Vec 2)) (K : ℕ) :
    ClosedSubmodule ℝ (JetL2 (volume.restrict U) K E) :=
  ⨅ j : Fin K, ⨅ w : DerivativeWord2 j.val, ⨅ i : Fin 2,
    ⨅ φ : WeakTest U, ⨅ e : E,
      (⊥ : ClosedSubmodule ℝ ℝ).comap (weakJetConstraint j w i φ e)

/-- The closed graph of cell jets satisfying global periodic weak identities. -/
def torusHkGraph (K : ℕ) :
    ClosedSubmodule ℝ (JetL2 (volume.restrict AVenhance.unitCube) K E) :=
  ⨅ j : Fin K, ⨅ w : DerivativeWord2 j.val, ⨅ i : Fin 2,
    ⨅ φ : WeakTest (Set.univ : Set (Vec 2)), ⨅ e : E,
      (⊥ : ClosedSubmodule ℝ ℝ).comap (periodicWeakJetConstraint j w i φ e)

/-- Hilbert realization of weak `H^K(U;E)` on an open domain. -/
abbrev PlaneHk (U : Set (Vec 2)) (K : ℕ) (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] := ↥(planeHkGraph (E := E) U K)

/-- Hilbert realization of periodic `H^K` on the unit two-dimensional torus. -/
abbrev TorusHk (K : ℕ) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :=
  ↥(torusHkGraph (E := E) K)

/-- The raw representative of a plane ambient jet. -/
def planeJetRepresentative {U : Set (Vec 2)} {K : ℕ}
    (D : JetL2 (volume.restrict U) K E) : RawJet2 K E := fun a x => D a x

end AVRegularity.Sobolev
