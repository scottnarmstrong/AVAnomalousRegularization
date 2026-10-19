-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFamily
public import AVRegularity.Statements.Intermediate.CycleReference.OcChart
public import AVRegularity.Statements.Construction.OcA
public import AVRegularity.Statements.Construction.OcTauP
public import AVRegularity.Statements.Construction.OcTau

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity

/-! Preparation charts, including their full availability hulls.
The recorded geometry interval is used as the availability hull, as for `IsNaturalPiece`.
The quantitative flow certificate covers earlier anchors and reference-chart transitions;
no construction-cover estimate is silently applied outside its observation interval. -/

def preparationPaddedWindow (tS tZ Cpad T : ℝ) : Set ℝ :=
  Set.Icc (tS - Cpad * T) (tZ + Cpad * T)

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}

/-- Full availability and reference paths of the pieces meeting the preparation window.
The finite label padding is explicit, and the natural map is evaluated at that same label. -/
structure IsPreparationChartSchedule (α q : ℝ) (Λ m : ℕ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
    (F : ChartedFamily ι h D P' Ctx) : Prop where
  pad_nonneg : 0 ≤ Cpad
  age_pos : 0 < Cage
  finite_pieces : {p | ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty}.Finite
  reference_mem : (l₀ : ℝ) * ocTauPP α q Λ m ∈
    preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m)
  availability_interval : ∀ p, ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty →
    Set.OrdConnected (F.piece p).geometry
  anchor_label : ∀ p, ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty →
    (F.piece p).anchor = ((F.piece p).label : ℝ) * ocTauPP α q Λ m
  natural : ∀ p, ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty →
    ∀ r ∈ (F.piece p).geometry, ∀ y,
      (F.piece p).material r y = ocChart α q Λ m φ hφ (F.piece p).label r y
  geometry_padded : ∀ p, ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty →
    (F.piece p).geometry ⊆ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m)
  anchor_age : ∀ p, ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty →
    ∀ r ∈ (F.piece p).geometry, |r - (F.piece p).anchor| ≤ Cage * ocTauPP α q Λ m
  reference_age : ∀ p, ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty →
    ∀ r ∈ (F.piece p).geometry,
      |r - (l₀ : ℝ) * ocTauPP α q Λ m| ≤ Cage * ocTauPP α q Λ m
  anchor_segments : ∀ p, ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty →
    ∀ r ∈ (F.piece p).geometry, Set.uIcc (F.piece p).anchor r ⊆ (F.piece p).geometry
  reference_segments : ∀ p, ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty →
    ∀ r ∈ (F.piece p).geometry, Set.uIcc ((l₀ : ℝ) * ocTauPP α q Λ m) r ⊆
      preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m)
  cover_labels : ∀ p, ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty →
    (F.piece p).label ∈ Set.Icc (l₀ - (Npad : ℤ)) (l₀ + (P : ℤ) - 1 + (Npad : ℤ))
  /-- Alignment of the pieces with the renewal blocks. A piece that carries an output
  time in the core of block `j` (the block of `j` minus a quiet margin of width `τ' - τ/24` at each end;
  the margin of the trimmed quiet times) has label `j`. The source retains for
  every active pulse its original chart and label. -/
  core_label : ∀ p, ∀ t ∈ (F.piece p).output ∩ Set.Icc tS tZ, ∀ j : ℤ,
    t ∈ Set.Ioo (((j : ℝ) - 1 / 2) * ocTauPP α q Λ m + (ocTauP α q Λ m - ocTau α q Λ m / 24))
      (((j : ℝ) + 1 / 2) * ocTauPP α q Λ m - (ocTauP α q Λ m - ocTau α q Λ m / 24)) →
    (F.piece p).label = j

/-- Finite version of the flow certificate, including inverse and transition flows in their own
spatial variables. Both time endpoints range over the padded geometry, not merely W. -/
structure IsPreparationFlowJets (α q : ℝ) (Λ m : ℕ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (tS tZ Cpad Cage : ℝ) (Jchart : ℕ) (Cchart : ℕ → ℝ) : Prop where
  short_age : 2 * Cage * ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤ 1 / 2
  smooth : ∀ r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m),
    ∀ σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m),
    ContDiff ℝ (Jchart + 1 : ℕ) (fun y => streamFlow φ hφ r y σ)
  jets : ∀ r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m),
    ∀ σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m),
    |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m → ∀ j ≤ Jchart, ∀ y : Vec 2,
      ‖iteratedFDeriv ℝ j (fun x =>
          fderiv ℝ (fun z => streamFlow φ hφ r z σ) x - ContinuousLinearMap.id ℝ (Vec 2)) y‖ ≤
        Cchart j * (j.factorial : ℝ) * (ocEpsilon q Λ (m - 1))⁻¹ ^ j *
          ocA α q Λ (m - 1) * |r - σ|

/-- Family-specific preparation chart certificate. The constants and reserve precede F in
`cycle_joint`. It asserts geometry and flow bounds, not a physical coefficient conclusion. -/
structure IsPreparationChartCertificate (α q : ℝ) (Λ m : ℕ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (tS tZ Cpad Cage : ℝ) (Npad Jchart : ℕ) (Cchart : ℕ → ℝ) (l₀ : ℤ) (P : ℕ)
    (F : ChartedFamily ι h D P' Ctx) : Prop where
  schedule : IsPreparationChartSchedule α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P F
  flow : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart

end AVRegularity
end
end

section
/-! Re-export. `IsPointwiseMolecularEnvelope` and the pointwise jet suprema
live in
`AVRegularity/Statements/Intermediate/Families/{PointwiseJetSupOn,PointwiseJetSupFam,PointwiseMolecularJet,IsPointwiseMolecularEnvelope}.lean`, with
unchanged bodies. This module keeps the old import path working. -/
end
