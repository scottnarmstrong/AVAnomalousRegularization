-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.ChartSchedule.Labels
public import AVRegularity.Definitions.Construction.DiagLetter
public import AVRegularity.Definitions.CycleJoint.IsPointwiseMolecularEnvelope
public import AVRegularity.Statements.Construction.IsAdmissibleQ

/-! Natural preparation chart schedules, including full availability hulls and core labels.
The padding and label constants are fixed; the age and depth floor are uniform in the family. -/

@[expose] public section

open Homogenization AVenhance

namespace AVRegularity.Providers

/-- **The scheduled availability hulls fit a fixed preparation enlargement**. -/
theorem preparation_chart_schedule (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (CH : ℝ) (hCH : 0 < CH) :
    ∃ (Cpad Cage : ℝ) (Npad mStar : ℕ), 0 ≤ Cpad ∧ 0 < Cage ∧
      ∀ (data : OCData), data.α = α → data.q = q → data.Λ = Λ →
      ∀ (Mnat m : ℕ), 2 ≤ m → mStar ≤ m → m ≤ Mnat →
      ∀ (tS : ℝ) (l₀ : ℤ) (P : ℕ), 1 ≤ P →
        ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ tS →
        tS < ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m →
        tS + CH * ocTauPP α q Λ m ≤ ((l₀ : ℝ) + P - 1 / 2) * ocTauPP α q Λ m →
      ∀ {ι : Type*} {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
        {D : ℕ} {Ctx : OddSlot → Type*} (F : ChartedFamily ι h D OddSlot Ctx),
        (∀ p, IsNaturalPiece data Mnat m p.val (F.piece p)) →
        IsPreparationChartSchedule α q Λ m (data.Φ (m - 1)) (data.hΦ (m - 1))
          tS (tS + CH * ocTauPP α q Λ m) Cpad Cage Npad l₀ P F  := by
  let B : CycleJointProofs.ChartSchedule.Parameters :=
    ⟨α, s, q, Λ, CH, hα₀, hα₁, hs₀, hs₁, hq, hΛ, hCH⟩
  exact CycleJointProofs.ChartSchedule.preparation_chart_schedule_of_ingredients B
    (CycleJointProofs.ChartSchedule.constants B)
    (CycleJointProofs.ChartSchedule.finite_reference B)
    (CycleJointProofs.ChartSchedule.availability B)
    (CycleJointProofs.ChartSchedule.padded_geometry B)
    (CycleJointProofs.ChartSchedule.ages B)
    (CycleJointProofs.ChartSchedule.segments B)
    (CycleJointProofs.ChartSchedule.cover_labels B)
    (CycleJointProofs.ChartSchedule.core_label B)


end AVRegularity.Providers
