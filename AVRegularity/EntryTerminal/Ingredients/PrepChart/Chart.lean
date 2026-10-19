-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.Intermediate.CycleComparison.OcFlowJets
import AVRegularity.Applications.Construction.StreamTail
public import AVRegularity.EntryTerminal.Assembly.Prep.ModelAssembly
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Proofs.Results.CycleJoint.PreparationChartSchedule

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.EntryTerminal.Ingredients

/-! **The flow certificate of the preparation charts** (`IsPreparationFlowJets`), level-generic,
from the normalized jets of the short flow charts (`oc_flow_jets`, with constants `c` and
`C ≥ 1`).

Proof:
- The chart constants are `Cchart j = C^{j+1}`, since
  `C j! (C/ε)^j (a|r-σ|) = C^{j+1} j! ε^{-j} a |r-σ|`.
- The age premise `a_{m-1} |r - σ| ≤ c` follows from `|r - σ| ≤ 2 Cage τ''_m` once
  `2 Cage a_{m-1} τ''_m ≤ min{1/2, c}`. That holds for every level above a threshold
  (`weak_anchor_product_eventually_small`) and also gives `short_age`.
- Spatial smoothness of the flow is `streamFlow_spatial_smooth`.

For `r = σ` the jets vanish and the bound is `0`; for `j = 0` the bound is `C² a |r - σ|`; for
`Jchart = 0` only `C¹` smoothness is asked. A large age constant `Cage` raises the threshold but
not the constants. -/

/-- The chart constants `Cchart j = C^{j+1}` of the flow certificate. -/
def prepChartConst (C : ℝ) (j : ℕ) : ℝ := C ^ (j + 1)

/-- **The flow certificate at every level above a threshold.** The constant `C` precedes `Λ`;
the threshold depends on `Λ` and the age constant only. -/
theorem prep_flow_jets (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Λ : ℕ, 128 ≤ Λ → ∀ Cage : ℝ, 0 < Cage →
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ (Φ : ℕ → ℝ → Vec 2 → ℝ), IsOCStreamSeq α q Λ ζ Φ →
    ∀ m : ℕ, M₀ ≤ m → ∀ (hφ : IsAdmissibleStream (Φ (m - 1))) (tS tZ Cpad : ℝ) (Jchart : ℕ),
      IsPreparationFlowJets α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Jchart (prepChartConst C) := by
  obtain ⟨cf, C, hcf, hC, hfj⟩ := Providers.oc_flow_jets α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨C, hC, fun Λ hΛ Cage _ => ?_⟩
  obtain ⟨M₀, hM₀, hsmall⟩ := EntryWeakProofs.weak_anchor_product_eventually_small α s q hα₀ hα₁
    hs₀ hs₁ hq Λ hΛ (2 * Cage) (min (1 / 2) cf) (lt_min (by norm_num) hcf)
  refine ⟨M₀, hM₀, fun Φ hΦ m hm hφ tS tZ Cpad Jchart => ?_⟩
  have hs := hsmall m hm
  have hA : 0 < ocA α q Λ (m - 1) := Applications.ocA_pos α q hq.1 Λ (m - 1) hΛ
  refine ⟨?_, ?_, ?_⟩
  · calc 2 * Cage * ocA α q Λ (m - 1) * ocTauPP α q Λ m
          = 2 * Cage * (ocA α q Λ (m - 1) * ocTauPP α q Λ m) := by ring
      _ ≤ min (1 / 2) cf := hs
      _ ≤ 1 / 2 := min_le_left _ _
  · intro r _ σ _
    exact (CycleReference.streamFlow_spatial_smooth hφ r σ).of_le (WithTop.coe_le_coe.mpr le_top)
  · intro r _ σ _ hrσ j _ y
    have hc : ocA α q Λ (m - 1) * |r - σ| ≤ cf :=
      calc ocA α q Λ (m - 1) * |r - σ|
            ≤ ocA α q Λ (m - 1) * (2 * Cage * ocTauPP α q Λ m) :=
              mul_le_mul_of_nonneg_left hrσ hA.le
        _ = 2 * Cage * (ocA α q Λ (m - 1) * ocTauPP α q Λ m) := by ring
        _ ≤ min (1 / 2) cf := hs
        _ ≤ cf := min_le_right _ _
    calc _ ≤ C * (j.factorial : ℝ) * (C / ocEpsilon q Λ (m - 1)) ^ j *
            (ocA α q Λ (m - 1) * |r - σ|) := hfj Λ hΛ Φ hΦ m (by omega) hφ r σ hc j y
      _ = prepChartConst C j * (j.factorial : ℝ) * (ocEpsilon q Λ (m - 1))⁻¹ ^ j *
            ocA α q Λ (m - 1) * |r - σ| := by
        unfold prepChartConst
        rw [div_eq_mul_inv, mul_pow, pow_succ]
        ring

end AVRegularity.EntryTerminal.Ingredients
end
end

section
/-! **The chart part of the capped preparation** (`PrepChartPart`): the preparation chart certificate of the weak
family on the window `[a_M, a_M + 2h]`.

It has two halves:
- the schedule, from `preparation_chart_schedule` at `CH = 2`.
  `prepChart_of_schedule` takes it as the named hypothesis `PrepChartScheduleStatement` (its text
  copy); `prepChart` discharges it with the proof of `preparation_chart_schedule`;
- the flow jets, from `prep_flow_jets`.

The natural pieces come from the weak stage. `IsWeakStage` contains `IsStageInvariant … (M + J_w)`,
whose first conjunct is `Gw.IsNatural (M + J_w)`, and `Gw.level = M`. The window premises come
from the renewal block `l₀ = ⌊a_M/h + 1/2⌋` (`prepBlock_spec`) and the cover's end.

The cases `P = 2` (`a_M = (l₀ - 1/2) h`) and `P = 3` both occur. If `a_M = l₀ h`, the reference
anchor is the start; for an empty weak family the schedule concerns no pieces. -/

@[expose] public section

open Homogenization AVenhance

universe u v w

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.EntryTerminal.Route

/-- The renewal block of `a_M`: `(l₀ - 1/2) h ≤ a_M < (l₀ + 1/2) h`. -/
theorem prepBlock_spec {h aM : ℝ} (hh : 0 < h) :
    ((prepBlock h aM : ℝ) - 1 / 2) * h ≤ aM ∧ aM < ((prepBlock h aM : ℝ) + 1 / 2) * h := by
  unfold prepBlock
  have h1 := Int.floor_le (aM / h + 1 / 2)
  have h2 := Int.lt_floor_add_one (aM / h + 1 / 2)
  constructor
  · have hle : ((⌊aM / h + 1 / 2⌋ : ℤ) : ℝ) - 1 / 2 ≤ aM / h := by linarith only [h1]
    calc _ ≤ aM / h * h := mul_le_mul_of_nonneg_right hle hh.le
      _ = aM := div_mul_cancel₀ aM hh.ne'
  · have hlt : aM / h < ((⌊aM / h + 1 / 2⌋ : ℤ) : ℝ) + 1 / 2 := by linarith only [h2]
    calc aM = aM / h * h := (div_mul_cancel₀ aM hh.ne').symm
      _ < _ := mul_lt_mul_of_pos_right hlt hh

/-- Text copy of the `preparation_chart_schedule`. -/
def PrepChartScheduleStatement : Prop :=
  ∀ (α s q : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 → IsAdmissibleQ α s q →
    ∀ (Λ : ℕ), 128 ≤ Λ → ∀ (CH : ℝ), 0 < CH →
    ∃ (Cpad Cage : ℝ) (Npad mStar : ℕ), 0 ≤ Cpad ∧ 0 < Cage ∧
      ∀ (data : OCData), data.α = α → data.q = q → data.Λ = Λ →
      ∀ (Mnat m : ℕ), 2 ≤ m → mStar ≤ m → m ≤ Mnat →
      ∀ (tS : ℝ) (l₀ : ℤ) (P : ℕ), 1 ≤ P →
        ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ tS →
        tS < ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m →
        tS + CH * ocTauPP α q Λ m ≤ ((l₀ : ℝ) + P - 1 / 2) * ocTauPP α q Λ m →
      ∀ {ι : Type u} {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
        {D : ℕ} {Ctx : OddSlot → Type w} (F : ChartedFamily ι h D OddSlot Ctx),
        (∀ p, IsNaturalPiece data Mnat m p.val (F.piece p)) →
        IsPreparationChartSchedule α q Λ m (data.Φ (m - 1)) (data.hΦ (m - 1))
          tS (tS + CH * ocTauPP α q Λ m) Cpad Cage Npad l₀ P F

/-- **The chart part of the capped preparation from the schedule producer.** -/
theorem prepChart_of_schedule (hS : PrepChartScheduleStatement.{0, 0, 0}) : PrepChartPart := by
  intro X
  obtain ⟨C, -, hflow⟩ := prep_flow_jets X.α X.s X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq X.ζ X.hζ
  refine ⟨128, le_rfl, fun PA hΛ _ Jchart => ?_⟩
  obtain ⟨Cpad, Cage, Npad, mStar, -, hage, hsch⟩ :=
    hS X.α X.s X.q X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq PA.Λ hΛ 2 two_pos
  obtain ⟨M₁, hM₁, hfl⟩ := hflow PA.Λ hΛ Cage hage
  refine ⟨Cpad, Cage, Npad, prepChartConst C, fun nW CL Cχ kW j₀ => ⟨max mStar M₁, fun M hM => ?_⟩⟩
  intro D hD a lawW PW Gw aM hW hφ P hP hwin
  obtain ⟨hDα, hDq, hDΛ, -, hstream, -, -⟩ := hD
  have hh : 0 < ocTauPP X.α X.q PA.Λ M :=
    Construction.Stream.ocTauPP_pos (le_trans (by norm_num) hΛ)
  obtain ⟨hb1, hb2⟩ := prepBlock_spec (aM := aM) hh
  have hM2 : 2 ≤ M := le_trans hM₁ (le_trans (le_max_right _ _) hM)
  have hnat : ∀ p, IsNaturalPiece D (M + PA.Jw) M p.1 (Gw.fam.piece p) := fun p =>
    (congrArg (fun i => IsNaturalPiece D (M + PA.Jw) i p.1 (Gw.fam.piece p)) hW.2.2.1).mp
      (hW.2.2.2.2.2.2.2.2.2.1.1 p)
  exact ⟨hsch D hDα hDq hDΛ (M + PA.Jw) M hM2 (le_trans (le_max_left _ _) hM)
      (Nat.le_add_right _ _) aM _ P hP hb1 hb2 hwin Gw.fam hnat,
    hfl D.Φ hstream M (le_trans (le_max_right _ _) hM) hφ aM _ Cpad Jchart⟩

/-- **The chart part of the capped preparation**: the schedule from the proof of
`preparation_chart_schedule`. -/
theorem prepChart : PrepChartPart :=
  prepChart_of_schedule @AVRegularity.Providers.preparation_chart_schedule

end AVRegularity.EntryTerminal.Ingredients
end
end
