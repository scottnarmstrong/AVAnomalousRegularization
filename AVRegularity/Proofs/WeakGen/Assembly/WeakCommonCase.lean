-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.PassageCert
public import AVRegularity.Construction.StageEnvelopes.Cauchy.Assembly
public import AVRegularity.EntryWeakAssembly.Assembly.EntryWeakInterfaces
import Mathlib.Analysis.Real.Pi.Bounds

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs.Assembly

/-! **`entry_coefficients` with the certificate and atlas ingredients discharged** (`entry_coefficients_of_remaining`). The
exact assembly `entry_coefficients_of_ingredients` at the certificate constant `weakCertConst`:
the certificate ingredient is `weakCommonPlan_cert` (the carrier calculus at one level and the weak ledger), the quiet atlas is
`weakStageQuietAtlas`. What remains: the shared context-envelope estimate, the quiet fast
independence, and the plan conditions (`WeakComplexContextPlanOK`, the bound on `Υ`,
the inherited weight condition `WeakInhPlanOK` of the kernel plan, and `WeakEnvPlanOK`).
`entry_coefficients_of_plan` discharges the context envelopes with `context_stage_envelopes`
and derives the bound on `Υ` from `WeakComplexContextPlanOK`. -/

open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance AVRegularity.EntryWeakProofs
open AVRegularity.WeakEntryProofs AVRegularity.Providers.WeakGen

/-- **`entry_coefficients` from the remaining ingredients.** -/
theorem entry_coefficients_of_remaining
    (basePlan : WeakCoefficientPlan)
    (hΥ : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakCoefficientRequest A),
      1 ≤ (basePlan.constants R).Υ)
    (hplan : WeakComplexContextPlanOK basePlan)
    (hLw : WeakInhPlanOK (weakKernelPlan basePlan))
    (hcontext : Construction.StageEnvelopes.ContextStageEnvelopesStatement)
    (henv : WeakEnvPlanOK (weakCommonPlan basePlan (weakCertConst basePlan))
      (weakEnvelopeEstimates hcontext))
    (hI12 : WeakStageIndependenceStatement (weakCommonPlan basePlan (weakCertConst basePlan))
      (weakGenEncodingChoice (weakCommonPlan basePlan (weakCertConst basePlan))
        (weakCertConst basePlan)))
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw : ℕ) (τ T₀ Pw η₀ : ℝ), 1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < η₀ →
      η₀ ≤ ocDelta α q / 8 →
    ∀ (Nw Rw Lw : ℕ), 1 ≤ Nw → Lw ≤ Jw * Nw →
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) → ∃ L₀ : ℕ,
    ∀ (L Kw sX sZ : ℕ) (nW : ℕ+) (kReq : InvConsts), 1 ≤ kReq.G0 → L₀ ≤ L → L + 1 ≤ 2 * (nW : ℕ) →
      Lw + 5 ≤ Kw →
    ∀ cK : ℝ, 0 < cK → cK ≤ 1 →
    ∃ (CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), kW.c₀ = cK ∧ IsWeakAllocation kW kReq L ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + Jw * Nw ≤ Dm →
    ∀ (P : ProvParams),
      (∃ stage : ℕ → GenStage D ScalarH Dm bw j₀, IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage) ∧
      ∀ stage : ℕ → GenStage D ScalarH Dm bw j₀, IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage →
      ∃ (Gw : GenStage D ScalarH Dm bw j₀) (rootM rootR : ℕ → ℝ) (ι : CompIn (stage M).comps ≃ CompIn Gw.comps),
        IsWeakEncoding Nw Jw η₀ rootM rootR (stage M) Gw ι ∧ (∀ r, 0 < rootM r) ∧ (∀ r, 0 < rootR r) ∧
      ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
      ∀ a aM : ℝ, a ≤ aM → aM ≤ a + 6 * Jw * ocTauPP α q Λ (M + 1) →
        IsWeakStage law P φ₀ hφ₀ M (M + Jw) Jw (Jw * Rw) (1 + Jw * Nw) nW kW a T₀ σw CL Cχ (weakChi α q η₀)
          Gw aM :=
  entry_coefficients_of_ingredients basePlan (weakCertConst basePlan) hΥ hplan
    (weakCommonPlan_cert basePlan hplan hLw) hcontext henv
    (weakStageQuietAtlas (weakCommonPlan_complexContext basePlan _ hplan) _ _ _) hI12
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-- **`entry_coefficients` from the base plan and the quiet fast independence.** The shared context-envelope estimate is
`context_stage_envelopes`, and the bound `1 ≤ Υ` follows from the `CarrierOK` of the carrier calculus. What remains
is the quiet fast independence and the plan conditions `WeakComplexContextPlanOK`,
`WeakInhPlanOK` of the kernel plan and `WeakEnvPlanOK`. -/
theorem entry_coefficients_of_plan
    (basePlan : WeakCoefficientPlan)
    (hplan : WeakComplexContextPlanOK basePlan)
    (hLw : WeakInhPlanOK (weakKernelPlan basePlan))
    (henv : WeakEnvPlanOK (weakCommonPlan basePlan (weakCertConst basePlan))
      (weakEnvelopeEstimates Construction.StageEnvelopes.Cauchy.context_stage_envelopes))
    (hI12 : WeakStageIndependenceStatement (weakCommonPlan basePlan (weakCertConst basePlan))
      (weakGenEncodingChoice (weakCommonPlan basePlan (weakCertConst basePlan))
        (weakCertConst basePlan)))
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw : ℕ) (τ T₀ Pw η₀ : ℝ), 1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < η₀ →
      η₀ ≤ ocDelta α q / 8 →
    ∀ (Nw Rw Lw : ℕ), 1 ≤ Nw → Lw ≤ Jw * Nw →
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) → ∃ L₀ : ℕ,
    ∀ (L Kw sX sZ : ℕ) (nW : ℕ+) (kReq : InvConsts), 1 ≤ kReq.G0 → L₀ ≤ L → L + 1 ≤ 2 * (nW : ℕ) →
      Lw + 5 ≤ Kw →
    ∀ cK : ℝ, 0 < cK → cK ≤ 1 →
    ∃ (CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), kW.c₀ = cK ∧ IsWeakAllocation kW kReq L ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + Jw * Nw ≤ Dm →
    ∀ (P : ProvParams),
      (∃ stage : ℕ → GenStage D ScalarH Dm bw j₀, IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage) ∧
      ∀ stage : ℕ → GenStage D ScalarH Dm bw j₀, IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage →
      ∃ (Gw : GenStage D ScalarH Dm bw j₀) (rootM rootR : ℕ → ℝ) (ι : CompIn (stage M).comps ≃ CompIn Gw.comps),
        IsWeakEncoding Nw Jw η₀ rootM rootR (stage M) Gw ι ∧ (∀ r, 0 < rootM r) ∧ (∀ r, 0 < rootR r) ∧
      ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
      ∀ a aM : ℝ, a ≤ aM → aM ≤ a + 6 * Jw * ocTauPP α q Λ (M + 1) →
        IsWeakStage law P φ₀ hφ₀ M (M + Jw) Jw (Jw * Rw) (1 + Jw * Nw) nW kW a T₀ σw CL Cχ (weakChi α q η₀)
          Gw aM :=
  entry_coefficients_of_remaining basePlan
    (fun R => le_trans (by norm_num) ((le_max_left _ _).trans (hplan.1 R).2)) hplan hLw
    Construction.StageEnvelopes.Cauchy.context_stage_envelopes henv hI12
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
section
/-! **The base plan of the `entry_coefficients` assembly** (`weakBasePlan`), chosen in two layers.
* Numeric layer (`weakNumericPlan`): `CH = 1`, `Υ = 400`, the level threshold `j₀ + 2`, and the
  request's invariant constants with `c₀ = cK`, `G₀ - 1`, `L_ker = L`,
  `m_env = 1/(2(H_prod + 1))` and `L_* ≥ liftWt N₀ (J_wR_w) N₀`. These give the carrier calculus's condition
  (`weakBasePlan_complexContext`) and the inherited weight condition of the kernel plan
  (`weakBasePlan_inh`).
* Envelope layer: `Ca`, `Cm` and the level threshold dominate the shared context-envelope estimate
  `context_stage_envelopes` at the numeric layer's parameters (`weakBasePlan_env`). The parameters
  read only the base data, `m_env` and the reserves, never `Ca`, `Cm` or the level threshold, so
  the choice is not circular.
`entry_coefficients_of_I12`: `entry_coefficients` from the quiet fast independence alone. -/

@[expose] public noncomputable section

namespace AVRegularity.WeakEntryProofs.Assembly

open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance AVRegularity.EntryWeakProofs
open AVRegularity.WeakEntryProofs AVRegularity.Providers.WeakGen
open AVRegularity.Construction.StageEnvelopes

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}

/-! ### The numeric layer -/

/-- The invariant constants of a request, with the envelope constants `Ca` and `Cm`. -/
def weakPlanKW (R : WeakCoefficientRequest A) (Ca : ℝ) (Cm : ℕ → ℝ) : InvConsts :=
  { R.kReq with
    c₀ := R.cK
    Ca := Ca
    mEnv := 1 / (2 * ((R.kReq.Hprod : ℝ) + 1))
    Cm := Cm
    Lker := R.L
    Lstar := max R.kReq.Lstar
      (Providers.GenSem.UEnv.liftWt (1 + A.Jw * A.Nw) (A.Jw * A.Rw) (1 + A.Jw * A.Nw))
    G0 := R.kReq.G0 - 1 }

theorem weakPlanKW_allocation (R : WeakCoefficientRequest A) (Ca : ℝ) (Cm : ℕ → ℝ) :
    IsWeakAllocation (weakPlanKW R Ca Cm) R.kReq R.L := by
  have hH : (0 : ℝ) < (R.kReq.Hprod : ℝ) + 1 := by positivity
  refine ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_max_left _ _, ?_, rfl, ?_, ?_, le_rfl⟩
  · have := R.kReq_G0
    change R.kReq.G0 - 1 + 1 ≤ R.kReq.G0
    omega
  · change (0 : ℝ) ≤ 1 / (2 * ((R.kReq.Hprod : ℝ) + 1))
    positivity
  · change 1 / (2 * ((R.kReq.Hprod : ℝ) + 1)) < 1 / ((R.kReq.Hprod : ℝ) + 1)
    exact one_div_lt_one_div_of_lt hH (by linarith)

/-- The plan constants of a request, with the envelope constants `Ca` and `Cm`. -/
def weakPlanConstants (R : WeakCoefficientRequest A) (Ca : ℝ) (Cm : ℕ → ℝ) :
    WeakCoefficientConstants R where
  CK := 1
  CL := 1
  Cχ := 1
  Cread := 1
  Cid := 1
  kW := weakPlanKW R Ca Cm
  radius := rfl
  allocation := weakPlanKW_allocation R Ca Cm
  length_one_le := le_rfl
  CH := 1
  Υ := 400
  history_one_le := le_rfl
  chain_pos := by norm_num

/-- **The numeric layer.** -/
def weakNumericPlan : WeakCoefficientPlan where
  baseThreshold _ := 128
  baseThreshold_ge _ := le_rfl
  momentThreshold _ := 0
  constants R := weakPlanConstants R 0 0
  levelThreshold _ j₀ := j₀ + 2

/-! ### The envelope layer -/

/-- The shared context-envelope estimate at the numeric layer's parameters. -/
def weakNumericEstimate (R : WeakCoefficientRequest A) (hΛ : 128 ≤ A.Λ) :
    ContextEnvelopeEstimate (weakEnvelopeParameters weakNumericPlan R hΛ) :=
  weakEnvelopeEstimates Cauchy.context_stage_envelopes _

/-- The analytic envelope constant of the base plan. -/
def weakEnvCa (R : WeakCoefficientRequest A) : ℝ :=
  if hΛ : 128 ≤ A.Λ then (weakNumericEstimate R hΛ).Ca else 0

/-- The molecular envelope constants of the base plan. -/
def weakEnvCm (R : WeakCoefficientRequest A) (j : ℕ) : ℝ :=
  if hΛ : 128 ≤ A.Λ then (weakNumericEstimate R hΛ).Cm j else 0

/-- The envelope part of the level threshold: the estimate's floor and the length floor. -/
def weakEnvLevel (R : WeakCoefficientRequest A) : ℕ :=
  max (if hΛ : 128 ≤ A.Λ then (weakNumericEstimate R hΛ).levelFloor else 0)
    (if hK : weakKernelBaseThreshold B ≤ A.Λ then weakEnvelopeLengthFloor R hK else 0)

/-- **The base plan** of the `entry_coefficients` assembly. -/
def weakBasePlan : WeakCoefficientPlan where
  baseThreshold _ := 128
  baseThreshold_ge _ := le_rfl
  momentThreshold _ := 0
  constants R := weakPlanConstants R (weakEnvCa R) (weakEnvCm R)
  levelThreshold R j₀ := max (j₀ + 2) (weakEnvLevel R)

/-! ### The plan conditions -/

/-- The carrier calculus's plan condition: `CarrierOK 100 1 400` and the level threshold `≥ j₀ + 2`. -/
theorem weakBasePlan_complexContext : WeakComplexContextPlanOK weakBasePlan := by
  refine ⟨fun R => ⟨le_rfl, ?_⟩, fun R j₀ => le_max_left _ _⟩
  change max (100 : ℝ) (4 * (8 * Real.pi ^ 2)) ≤ 400
  have h2 : Real.pi ^ 2 < (3.15 : ℝ) ^ 2 := by
    have := Real.pi_lt_d2
    gcongr
  exact max_le (by norm_num) (by norm_num at h2 ⊢; linarith)

/-- The inherited weight condition of the kernel plan, which keeps `L_*`. -/
theorem weakBasePlan_inh : WeakInhPlanOK (weakKernelPlan weakBasePlan) :=
  fun _ => le_max_right _ _

/-- The envelope condition of the common plan. The common plan keeps `m_env`, the reserves, `Ca`
and `Cm`, and only raises the base and level thresholds. -/
theorem weakBasePlan_env :
    WeakEnvPlanOK (weakCommonPlan weakBasePlan (weakCertConst weakBasePlan))
      (weakEnvelopeEstimates Cauchy.context_stage_envelopes) := by
  refine ⟨fun _ => le_max_right _ _, ?_⟩
  intro B A R hΛ
  have h128 : 128 ≤ A.Λ :=
    ((weakCommonPlan weakBasePlan (weakCertConst weakBasePlan)).baseThreshold_ge B).trans hΛ
  dsimp only
  refine ⟨?_, fun j => ?_, fun j₀ => ⟨?_, fun hK => ?_⟩⟩
  · change _ ≤ weakEnvCa R
    unfold weakEnvCa
    rw [dite_eq_left h128]
    exact le_rfl
  · change _ ≤ weakEnvCm R j
    unfold weakEnvCm
    rw [dite_eq_left h128]
    exact le_rfl
  · have h1 : (weakNumericEstimate R h128).levelFloor ≤ weakEnvLevel R := by
      unfold weakEnvLevel
      rw [dite_eq_left h128]
      exact le_max_left _ _
    exact (h1.trans (le_max_right _ _)).trans ((le_max_left _ _).trans (le_max_left _ _))
  · have h1 : weakEnvelopeLengthFloor R hK ≤ weakEnvLevel R := by
      unfold weakEnvLevel
      rw [dite_eq_left hK]
      exact le_max_right _ _
    exact (h1.trans (le_max_right _ _)).trans ((le_max_left _ _).trans (le_max_left _ _))

/-! ### The quiet independence at the base plan -/

/-- Holomorphic generation descends along every construction of the common plan (the generation ingredient, from the
certificate ingredient). -/
theorem weakBasePlan_gen :
    WeakPassageGenStatement (weakCommonPlan weakBasePlan (weakCertConst weakBasePlan)) := by
  have hcert := weakPassageCert_of_one
    (weakCommonPlan_cert weakBasePlan weakBasePlan_complexContext weakBasePlan_inh)
  intro c i hi hiJ _
  have hW := weakCertified_stage c hcert (c.inst.M + c.inst.physical.Jw - (i - 1)) (by omega)
  rw [show c.inst.M + c.inst.physical.Jw - (c.inst.M + c.inst.physical.Jw - (i - 1)) = i - 1
    by omega] at hW
  exact hW.2.weakHolGen

/-- **The quiet fast independence at the base plan** (on the trimmed quiet times). -/
theorem weakBasePlan_I12 :
    WeakStageIndependenceStatement (weakCommonPlan weakBasePlan (weakCertConst weakBasePlan))
      (weakGenEncodingChoice (weakCommonPlan weakBasePlan (weakCertConst weakBasePlan))
        (weakCertConst weakBasePlan)) := by
  have hplan := weakCommonPlan_complexContext weakBasePlan (weakCertConst weakBasePlan) weakBasePlan_complexContext
  have hΥ : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
      (R : WeakCoefficientRequest A),
      1 ≤ ((weakCommonPlan weakBasePlan (weakCertConst weakBasePlan)).constants R).Υ :=
    fun R => le_trans (by norm_num) ((le_max_left _ _).trans (hplan.1 R).2)
  exact weakStageIndependence hplan _ _ _ fun c =>
    weakGen_stage_slot_laws _ hΥ weakBasePlan_gen c c.inst.M le_rfl (by omega)

/-! ### `entry_coefficients` up to the quiet independence -/

/-- **`entry_coefficients` from the quiet fast independence alone**, at the
base plan `weakBasePlan`. -/
theorem entry_coefficients_of_I12
    (hI12 : WeakStageIndependenceStatement (weakCommonPlan weakBasePlan (weakCertConst weakBasePlan))
      (weakGenEncodingChoice (weakCommonPlan weakBasePlan (weakCertConst weakBasePlan))
        (weakCertConst weakBasePlan)))
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw : ℕ) (τ T₀ Pw η₀ : ℝ), 1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < η₀ →
      η₀ ≤ ocDelta α q / 8 →
    ∀ (Nw Rw Lw : ℕ), 1 ≤ Nw → Lw ≤ Jw * Nw →
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) → ∃ L₀ : ℕ,
    ∀ (L Kw sX sZ : ℕ) (nW : ℕ+) (kReq : InvConsts), 1 ≤ kReq.G0 → L₀ ≤ L → L + 1 ≤ 2 * (nW : ℕ) →
      Lw + 5 ≤ Kw →
    ∀ cK : ℝ, 0 < cK → cK ≤ 1 →
    ∃ (CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), kW.c₀ = cK ∧ IsWeakAllocation kW kReq L ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + Jw * Nw ≤ Dm →
    ∀ (P : ProvParams),
      (∃ stage : ℕ → GenStage D ScalarH Dm bw j₀, IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage) ∧
      ∀ stage : ℕ → GenStage D ScalarH Dm bw j₀, IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage →
      ∃ (Gw : GenStage D ScalarH Dm bw j₀) (rootM rootR : ℕ → ℝ) (ι : CompIn (stage M).comps ≃ CompIn Gw.comps),
        IsWeakEncoding Nw Jw η₀ rootM rootR (stage M) Gw ι ∧ (∀ r, 0 < rootM r) ∧ (∀ r, 0 < rootR r) ∧
      ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
      ∀ a aM : ℝ, a ≤ aM → aM ≤ a + 6 * Jw * ocTauPP α q Λ (M + 1) →
        IsWeakStage law P φ₀ hφ₀ M (M + Jw) Jw (Jw * Rw) (1 + Jw * Nw) nW kW a T₀ σw CL Cχ (weakChi α q η₀)
          Gw aM :=
  entry_coefficients_of_plan weakBasePlan weakBasePlan_complexContext weakBasePlan_inh weakBasePlan_env hI12
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
/-! **The certified case of a weak construction.** A weak
construction on a carrier start at the common plan's constants `CH = 1`, `Υ = 400`, above the
common plan's thresholds, is a case of the common plan of `entry_coefficients`
(`weakCommonCase`, with the same stage function by definition). Its stages are holomorphically
generated (`weakCommonCase_holGen`) and carry the weak size certificate
(`weakCommonCase_certified`). The passage and entry leaves read these facts through the floor
conditions `WeakPassageCommonOK` and `WeakEntryCommonOK`. -/

@[expose] public noncomputable section

namespace AVRegularity.WeakEntryProofs.Assembly

open Homogenization AVRegularity.Providers.WeakGen

/-- The common coefficient plan of `entry_coefficients`. -/
abbrev weakCommonCoeffPlan : WeakCoefficientPlan :=
  weakCommonPlan weakBasePlan (weakCertConst weakBasePlan)

/-- The coefficient request of a passage request, at the molecular radius `1`. -/
def weakCoeffRequestOne {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) : WeakCoefficientRequest A :=
  ⟨R.L, R.Kw, R.sX, R.sZ, R.nW, R.kReq, R.request_grade, R.kernel_order, R.field_order, 1,
    one_pos, le_rfl⟩

/-- The floors of a passage plan dominate the common plan's thresholds. -/
def WeakPassageCommonOK (plan : WeakPassagePlan) : Prop :=
  (∀ B, weakCommonCoeffPlan.baseThreshold B ≤ plan.baseFloor B) ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) (j₀ : ℕ),
    weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne R) j₀ ≤ plan.levelFloor R j₀

/-- The floors of an entry glue plan dominate the common plan's thresholds. -/
def WeakEntryCommonOK (plan : WeakEntryGluePlan) : Prop :=
  (∀ B, weakCommonCoeffPlan.baseThreshold B ≤ plan.baseFloor B) ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (j₀ : ℕ),
    weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne R) j₀ ≤ plan.levelFloor R C j₀

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}

/-- **The certified case** of a weak construction on a carrier start at `CH = 1`, `Υ = 400`. -/
def weakCommonCase (R : WeakPassageRequest A) (hbase : weakCommonCoeffPlan.baseThreshold B ≤ A.Λ)
    (j₀ : ℕ) (hcar : IsCarrierStart B.α B.q A.Λ A.bw 1 400 j₀) (M : ℕ)
    (hlev : weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne R) j₀ ≤ M) (D : OCData)
    (hα : D.α = B.α) (hq : D.q = B.q) (hΛ : D.Λ = A.Λ) (hζ : D.ζ = B.ζ)
    (hs : IsOCStreamSeq B.α B.q A.Λ B.ζ D.Φ) (hb : IsOCBandChain B.α B.q A.Λ B.ζ M D.κ)
    (ht : D.term = M) (Dm : ℕ) (hDm : 1 + A.Jw * A.Nw ≤ Dm) (P : ProvParams)
    (stage : ℕ → GenStage D ScalarH Dm A.bw j₀)
    (hc : IsWeakConstruction D P (⟨A.Nw, A.Rw, R.sX, R.sZ, A.η₀, M + A.Jw⟩ : WeakMenu) M A.Jw
      (D.termRW A.σw M) 0 stage) :
    WeakCoefficientCase weakCommonCoeffPlan :=
  ⟨⟨B, A, weakCoeffRequestOne R, hbase, Nat.zero_le _, j₀, hcar, M, hlev, D, hα, hq, hΛ, hζ, hs,
    hb, ht, Dm, hDm, P⟩, stage, hc⟩

/-- **The stages of the certified case are holomorphically generated.** -/
theorem weakCommonCase_holGen (R : WeakPassageRequest A)
    (hbase : weakCommonCoeffPlan.baseThreshold B ≤ A.Λ) (j₀ : ℕ)
    (hcar : IsCarrierStart B.α B.q A.Λ A.bw 1 400 j₀) (M : ℕ)
    (hlev : weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne R) j₀ ≤ M) (D : OCData)
    (hα : D.α = B.α) (hq : D.q = B.q) (hΛ : D.Λ = A.Λ) (hζ : D.ζ = B.ζ)
    (hs : IsOCStreamSeq B.α B.q A.Λ B.ζ D.Φ) (hb : IsOCBandChain B.α B.q A.Λ B.ζ M D.κ)
    (ht : D.term = M) (Dm : ℕ) (hDm : 1 + A.Jw * A.Nw ≤ Dm) (P : ProvParams)
    (stage : ℕ → GenStage D ScalarH Dm A.bw j₀)
    (hc : IsWeakConstruction D P (⟨A.Nw, A.Rw, R.sX, R.sZ, A.η₀, M + A.Jw⟩ : WeakMenu) M A.Jw
      (D.termRW A.σw M) 0 stage) (i : ℕ) (hi : M ≤ i) (hiJ : i ≤ M + A.Jw) :
    WeakHolGen (stage i) := by
  have h : WeakHolGen (stage (M + A.Jw - (M + A.Jw - i))) := weakHolGen_stage
    (weakCommonCase R hbase j₀ hcar M hlev D hα hq hΛ hζ hs hb ht Dm hDm P stage hc)
    weakBasePlan_gen (M + A.Jw - i) (show M + A.Jw - i ≤ A.Jw by omega)
  rwa [show M + A.Jw - (M + A.Jw - i) = i by omega] at h

/-- **The stages of the certified case carry the weak size certificate** (the certificate ingredient at the common plan,
with the constants `K_c^k(1)`, `K_c = weakCertConst weakBasePlan`). -/
theorem weakCommonCase_certified (R : WeakPassageRequest A)
    (hbase : weakCommonCoeffPlan.baseThreshold B ≤ A.Λ) (j₀ : ℕ)
    (hcar : IsCarrierStart B.α B.q A.Λ A.bw 1 400 j₀) (M : ℕ)
    (hlev : weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne R) j₀ ≤ M) (D : OCData)
    (hα : D.α = B.α) (hq : D.q = B.q) (hΛ : D.Λ = A.Λ) (hζ : D.ζ = B.ζ)
    (hs : IsOCStreamSeq B.α B.q A.Λ B.ζ D.Φ) (hb : IsOCBandChain B.α B.q A.Λ B.ζ M D.κ)
    (ht : D.term = M) (Dm : ℕ) (hDm : 1 + A.Jw * A.Nw ≤ Dm) (P : ProvParams)
    (stage : ℕ → GenStage D ScalarH Dm A.bw j₀)
    (hc : IsWeakConstruction D P (⟨A.Nw, A.Rw, R.sX, R.sZ, A.η₀, M + A.Jw⟩ : WeakMenu) M A.Jw
      (D.termRW A.σw M) 0 stage) (k : ℕ) (hk : k ≤ A.Jw) :
    let c := weakCommonCase R hbase j₀ hcar M hlev D hα hq hΛ hζ hs hb ht Dm hDm P stage hc
    0 ≤ (weakCertConst weakBasePlan c.inst.request)^[k] 1 ∧
      WeakCertified ((weakCertConst weakBasePlan c.inst.request)^[k] 1)
        (weakReserve c.inst (M + A.Jw - k)) (weakWeight c.inst (M + A.Jw - k))
        (stage (M + A.Jw - k)) :=
  weakCertified_stage _ (weakPassageCert_of_one
    (weakCommonPlan_cert weakBasePlan weakBasePlan_complexContext weakBasePlan_inh)) k hk

end AVRegularity.WeakEntryProofs.Assembly
end
end
end
