-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeak.UniformWeakPhysicalCoefficientProduction
public import AVRegularity.Definitions.EntryWeak.WeakReduction
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain

/-! Genuine positive-response coefficient production for every supplied weak menu. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryWeakProofs
namespace AVRegularity.Providers

/-- **request tuple**. -/
theorem entry_weak_coefficient_bound (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (_hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw : ℕ) (τ T₀ Pw η₀ : ℝ), 1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < η₀ →
      η₀ ≤ ocDelta α q / 8 →
    ∀ (Nw Rw Lw : ℕ), 1 ≤ Nw → Lw ≤ Jw * Nw →
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) → ∃ L₀ : ℕ,
    ∀ (L Kw sX sZ : ℕ) (nW : ℕ+) (kReq : InvConsts), 1 ≤ kReq.G0 → L₀ ≤ L → L + 1 ≤ 2 * (nW : ℕ) →
      Lw + 5 ≤ Kw →
    ∃ (cK CK _CL _Cχ _Cread _Cid : ℝ) (kW : InvConsts),
      0 < cK ∧ kW.c₀ = cK ∧ IsWeakAllocation kW kReq L ∧
    ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + Jw * Nw ≤ Dm →
    ∀ (P : ProvParams) (stage : ℕ → GenStage D ScalarH Dm bw j₀),
      IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage →
    ∀ i : ℕ, M ≤ i → i < M + Jw →
    ∀ (v u : CompIn (stage i).comps) (γ : (stage i).fam.Γ v u) (d k : ℕ), 2 ≤ d →
      d ≤ ((stage i).fam.identity v u γ).maxOrder → k ≤ kW.Ks →
    ∀ t₀ t₁ : ℝ,
      coefficientSeminorm (cK * D.eps i) k t₀ t₁ ((stage i).physCoeff v u γ d) ≤
        ENNReal.ofReal (CK * ((stage i).fam.identity v u γ).record.size * D.κ M *
          D.eps (i + 1) ^ (((stage i).fam.identity v u γ).maxOrder - 2) *
          D.eps i ^ ((d : ℝ) - (((stage i).fam.identity v u γ).maxOrder : ℝ))) := by
  refine ⟨128, le_rfl, ?_⟩
  intro Λ hΛ _φ₀ _hφ₀ _hφsmooth _hφnonneg _hφmass _hφsupport bw hbw hbw₁
    Jw _τ _T₀ Pw η₀ hJ _hτ _hτT _hPw _hη _hηδ Nw Rw _Lw _hN _hL σw _hσ _hσmax
  refine ⟨Nat.ceil ((Pw + 2 * q ^ Jw + 1) / σw) + 1, ?_⟩
  intro L _Kw sX sZ _nW kReq hG0 _hL₀ _hnW _hKw
  obtain ⟨CK, _hCK, M₀, _hM₀, hprod⟩ := uniform_weak_physical_coefficient_production
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ bw hbw hbw₁ Jw Nw Rw sZ kReq.Ks hJ
  refine ⟨1, CK, 1, 1, 1, 1, requestedWeakAllocation kReq L, by norm_num, rfl,
    (requestedWeakAllocation_valid kReq L hG0).2, ?_⟩
  intro j₀
  refine ⟨M₀, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm Dm hDm P stage hc i hi hit v u γ d k hd hdn hk t₀ t₁
  have hband' : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have hs := hprod D (by rw [hterm]; exact hM) hDα hDq hDΛ hDζ hstream hband' Dm hDm j₀ stage P
    M sX 0 η₀ (D.termRW σw M) hterm hc i hi hit v u γ d k hd hdn hk t₀ t₁
  simpa only [one_mul] using hs

end AVRegularity.Providers
