-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.EntryWeak.WeakReduction
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
import AVRegularity.EntryWeakAssembly.Assembly.WeakReadoutBound

section
@[expose] public section
open Homogenization
namespace AVRegularity.Providers

/-! Proof of `entry_weak_scales`. -/

/-- **The weak scales**. -/
theorem entry_weak_scales (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ Jw : ℕ, ∃ (C : ℝ) (M₀ : ℕ), 1 ≤ C ∧
    ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ i : ℕ, M < i → i ≤ M + Jw →
      D.weakPe i ≤ C * D.eps (i - 1) ^ weakAStar α q ∧
      ocA α q Λ (i - 1) * D.eps (i - 1) ^ 2 / D.κ M ≤ C * D.eps (i - 1) ^ ocGamma α q ∧
      D.eps (i - 1) ^ 2 / (D.κ M * ocTauP α q Λ i) ≤
        C * D.eps (i - 1) ^ (ocGamma α q - 3 * ocDelta α q) ∧
      C⁻¹ * D.eps (i - 1) ^ (-(2 * (q - 1) + ocGamma α q - 4 * ocDelta α q)) ≤
        D.κ M * ocTau α q Λ i / D.eps i ^ 2 ∧
      ocTauPP α q Λ (i + 1) / ocTauP α q Λ i ≤
        C * D.eps (i - 1) ^ (q * ocGamma α q + (2 * q + 5) * ocDelta α q) := by
  obtain ⟨C, hC, hcore⟩ := EntryScales.weak_scales_core hα₀ hα₁ hs₀ hs₁ hq
  refine ⟨128, le_refl _, fun Λ hΛ Jw => ⟨C, 0, hC, ?_⟩⟩
  intro M _ D hDα hDq hDΛ _ _ hκ hterm i hMi _
  have hε : ∀ k, D.eps k = ocEpsilon q Λ k := fun k => by
    simp only [OCData.eps, hDq, hDΛ]
  have hkap : D.kap i = D.κ M := by
    simp only [OCData.kap, hterm]
    exact congrArg D.κ (min_eq_right hMi.le)
  obtain ⟨k1, k2, k3, k4, k5⟩ := hcore Λ hΛ M (D.κ M) hκ.1 i hMi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [OCData.weakPe, hkap, hε, hDα, weakAStar]
    exact k1
  · simp only [hε]; exact k2
  · simp only [hε]; exact k3
  · simp only [hε]; exact k4
  · simp only [hε]; exact k5

end AVRegularity.Providers
end
end

section
@[expose] public section

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance AVRegularity.EntryWeakProofs
open AVRegularity.WeakEntryProofs.Assembly
namespace AVRegularity.Providers

/-! Proof of `entry_coefficients`: the exact assembly `entry_coefficients_of_I12` at the base plan
`weakBasePlan`, with the quiet fast independence proved on the trimmed quiet times
(`weakBasePlan_I12`). -/

/-- **The weak-stage coefficients** (Lemma 14.4(b) of the paper). -/
theorem entry_coefficients
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
  entry_coefficients_of_I12 weakBasePlan_I12 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.Providers
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.WeakEntryProofs.Assembly
namespace AVRegularity.Providers

/-! Proof of `weak_passage_quiet_trace`: the exact assembly
`weak_passage_quiet_trace_of_ingredients` at the joint plan
`weakQuietJointPlan weakQuietBasePlan weakQuietBasePrices`, on which both layers are proved:
- the parent-scale coefficient jets on the middle half of the slow quiet margin
  (`weak_quiet_coefficient`);
- the finite ordered-source-path smoothing (`weak_quiet_smoothing_of_plan_conditions`).
The carrier constants are `(1, 400)`. -/

/-- **The quiet margin trace of a weak passage**. -/
theorem weak_passage_quiet_trace (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
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
    ∃ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts),
      0 < cK ∧ kW.c₀ = cK ∧ IsWeakAllocation kW kReq L ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + Jw * Nw ≤ Dm →
    ∀ (P : ProvParams) (stage : ℕ → GenStage D ScalarH Dm bw j₀),
      IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage →
    ∀ (a : ℝ) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
      IsWeakSolutionOn (streamVel (D.Φ (M + Jw))) (D.κ M) a (a + T₀) f θ →
    ∀ (tq : ℕ → ℝ)
      (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk Kw (ScalarH v.1.root))
      (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
      (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ → TorusHk (Kw + Dm - 1) (ScalarH u.1.root)),
      IsWeakReduction P φ₀ hφ₀ nW M Jw Kw 0 a (a + T₀) θ stage tq Ur Urw Urk →
    ∀ i : ℕ, M < i → i ≤ M + Jw → ∀ B : ℝ,
      (∀ t ∈ Set.Icc (tq (i + 1)) (tq i),
        weightedNorm 1 (fun v => weakMass D Nw Jw η₀ v.1) (fun _ => 1)
          (fun v => truncateTorusHk (Nat.zero_le Kw) (Ur i v t)) ≤ B) →
      weightedNorm (cK * D.eps (i - 1)) (fun v => weakMass D Nw Jw η₀ v.1) (fun _ => 1)
          (fun v => Ur i v (tq i)) ≤ CK * B :=
  weak_passage_quiet_trace_statement α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.Providers
end
end
end
