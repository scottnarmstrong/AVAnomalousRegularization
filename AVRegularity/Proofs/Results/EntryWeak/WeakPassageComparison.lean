-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.WeakGen.Residual.Window.StoredFluxOnPlan
public import AVRegularity.Definitions.EntryWeak.WeakReduction
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain

@[expose] public section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Comparison
open AVRegularity.Providers.WeakGen.Window
open AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean
namespace AVRegularity.Providers

/-! Proof of `entry_weak`.

`entry_weak` is `entry_weak_of_storedFlux` at the stored-letter identity of the mean presentation
on the plan (`weakStoredMeanFlux_on_seedPlan`; both in the module
`Proofs.WeakGen.Residual.Window.StoredFluxOnPlan`): the lifted comparison
of the weak passages under the plan conditions, the passage plan
`weakTopSeedPlan`, the entry plan on it (`weakEntryLanePlan_exists`). The carrier constants are
`(1, 400)`. -/

/-- **Entry at the terminal wavelength**. Part (iv) of Proposition 14.5 of the paper follows from
it. -/
theorem entry_weak (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw : ℕ) (τ T₀ Pw η₀ : ℝ), 1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < η₀ →
      η₀ ≤ ocDelta α q / 8 →
    ∃ (Nw Rw Lw : ℕ), 1 ≤ Nw ∧ Lw = Jw * Nw ∧
      Pw + 2 * q ^ Jw + 1 + 2 < Nw * (q - 1) ∧
      Pw + 2 * q ^ Jw + 1 + q ^ Jw + 1 < 2 * weakAStar α q * (Rw + 1) ∧
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) → ∃ L₀ SX SZ : ℕ,
    ∀ (L Kw sX sZ : ℕ) (nW : ℕ+) (kReq : InvConsts), 1 ≤ kReq.G0 → L₀ ≤ L → SX ≤ sX → SZ ≤ sZ →
      L + 1 ≤ 2 * (nW : ℕ) → Lw + 5 ≤ Kw →
    ∃ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts),
      0 < cK ∧ kW.c₀ = cK ∧ IsWeakAllocation kW kReq L ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + Jw * Nw ≤ Dm →
    ∀ (P : ProvParams) (a : ℝ),
    ∃ (stage : ℕ → GenStage D ScalarH Dm bw j₀) (Gw : GenStage D ScalarH Dm bw j₀) (rootM rootR : ℕ → ℝ)
      (ι : CompIn (stage M).comps ≃ CompIn Gw.comps) (aM : ℝ)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
      (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage ∧
      IsWeakEncoding Nw Jw η₀ rootM rootR (stage M) Gw ι ∧
      (∀ r, 0 < rootM r) ∧ (∀ r, 0 < rootR r) ∧
      (∀ i, M < i → i ≤ M + Jw → IsWeakReadoutLifts i Nw (Jw * Rw) sX sZ (stage i) (CcR i)) ∧
      IsWeakReadoutChain M Jw Nw 0 η₀ (fun _ => (Jw * Rw)) stage CcR W ∧
      ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
        IsWeakStage law P φ₀ hφ₀ M (M + Jw) Jw (Jw * Rw) (1 + Jw * Nw) nW kW a T₀ σw CL Cχ (weakChi α q η₀)
          Gw aM ∧
        ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
          IsWeakSolutionOn (streamVel (D.Φ (M + Jw))) (D.κ M) a (a + T₀) f θ →
        ∃ (tq : ℕ → ℝ)
          (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk Kw (ScalarH v.1.root))
          (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
          (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ → TorusHk (Kw + Dm - 1) (ScalarH u.1.root))
          (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
          (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
          (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
          (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + Dm - 1) (ScalarH u.1.root)),
          IsWeakReduction P φ₀ hφ₀ nW M Jw Kw 0 a (a + T₀) θ stage tq Ur Urw Urk ∧
          tq (M + 1) = aM ∧ (U₀ = fun v => rerootFamily ι (Ur M) v aM) ∧ U = rerootFamily ι (Ur M) ∧
          IsWeakPaired P φ₀ hφ₀ law M Kw L nW a T₀ σw (weakChi α q η₀) cK CK f Gw aM
            U₀ U V Uw Vw Uk Vk ∧
          IsWeakReadout law M Jw Lw Kw (D.κ M) a τ T₀ s Pw cK Cread Cid f θ Gw
            (fun t g x => W M t (fun v x' => g (ι v) x') x) V :=
  entry_weak_of_storedFlux weakStoredMeanFlux_on_seedPlan α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-! Proof of `weak_passage_comparison`.

`weak_passage_comparison` is `weak_passage_comparison_of_storedFlux` at the stored-letter identity
of the mean presentation on the plan (`weakStoredMeanFlux_on_seedPlan`). The four constants `CL`,
`Cχ`, `Cread`, `Cid` of the statement's binder list do not occur in this statement; they are
written `_CL`, `_Cχ`, `_Cread`, `_Cid` (the same type up to the names of bound variables), since
the unused-variable linter reports them once the statement has a proof. The carrier constants are
`(1, 400)`. -/

/-- **One weak comparison**. -/
theorem weak_passage_comparison (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw : ℕ) (τ T₀ Pw η₀ : ℝ), 1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < η₀ →
      η₀ ≤ ocDelta α q / 8 →
    ∀ (Nw Rw Lw : ℕ), 1 ≤ Nw → Lw ≤ Jw * Nw →
      Pw + 2 * q ^ Jw + 1 + 2 < Nw * (q - 1) →
      Pw + 2 * q ^ Jw + 1 + q ^ Jw + 1 < 2 * weakAStar α q * (Rw + 1) →
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) → ∃ L₀ SX SZ : ℕ,
    ∀ (L Kw sX sZ : ℕ) (nW : ℕ+) (kReq : InvConsts), 1 ≤ kReq.G0 → L₀ ≤ L → SX ≤ sX → SZ ≤ sZ →
      L + 1 ≤ 2 * (nW : ℕ) → Lw + 5 ≤ Kw →
    ∃ (cK CK _CL _Cχ _Cread _Cid : ℝ) (kW : InvConsts),
      0 < cK ∧ kW.c₀ = cK ∧ IsWeakAllocation kW kReq L ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + Jw * Nw ≤ Dm →
    ∀ (P : ProvParams) (stage : ℕ → GenStage D ScalarH Dm bw j₀)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root)),
      IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage →
      (∀ i, M < i → i ≤ M + Jw → IsWeakReadoutLifts i Nw (Jw * Rw) sX sZ (stage i) (CcR i)) →
    ∀ (a : ℝ) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
      IsWeakSolutionOn (streamVel (D.Φ (M + Jw))) (D.κ M) a (a + T₀) f θ →
    ∀ (tq : ℕ → ℝ)
      (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk Kw (ScalarH v.1.root))
      (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
      (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ → TorusHk (Kw + Dm - 1) (ScalarH u.1.root)),
      IsWeakReduction P φ₀ hφ₀ nW M Jw Kw 0 a (a + T₀) θ stage tq Ur Urw Urk →
      a < tq (M + Jw + 1) →
    ∀ i : ℕ, M < i → i ≤ M + Jw → ∀ (Φ : ℝ) (aU : ℝ → CompIn (stage (i - 1)).comps → Vec 2 → ℝ)
      (ê : ∀ v : CompIn (stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (êw : ∀ v : CompIn (stage i).comps, ℝ → TorusHk 1 (ScalarH v.1.root)),
      (∀ t ∈ Set.Icc (tq (i + 1)) (a + T₀),
        weightedNorm 1 (fun v => weakMass D Nw Jw η₀ v.1) (fun _ => 1)
          (fun v => truncateTorusHk (Nat.zero_le Kw) (Ur i v t)) ≤ Φ) →
      (∀ v, ∀ t ∈ Set.Icc (tq i) (a + T₀), IsClassicalRep (Ur (i - 1) v t) (aU t v) Lw) →
      (∀ v, ∀ t ∈ Set.Icc (tq i) (a + T₀),
        (ê v t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict AVenhance.unitCube]
          fun x => (truncateTorusHk (Nat.zero_le Kw) (Ur i v t)).toFunction.jet (valueIndex2 0) x -
            weakGluedLift i Nw (Jw * Rw) (stage i) (CcR i) t
              (weakReadoutStep i η₀ (stage i) (stage (i - 1)) (aU t)) v x) →
      (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc (tq i) (a + T₀))),
        truncateTorusHk (Nat.le_succ 0) (êw v t) = ê v t) →
      strongEnergy 1 (D.κ M) (fun v => weakMass D Nw Jw η₀ v.1) (tq i) (a + T₀) ê êw ≤
        ENNReal.ofReal (CK * D.eps M ^ (Pw + 2 * q ^ Jw + 1) * Φ) :=
  weak_passage_comparison_of_storedFlux weakStoredMeanFlux_on_seedPlan α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.Providers
end
