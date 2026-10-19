-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.InitialValue.Cascade
public import AVRegularity.Definitions.Entry.TerminalResidualClauses
import AVRegularity.Construction.EntryScales.TerminalCore
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
import AVRegularity.CycleWords.Assembly.MixedWordsB1SharpBlocks
import AVRegularity.CycleWords.Interior.NegativeAdjoint
public import AVRegularity.Definitions.CycleWords.ScalarPackage
public import AVRegularity.Statements.Intermediate.CycleEvolution.IsMetricNearIdentity

section
/-! Proof of `entry_terminal_initial_value`: at the start `tp` the covariance
primitive vanishes, so the dual readout image is the readout itself, which is the terminal datum
`g` on the weak components (their roots have no births); the remaining clauses are the lifted
field relation at `tp` and an algebraic identity. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

namespace InitialValue

theorem covPolyP_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℕ)
    (φ : Vec 2 → E) : covPolyP (0 : Matrix (Fin 2) (Fin 2) ℝ) p φ = φ := by
  have h0 : ∀ ψ : Vec 2 → E, covOperator (0 : Matrix (Fin 2) (Fin 2) ℝ) ψ = 0 := by
    intro ψ; funext x; simp [covOperator]
  unfold covPolyP
  rw [Finset.sum_range_succ']
  have hz : ∀ l ∈ Finset.range p, ((((l + 1).factorial : ℝ))⁻¹) •
      (covOperator (0 : Matrix (Fin 2) (Fin 2) ℝ))^[l + 1] φ = 0 := by
    intro l _
    rw [Function.iterate_succ_apply', h0, smul_zero]
  rw [Finset.sum_eq_zero hz]
  simp

theorem readout_terminal {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (Gw Gt : GenStage D ScalarH Dm b j₀) (M Kout : ℕ) (E η₀ : ℝ)
    (hroot : ∀ v : CompIn Gw.comps, v.1.births = []) (hsub : Gw.comps ⊆ Gt.comps)
    (g : ∀ v : CompIn Gw.comps, TorusHk Kout (ScalarH v.1.root))
    (Z₀ : ∀ v : CompIn Gt.comps, TorusHk Kout (ScalarH v.1.root))
    (htr : IsTerminalTrace Gw Gt g Z₀) (v : CompIn Gw.comps) :
    succReadout (hr := ScalarH) M E η₀ Kout Z₀ v = g v := by
  have hpar : ∀ c : Comp, c.births = [] → compParent M c = c := by
    intro c hc; unfold compParent; rw [hc]
  have hword : ∀ c : Comp, c.births = [] → compWord M c = [] := by
    intro c hc; unfold compWord; rw [hc]
  unfold succReadout
  rw [Finset.sum_eq_single (⟨v.1, hsub v.2⟩ : CompIn Gt.comps)]
  · rw [dite_eq_left_of_eq_true (eq_true (hpar v.1 (hroot v)))]
    rw [hword v.1 (hroot v)]
    simp only [List.length_nil, Nat.cast_zero, mul_zero, Real.rpow_zero, one_smul]
    rw [htr.1 ⟨v.1, hsub v.2⟩ v.2]
    rfl
  · intro v' _ hne
    by_cases hv : v'.1 ∈ Gw.comps
    · have hneq : ¬ compParent M v'.1 = v.1 := by
        intro h
        apply hne
        apply Subtype.ext
        rw [← h, hpar v'.1 (hroot ⟨v'.1, hv⟩)]
      rw [dite_eq_right_of_eq_false (eq_false hneq)]
    · rw [htr.2 v' hv]
      split_ifs <;> simp
  · intro h; exact absurd (Finset.mem_univ _) h

theorem termCovPrimitive_self (D : OCData) (M : ℕ) (t : ℝ) : termCovPrimitive D M t t = 0 := by
  ext i j
  simp [termCovPrimitive, ocCovariance]

end InitialValue

end AVRegularity

namespace AVRegularity.Providers

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The initial value of the terminal comparison**. -/
theorem entry_terminal_initial_value (Gw Gt : GenStage D ScalarH Dm b j₀) (M p Kout N depth sX sZ : ℕ)
    (η₀ tp tf cr : ℝ) (htp : tp ≤ tf) (hroot : ∀ v : CompIn Gw.comps, v.1.births = [])
    (hsub : Gw.comps ⊆ Gt.comps)
    (g : ∀ v : CompIn Gw.comps, TorusHk Kout (ScalarH v.1.root))
    (Z₀ : ∀ v : CompIn Gt.comps, TorusHk Kout (ScalarH v.1.root))
    (Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk Kout (ScalarH v.1.root))
    (htr : IsTerminalTrace Gw Gt g Z₀) (hZ : ∀ v, Z v tp = Z₀ v)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
    (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kout - 2 * p) (ScalarH v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
    (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (hlift : IsTerminalLiftedField Gw Gt M p Kout N depth sX sZ η₀ tp tf cr Z CcT PZ aRep û) :
    (∀ v, PZ v tp = truncateTorusHk (Nat.sub_le Kout (2 * p)) (g v)) ∧
    (∀ v, IsClassicalRep (truncateTorusHk (Nat.sub_le Kout (2 * p)) (g v)) (fun x => aRep tp x v)
      (Kout - 2 * p)) ∧
    (∀ v, (û v tp).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => termLiftedRep Gw M N depth cr CcT aRep tp x v) ∧
    ∀ v (V₀ : TorusHk 0 (ScalarH v.1.root)),
      V₀ - û v tp = (V₀ - truncateTorusHk (Nat.zero_le Kout) (g v)) -
        (û v tp - truncateTorusHk (Nat.zero_le Kout) (g v)) := by
  obtain ⟨-, hcov, hû⟩ := hlift
  have htp' : tp ∈ Set.Icc tp tf := ⟨le_rfl, htp⟩
  have hread : ∀ v, succReadout (hr := ScalarH) M (D.eps (M - 1)) η₀ Kout
      (fun v' => Z v' tp) v = g v := by
    intro v
    have : (fun v' => Z v' tp) = Z₀ := funext hZ
    rw [this]
    exact InitialValue.readout_terminal Gw Gt M Kout _ η₀ hroot hsub g Z₀ htr v
  have h1 : ∀ v, PZ v tp = truncateTorusHk (Nat.sub_le Kout (2 * p)) (g v) := by
    intro v
    have hc := (hcov v tp htp').1
    rw [hread v, InitialValue.termCovPrimitive_self] at hc
    apply InitialValue.torusHk_ext_of_jet_ae
    have htr' := KernelEnergy.truncateTorusHk_toFunction_jet_ae (Nat.sub_le Kout (2 * p)) (g v)
      (valueIndex2 (Kout - 2 * p))
    refine (InitialValue.ae_eq_of_cellInner_eq (InitialValue.torusHk_integrableOn_jet _ _)
      (InitialValue.torusHk_integrableOn_jet (g v) _) fun φ hφ hφp => ?_).trans htr'.symm
    rw [hc φ hφ hφp, InitialValue.covPolyP_zero]
    rfl
  refine ⟨h1, fun v => ?_, fun v => hû v tp htp', fun v V₀ => by abel⟩
  rw [← h1 v]
  exact (hcov v tp htp').2

end AVRegularity.Providers
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.Providers

/-! Proof of `entry_terminal_widths`. -/

/-- **The entry widths**. -/
theorem entry_terminal_widths (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (σw tT c₀ cr : ℝ), 0 < σw → σw < min (ocC α q) (q - 1) → 0 < tT → 0 < c₀ → 0 < cr →
    ∃ (C : ℝ) (M₀ : ℕ), ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
      D.termRW σw M / rhoStar D c₀ (M - 1) ≤
          C * D.eps (M - 1) ^ (q * ocGamma α q + 4 * ocDelta α q + q * σw) ∧
        D.termRNew cr tT M / rhoStar D c₀ (M - 1) ≤ C * D.eps (M - 1) ^ (ocDelta α q + tT) ∧
        D.termRW σw M / rhoEnh D cr (M - 1) ≤
          C * D.eps (M - 2) ^ (q ^ 2 * (1 + σw) - 1 - ocC α q) ∧
        D.termRNew cr tT M / rhoEnh D cr (M - 1) ≤
          C * D.eps (M - 2) ^ (q * (1 + ocC α q + tT) - 1 - ocC α q) ∧
        3 * ocDelta α q < q ^ 2 * (1 + σw) - 1 - ocC α q ∧
        4 * ocDelta α q < q * (1 + ocC α q + tT) - 1 - ocC α q := by
  obtain ⟨Λ₀, hΛ₀, hcore⟩ := EntryScales.widths_core hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ σw tT c₀ cr hσ _hσ' ht hc₀ hcr => ?_⟩
  obtain ⟨C, hC, hM⟩ := hcore Λ hΛ σw tT c₀ cr hσ ht hc₀ hcr
  refine ⟨C, 3, fun M hM₃ D hDα hDq hDΛ _ _ hκ _ => ?_⟩
  obtain ⟨k1, k2, k3, k4⟩ := hM M hM₃ D.κ hκ
  have hε : ∀ k, D.eps k = ocEpsilon q Λ k := fun k => by
    simp only [OCData.eps, hDq, hDΛ]
  have hM2 : M - 2 = M - 1 - 1 := by omega
  have hH : D.termH M = ocTauPP α q Λ M := by
    simp only [OCData.termH, hDα, hDq, hDΛ]
  have hρ : D.termRho cr M = cr * Real.sqrt (D.κ (M - 1) * ocTauPP α q Λ M) := by
    simp only [OCData.termRho, OCData.termB, hH]
  have hρn : rhoEnh D cr (M - 1) =
      cr * Real.sqrt (D.κ (M - 1 - 1) * ocTauPP α q Λ (M - 1)) := by
    simp only [rhoEnh, hDα, hDq, hDΛ]
  have hρs : rhoStar D c₀ (M - 1) =
      c₀ * min (ocEpsilon q Λ (M - 1))
        (Real.sqrt (D.κ (M - 1) / ocA α q Λ (M - 1))) := by
    simp only [rhoStar, hε, hDα, hDq, hDΛ]
  have hRW : D.termRW σw M = ocEpsilon q Λ M ^ (1 + σw) := by
    simp only [OCData.termRW, hε]
  have hRN : D.termRNew cr tT M =
      cr * Real.sqrt (D.κ (M - 1) * ocTauPP α q Λ M) * ocEpsilon q Λ (M - 1) ^ tT := by
    simp only [OCData.termRNew, hρ, hε]
  have hgaps := EntryScales.width_exponent_gaps hα₀ hα₁ hs₀ hs₁ hq hσ ht
  rw [hRW, hRN, hρs, hρn, hε (M - 1), hε (M - 2), hM2]
  exact ⟨k1, k2, k3, k4, hgaps.1, hgaps.2⟩

end AVRegularity.Providers
end
end

section
@[expose] public section
open Filter Topology Homogenization
namespace AVRegularity.Providers

/-! Proof of `entry_terminal_scales`. -/

/-- **The terminal scales**. -/
theorem entry_terminal_scales (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    (Tendsto (fun M : ℕ => ocTauPP α q Λ (M + 1) / ocTauP α q Λ M) atTop (𝓝 0)) ∧
    ∀ cr : ℝ, 0 < cr → ∃ (C : ℝ) (M₀ : ℕ), 1 ≤ C ∧ ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
      1 ≤ D.termB M / D.termNu M ∧ D.termB M / D.termNu M ≤ 2 ∧
      D.termPe M ≤ C * D.eps M ^ ocGamma α q ∧
      C⁻¹ * D.eps (M - 1) ^ ocC α q ≤ D.termRho cr M / D.eps (M - 1) ∧
      D.termRho cr M / D.eps (M - 1) ≤ C * D.eps (M - 1) ^ ocC α q ∧
      C⁻¹ * D.eps (M - 1) ^ D.termZeta ≤ D.termEpsCell cr M ∧
      D.termEpsCell cr M ≤ C * D.eps (M - 1) ^ D.termZeta ∧
      ocA α q Λ (M - 1) * D.termH M ≤ C * D.eps (M - 1) ^ (2 * ocDelta α q) ∧
      C⁻¹ * D.eps (M - 1) ^ (-(2 * D.termZeta)) ≤ D.termH M / D.termEllSq M ∧
      D.termH M / D.termEllSq M ≤ C * D.eps (M - 1) ^ (-(2 * D.termZeta)) ∧
      C⁻¹ * D.eps (M - 1) ^ (-(2 * q * ocGamma α q + 4 * ocDelta α q)) ≤
        ocTau α q Λ M / D.termEllSq M ∧
      D.termRho cr M = rhoEnh D cr M := by
  obtain ⟨Λ₀, hΛ₀, hcore⟩ := EntryScales.terminal_scales_core hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ => ⟨EntryScales.tauRatio_tendsto hα₀ hα₁ hs₀ hs₁ hq
    (le_trans hΛ₀ hΛ), fun cr hcr => ?_⟩⟩
  obtain ⟨C, M₀, hC, hM⟩ := hcore Λ hΛ cr hcr
  refine ⟨C, M₀, hC, fun M hM₀ D hDα hDq hDΛ _ _ hκ _ => ?_⟩
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := hM M hM₀ D.κ hκ
  have hε : ∀ k, D.eps k = ocEpsilon q Λ k := fun k => by
    simp only [OCData.eps, hDq, hDΛ]
  have hZ : D.termZeta = q * ocGamma α q + 3 * ocDelta α q := by
    simp only [OCData.termZeta, hDα, hDq]
  have hH : D.termH M = ocTauPP α q Λ M := by
    simp only [OCData.termH, hDα, hDq, hDΛ]
  refine ⟨k1, k2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp only [OCData.termPe, OCData.termNu, hε, hDα]; exact k3
  · simp only [OCData.termRho, OCData.termB, hH, hε]; exact k4
  · simp only [OCData.termRho, OCData.termB, hH, hε]; exact k5
  · simp only [OCData.termEpsCell, OCData.termDstar, OCData.termRho, OCData.termB,
      OCData.termNu, hH, hZ, hε]; exact k6
  · simp only [OCData.termEpsCell, OCData.termDstar, OCData.termRho, OCData.termB,
      OCData.termNu, hH, hZ, hε]; exact k7
  · simp only [hH, hε]; exact k8
  · simp only [OCData.termEllSq, OCData.termNu, hH, hZ, hε]; exact k9
  · simp only [OCData.termEllSq, OCData.termNu, hH, hZ, hε]; exact k10
  · simp only [OCData.termEllSq, OCData.termNu, hε]; exact k11

end AVRegularity.Providers
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers

/-! Proof of `scalar_package_terminal`: the interior package at the terminal level `m = M`, with
the thresholds `Θ₀ = 3K.θs`, `1 ≤ K.θs` of the assembly, and `M₀` the level from which every
renewal block is admissible at `(Θ₀, K.θs)` (`bandChain_eventual_block_admissibility`). -/

/-- **The terminal scalar package**. -/
theorem scalar_package_terminal (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ ξ₀ ξmax c Cg : ℝ, 0 < g₀ ∧ 0 < ξmax ∧
      ξmax < ξ₀ ∧ 0 < c ∧ 0 < Cg ∧
      ∀ ξlo : ℝ, 0 < ξlo → 2 * ξlo ≤ ξmax →
      ∃ (K : ScalarConstants) (Θ₀ : ℝ) (M₀ : ℕ), K.ξlo = ξlo ∧ K.g0 = g₀ ∧ K.ξ0 = ξ₀ ∧ K.Cg = Cg ∧
        K.cGauss = c ∧ 1 ≤ Θ₀ ∧
        ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
          2 ≤ M → M₀ ≤ M → ∀ ν B : ℝ, κ M = ν → κ (M - 1) = B →
          (∀ l : ℤ, IsOCAdmissibleInterval α q Λ ζ M ν B Θ₀ K.θs
            (((l : ℝ) - 1 / 2) * ocTauPP α q Λ M) (ocTauPP α q Λ M)) ∧
          ∀ y₀ : Vec 2, ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ),
            IsCellMetric (fun t _ => G t) → 0 ≤ g → g ≤ K.g0 →
            IsMetricNearIdentity (fun t _ => G t) g →
            IsCellDrift (ocCellDrift α q Λ ζ M ν y₀) ∧
            (∀ t (k : Fin 2),
              cellMean (fun x => (ocCellDrift α q Λ ζ M ν y₀ t x k : ℂ)) = 0) ∧
            (∀ t, ContDiff ℝ (⊤ : ℕ∞) (ocCellDrift α q Λ ζ M ν y₀ t)) ∧
            (∀ t x, Real.sqrt (ν / B) *
              Real.sqrt (∑ i, ocCellDrift α q Λ ζ M ν y₀ t x i ^ 2) ≤ K.Cw) ∧
            (∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j
              (fun z' => Real.sqrt (ν / B) • ocCellDrift α q Λ ζ M ν y₀ t z') z‖ ≤ K.Cvj j) ∧
            ∀ ta T : ℝ, IsOCAdmissibleInterval α q Λ ζ M ν B Θ₀ K.θs ta T →
              ∃ reg : BlockRegions,
                (∀ t ∈ Set.Icc (ta / ocEll q Λ M ν ^ 2) ((ta + T) / ocEll q Λ M ν ^ 2),
                  t ∈ reg.quiet ↔
                    ∀ s ∈ Set.Icc (t - ocTau α q Λ M / (24 * ocEll q Λ M ν ^ 2))
                        (t + ocTau α q Λ M / (24 * ocEll q Λ M ν ^ 2)),
                      ∀ z, ocCellDrift α q Λ ζ M ν y₀ s z = 0) ∧
                (∀ p, ∃ k : ℤ, Odd k ∧
                  (∀ t ∈ Set.Icc (reg.lo p) (reg.hi p),
                    |ocEll q Λ M ν ^ 2 * t - k * ocTau α q Λ M| ≤ 3 / 4 * ocTau α q Λ M) ∧
                  reg.orient p = (if k % 4 = 3 then 0 else 1)) ∧
                ((∀ t ∈ Set.Icc (ta / ocEll q Λ M ν ^ 2 - ocTau α q Λ M / (24 * ocEll q Λ M ν ^ 2))
                      (ta / ocEll q Λ M ν ^ 2 + 7 * ocTau α q Λ M / (24 * ocEll q Λ M ν ^ 2)) ∪
                    Set.Icc ((ta + T) / ocEll q Λ M ν ^ 2 - 7 * ocTau α q Λ M / (24 * ocEll q Λ M ν ^ 2))
                      ((ta + T) / ocEll q Λ M ν ^ 2 + ocTau α q Λ M / (24 * ocEll q Λ M ν ^ 2)),
                    ∀ z, ocCellDrift α q Λ ζ M ν y₀ t z = 0) →
                  min (ocTau α q Λ M / (4 * ocEll q Λ M ν ^ 2)) (T / ocEll q Λ M ν ^ 2) ≤
                    reg.buffer) ∧
                (reg.joins : ℝ) ≤ T / ocTau α q Λ M + 4 ∧
                Nonempty (ScalarPackage K (ν / B) G (ocCellDrift α q Λ ζ M ν y₀)
                  (ta / ocEll q Λ M ν ^ 2) (T / ocEll q Λ M ν ^ 2)
                  (Real.sqrt ((ν / B) / (T / ocEll q Λ M ν ^ 2))) reg) := by
  obtain ⟨Λ₁, h128, hint⟩ := CycleWords.Assembly.scalar_package_interior_thresholds_of_ingredients
    CycleWords.Interior.interiorDriftScale CycleWords.Interior.cellQuietGap
    CycleWords.Interior.interiorHighSmoothing CycleWords.Interior.cellChartWeights
    CycleWords.Interior.cellNegativeAdjoint α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λb, -, hblock⟩ :=
    CycleDamping.bandChain_eventual_block_admissibility hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λ₁ Λb, h128.trans (le_max_left _ _), fun Λ hΛ => ?_⟩
  obtain ⟨g₀, ξ₀, ξmax, c, Cg, h1, h2, h3, h4, h5, hξ⟩ := hint Λ ((le_max_left _ _).trans hΛ)
  refine ⟨g₀, ξ₀, ξmax, c, Cg, h1, h2, h3, h4, h5, fun ξlo hlo hξlo => ?_⟩
  obtain ⟨K, Θ₀, e1, e2, e3, e4, e5, hΘ, hΘeq, hθ, hpkg⟩ := hξ ξlo hlo hξlo
  obtain ⟨mStar, hm⟩ := hblock Λ ((le_max_right _ _).trans hΛ) Θ₀ K.θs hΘ (by linarith)
    (by linarith)
  refine ⟨K, Θ₀, mStar, e1, e2, e3, e4, e5, hΘ, ?_⟩
  intro M κ hband hM2 hMM ν B hν hB
  exact ⟨fun l => hm M κ hband M hM2 hMM le_rfl ν B hν hB l,
    hpkg M κ hband M hM2 le_rfl ν B hν hB⟩

end AVRegularity.Providers
end
end
