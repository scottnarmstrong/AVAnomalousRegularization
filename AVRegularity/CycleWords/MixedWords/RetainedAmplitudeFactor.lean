-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.B1WWellHalf
import AVRegularity.CycleWords.MixedWords.StageExpansionLetter
import AVRegularity.CycleWords.MixedWords.SharpBlocksSameComm
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import AVRegularity.CycleWords.MixedWords.ZeroAmplitudeWordStep
import AVRegularity.CycleWords.MixedWords.WeightedPlainDecay
public import AVRegularity.CycleWords.Assembly.MixedWordsB1SharpBlocks
import AVRegularity.CycleWords.MixedWords.AdjointExists
import AVRegularity.CycleWords.MixedWords.AfwCrude
import AVRegularity.CycleWords.MixedWords.BlochContinuity

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The word fibre facts from their inputs

`wordFibreFacts_of_open`: `WordFibreFactsStatement` from its input statements, by the case
split of every frame at the threshold `C₀ P_e^{Q₀}(1+S)^{Q₀}((1+J)e^{-c₀D} + e^{-c₀D_q})`:
* poorly buffered (`≥ 1`): the crude pass (`b1w_crude_objects`, `b1w_poor_frame`);
* well buffered (`< 1`): the weighted pass (`b1w_well_half`).

Order of the constants:
* All exponents are computed at `ρ* = 2ξ_lo`, before `C_H` and `ρ`. Every `ρ` of the statement is
  at most `ρ*`, and `ρ* < ξ_0` is a field of every package. Without it, no package exists and the
  statement is vacuous.
* `Q = Q₂ + Q₀`: `Q₂` from the crude objects, `Q₀` from the well half.
* The other constants are chosen after `C_H`: `C_z = 2C_H`, `C_d` the maximum of both halves,
  `C_out = m!`, `Θ` and `C_f = 3C_d'` from the well half, and `c_E = c₀`. -/

universe u v

/-- **The word fibre facts from their inputs.** -/
theorem wordFibreFacts_of_open (hMeas : AmplitudeIdFibresMeasStatement.{u, v})
    (hMom : AmplitudeIdMomentsStatement.{u, v}) (hR : CellDriftRegularityStatement)
    (hL : LevelZeroDataStatement.{v}) (hSL : SameLevelTransformBoundStatement.{u, v})
    (hLT : LetterTransformBoundAEStatement.{u, v}) (hLB : LetterBlochStatement.{u, v})
    (hExp : StageExpansionStatement.{u, v}) (hEarly : StageTransformEarlierStatement.{u, v})
    (hZ : ZeroAmplitudeWordStatement.{u, v}) (hTO : TerminalOutputStatement.{u, v})
    (hSS : SharpSameLevelStatement.{u, v}) (hSLa : SharpLetterAEStatement.{u, v})
    (hW : WeightedSharpDecayStatement) (hSlow : SharpSlowTestStatement) :
    WordFibreFactsStatement.{u, v} := by
  rw [wordFibreFactsStatement_iff]
  intro K
  obtain ⟨gM, hgM, hMK⟩ := hMeas K
  refine ⟨gM, hgM, ?_⟩
  intro Nw D H m d Ks pos
  by_cases hK : 2 * K.ξlo < K.ξ0 ∧ 0 < K.ξlo
  swap
  · -- no package exists
    refine ⟨b1wM Nw m Ks, b1wOut Nw Ks, 0, fun β hβ => b1wOut_lt hβ, ?_⟩
    intro CH ρ _ _
    refine ⟨0, 0, 0, 0, 0, 1, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, one_pos, ?_⟩
    intro ι _ h _ _ _ _ _ _ J π letters _ η S ηg t₀ Sw ϖ a b Dq G v g reg pkg
    exact absurd ⟨pkg.consts_pos.2.2.1, pkg.consts_pos.2.1⟩ hK
  obtain ⟨hKρ, hξlo⟩ := hK
  have hρs0 : 0 ≤ 2 * K.ξlo := by positivity
  -- the exponents, at `ρ* = 2ξ_lo`
  obtain ⟨C₀, c₀, Q₀, Cad, Θ, cq, hC₀, hc₀, hCad, hΘ, hcq, hwell⟩ :=
    b1w_well_half hR hL hLB hExp hEarly hZ hTO hSS hSLa hW hSlow K Nw D m d Ks pos hKρ le_rfl
      hρs0
  obtain ⟨Q₂, _Q₃, hcr⟩ := b1w_crude_objects hR hL hSL hLT hLB hExp hEarly K Nw D m d Ks pos
    (2 * K.ξlo) hKρ le_rfl hρs0
  refine ⟨b1wM Nw m Ks, b1wOut Nw Ks, Q₂ + Q₀, fun β hβ => b1wOut_lt hβ, ?_⟩
  intro CH ρ _ hρlo
  by_cases hCH : 0 ≤ CH
  swap
  · refine ⟨0, 0, 0, 0, 0, 1, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, one_pos, ?_⟩
    intro ι _ h _ _ _ _ _ _ J π letters _ η S ηg t₀ Sw ϖ a b Dq G v g reg pkg hB _ hab _ hbS
    exfalso
    have hS : 0 < S := lt_of_lt_of_le zero_lt_one hB.hS
    have : CH * S < 0 := mul_neg_of_neg_of_pos (not_le.1 hCH) hS
    linarith
  -- the constants after `C_H`
  obtain ⟨C₂, cq', _C₃, hC₂, hcq', _hC₃, hobj⟩ := hcr CH hCH
  have hC₀0 : 0 ≤ C₀ := zero_le_one.trans hC₀
  refine ⟨2 * CH, max (max cq' (C₂ * C₀)) (cq + 3 * Cad), (m.factorial : ℝ), Θ, 3 * Cad, c₀,
    by positivity, (hcq'.trans (le_max_left _ _)).trans (le_max_left _ _), Nat.cast_nonneg _, hΘ,
    by positivity, hc₀, ?_⟩
  intro ι _ h _ _ _ _ _ _ J π letters hletters η S ηg t₀ Sw ϖ a b Dq G v g reg pkg hB ht₀a hab hb
    hbS hDq hq hJ X₀ κ hκ f u w hf hch θ hθ
  obtain ⟨φ, hφ, hdatum⟩ := planeDatum_rep f hf
  have hcap : ∀ j x, cappedWordSlots κ 0 d j x ≤ J := fun j x =>
    (cappedWordSlots_le_reserve κ 0 m d Ks j x).trans hJ
  let F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K gM :=
    b1wCappedFrame K gM H J π letters d (fun i => (hletters i).1) η S ηg t₀ Sw ϖ a b G v g reg pkg
      hB ht₀a hab hb X₀ κ hκ hcap φ hφ f u w hdatum hch
  have hJF : b1wLadderTop (Finset.univ.sup d + 4) d Ks m + Finset.univ.sup d ≤ F.J := by
    have hsd := sup_le_sum_nat d
    change b1wLadderTop (Finset.univ.sup d + 4) d Ks m + Finset.univ.sup d ≤ J
    unfold b1wLadderTop
    unfold wordReserveJstar wordReserveKstar wordReserveN at hJ
    omega
  have hθs : fibreNorm (planeFibreFrequency F.η θ) ≤ 2 * K.ξlo := hθ.trans hρlo
  have hJ0 : (fun n => datumJets F.π F.ϖ n F.φ θ) =
      fun n => datumJets π ϖ n (fun x => planeValue (f x)) θ :=
    funext fun n => datumJets_congr_ae π ϖ n (fun x => (hdatum x).symm) θ
  have hAmp : (fun β => momentAmpNorm F.π F.ϖ β
      (fun x => planeValue (F.u (Fin.last Nw) x F.b)) θ) =
      fun β => momentAmpNorm π ϖ β (fun x => planeValue (u (Fin.last Nw) x b)) θ := by
    funext β
    congr 1
  suffices hfr : WordFibreFactsAt K m Ks (b1wM Nw m Ks) (b1wOut Nw Ks) (Q₂ + Q₀) (2 * CH)
      (max (max cq' (C₂ * C₀)) (cq + 3 * Cad)) (m.factorial : ℝ) Θ (3 * Cad) c₀ F.letters F.η
      F.S F.ηg F.t₀ F.Sw F.ϖ F.a F.b Dq F.G F.v F.reg F.pkg (fun n => datumJets F.π F.ϖ n F.φ θ)
      (fun β => momentAmpNorm F.π F.ϖ β (fun x => planeValue (F.u (Fin.last Nw) x F.b)) θ) θ by
    rw [hJ0, hAmp] at hfr
    exact hfr
  by_cases hpoor : 1 ≤ C₀ * peFactor F.η ^ Q₀ * (1 + F.S) ^ Q₀ * ((1 + (F.reg.joins : ℝ)) *
      Real.exp (-c₀ * F.reg.buffer) + Real.exp (-c₀ * Dq))
  · -- poorly buffered: the crude pass
    obtain ⟨V, hb', Dθ, src, Fl, Good, q, qs, εs, hW', hq', hqb, hval, hmem, hD0, hεm, hε0, hsrc,
      hbud, -⟩ := hobj gM F θ hletters hJF hθs hbS (hMom K gM F) fun j x e β => hMK F j x e θ β
    exact b1w_poor_frame hL hZ hTO F θ hKρ le_rfl hθs (hMom K gM F) V hb' Dθ src Fl Good q qs
      εs hW' hq' hqb hval hmem cq' hcq' hD0 hεm hε0 hsrc C₂ hC₂ Q₂ hbud C₀ hC₀0 Q₀ c₀ (Q₂ + Q₀)
      (2 * CH) _ (m.factorial : ℝ) Θ (3 * Cad) c₀ Dq le_rfl (by positivity)
      ((le_max_left _ _).trans (le_max_left _ _)) ((le_max_right _ _).trans (le_max_left _ _))
      le_rfl hΘ (by positivity) le_rfl hDq hpoor
  · -- well buffered: the weighted pass
    exact hwell gM F θ hletters hJF hθs (hMom K gM F) (fun j x e β => hMK F j x e θ β) CH Dq hCH
      hbS hDq hq (not_le.1 hpoor) (Q₂ + Q₀) (2 * CH) _ (m.factorial : ℝ) c₀ le_rfl
      (le_max_right _ _) le_rfl

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords.Assembly

/-! # The fibre facts of the words

* `amplitudeIdForcingCurves`: the literal forcing of every stage has `L²` time carriers. It
  combines `amplitudeId_word_moment_families` and `amplitudeId_moment_forcing_curves`.
* `wordFibreFacts`: `WordFibreFactsStatement`, i.e. `wordFibreFacts_of_open` with its
  inputs supplied by:
  - the amplitude identification, its moments and its measurable fibres;
  - the reduced transverse regularity, transform bound and sharp-decay estimates;
  - the transform bounds and the sharp families. -/

universe u v

/-- **The literal forcing has `L²` time carriers.** -/
theorem amplitudeIdForcingCurves : AmplitudeIdForcingCurvesStatement.{u, v} := by
  intro K g₁ ι _ h _ _ _ _ _ _ D Nw F j x e θ β
  obtain ⟨⟨Mu⟩, hMS⟩ := amplitudeId_word_moment_families F j x θ e
  obtain ⟨h1, h2⟩ := amplitudeId_moment_forcing_curves (Icc F.a F.b) F.G F.piece.hGm F.v
    F.piece.hv θ β _ _ Mu fun i => (hMS i).some
  exact ⟨h1, h2⟩

/-- **The fibre facts of the words.** -/
theorem wordFibreFacts : WordFibreFactsStatement.{u, v} :=
  wordFibreFacts_of_open
    (amplitudeIdFibresMeas_of_literal amplitudeIdentification amplitudeIdForcingCurves)
    amplitudeIdMoments cellDriftRegularity levelZeroData sameLevelTransformBound
    letterTransformBoundAE letterBloch stageExpansion stageTransformEarlier zeroAmplitudeWord
    terminalOutput sharpSameLevel sharpLetterAE
    (weightedSharpDecay quietHsDecay (weightedPlainDecay quietHsDecay)) sharpSlowTest

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords.Assembly

/-! # The retained amplitude factor and the ingredients of `cycle_mixed_words` without the discard

* `retainedAmplitudeFactor`: `RetainedAmplitudeFactorStatement`. The chain is the word fibre facts
  (`wordFibreFacts`) → the word stage bound (`wordStage_of_fibreFacts`) → the moment amplitudes
  (`momentAmplitude_of_wordStage`) → the retained amplitude factor
  (`retainedAmplitudeFactor_of_moments_of_ingredients`, with the amplitude identification and the
  factor calculus).
* Two of the four ingredients of `cycle_mixed_words_of_ingredients`, unconditionally:
  `retainedMapExists`, `retainedGaussian`.
* `mixedWordsIngredients_of_discard`: all four, from the three discard statements
  (`ChainFullFieldStatement`, `QuietHighStatement`, `MarksBandStatement`). -/

universe u v

/-- **The retained amplitude factor.** -/
theorem retainedAmplitudeFactor : RetainedAmplitudeFactorStatement.{u, v} :=
  retainedAmplitudeFactor_of_moments_of_ingredients amplitudeIdentification
    (momentAmplitude_of_wordStage (wordStage_of_fibreFacts wordFibreFacts)) factorMomentCalculus

theorem retainedMapExists : RetainedMapExistsStatement.{u, v} :=
  retainedMapExists_of_leaves chainCombination compactChainExistence compactDensity
    amplitudePlancherel (compactChainGaussian_of_open retainedAmplitudeFactor) gaussianPlancherel

theorem retainedGaussian : RetainedGaussianStatement.{u, v} :=
  retainedGaussian_of_leaves chainCombination compactChainExistence compactDensity
    amplitudePlancherel (compactChainGaussian_of_open retainedAmplitudeFactor)
    blochFibreContinuity

/-- **The ingredients of `cycle_mixed_words` from the three discard statements.** -/
theorem mixedWordsIngredients_of_discard (hFF : ChainFullFieldStatement.{u, v})
    (hQH : QuietHighStatement.{u, v}) (hMB : MarksBandStatement.{u, v}) :
    RetainedMapExistsStatement.{u, v} ∧ RetainedModelJetsStatement.{u, v} ∧
      ChainDiscardStatement.{u, v} ∧ RetainedGaussianStatement.{u, v} :=
  mixedWordsIngredients_of_open retainedAmplitudeFactor hFF hQH hMB

end AVRegularity.CycleWords.Assembly
end
end
