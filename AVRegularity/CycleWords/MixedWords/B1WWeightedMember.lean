-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.SharpLetterVarNum
import AVRegularity.CycleWords.MixedWords.B1WWeightedNormFacts
import AVRegularity.CycleWords.MixedWords.B1WData
import AVRegularity.CycleWords.MixedWords.B1WRepresentation
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # one constituent of one variant at block level

`br_gain`, `br_zero`: the analogs of `br_gamma` for the gain and the zero part of the
letter transform: the block family of one `(w, d, γ)` with the four block bounds. -/

section
universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

theorem rq_widen {L n Nmin : ℕ} {G : (Vec 2 → ℂ) → Vec 2 → ℂ} {B1 B2 B3 B4 : ℝ}
    (h : RQ L n Nmin G B1 B2 B3 B4) :
    RQ L n Nmin G B1 B1 (B1 * ‖torusHigherConstant L 1‖) B4 := by
  obtain ⟨A, hv, b1, b2, b3, b4⟩ := h
  refine ⟨A, hv, b1, fun ψ => (sl86_mean_le _).trans (b1 ψ), fun z => ?_, b4⟩
  refine (b1 _).trans (le_of_eq ?_)
  rw [slConstCLM_apply, torusHigherConstant_norm L z]
  ring

theorem letterVars_low (β : ℕ × ℕ) :
    ∀ w ∈ letterVars β, w.2.2.2 = false → w.1 ≠ 0 → w.2.1.1 + w.2.1.2 + 1 = β.1 + β.2 := by
  intro w hw hf hne
  simp only [letterVars, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · have : β.1 ≠ 0 := fun h0 => hne (by simp [h0])
    simp only; omega
  · have : β.2 ≠ 0 := fun h0 => hne (by simp [h0])
    simp only; omega
  · simp at hf
  · simp at hf

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem br_gain
    (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw) (a b : ℝ)
    (J H : ℕ) (hL : IsCycleLetter π (letters l) (Icc a b ×ˢ Set.univ) J H) (r : ℝ)
    (hr : r ∈ Icc a b) (hg : LetterGood (letters l) (Icc a b) J r) (hπ : ∀ x, 0 < π x)
    (ϖ ηg : ℝ) (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hg0 : 0 < ηg) (hg1 : ηg ≤ 1) (θ : Vec 2) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (ζ t : ℝ) (hϖζ : ϖ ≤ ζ) (hζ1 : ζ ≤ 1) (ht0 : 0 ≤ t) (htρ : t ≤ ρ)
    (htζ : t ≤ (1 + ρ) * ζ) (hθt : ∀ k, |θ k| ≤ t) (X₀ : Vec 2)
    (n L Nmin Dmax M0 S : ℕ)
    (hord : (letters l).order ≤ Dmax) (hslow : (letters l).slow ≤ S) (hJ : n + Dmax ≤ J)
    (hL1 : n + (letters l).order ≤ L) (hNmin : (letters l).order + 3 ≤ Nmin) (x x' : ι)
    (β β' : ℕ × ℕ)
    (hβM : β.1 + β.2 ≤ M0) (hβ'M : β'.1 + β'.2 ≤ M0) (hθpos : 0 < (letters l).theta)
    (w : ℝ × (ℕ × ℕ) × Fin 2 × Bool) (hw : w ∈ letterVars β) (d : ℕ) (hd : d ∈ Finset.Icc 2 D)
    (γ : Constituent d (h x') (h x)) (hγ : γ ∈ (letters l).edge x x' ⟨d, hd⟩)
    :
    BRQ (m₁ := Module.finrank ℝ (h x)) (m₂ := Module.finrank ℝ (h x')) L n Nmin
      (fun b b' f z =>
        ((letterMat (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map b b' : ℝ) : ℂ) *
          (((letterRatioReal π ϖ ηg letters l x x' β β' * w.1 : ℝ) : ℂ) *
            star (letterGamP (slSel true β w.2.1) θ (letters l).positive (letters l).slow (ϖ * ηg) X₀ r d
              γ.coeff w.2.1 w.2.2.1 β' (variantFun w.2.2.2 (-θ) w.2.2.1 (fun y => star (f y))) z)))
      (‖γ.map‖ * (ϖ * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
        jetTotal (Icc a b) (letters l).slow J d γ.coeff))) (‖γ.map‖ * (ϖ * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
        jetTotal (Icc a b) (letters l).slow J d γ.coeff))) (‖γ.map‖ * (ϖ * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
        jetTotal (Icc a b) (letters l).slow J d γ.coeff) * ‖torusHigherConstant L 1‖))
      (‖γ.map‖ * (ζ ^ 2 * ‖torusHigherConstant L 1‖ * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
        jetTotal (Icc a b) (letters l).slow J d γ.coeff))) := by
  classical
  have hθρ : ∀ k, |θ k| ≤ ρ := fun k => (hθt k).trans htρ
  set Zj := gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
    jetTotal (Icc a b) (letters l).slow J d γ.coeff with hZj
  by_cases hm : γ.map = 0
  · have h0 : BRQ (m₁ := Module.finrank ℝ (h x)) (m₂ := Module.finrank ℝ (h x')) L n Nmin
        (fun b b' f z =>
        ((letterMat (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map b b' : ℝ) : ℂ) *
          (((letterRatioReal π ϖ ηg letters l x x' β β' * w.1 : ℝ) : ℂ) *
            star (letterGamP (slSel true β w.2.1) θ (letters l).positive (letters l).slow (ϖ * ηg) X₀ r d
              γ.coeff w.2.1 w.2.2.1 β' (variantFun w.2.2.2 (-θ) w.2.2.1 (fun y => star (f y))) z))) 0 0 0 0 :=
      brq_congr brq_zero fun N _ _ b b' ψ => by simp [letterMat, hm]
    refine brq_mono h0 ?_ ?_ ?_ ?_ <;> simp [hm]
  · obtain ⟨k, hk⟩ := List.mem_iff_get.1 hγ
    subst hk
    obtain ⟨hwb, hw1, hw2, hw3, hw4, hw5⟩ := letterVars_props β M0 hβM w hw
    set γ := ((letters l).edge x x' ⟨d, hd⟩).get k with hγdef
    have hdle : d ≤ (letters l).order := by
      by_contra hlt
      have := hL.edge_order x x' ⟨d, hd⟩ (by simpa using not_le.1 hlt)
      have hk' := k.2
      simp [this] at hk'
    have hd2 : 2 ≤ d := (Finset.mem_Icc.1 hd).1
    let jet : DerivativeWord2 (d - 1) → ℕ → ℕ → ℝ := fun α s q =>
      (jetSupOn (Icc a b ×ˢ Set.univ) s q (γ.coeff α)).toReal
    have hjet0 : ∀ α s q, 0 ≤ jet α s q := fun _ _ _ => ENNReal.toReal_nonneg
    have hfacts : ∀ α s, s ≤ (letters l).slow → ∀ (ω : DerivativeWord2 s) (k' : Fin 2),
        ContDiff ℝ (J : ℕ∞) (tbTermCoef (γ.coeff α r) s ω X₀ k') ∧
        AVenhance.IsZ2Periodic (tbTermCoef (γ.coeff α r) s ω X₀ k') ∧
        ∀ q ≤ J, ∀ z, ‖iteratedFDeriv ℝ q (tbTermCoef (γ.coeff α r) s ω X₀ k') z‖ ≤ jet α s q :=
      fun α s hs ω k' => letter_term_facts π (letters l) a b J H hL r hr hg x x' ⟨d, hd⟩ k hm α s hs
        ω X₀ k'
    have hreal := rq_gamP (slSel true β w.2.1) θ ρ hθρ n L Nmin J d hd2 (by omega) (by omega)
      (by omega) (letters l).positive (letters l).slow (ϖ * ηg) X₀ r γ.coeff jet hjet0 hfacts
      (letterRatioReal π ϖ ηg letters l x x' β β' * w.1) w.2.1 w.2.2.1 β' w.2.2.2
    have hJt : ∀ α s, 0 ≤ ∑ q ∈ Finset.range (J + 1), jet α s q :=
      fun α s => Finset.sum_nonneg fun q _ => hjet0 α s q
    have hkc : 0 ≤ ‖torusHigherConstant L 1‖ := norm_nonneg _
    have hnum := gain_sum π ϖ ηg letters l x x' β β' w.2.1 d M0 D n S hslow ρ hρ w.2.2.2 w.2.2.1 w.1
      hwb (hπ x) (hπ x') hϖ0 hϖ1 hg0 hg1 hθpos (Finset.mem_Icc.1 hd).2 hd2 hw1 hβM hβ'M
      (letterVars_low β w hw) ζ t hϖζ hζ1 ht0 htζ θ hθt ‖torusHigherConstant L 1‖ hkc
      (fun α s => ∑ q ∈ Finset.range (J + 1), jet α s q) hJt
    have hJe : ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range ((letters l).slow + 1),
        ∑ q ∈ Finset.range (J + 1), jet α s q = jetTotal (Icc a b) (letters l).slow J d γ.coeff := rfl
    rw [hJe] at hnum
    have hw' := rq_widen hreal
    refine brq_mono (brq_of_rq (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map
      ?_ ?_ ?_ ?_ hw') ?_ ?_ ?_ ?_
    · exact sgSum_nonneg _ _ _ _ fun α s w' a' => sgU1_nonneg ρ hρ n _ _ _ _ _ (hJt α s)
    · exact sgSum_nonneg _ _ _ _ fun α s w' a' => sgU1_nonneg ρ hρ n _ _ _ _ _ (hJt α s)
    · exact mul_nonneg (sgSum_nonneg _ _ _ _ fun α s w' a' => sgU1_nonneg ρ hρ n _ _ _ _ _ (hJt α s)) hkc
    · exact sgSum_nonneg _ _ _ _ fun α s w' a' => sgU4_nonneg θ n _ _ _ hkc _ _ _ _ (hJt α s)
    · exact mul_le_mul_of_nonneg_left hnum.1 (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_left hnum.1 (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_left (by nlinarith [hnum.1, hkc]) (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_left (by linarith [hnum.2]) (norm_nonneg _)

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem br_zero
    (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw) (a b : ℝ)
    (J H : ℕ) (hL : IsCycleLetter π (letters l) (Icc a b ×ˢ Set.univ) J H) (r : ℝ)
    (hr : r ∈ Icc a b) (hg : LetterGood (letters l) (Icc a b) J r) (hπ : ∀ x, 0 < π x)
    (ϖ ηg : ℝ) (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hg0 : 0 < ηg) (hg1 : ηg ≤ 1) (θ : Vec 2) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (ζ t : ℝ) (hϖζ : ϖ ≤ ζ) (hζ1 : ζ ≤ 1) (ht0 : 0 ≤ t) (htρ : t ≤ ρ)
    (htζ : t ≤ (1 + ρ) * ζ) (hθt : ∀ k, |θ k| ≤ t) (X₀ : Vec 2)
    (n L Nmin Dmax M0 S : ℕ)
    (hord : (letters l).order ≤ Dmax) (hslow : (letters l).slow ≤ S) (hJ : n + Dmax ≤ J)
    (hL1 : n + (letters l).order ≤ L) (hNmin : (letters l).order + 3 ≤ Nmin) (x x' : ι)
    (β β' : ℕ × ℕ)
    (hβM : β.1 + β.2 ≤ M0) (hβ'M : β'.1 + β'.2 ≤ M0) (hθpos : 0 < (letters l).theta)
    (w : ℝ × (ℕ × ℕ) × Fin 2 × Bool) (hw : w ∈ letterVars β) (d : ℕ) (hd : d ∈ Finset.Icc 2 D)
    (γ : Constituent d (h x') (h x)) (hγ : γ ∈ (letters l).edge x x' ⟨d, hd⟩)
    :
    BRQ (m₁ := Module.finrank ℝ (h x)) (m₂ := Module.finrank ℝ (h x')) L n Nmin
      (fun b b' f z =>
        ((letterMat (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map b b' : ℝ) : ℂ) *
          (((letterRatioReal π ϖ ηg letters l x x' β β' * w.1 : ℝ) : ℂ) *
            star (letterGamP (slSel false β w.2.1) θ (letters l).positive (letters l).slow (ϖ * ηg) X₀ r d
              γ.coeff w.2.1 w.2.2.1 β' (variantFun w.2.2.2 (-θ) w.2.2.1 (fun y => star (f y))) z)))
      (‖γ.map‖ * (1 * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
        jetTotal (Icc a b) (letters l).slow J d γ.coeff))) (‖γ.map‖ * (t * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
        jetTotal (Icc a b) (letters l).slow J d γ.coeff))) (‖γ.map‖ * (t * ‖torusHigherConstant L 1‖ * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
        jetTotal (Icc a b) (letters l).slow J d γ.coeff)))
      (‖γ.map‖ * (ζ ^ 2 * ‖torusHigherConstant L 1‖ * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
        jetTotal (Icc a b) (letters l).slow J d γ.coeff))) := by
  classical
  have hθρ : ∀ k, |θ k| ≤ ρ := fun k => (hθt k).trans htρ
  set Zj := gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
    jetTotal (Icc a b) (letters l).slow J d γ.coeff with hZj
  by_cases hm : γ.map = 0
  · have h0 : BRQ (m₁ := Module.finrank ℝ (h x)) (m₂ := Module.finrank ℝ (h x')) L n Nmin
        (fun b b' f z =>
        ((letterMat (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map b b' : ℝ) : ℂ) *
          (((letterRatioReal π ϖ ηg letters l x x' β β' * w.1 : ℝ) : ℂ) *
            star (letterGamP (slSel false β w.2.1) θ (letters l).positive (letters l).slow (ϖ * ηg) X₀ r d
              γ.coeff w.2.1 w.2.2.1 β' (variantFun w.2.2.2 (-θ) w.2.2.1 (fun y => star (f y))) z))) 0 0 0 0 :=
      brq_congr brq_zero fun N _ _ b b' ψ => by simp [letterMat, hm]
    refine brq_mono h0 ?_ ?_ ?_ ?_ <;> simp [hm]
  · obtain ⟨k, hk⟩ := List.mem_iff_get.1 hγ
    subst hk
    obtain ⟨hwb, hw1, hw2, hw3, hw4, hw5⟩ := letterVars_props β M0 hβM w hw
    set γ := ((letters l).edge x x' ⟨d, hd⟩).get k with hγdef
    have hdle : d ≤ (letters l).order := by
      by_contra hlt
      have := hL.edge_order x x' ⟨d, hd⟩ (by simpa using not_le.1 hlt)
      have hk' := k.2
      simp [this] at hk'
    have hd2 : 2 ≤ d := (Finset.mem_Icc.1 hd).1
    let jet : DerivativeWord2 (d - 1) → ℕ → ℕ → ℝ := fun α s q =>
      (jetSupOn (Icc a b ×ˢ Set.univ) s q (γ.coeff α)).toReal
    have hjet0 : ∀ α s q, 0 ≤ jet α s q := fun _ _ _ => ENNReal.toReal_nonneg
    have hfacts : ∀ α s, s ≤ (letters l).slow → ∀ (ω : DerivativeWord2 s) (k' : Fin 2),
        ContDiff ℝ (J : ℕ∞) (tbTermCoef (γ.coeff α r) s ω X₀ k') ∧
        AVenhance.IsZ2Periodic (tbTermCoef (γ.coeff α r) s ω X₀ k') ∧
        ∀ q ≤ J, ∀ z, ‖iteratedFDeriv ℝ q (tbTermCoef (γ.coeff α r) s ω X₀ k') z‖ ≤ jet α s q :=
      fun α s hs ω k' => letter_term_facts π (letters l) a b J H hL r hr hg x x' ⟨d, hd⟩ k hm α s hs
        ω X₀ k'
    have hreal := rq_gamP (slSel false β w.2.1) θ ρ hθρ n L Nmin J d hd2 (by omega) (by omega)
      (by omega) (letters l).positive (letters l).slow (ϖ * ηg) X₀ r γ.coeff jet hjet0 hfacts
      (letterRatioReal π ϖ ηg letters l x x' β β' * w.1) w.2.1 w.2.2.1 β' w.2.2.2
    have hJt : ∀ α s, 0 ≤ ∑ q ∈ Finset.range (J + 1), jet α s q :=
      fun α s => Finset.sum_nonneg fun q _ => hjet0 α s q
    have hkc : 0 ≤ ‖torusHigherConstant L 1‖ := norm_nonneg _
    have hnum := zero_sum π ϖ ηg letters l x x' β β' w.2.1 d M0 D n S hslow ρ hρ w.2.2.2 w.2.2.1 w.1
      hwb (hπ x) (hπ x') hϖ0 hϖ1 hg0 hg1 hθpos (Finset.mem_Icc.1 hd).2 hd2 hw1 hβM hβ'M
      (letterVars_low β w hw) ζ t hϖζ hζ1 ht0 htρ htζ θ hθt ‖torusHigherConstant L 1‖ hkc
      (fun α s => ∑ q ∈ Finset.range (J + 1), jet α s q) hJt
    have hJe : ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range ((letters l).slow + 1),
        ∑ q ∈ Finset.range (J + 1), jet α s q = jetTotal (Icc a b) (letters l).slow J d γ.coeff := rfl
    rw [hJe] at hnum
    refine brq_mono (brq_of_rq (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map
      ?_ ?_ ?_ ?_ hreal) ?_ ?_ ?_ ?_
    · exact sgSum_nonneg _ _ _ _ fun α s w' a' => sgU1_nonneg ρ hρ n _ _ _ _ _ (hJt α s)
    · exact sgSum_nonneg _ _ _ _ fun α s w' a' => sgU2_nonneg θ ρ hρ n _ _ _ _ _ (hJt α s)
    · exact sgSum_nonneg _ _ _ _ fun α s w' a' =>
        sgU3_nonneg θ ρ hρ n _ _ _ hkc _ _ _ _ (hJt α s)
    · exact sgSum_nonneg _ _ _ _ fun α s w' a' => sgU4_nonneg θ n _ _ _ hkc _ _ _ _ (hJt α s)
    · exact mul_le_mul_of_nonneg_left hnum.1 (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_left hnum.2.1 (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_left hnum.2.2.1 (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_left hnum.2.2.2 (norm_nonneg _)
end

/-! # the filtered families vanish off the moment relation

`letterGamP_eq_zero_of_not_rel`, `letterGfamP_zero_rel`, `letterGfamP_zero_R` are the copies of the
unfiltered statements for the filtered families `letterGamP`, `letterGfamP`. -/

section
universe u v

open Classical in
theorem letterGamP_eq_zero_of_not_rel (P : ℕ × ℕ → Prop) (θ : Vec 2) (pos : Bool) (slow : ℕ)
    (δ : ℝ) (X₀ : Vec 2) (r : ℝ) (d : ℕ)
    (coeff : DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec 2 → Vec 2)
    (β₀ β β' : ℕ × ℕ) (k : Fin 2) (ψ : Vec 2 → ℂ) (S Dmax : ℕ) (hd : d ≤ Dmax) (hsl : slow ≤ S)
    (hb1 : β.1 ≤ β₀.1 + 1) (hb2 : β.2 ≤ β₀.2 + 1) (hb3 : β₀.1 ≤ β.1) (hb4 : β₀.2 ≤ β.2)
    (hn : ¬ LetterMomRel S (Dmax + 1) β β') :
    letterGamP P θ pos slow δ X₀ r d coeff β₀ k β' ψ = 0 := by
  funext z
  unfold letterGamP
  refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun s hs => Finset.sum_eq_zero fun ω _ => ?_
  have hs2 := (Finset.mem_Icc.1 hs).2
  have hwa := wordCount_sum α
  have hwo := wordCount_sum ω
  have : ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ Finset.range ((wordCount α).2 + 1),
      (if β' = (β₀.1 + (wordCount ω).1 - a.1, β₀.2 + (wordCount ω).2 - a.2) ∧ P a then
        ((((wordCount α).1.choose a.1 * (wordCount α).2.choose a.2 *
          (β₀.1 + (wordCount ω).1).descFactorial a.1 *
          (β₀.2 + (wordCount ω).2).descFactorial a.2 : ℕ) : ℂ) *
        fibreCovPow (-θ) ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
          (fun z' => ((iteratedFDeriv ℝ s (fun X => coeff α r X z' k) X₀
            (fun n => basisVec (ω n)) : ℝ) : ℂ) * ψ z') z) else 0) = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    obtain ⟨ha1, ha2⟩ := Finset.mem_product.1 ha
    have ha1' := Finset.mem_range.1 ha1
    have ha2' := Finset.mem_range.1 ha2
    by_cases h1 : β' = (β₀.1 + (wordCount ω).1 - a.1, β₀.2 + (wordCount ω).2 - a.2)
    · by_cases h2 : a.1 ≤ β₀.1 + (wordCount ω).1 ∧ a.2 ≤ β₀.2 + (wordCount ω).2
      · exfalso
        apply hn
        have e1 : β'.1 = β₀.1 + (wordCount ω).1 - a.1 := by rw [h1]
        have e2 : β'.2 = β₀.2 + (wordCount ω).2 - a.2 := by rw [h1]
        unfold LetterMomRel
        omega
      · have := gamCoefNat_eq_zero (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a h2
        unfold gamCoefNat at this
        simp [h1, this]
    · simp [h1]
  rw [this]
  simp

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D Nw : ℕ}

omit [Fintype ι] in
open Classical in
theorem letterGfamP_zero_R (g : Bool) (θ : Vec 2) (L : CycleLetter ι h D) (A : Finset ℕ) (δ : ℝ)
    (X₀ : Vec 2) (r : ℝ) (x x' : ι) (β β' : ℕ × ℕ) (b b' f z) :
    letterGfamP g θ L A δ X₀ r x x' β β' 0 b b' f z = 0 := by
  unfold letterGfamP
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : d ∈ Finset.Icc 2 D
  · simp only [hd, dite_true]
    refine List.sum_eq_zero fun u hu => ?_
    obtain ⟨γ, -, rfl⟩ := List.mem_map.1 hu
    simp
  · simp [hd]

open Classical in
theorem letterGfamP_zero_rel (g : Bool) (θ : Vec 2) (π : ι → ℝ) (Jstar H : ℕ) (dom : Set (ℝ × Vec 2))
    (L : CycleLetter ι h D) (hL : IsCycleLetter π L dom Jstar H) (A : Finset ℕ) (δ : ℝ)
    (X₀ : Vec 2) (r : ℝ) (x x' : ι) (β β' : ℕ × ℕ) (R : ℝ) (S Dmax : ℕ)
    (hord : L.order ≤ Dmax) (hslow : L.slow ≤ S) (hn : ¬ LetterMomRel S (Dmax + 1) β β') (b b' f z) :
    letterGfamP g θ L A δ X₀ r x x' β β' R b b' f z = 0 := by
  unfold letterGfamP
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
  obtain ⟨-, -, hw2, hw3, hw4, hw5⟩ := letterVars_props β (β.1 + β.2) le_rfl w hw
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : d ∈ Finset.Icc 2 D
  · simp only [hd, dite_true]
    refine List.sum_eq_zero fun u hu => ?_
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hu
    have hdle : d ≤ L.order := by
      by_contra hlt
      have := hL.edge_order x x' ⟨d, hd⟩ (by simpa using not_le.1 hlt)
      simp [this] at hγ
    have hz := letterGamP_eq_zero_of_not_rel (slSel g β w.2.1) θ L.positive L.slow δ X₀ r d γ.coeff
      w.2.1 β β' w.2.2.1 (variantFun w.2.2.2 (-θ) w.2.2.1 (fun y => star (f y))) S Dmax
      (hdle.trans hord) hslow hw2 hw3 hw4 hw5 hn
    rw [hz]
    simp
  · simp [hd]

omit [∀ i, FiniteDimensional ℝ (h i)] in
open Classical in
/-- The numerical envelope of the four variants (the second half of `letterBlock_exists`). -/
theorem env1 (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw) (a b : ℝ)
    (J H : ℕ) (hL : IsCycleLetter π (letters l) (Icc a b ×ˢ Set.univ) J H) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (n Dmax M0 S : ℕ) (x x' : ι) (β β' : ℕ × ℕ) (A : Finset ℕ)
    (hrel : LetterMomRel S (Dmax + 1) β β') (hθpos : 0 < (letters l).theta) :
    ((letterVars β).map fun _ => ∑ d ∈ A, (if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ *
          (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
            jetTotal (Icc a b) (letters l).slow J d γ.coeff))).sum else 0)).sum ≤
      4 * gamCfin D n ρ M0 S * (if LetterMomRel S (Dmax + 1) β β' then 1 else 0) *
        letterCompWeight (letters l) x x' := by
  have hθ0 : ¬ (letters l).theta = 0 := hθpos.ne'
  set K := gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) with hK
  set Jt : ∀ d : ℕ, Constituent d (h x') (h x) → ℝ := fun d γ =>
    jetTotal (Icc a b) (letters l).slow J d γ.coeff with hJt
  -- the numerical bound of the block constant
  have hJt0 : ∀ d γ, 0 ≤ Jt d γ := fun d γ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      ENNReal.toReal_nonneg
  set Ψ : ℕ → ℝ := fun d => if hd : d ∈ Finset.Icc 2 D then
      ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ * Jt d γ)).sum else 0 with hΨ
  have hΨ0 : ∀ d, 0 ≤ Ψ d := by
    intro d
    by_cases hd : d ∈ Finset.Icc 2 D
    · simp only [hΨ, hd, dite_true]
      rw [list_map_sum_get]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (hJt0 _ _)
    · simp only [hΨ]
      split_ifs
      exact le_rfl
  have hcw : ∑ d ∈ A, (if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ * (K * Jt d γ))).sum else 0) =
      K * ∑ d ∈ A, Ψ d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hd : d ∈ Finset.Icc 2 D
    · simp only [hΨ, hd, dite_true]
      rw [list_map_sum_get, list_map_sum_get, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    · simp only [hΨ]
      split_ifs
      simp
  have hsub : ∑ d ∈ A, Ψ d ≤ ∑ o : Finset.Icc 2 D, ∑ k : Fin ((letters l).edge x x' o).length,
      ‖(((letters l).edge x x' o).get k).map‖ * Jt o.1 (((letters l).edge x x' o).get k) := by
    calc ∑ d ∈ A, Ψ d = ∑ d ∈ A.filter (· ∈ Finset.Icc 2 D), Ψ d :=
          (Finset.sum_filter_of_ne (fun d _ hne => by
            by_contra hnd; exact hne (by
              simp only [hΨ]
              split_ifs
              rfl))).symm
      _ ≤ ∑ d ∈ Finset.Icc 2 D, Ψ d := Finset.sum_le_sum_of_subset_of_nonneg
          (fun d hd => (Finset.mem_filter.1 hd).2) (fun d _ _ => hΨ0 d)
      _ = ∑ o : Finset.Icc 2 D, Ψ o.1 := (Finset.sum_coe_sort (Finset.Icc 2 D) Ψ).symm
      _ = _ := by
          refine Finset.sum_congr rfl fun o _ => ?_
          simp only [hΨ, o.2, dite_true]
          rw [list_map_sum_get]
  have henv := envelope_real_sum_le π (letters l) (Icc a b ×ˢ Set.univ) J H hL x x'
  have hθ' : 0 < (letters l).theta := hθpos
  have hcwle : K * ∑ d ∈ A, Ψ d ≤ gamCfin D n ρ M0 S * ((letters l).majorant x x' / (letters l).theta) := by
    have hK0 : 0 ≤ K := by
      have : 0 ≤ gamCfin D n ρ M0 S := by
        unfold gamCfin gamPr
        have := gamCc_nonneg D M0 S
        have h1 : 0 ≤ ((D : ℝ) + 1) ^ 2 := by positivity
        have h2 : 0 ≤ (1 + ρ) ^ D := by positivity
        have h3 : 0 ≤ ∑ K ∈ Finset.range (n + D + 1), |cellDriftNativePrice K| :=
          Finset.sum_nonneg fun _ _ => abs_nonneg _
        positivity
      positivity
    calc K * ∑ d ∈ A, Ψ d ≤ K * ∑ o : Finset.Icc 2 D, ∑ k : Fin ((letters l).edge x x' o).length,
          ‖(((letters l).edge x x' o).get k).map‖ * Jt o.1 (((letters l).edge x x' o).get k) :=
          mul_le_mul_of_nonneg_left hsub hK0
      _ = gamCfin D n ρ M0 S / (letters l).theta * (Real.sqrt (π x' / π x) *
          ∑ o : Finset.Icc 2 D, ∑ k : Fin ((letters l).edge x x' o).length,
          ‖(((letters l).edge x x' o).get k).map‖ * Jt o.1 (((letters l).edge x x' o).get k)) := by
          rw [hK]; field_simp
      _ ≤ gamCfin D n ρ M0 S / (letters l).theta * (letters l).majorant x x' := by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg ?_ hθ'.le)
          · exact henv
          · unfold gamCfin gamPr
            have := gamCc_nonneg D M0 S
            have h1 : 0 ≤ ((D : ℝ) + 1) ^ 2 := by positivity
            have h2 : 0 ≤ (1 + ρ) ^ D := by positivity
            have h3 : 0 ≤ ∑ K ∈ Finset.range (n + D + 1), |cellDriftNativePrice K| :=
              Finset.sum_nonneg fun _ _ => abs_nonneg _
            positivity
      _ = _ := by ring
  have hw : letterCompWeight (letters l) x x' = (letters l).majorant x x' / (letters l).theta := by
    unfold letterCompWeight; simp [hθ0]
  simp only [hrel, ↓reduceIte, hw]
  have hsum : ((letterVars β).map fun _ => ∑ d ∈ A, (if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ * (K * Jt d γ))).sum else 0)).sum =
      4 * ∑ d ∈ A, (if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ * (K * Jt d γ))).sum else 0) := by
    simp [letterVars]; ring
  refine (le_of_eq hsum).trans ?_
  rw [hcw]
  linarith [hcwle]

omit [∀ i, FiniteDimensional ℝ (h i)] in
open Classical in
/-- The envelope with a scalar factor `T ≥ 0`. -/
theorem envT (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw) (a b : ℝ)
    (J H : ℕ) (hL : IsCycleLetter π (letters l) (Icc a b ×ˢ Set.univ) J H) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (n Dmax M0 S : ℕ) (x x' : ι) (β β' : ℕ × ℕ) (A : Finset ℕ)
    (hrel : LetterMomRel S (Dmax + 1) β β') (hθpos : 0 < (letters l).theta) (T : ℝ) (hT : 0 ≤ T) :
    ((letterVars β).map fun _ => ∑ d ∈ A, (if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ *
          (T * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
            jetTotal (Icc a b) (letters l).slow J d γ.coeff)))).sum else 0)).sum ≤
      T * (4 * gamCfin D n ρ M0 S * (if LetterMomRel S (Dmax + 1) β β' then 1 else 0) *
        letterCompWeight (letters l) x x') := by
  have hX : ∑ d ∈ A, (if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ *
          (T * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
            jetTotal (Icc a b) (letters l).slow J d γ.coeff)))).sum else 0) =
      T * ∑ d ∈ A, (if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ *
          (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
            jetTotal (Icc a b) (letters l).slow J d γ.coeff))).sum else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hd : d ∈ Finset.Icc 2 D
    · simp only [hd, dite_true]
      rw [← List.sum_map_mul_left]
      congr 1
      exact List.map_congr_left fun γ _ => by ring
    · simp [hd]
  simp only [hX]
  rw [List.sum_map_mul_left]
  exact mul_le_mul_of_nonneg_left (env1 π letters l a b J H hL ρ hρ n Dmax M0 S x x' β β' A hrel
    hθpos) hT

open Classical in
/-- **The four bounds of the gain or zero family of a pair of components and moments**: assembled
from the bounds of the single constituents (the analog of `letterBlock_exists`). -/
theorem block_gen (g : Bool) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw)
    (a b : ℝ) (J H : ℕ) (hL : IsCycleLetter π (letters l) (Icc a b ×ˢ Set.univ) J H) (ϖ ηg : ℝ)
    (θ : Vec 2) (ρ : ℝ) (hρ : 0 ≤ ρ) (X₀ : Vec 2) (r : ℝ) (A : Finset ℕ) (n L Nmin Dmax M0 S : ℕ)
    (hord : (letters l).order ≤ Dmax) (hslow : (letters l).slow ≤ S) (x x' : ι) (β β' : ℕ × ℕ)
    (T1 T2 T3 T4 : ℝ) (h1 : 0 ≤ T1) (h2 : 0 ≤ T2) (h3 : 0 ≤ T3) (h4 : 0 ≤ T4)
    (hper : 0 < (letters l).theta → ∀ w ∈ letterVars β, ∀ (d : ℕ) (hd : d ∈ Finset.Icc 2 D),
      ∀ γ ∈ (letters l).edge x x' ⟨d, hd⟩,
      BRQ (m₁ := Module.finrank ℝ (h x)) (m₂ := Module.finrank ℝ (h x')) L n Nmin
        (fun b b' f z =>
          ((letterMat (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map b b' :
            ℝ) : ℂ) *
            (((letterRatioReal π ϖ ηg letters l x x' β β' * w.1 : ℝ) : ℂ) *
              star (letterGamP (slSel g β w.2.1) θ (letters l).positive (letters l).slow (ϖ * ηg)
                X₀ r d γ.coeff w.2.1 w.2.2.1 β'
                (variantFun w.2.2.2 (-θ) w.2.2.1 (fun y => star (f y))) z)))
        (‖γ.map‖ * (T1 * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
          jetTotal (Icc a b) (letters l).slow J d γ.coeff)))
        (‖γ.map‖ * (T2 * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
          jetTotal (Icc a b) (letters l).slow J d γ.coeff)))
        (‖γ.map‖ * (T3 * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
          jetTotal (Icc a b) (letters l).slow J d γ.coeff)))
        (‖γ.map‖ * (T4 * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
          jetTotal (Icc a b) (letters l).slow J d γ.coeff)))) :
    BRQ (m₁ := Module.finrank ℝ (h x)) (m₂ := Module.finrank ℝ (h x')) L n Nmin
      (letterGfamP g θ (letters l) A (ϖ * ηg) X₀ r x x' β β'
        (letterRatioReal π ϖ ηg letters l x x' β β'))
      (T1 * (4 * gamCfin D n ρ M0 S * (if LetterMomRel S (Dmax + 1) β β' then 1 else 0) *
        letterCompWeight (letters l) x x'))
      (T2 * (4 * gamCfin D n ρ M0 S * (if LetterMomRel S (Dmax + 1) β β' then 1 else 0) *
        letterCompWeight (letters l) x x'))
      (T3 * (4 * gamCfin D n ρ M0 S * (if LetterMomRel S (Dmax + 1) β β' then 1 else 0) *
        letterCompWeight (letters l) x x'))
      (T4 * (4 * gamCfin D n ρ M0 S * (if LetterMomRel S (Dmax + 1) β β' then 1 else 0) *
        letterCompWeight (letters l) x x')) := by
  by_cases hrel : LetterMomRel S (Dmax + 1) β β'
  swap
  · have h0 := brq_congr (brq_zero (m₁ := Module.finrank ℝ (h x)) (m₂ := Module.finrank ℝ (h x'))
      (L := L) (n := n) (Nmin := Nmin))
      (G' := letterGfamP g θ (letters l) A (ϖ * ηg) X₀ r x x' β β'
        (letterRatioReal π ϖ ηg letters l x x' β β'))
      (fun N _ _ b b' ψ => funext fun z => (letterGfamP_zero_rel g θ π J H _ (letters l) hL A (ϖ * ηg)
        X₀ r x x' β β' _ S Dmax hord hslow hrel b b' _ z).symm)
    refine brq_mono h0 ?_ ?_ ?_ ?_ <;> simp [hrel]
  by_cases hθ0 : (letters l).theta = 0
  · have hR : letterRatioReal π ϖ ηg letters l x x' β β' = 0 := by
      unfold letterRatioReal letterFac
      simp [hθ0]
    have hcw : letterCompWeight (letters l) x x' = 0 := by simp [letterCompWeight, hθ0]
    have h0 := brq_congr (brq_zero (m₁ := Module.finrank ℝ (h x)) (m₂ := Module.finrank ℝ (h x'))
      (L := L) (n := n) (Nmin := Nmin))
      (G' := letterGfamP g θ (letters l) A (ϖ * ηg) X₀ r x x' β β'
        (letterRatioReal π ϖ ηg letters l x x' β β'))
      (fun N _ _ b b' ψ => by
        rw [hR]; exact funext fun z =>
          (letterGfamP_zero_R g θ (letters l) A (ϖ * ηg) X₀ r x x' β β' b b' _ z).symm)
    refine brq_mono h0 ?_ ?_ ?_ ?_ <;> simp [hcw]
  have hθpos : 0 < (letters l).theta := lt_of_le_of_ne hL.theta_nonneg (Ne.symm hθ0)
  have hvar : ∀ w ∈ letterVars β, BRQ (m₁ := Module.finrank ℝ (h x))
      (m₂ := Module.finrank ℝ (h x')) L n Nmin
      (fun b b' f z => ∑ d ∈ A, if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ =>
          ((letterMat (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map b b' : ℝ) :
            ℂ) *
            (((letterRatioReal π ϖ ηg letters l x x' β β' * w.1 : ℝ) : ℂ) *
              star (letterGamP (slSel g β w.2.1) θ (letters l).positive (letters l).slow (ϖ * ηg) X₀ r
                d γ.coeff w.2.1 w.2.2.1 β' (variantFun w.2.2.2 (-θ) w.2.2.1
                  (fun y => star (f y))) z))).sum)
        else 0)
      (∑ d ∈ A, if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ *
          (T1 * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
            jetTotal (Icc a b) (letters l).slow J d γ.coeff)))).sum else 0)
      (∑ d ∈ A, if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ *
          (T2 * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
            jetTotal (Icc a b) (letters l).slow J d γ.coeff)))).sum else 0)
      (∑ d ∈ A, if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ *
          (T3 * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
            jetTotal (Icc a b) (letters l).slow J d γ.coeff)))).sum else 0)
      (∑ d ∈ A, if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ *
          (T4 * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
            jetTotal (Icc a b) (letters l).slow J d γ.coeff)))).sum else 0) := by
    intro w hw
    refine brq_finset_sum A fun d _ => ?_
    by_cases hd : d ∈ Finset.Icc 2 D
    · simp only [hd, dite_true]
      exact brq_list_sum _ fun γ hγ => hper hθpos w hw d hd γ hγ
    · simpa [hd] using (brq_zero (m₁ := Module.finrank ℝ (h x)) (m₂ := Module.finrank ℝ (h x'))
        (L := L) (n := n) (Nmin := Nmin))
  have hmain := brq_list_sum (letterVars β) hvar
  refine brq_mono hmain ?_ ?_ ?_ ?_
  · exact envT π letters l a b J H hL ρ hρ n Dmax M0 S x x' β β' A hrel hθpos T1 h1
  · exact envT π letters l a b J H hL ρ hρ n Dmax M0 S x x' β β' A hrel hθpos T2 h2
  · exact envT π letters l a b J H hL ρ hρ n Dmax M0 S x x' β β' A hrel hθpos T3 h3
  · exact envT π letters l a b J H hL ρ hρ n Dmax M0 S x x' β β' A hrel hθpos T4 h4
end

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # The context of the crude pass for one frame and frequency

* The fibre hypotheses of the actual coefficients at the plane frequency of `θ`
  (`b1w_transverseLocalHyp`): from the piece and the package.
* The gauge: `‖N₀‖ Γ(r) = ‖e^{∫_r^b λ}‖` with `N₀ = e^{Ξ(a,b)}` and `Γ = |e^{-Ξ(a,·)}|`
  (`b1w_gauge_eq`), and its growth at the rate `π²/16` (`b1w_gauge_growth`).
* The slow test's representatives at every stage `k < M` of the ladder, from one representative at
  the top of the ladder (`b1w_slow_reps`). -/

section
universe u v

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

/-- `K.Cw` is nonnegative on a word piece. -/
theorem AmplitudeIdFrame.Cw_nonneg {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) : 0 ≤ K.Cw :=
  (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans (F.piece.hvw 0 0)


/-- **The fibre hypotheses of a frame** at a frequency of the disc `|ξ| ≤ ρ`. -/
theorem b1w_transverseLocalHyp {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) {ρ : ℝ}
    (hρ : ρ < K.ξ0) (hρlo : ρ ≤ 2 * K.ξlo)
    (hθ : fibreNorm (planeFibreFrequency F.η θ) ≤ ρ) :
    TransverseLocalHyp K F.η F.G F.v (planeFibreFrequency F.η θ) := by
  have hCg : 0 ≤ K.Cg := F.pkg.consts_pos.2.2.2.1.le
  have hCw := F.Cw_nonneg
  have hn0 := fibreNorm_nonneg (planeFibreFrequency F.η θ)
  have hsep : (2 + K.Cw * K.Cg) * fibreNorm (planeFibreFrequency F.η θ) ^ 2 ≤
      Real.pi ^ 2 / 16 := by
    have h2 : fibreNorm (planeFibreFrequency F.η θ) ^ 2 ≤ (2 * K.ξlo) ^ 2 :=
      pow_le_pow_left₀ hn0 (hθ.trans hρlo) 2
    exact (mul_le_mul_of_nonneg_left h2 (by positivity)).trans
      F.pkg.consts_pos.2.2.2.2.2.2.2.2.2
  exact ⟨F.piece.hη.le, F.piece.hη1, hCg, hCw, F.piece.hGm, F.piece.hv, F.piece.hv0,
    F.piece.hvw, planeFibreFrequency_im F.η θ, lt_of_le_of_lt hθ hρ, hsep⟩

/-- **The gauge identity** `‖N₀‖ Γ(r) = ‖e^{∫_r^b λ}‖`. -/
theorem b1w_gauge_eq {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (hθ : fibreNorm (planeFibreFrequency F.η θ) < K.ξ0) {r : ℝ} (hr : r ∈ Icc F.a F.b) :
    ‖Complex.exp (blockGauge F.pkg.actual.lam F.η F.a F.b θ)‖ *
        b1wGamma F.pkg.actual.lam F.η F.a θ r =
      ‖Complex.exp (∫ τ in r..F.b, fibreSeriesC F.pkg.actual.lam
        (planeFibreFrequency F.η θ) τ)‖ := by
  have hint : ∀ c d, c ≤ d → IntervalIntegrable
      (fun τ => fibreSeriesC F.pkg.actual.lam (planeFibreFrequency F.η θ) τ) volume c d :=
    fun c d hcd => (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd).mpr
      (symbol_integrableOn F.pkg.actual F.piece.hη.le F.piece.hη1 F.pkg.consts_pos.2.2.2.1.le
        F.Cw_nonneg F.piece.hGm F.piece.hv F.piece.hvw hθ c d)
  unfold b1wGamma blockGauge
  rw [← norm_mul, ← Complex.exp_add,
    ← intervalIntegral.integral_add_adjacent_intervals (hint F.a r hr.1) (hint r F.b hr.2)]
  congr 2
  ring

/-- **The gauge grows at most at the rate `π²/16`** on the piece. -/
theorem b1w_gauge_growth {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) {ρ : ℝ}
    (hρ : ρ < K.ξ0) (hρlo : ρ ≤ 2 * K.ξlo)
    (hθ : fibreNorm (planeFibreFrequency F.η θ) ≤ ρ) :
    ∀ r s, F.a ≤ r → r ≤ s → s ≤ F.b →
      b1wGamma F.pkg.actual.lam F.η F.a θ s ≤
        Real.exp (Real.pi ^ 2 / 16 * (s - r)) * b1wGamma F.pkg.actual.lam F.η F.a θ r :=
  fun _ _ har hrs _ => b1wGamma_growth F.pkg.actual F.piece.hη.le F.piece.hη1
    F.pkg.consts_pos.2.2.2.1.le F.Cw_nonneg F.piece.hGm F.piece.hv F.piece.hvw
    F.pkg.consts_pos.2.2.2.2.2.2.2.2.2 hρ hρlo θ hθ (planeFibreFrequency_im F.η θ) F.a har hrs

end Frame

/-- **The slow test's representatives at every stage** `k < M`, from one representative at the
top of the ladder. -/
theorem b1w_slow_reps {Nw : ℕ} (s₀ m : ℕ) (d Ks : Fin Nw → ℕ) {q : ComplexCellL2} {c : ℝ}
    (w : TorusHk (b1wLadderTop s₀ d Ks m) ℂ) (hwq : torusHkValueCLM w = q) (hw : ‖w‖ ≤ c) :
    ∀ k < b1wM Nw m Ks, ∃ U : TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
      torusHkValueCLM U = q ∧ ‖U‖ ≤ c := fun _ hk =>
  ⟨truncateTorusHk (b1wLadderAt_le_top s₀ m d Ks hk) w,
    by rw [torusHigher_truncate_value, hwq], (truncateTorusHk_norm_le _ w).trans hw⟩
end

/-! # The sharp pass: the sharp block decomposition at one time

At a time `r` the slow tests are `ψ_i = conj(β_i) w`, where `w = E_q + D` is an `H^N` representative
of the slow test, with `‖D‖ ≤ M₀|ξ||E_q|`. The stage representation of the tested sources
(`b1w_stage_representation`) and the sharp families give the per-stage aggregates
(`b1w_sharp_repr_at`):
* slow pairings `A_s = Bζ²|E_q| ‖β‖`;
* sizes `A_f = Bζ|E_q| ‖β‖`;
* window defects `A_d = Bδ_N‖β‖`, where `δ_N` bounds `‖w − P_N w‖` in the least window.

The representation then splits into:
* the slow coefficients;
* sharp-admissible remainders;
* defect brackets. Their pairings with the stage values are bounded through the crude stage
  quantities: the absolute error of the sharp pass. -/

section
universe u v

/-- A realization of the transverse projection on `TorusHk` commutes with complex scalars. -/
theorem torusHk_projection_scalar {N : ℕ} (e : Fin 2) (P : TorusHk N ℂ →L[ℝ] TorusHk N ℂ)
    (hP : ∀ U, torusHkValueCLM (P U) = cellTransverseProjection e (torusHkValueCLM U)) (c : ℂ)
    (U : TorusHk N ℂ) : P (torusHigherScalarCLM N c U) = torusHigherScalarCLM N c (P U) := by
  apply TorusHk.ext_value
  change torusHkValueCLM (P (torusHigherScalarCLM N c U)) =
    torusHkValueCLM (torusHigherScalarCLM N c (P U))
  rw [hP, torusHigherScalarCLM_value, torusHigherScalarCLM_value, hP, cellScalarCLM_smul,
    cellScalarCLM_smul, cellTransverseProjection_complex_smul]

section Frame

end Frame
end

/-! # Sharp pass: the stage representation with the sharp families, at one time

The tested sources of the slow tests `ψ_i = conj(β_i) w` are the stage representation
`∑_i β_i ⟨S_i, q⟩ = ∑_{k'<k} ∑_{i'} ⟨W_{i'}, Φ_{i'}⟩`. Here `Φ` is read off the sharp families of
the families: `U_Φ k'` at stage `k'`, carrying the sharp facts (`B1WSharpFamily`)
(`b1w_sharp_repr_at`). This is the common first half of the sharp and the weighted block
decompositions. -/

section
universe u v

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The stage representation with the sharp families, at one time.** -/
theorem b1w_sharp_repr_at {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (k : ℕ) (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ) (s : ℕ → ℕ) (n N : ℕ) (hN : n + 3 ≤ N)
    (W S : B1WIndex ι h Nw m Ks → ComplexCellL2)
    (Fl : B1WIndex ι h Nw m Ks → Fin 2 → ComplexCellL2) (q : ComplexCellL2)
    (qs : TorusHk 1 ℂ) (w : TorusHk N ℂ) (hwq : torusHkValueCLM w = q)
    (hqs : torusHkValueCLM qs = q)
    (hS : ∀ i ∈ stageSet b1wSt k, (S i : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y)
    (hF : ∀ i ∈ stageSet b1wSt k, ∀ j, (Fl i j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y j)
    (hExp : ∀ i ∈ stageSet b1wSt k, ∀ φ : Vec 2 → ℂ, ContDiff ℝ n φ →
      AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hearly : ∀ i ∈ stageSet b1wSt k, ∀ i' : B1WIndex ι h Nw m Ks, ¬ b1wSt i' < k →
      ∀ φ : Vec 2 → ℂ,
      b1wTestTransform F θ i i' r φ = 0)
    (hW : ∀ i' : B1WIndex ι h Nw m Ks, (W i' : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i' * b1wStageVal F θ i' r y)
    (B M₀ : ℝ)
    (hprov : ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ, ∀ k' < k,
      ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
        B1WSharpFamily F θ r k k' N (s k') ψ Φ B M₀)
    (β : B1WIndex ι h Nw m Ks → ℂ) :
    ∃ (UΦ : ∀ k', B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ)
      (Φall : B1WIndex ι h Nw m Ks → ComplexCellL2),
      (∀ k' < k, ∀ i' ∈ stageSet b1wSt k', torusHkValueCLM (UΦ k' i') = Φall i') ∧
      (∀ k' < k, B1WSharpFamily F θ r k k' N (s k')
        (fun i => torusHigherScalarCLM N (star (β i)) w) (UΦ k') B M₀) ∧
      ∑ i ∈ stageSet b1wSt k, β i * cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) qs =
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k', cellComplexPair (W i') (Φall i') := by
  classical
  -- the slow tests
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
      ψ = fun i => torusHigherScalarCLM N (star (β i)) w := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : B1WIndex ι h Nw m Ks → TorusHk 1 ℂ,
      z = fun i => cellH1Scalar (star (β i)) qs := ⟨_, rfl⟩
  have hzψ : ∀ i, torusHkValueCLM (z i) = torusHkValueCLM (ψ i) := by
    intro i
    refine Lp.ext ?_
    have h1 := cellH1Scalar_jet_ae (star (β i)) qs (valueIndex2 1)
    have h3 := cellScalarCLM_ae (star (β i)) q
    have h4 : torusHkValueCLM (ψ i) = cellScalarCLM (star (β i)) q := by
      rw [hψdef, torusHigherScalarCLM_value, hwq]
    rw [h4, hz]
    filter_upwards [h1, h3] with y hy1 hy3
    rw [hy3]
    change (cellH1Scalar (star (β i)) qs).val (valueIndex2 1) y = _
    rw [hy1]
    change star (β i) * (torusHkValueCLM qs) y = _
    rw [hqs]
  have hXz : ∑ i ∈ stageSet b1wSt k, β i *
      cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) qs =
      ∑ i ∈ stageSet b1wSt k, cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) (z i) :=
    Finset.sum_congr rfl fun i _ => by
      rw [hz]
      exact (congrArg (fun c => c * _) (star_star (β i)).symm).trans
        (cellComplexSource_scalar_test _ _ _ qs (star (β i))).symm
  -- the families of the slow tests
  choose Φf hΦf using hprov ψ
  obtain ⟨UΦ, hUΦdef⟩ : ∃ UΦ : ∀ k', B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
      UΦ = fun k' => if hk : k' < k then Φf k' hk else fun _ => 0 := ⟨_, rfl⟩
  have hUΦk : ∀ k' (hk : k' < k), UΦ k' = Φf k' hk := fun k' hk => by
    rw [hUΦdef]
    simp only [hk, dite_true]
  obtain ⟨Φall, hΦall⟩ : ∃ Φall : B1WIndex ι h Nw m Ks → ComplexCellL2,
      Φall = fun i' => torusHkValueCLM (UΦ (b1wSt i') i') := ⟨_, rfl⟩
  have hUΦval : ∀ k' < k, ∀ i' ∈ stageSet b1wSt k', torusHkValueCLM (UΦ k' i') = Φall i' := by
    intro k' _ i' hi'
    have hst : b1wSt i' = k' := (Finset.mem_filter.1 hi').2
    rw [hΦall]
    subst hst
    rfl
  -- the classical representatives of the tests
  have hcl : ∀ i, ContDiff ℝ (n + 1 : ℕ) (torusHigherClassicalValue N (ψ i)) := fun i =>
    torusHigherClassicalValue_contDiff N (n + 1) (by omega) (ψ i)
  have hzcl : ∀ i, (torusHkValueCLM (z i) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      torusHigherClassicalValue N (ψ i) := by
    intro i
    rw [hzψ i]
    exact (torusHigherClassicalValue_ae N (by omega) (ψ i)).symm
  have hstc : ∀ i, ContDiff ℝ n (fun y => star (torusHigherClassicalValue N (ψ i) y)) :=
    fun i => Complex.conjCLE.toContinuousLinearMap.contDiff.comp
      ((hcl i).of_le (by exact_mod_cast Nat.le_succ n))
  have hper : ∀ i, AVenhance.IsZ2Periodic (fun y => star (torusHigherClassicalValue N (ψ i) y)) :=
    fun i mm y => by simp only [torusHigherClassicalValue_periodic N (ψ i) mm y]
  have hc1 : ∀ i, ContDiff ℝ 1 (torusHigherClassicalValue N (ψ i)) := fun i =>
    (hcl i).of_le (by exact_mod_cast (by omega : 1 ≤ n + 1))
  have hint : ∀ i ∈ stageSet b1wSt k, ∀ i', b1wSt i' < k →
      Integrable (fun y => b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' * (W i' y *
        b1wTestTransform F θ i i' r (fun y => star (torusHigherClassicalValue N (ψ i) y)) y))
        (volume.restrict AVenhance.unitCube) := by
    intro i hi i' hi'
    obtain ⟨Φ1, hΦ1⟩ := hprov (fun j => if j = i then ψ i else 0) (b1wSt i') hi'
    have hv := hΦ1.1 i' (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
    refine (cellComplex_pairing_integrable (W i') (torusHkValueCLM (Φ1 i'))).congr ?_
    filter_upwards [hv] with y hy
    rw [hy, Finset.sum_eq_single_of_mem i hi fun j _ hj => ?_]
    · simp only [ite_true, star_mul', star_star, b1wScaleRatio_star]
      ring
    · simp only [hj, ite_false, torusHigherClassicalValue_zero N (by omega), Pi.zero_apply,
        star_zero, b1wTestTransform_zero_test, mul_zero]
  have hrep := b1w_stage_representation F θ r k hπ hϖ W S Fl z
    (fun i => torusHigherClassicalValue N (ψ i)) (fun i _ => hc1 i)
    (fun i _ => hzcl i) hS hF (fun i hi => hExp i hi _ (hstc i) (hper i))
    (fun i hi i' hi' => hearly i hi i' hi' _) hW hint Φall
    (fun i' hi' => by
      rw [hΦall]
      simp only []
      rw [hUΦk _ hi']
      exact (hΦf (b1wSt i') hi').1 i' (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩))
  refine ⟨UΦ, Φall, hUΦval, fun k' hk' => ?_, hXz.trans hrep⟩
  rw [hUΦk k' hk']
  have := hΦf k' hk'
  rw [hψdef] at this
  exact this

end Frame
end

/-! # Sharp pass: the stage representation with the sharp families, for general tests

This is the general-test form of `b1w_sharp_repr_at`, for the tests `ψ_i ∈ H^N` (with `H¹` values
`z_i`) of the H4 decompositions along the adjoint curves. The tested sources are
`∑_i ⟨S_i, z_i⟩ = ∑_{k'<k} ∑_{i'} ⟨W_{i'}, Φ_{i'}⟩`, with `Φ` read off the sharp families of the
proof (`b1w_sharp_repr_general_at`). -/

section
universe u v

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The stage representation with the sharp families, for general tests.** -/
theorem b1w_sharp_repr_general_at {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (k : ℕ) (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ) (s : ℕ → ℕ) (n N : ℕ) (hN : n + 3 ≤ N)
    (W S : B1WIndex ι h Nw m Ks → ComplexCellL2)
    (Fl : B1WIndex ι h Nw m Ks → Fin 2 → ComplexCellL2)
    (hS : ∀ i ∈ stageSet b1wSt k, (S i : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y)
    (hF : ∀ i ∈ stageSet b1wSt k, ∀ j, (Fl i j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y j)
    (hExp : ∀ i ∈ stageSet b1wSt k, ∀ φ : Vec 2 → ℂ, ContDiff ℝ n φ →
      AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hearly : ∀ i ∈ stageSet b1wSt k, ∀ i' : B1WIndex ι h Nw m Ks, ¬ b1wSt i' < k →
      ∀ φ : Vec 2 → ℂ,
      b1wTestTransform F θ i i' r φ = 0)
    (hW : ∀ i' : B1WIndex ι h Nw m Ks, (W i' : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i' * b1wStageVal F θ i' r y)
    (B M₀ : ℝ)
    (hprov : ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ, ∀ k' < k,
      ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
        B1WSharpFamily F θ r k k' N (s k') ψ Φ B M₀)
    (z : B1WIndex ι h Nw m Ks → TorusHk 1 ℂ) (ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ)
    (hzψ : ∀ i, torusHkValueCLM (z i) = torusHkValueCLM (ψ i)) :
    ∃ (UΦ : ∀ k', B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ)
      (Φall : B1WIndex ι h Nw m Ks → ComplexCellL2),
      (∀ k' < k, ∀ i' ∈ stageSet b1wSt k', torusHkValueCLM (UΦ k' i') = Φall i') ∧
      (∀ k' < k, B1WSharpFamily F θ r k k' N (s k') ψ (UΦ k') B M₀) ∧
      ∑ i ∈ stageSet b1wSt k, cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) (z i) =
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k', cellComplexPair (W i') (Φall i') := by
  classical
  -- the families of the tests
  choose Φf hΦf using hprov ψ
  obtain ⟨UΦ, hUΦdef⟩ : ∃ UΦ : ∀ k', B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
      UΦ = fun k' => if hk : k' < k then Φf k' hk else fun _ => 0 := ⟨_, rfl⟩
  have hUΦk : ∀ k' (hk : k' < k), UΦ k' = Φf k' hk := fun k' hk => by
    rw [hUΦdef]
    simp only [hk, dite_true]
  obtain ⟨Φall, hΦall⟩ : ∃ Φall : B1WIndex ι h Nw m Ks → ComplexCellL2,
      Φall = fun i' => torusHkValueCLM (UΦ (b1wSt i') i') := ⟨_, rfl⟩
  have hUΦval : ∀ k' < k, ∀ i' ∈ stageSet b1wSt k', torusHkValueCLM (UΦ k' i') = Φall i' := by
    intro k' _ i' hi'
    have hst : b1wSt i' = k' := (Finset.mem_filter.1 hi').2
    rw [hΦall]
    subst hst
    rfl
  -- the classical representatives of the tests
  have hcl : ∀ i, ContDiff ℝ (n + 1 : ℕ) (torusHigherClassicalValue N (ψ i)) := fun i =>
    torusHigherClassicalValue_contDiff N (n + 1) (by omega) (ψ i)
  have hzcl : ∀ i, (torusHkValueCLM (z i) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      torusHigherClassicalValue N (ψ i) := by
    intro i
    rw [hzψ i]
    exact (torusHigherClassicalValue_ae N (by omega) (ψ i)).symm
  have hstc : ∀ i, ContDiff ℝ n (fun y => star (torusHigherClassicalValue N (ψ i) y)) :=
    fun i => Complex.conjCLE.toContinuousLinearMap.contDiff.comp
      ((hcl i).of_le (by exact_mod_cast Nat.le_succ n))
  have hper : ∀ i, AVenhance.IsZ2Periodic (fun y => star (torusHigherClassicalValue N (ψ i) y)) :=
    fun i mm y => by simp only [torusHigherClassicalValue_periodic N (ψ i) mm y]
  have hc1 : ∀ i, ContDiff ℝ 1 (torusHigherClassicalValue N (ψ i)) := fun i =>
    (hcl i).of_le (by exact_mod_cast (by omega : 1 ≤ n + 1))
  have hint : ∀ i ∈ stageSet b1wSt k, ∀ i', b1wSt i' < k →
      Integrable (fun y => b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' * (W i' y *
        b1wTestTransform F θ i i' r (fun y => star (torusHigherClassicalValue N (ψ i) y)) y))
        (volume.restrict AVenhance.unitCube) := by
    intro i hi i' hi'
    obtain ⟨Φ1, hΦ1⟩ := hprov (fun j => if j = i then ψ i else 0) (b1wSt i') hi'
    have hv := hΦ1.1 i' (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
    refine (cellComplex_pairing_integrable (W i') (torusHkValueCLM (Φ1 i'))).congr ?_
    filter_upwards [hv] with y hy
    rw [hy, Finset.sum_eq_single_of_mem i hi fun j _ hj => ?_]
    · simp only [ite_true, star_mul', star_star, b1wScaleRatio_star]
      ring
    · simp only [hj, ite_false, torusHigherClassicalValue_zero N (by omega), Pi.zero_apply,
        star_zero, b1wTestTransform_zero_test, mul_zero]
  have hrep := b1w_stage_representation F θ r k hπ hϖ W S Fl z
    (fun i => torusHigherClassicalValue N (ψ i)) (fun i _ => hc1 i)
    (fun i _ => hzcl i) hS hF (fun i hi => hExp i hi _ (hstc i) (hper i))
    (fun i hi i' hi' => hearly i hi i' hi' _) hW hint Φall
    (fun i' hi' => by
      rw [hΦall]
      simp only []
      rw [hUΦk _ hi']
      exact (hΦf (b1wSt i') hi').1 i' (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩))
  refine ⟨UΦ, Φall, hUΦval, fun k' hk' => ?_, hrep⟩
  rw [hUΦk k' hk']
  exact hΦf k' hk'

end Frame
end

/-! # The sharp pass (weighted norm): one member of a test family

A test family member `Φ` is split exactly along the slow test, `Φ = κ q + φ`, with
`κ = conj(⟨1 + r, Φ⟩ / ⟨1 + r, q⟩)`. The remainder `φ` is actual-fast, so it lies in the crude
admissible class (`b1wAdm`). Under the weighted norm no projection and no bracket are needed:
through an `H^{s_k}` realization `P` of the transverse projection,
`ν_r(φ) ≤ ‖U_Φ‖ + |κ|‖U_q‖ + Ω(r)(‖U_Φ − PU_Φ‖ + |κ|‖U_q − PU_q‖)` (`b1w_weighted_member`). -/

/-- **One member of a test family, split along the slow test, in the weighted norm.** -/
theorem b1w_weighted_member (s : ℕ → ℕ) (Ω : ℕ → ℝ → ℝ) (e : ℝ → Fin 2)
    (tr : ℝ → ComplexCellL2) (k : ℕ) (r : ℝ) (hΩ : 0 ≤ Ω k r)
    (P : TorusHk (s k) ℂ →L[ℝ] TorusHk (s k) ℂ)
    (hP : ∀ U, torusHkValueCLM (P U) = cellTransverseProjection (e r) (torusHkValueCLM U))
    (hPn : ∀ U, ‖P U‖ ≤ ‖U‖) (q : ComplexCellL2) (Uq : TorusHk (s k) ℂ)
    (hUq : torusHkValueCLM Uq = q) (hg : cellComplexPair (tr r + cellConstantCLM 1) q ≠ 0)
    (Φ : ComplexCellL2) (UΦ : TorusHk (s k) ℂ) (hUΦ : torusHkValueCLM UΦ = Φ) :
    ∃ (κ : ℂ) (φ : ComplexCellL2),
      b1wAdm s tr k r φ ∧
      ‖κ‖ = ‖cellComplexPair (tr r + cellConstantCLM 1) Φ‖ /
        ‖cellComplexPair (tr r + cellConstantCLM 1) q‖ ∧
      b1wNuW s Ω e k r φ ≤ ‖UΦ‖ + ‖κ‖ * ‖Uq‖ +
        Ω k r * (‖UΦ - P UΦ‖ + ‖κ‖ * ‖Uq - P Uq‖) ∧
      ∀ W : ComplexCellL2, cellComplexPair W Φ =
        star κ * cellComplexPair W q + cellComplexPair W φ := by
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, κ = star (cellComplexPair (tr r + cellConstantCLM 1) Φ /
      cellComplexPair (tr r + cellConstantCLM 1) q) := ⟨_, rfl⟩
  have hU : torusHkValueCLM (UΦ - torusHigherScalarCLM (s k) κ Uq) = Φ - cellScalarCLM κ q := by
    rw [map_sub, torusHigherScalarCLM_value, hUΦ, hUq]
  have hfast : cellComplexPair (tr r + cellConstantCLM 1) (Φ - cellScalarCLM κ q) = 0 := by
    rw [cellComplexPair_sub_right, cellComplexPair_scalar_right, hκ, star_star,
      div_mul_cancel₀ _ hg, sub_self]
  have hPs := torusHk_projection_scalar (e r) P hP κ Uq
  have hν : b1wNuW s Ω e k r (Φ - cellScalarCLM κ q) ≤ ‖UΦ‖ + ‖κ‖ * ‖Uq‖ +
      Ω k r * (‖UΦ - P UΦ‖ + ‖κ‖ * ‖Uq - P Uq‖) := by
    refine (b1wNuW_le_proj s Ω e k r hΩ P hP _ hU).trans (add_le_add ?_ ?_)
    · refine (hPn _).trans ((norm_sub_le _ _).trans (add_le_add le_rfl ?_))
      rw [torusHigherScalarCLM_norm]
    · refine mul_le_mul_of_nonneg_left ?_ hΩ
      have he : UΦ - torusHigherScalarCLM (s k) κ Uq - P (UΦ - torusHigherScalarCLM (s k) κ Uq) =
          (UΦ - P UΦ) - torusHigherScalarCLM (s k) κ (Uq - P Uq) := by
        rw [map_sub, hPs, map_sub]
        abel
      rw [he]
      refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
      rw [torusHigherScalarCLM_norm]
  refine ⟨κ, Φ - cellScalarCLM κ q, ⟨⟨_, hU⟩, hfast⟩, ?_, hν, fun W => ?_⟩
  · rw [hκ, norm_star, norm_div]
  · rw [cellComplexPair_sub_right, cellComplexPair_scalar_right]
    ring

end AVRegularity.CycleWords.Assembly
end
