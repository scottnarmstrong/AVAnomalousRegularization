-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.B1WCrudeH4
import AVRegularity.CycleWords.MixedWords.B1WWeightedMember
import AVRegularity.CycleWords.MixedWords.AfwCrude
public import AVRegularity.CycleWords.MixedWords.SharpLetterHelperUnits
import AVRegularity.CycleWords.MixedWords.SharpLetterCommFact
public import AVRegularity.CycleWords.MixedWords.B1WData
import AVRegularity.CycleWords.MixedWords.WeightedPlainDecayKappa
import Mathlib.CategoryTheory.Countable

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # The crude pass of the word fibre facts

The objects of the word fibre facts (`WordFibreFactsStatement`) for one frame and frequency: the
coefficients `⟨G, v, √η ξ, 0⟩` (`b1wCoeff`), the row trace `r(t)` (`b1wRow`), the slow symbol factor
`e^{∫_r^b λ}` (`b1wSlowE`), the stage curves `W_i = c_i Dθ_i` (`b1wW`, `b1wWs`) and their forcing
set to `0` off the good times (`b1wSr`, `b1wFl`). The crude pass (`b1w_crude_pass`) runs the
abstract fibre word with the crude H3s and H4 (`b1w_crude_H3s`, `b1w_crude_H4`, one
`Θ = B (1 + C_w)(1 + c_R + c_R C_w)`, `c_R = C_g ρ + ‖1‖`), the gauge `Γ = |e^{-Ξ(a,·)}|` (rate
`π²/16 < π²/8`). It bounds every gauged stage quantity (`afw_crude_stages`) and every tested stage
source (`afw_crude_sources`). -/

universe u v

/-- The crude letter constant `Θ = B (1 + C_w)(1 + c_R + c_R C_w)`. -/
def b1wCrudeΘ (B Cw cR : ℝ) : ℝ := B * (1 + Cw) * (1 + cR + cR * Cw)

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The coefficients of the stage curves at the plane frequency of `θ`. -/
def b1wCoeff {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) :
    CellCoefficients :=
  ⟨fun t _ => F.G t, F.v, fun k => (Real.sqrt F.η : ℂ) * planeFibreFrequency F.η θ k, 0⟩

/-- The row trace of the actual package at the plane frequency of `θ`. -/
def b1wRow {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) :
    ℝ → ComplexCellL2 :=
  cellRawTrace (fibreSeriesJet F.pkg.actual.r (planeFibreFrequency F.η θ))

/-- The slow symbol factor `e^{∫_r^b λ}`. -/
def b1wSlowE {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ) : ℂ :=
  Complex.exp (∫ τ in r..F.b, fibreSeriesC F.pkg.actual.lam (planeFibreFrequency F.η θ) τ)

/-- The normalization `N₀ = e^{Ξ(a,b)}`. -/
def b1wN₀ {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) : ℂ :=
  Complex.exp (blockGauge F.pkg.actual.lam F.η F.a F.b θ)

/-- The stage curves. -/
def b1wW {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ) (i : B1WIndex ι h Nw m Ks) (t : ℝ) :
    ComplexCellL2 :=
  cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellRawTrace (Dθ i) t)

/-- The `H¹` slices of the stage curves. -/
def b1wWs {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ) (i : B1WIndex ι h Nw m Ks) (t : ℝ) :
    TorusHk 1 ℂ :=
  cellH1Scalar (b1wScale F.π F.ϖ F.ηg F.letters i) (cellH1Slice (Dθ i) t)

/-- The stage sources, set to `0` off the good times. -/
def b1wSr {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (src : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → ℂ) (Good : Set ℝ) (i : B1WIndex ι h Nw m Ks) :
    ℝ → ComplexCellL2 :=
  Good.indicator fun t =>
    cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) t)

/-- The stage fluxes, set to `0` off the good times. -/
def b1wFl {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (Fl : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (Good : Set ℝ)
    (i : B1WIndex ι h Nw m Ks) : ℝ → Fin 2 → ComplexCellL2 :=
  Good.indicator fun t j => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
    (cellSourceSlice (fun r z => Fl i r z j) t)

/-- **The crude pass**: every tested stage source is bounded by the crude stage bounds. -/
theorem b1w_crude_pass {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) {ρ : ℝ}
    (hρ : ρ < K.ξ0) (hρlo : ρ ≤ 2 * K.ξlo) (hθ : fibreNorm (planeFibreFrequency F.η θ) ≤ ρ)
    (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ) (s : ℕ → ℕ) (n : ℕ) (hn : ∀ k, n + 3 ≤ s k) (M : ℕ)
    (V : ℝ) (hb : ∀ t x, ∑ i, F.v t x i ^ 2 ≤ V ^ 2)
    (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ) (src : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → ℂ)
    (Fl : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hW : ∀ i, CellWeakHilbertCurve F.a F.b (b1wW F Dθ i) (b1wWs F Dθ i) (fun t =>
      cellDualDerivative (b1wCoeff F θ) F.piece.hGm V F.piece.hv.1 hb t (b1wWs F Dθ i t)
        (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) t))
        (fun k => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
          (cellSourceSlice (fun r z => Fl i r z k) t))))
    (hval : ∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
        inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y)))
    (hmem : ∀ i, ∀ t ∈ Icc F.a F.b,
      MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube))
    (Good : Set ℝ) (hGood : ∀ᵐ t ∂volume.restrict (Icc F.a F.b), t ∈ Good)
    (hGsrc : ∀ r ∈ Good, ∀ i, MemLp (src i r) 2 (volume.restrict AVenhance.unitCube) ∧
      src i r =ᵐ[volume.restrict AVenhance.unitCube]
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r ∧
      (∀ j : Fin 2, MemLp (fun z => Fl i r z j) 2 (volume.restrict AVenhance.unitCube)) ∧
      Fl i r =ᵐ[volume.restrict AVenhance.unitCube]
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r)
    (hGexp : ∀ r ∈ Good, ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ), ContDiff ℝ n φ →
      AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hearly : ∀ (i i' : B1WIndex ι h Nw m Ks), ¬ b1wSt i' < b1wSt i →
      ∀ (r : ℝ) (φ : Vec 2 → ℂ), b1wTestTransform F θ i i' r φ = 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hprov : ∀ r ∈ Good, ∀ (k k' : ℕ), k' < k →
      ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (s k) ℂ,
        ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
          (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
            =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
              ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
                star (b1wTestTransform F θ i i' r (fun y => star
                  (torusHigherClassicalValue (s k) (ψ i) y)) y)) ∧
          ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)
    (q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ)
    (hq : CellWeakHilbertCurve F.a F.b q qs (fun t =>
      -cellDualDerivative (cellAdjointCoefficients (b1wCoeff F θ)) F.piece.hGm V
        (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) t (qs t) 0 0))
    (hGq : ∀ r ∈ Good, torusHkValueCLM (qs r) = q r)
    (hE : ∀ r ∈ Icc F.a F.b,
      cellComplexPair (b1wRow F θ r + cellConstantCLM 1) (q r) = b1wSlowE F θ r)
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hrep : ∀ r ∈ Icc F.a F.b, ∀ k < M, ∃ U : TorusHk (s k) ℂ,
      torusHkValueCLM U = q r ∧ ‖U‖ ≤ Cw * ‖b1wSlowE F θ r‖)
    (Ca : ℝ) (hCa : 0 ≤ Ca)
    (hadj : ∀ k < M, ∀ T ∈ Icc F.a F.b, ∀ ψ : ComplexCellL2, b1wAdm s (b1wRow F θ) k T ψ →
      ∃ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve F.a T Ψv Ψs (fun r =>
          -cellDualDerivative (cellAdjointCoefficients (b1wCoeff F θ)) F.piece.hGm V
            (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) r (Ψs r) 0 0) ∧
        Ψv T = ψ ∧
        ∀ r ∈ Icc F.a T, b1wAdm s (b1wRow F θ) k r (Ψv r) ∧
          b1wNu s k (Ψv r) ≤ Ca * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) * b1wNu s k ψ)
    (Dd Dp : ℕ → ℝ) (hDm : Monotone Dd) (hDpm : Monotone Dp) (hD : ∀ k, 0 ≤ Dd k)
    (hDp : ∀ k, 0 ≤ Dp k) (hDDp : ∀ k, Dp k ≤ Dd k)
    (hD0 : ∀ k < M, slowStage b1wSt k (b1wW F Dθ) q (b1wN₀ F θ) F.a 0 ≤ Dd k)
    (hDp0 : ∀ k < M, Ca * fastStage b1wSt k (b1wW F Dθ) (b1wAdm s (b1wRow F θ))
      (fun k' _ => b1wNu s k') (b1wGamma F.pkg.actual.lam F.η F.a θ) F.a 0 ≤ Dp k) :
    (∀ k < M, ∀ t ∈ Icc 0 (F.b - F.a),
      slowStage b1wSt k (b1wW F Dθ) q (b1wN₀ F θ) F.a t ≤
          (1 + b1wCrudeΘ B Cw (K.Cg * ρ + ‖(cellConstantCLM 1 : ComplexCellL2)‖) *
            max 1 Ca * M * (2 + 2 / (Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16))) ^ k *
            (1 + (F.b - F.a)) ^ k * (2 * Dd k + Dp k) ∧
      fastStage b1wSt k (b1wW F Dθ) (b1wAdm s (b1wRow F θ)) (fun k' _ => b1wNu s k')
          (b1wGamma F.pkg.actual.lam F.η F.a θ) F.a t ≤
          (1 + b1wCrudeΘ B Cw (K.Cg * ρ + ‖(cellConstantCLM 1 : ComplexCellL2)‖) *
            max 1 Ca * M * (2 + 2 / (Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16))) ^ k *
            (1 + (F.b - F.a)) ^ k * (2 * Dd k + Dp k)) ∧
    ∀ r ∈ Icc F.a F.b, ∀ k < M, ∀ β : B1WIndex ι h Nw m Ks → ℂ,
      ‖∑ i ∈ stageSet b1wSt k, β i * cellComplexSource (b1wCoeff F θ).θ
          (b1wSr F src Good i r) (b1wFl F Fl Good i r) (qs r)‖ ≤
        ‖b1wN₀ F θ‖ * (b1wCrudeΘ B Cw (K.Cg * ρ + ‖(cellConstantCLM 1 : ComplexCellL2)‖) *
          ∑ k' ∈ Finset.range k,
            (1 + b1wCrudeΘ B Cw (K.Cg * ρ + ‖(cellConstantCLM 1 : ComplexCellL2)‖) *
              max 1 Ca * M * (2 + 2 / (Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16))) ^ k' *
              (1 + (F.b - F.a)) ^ k' * (2 * Dd k' + Dp k')) * stageNorm b1wSt k β := by
  set cR := K.Cg * ρ + ‖(cellConstantCLM 1 : ComplexCellL2)‖ with hcRdef
  have hCg : 0 ≤ K.Cg := F.pkg.consts_pos.2.2.2.1.le
  have hξ0 : fibreNorm (planeFibreFrequency F.η θ) < K.ξ0 := lt_of_le_of_lt hθ hρ
  have hcR : ∀ r ∈ Icc F.a F.b, ‖b1wRow F θ r + cellConstantCLM 1‖ ≤ cR := fun r _ =>
    (norm_add_le _ _).trans (add_le_add_left
      ((AVRegularity.CycleWords.scalarPackageGraphCorrection_norm_le F.pkg.actual hCg _ hξ0 r).trans
        (mul_le_mul_of_nonneg_left hθ hCg)) _)
  have hcR0 : 0 ≤ cR := (norm_nonneg _).trans (hcR F.a ⟨le_rfl, F.ordered⟩)
  have hΘ3 : B * Cw * (1 + cR + cR * Cw) ≤ b1wCrudeΘ B Cw cR := by
    unfold b1wCrudeΘ
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hB)
      (by positivity)
  have hΘ4 : B * (1 + cR + cR * Cw) ≤ b1wCrudeΘ B Cw cR := by
    unfold b1wCrudeΘ
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hB (by linarith)) (by positivity)
  have hΘ0 : 0 ≤ b1wCrudeΘ B Cw cR := (mul_nonneg hB (by positivity)).trans hΘ4
  have hNΓ : ∀ r ∈ Icc F.a F.b, ‖b1wN₀ F θ‖ * b1wGamma F.pkg.actual.lam F.η F.a θ r =
      ‖b1wSlowE F θ r‖ := fun r hr => b1w_gauge_eq F θ hξ0 hr
  have hE0 : ∀ r, b1wSlowE F θ r ≠ 0 := fun r => Complex.exp_ne_zero _
  have hW' := fun i => cellWeakHilbertCurve_indicator_forcing (b1wCoeff F θ) F.piece.hGm V
    F.piece.hv hb (hW i) Good hGood
  have H3s := b1w_crude_H3s F θ hπ hϖ F.piece.hη s n hn Dθ src Fl hval hmem Good hGsrc hGexp
    hearly B hB hprov (b1wRow F θ) q qs hGq (b1wSlowE F θ) hE hE0 Cw hCw M hrep cR hcR
    (b1wN₀ F θ) (b1wGamma F.pkg.actual.lam F.η F.a θ) hNΓ _ hΘ3
  have H4 := b1w_crude_H4 F θ hπ hϖ F.piece.hη s n hn Dθ src Fl hval hmem Good hGsrc hGexp
    hearly B hB hprov (b1wRow F θ) q (b1wSlowE F θ) hE hE0 Cw hCw M hrep cR hcR (b1wN₀ F θ)
    (b1wGamma F.pkg.actual.lam F.η F.a θ) hNΓ (b1wCoeff F θ) rfl F.piece.hGm V F.piece.hv hb
    Ca hCa hadj _ hΘ4
  have hσ : Real.pi ^ 2 / 16 < Real.pi ^ 2 / 8 := by
    have : 0 < Real.pi ^ 2 := by positivity
    linarith
  exact ⟨afw_crude_stages (b1wCoeff F θ) F.piece.hGm V F.piece.hv hb b1wSt M (b1wW F Dθ)
    (b1wWs F Dθ) (b1wSr F src Good) (b1wFl F Fl Good) hW' q qs hq (b1wN₀ F θ)
    (Complex.exp_ne_zero _) (b1wGamma F.pkg.actual.lam F.η F.a θ) (b1wGamma_pos _ _ _ _)
    (Real.pi ^ 2 / 16) (Real.pi ^ 2 / 8) hσ (b1w_gauge_growth F θ hρ hρlo hθ)
    (b1wAdm s (b1wRow F θ)) (fun k' _ => b1wNu s k') (fun k' r c ψ h => b1wAdm_smul s _ k' r c ψ h)
    (fun k' _ c ψ => b1wNu_smul s k' c ψ) (fun k' r ψ h => b1wNu_ge s k' ψ h.1) hΘ0 hCa
    H3s H4 Dd Dp hDm hDpm hD hDp hDDp hD0 hDp0,
    afw_crude_sources (b1wCoeff F θ) F.piece.hGm V F.piece.hv hb b1wSt M (b1wW F Dθ)
    (b1wWs F Dθ) (b1wSr F src Good) (b1wFl F Fl Good) hW' q qs hq (b1wN₀ F θ)
    (Complex.exp_ne_zero _) (b1wGamma F.pkg.actual.lam F.η F.a θ) (b1wGamma_pos _ _ _ _)
    (Real.pi ^ 2 / 16) (Real.pi ^ 2 / 8) hσ (b1w_gauge_growth F θ hρ hρlo hθ)
    (b1wAdm s (b1wRow F θ)) (fun k' _ => b1wNu s k') (fun k' r c ψ h => b1wAdm_smul s _ k' r c ψ h)
    (fun k' _ c ψ => b1wNu_smul s k' c ψ) (fun k' r ψ h => b1wNu_ge s k' ψ h.1) hΘ0 hCa
    H3s H4 Dd Dp hDm hDpm hD hDp hDDp hD0 hDp0⟩

end Frame

end AVRegularity.CycleWords.Assembly
end

section
namespace AVRegularity.CycleWords.Assembly

/-! # the sharp letter operators and the a.e. letter statement from the two helpers -/

universe u v

/-- `SharpLetterOpsStatement` from the two helper statements. -/
theorem sharpLetterOps_of_helpers (hG : SharpLetterGainFact.{u, v})
    (hM : SharpLetterConstMeanFact.{u, v}) : SharpLetterOpsStatement.{u, v} :=
  sharpLetterOps_of_facts (sharpLetterPair_of_gain hG) (sharpLetterSlowNorm_of_gain hG)
    (sharpLetterSlowPair_of hG hM) sharpLetterComm

/-- `SharpLetterAEStatement` from the two helper statements. -/
theorem sharpLetterAE_of_helpers (hG : SharpLetterGainFact.{u, v})
    (hM : SharpLetterConstMeanFact.{u, v}) : SharpLetterAEStatement.{u, v} :=
  sharpLetterAE_of_ops (sharpLetterOps_of_helpers hG hM)

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # The start data of the crude pass

At the start `a` of the piece the gauge is `Γ(a) = 1` and `N₀ = e^{∫_a^b λ}`, so the slow stage
is at most `‖q(a)‖/‖N₀‖` times the stage values, and the fast stage at most the stage values (the
test norm dominates `L²`). The stage values at `a` are bounded by the data `b1wDd`
(`b1w_stage_data_le`), so (`b1w_crude_data`) `slowStage(k, 0) ≤ c_q · b1wDd_k` when
`‖q(a)‖ ≤ c_q ‖e^{∫_a^b λ}‖`, and `fastStage(k, 0) ≤ b1wDd_k`. -/

section
universe u v

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The gauge is `1` at the start of the piece. -/
theorem b1wGamma_self (lam : ℕ × ℕ → ℝ → ℂ) (η a : ℝ) (θ : Vec 2) :
    b1wGamma lam η a θ a = 1 := by
  unfold b1wGamma blockGauge
  rw [intervalIntegral.integral_same, neg_zero, Complex.exp_zero, norm_one]

/-- **The start data of the crude pass.** -/
theorem b1w_crude_data (hL : LevelZeroDataStatement.{v}) {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (s : ℕ → ℕ) (tr : ℝ → ComplexCellL2) (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ)
    (hval : ∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
        inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y)))
    (hmem : ∀ i, ∀ t ∈ Icc F.a F.b,
      MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube))
    (q : ℝ → ComplexCellL2) (cq : ℝ) (hqa : ‖q F.a‖ ≤ cq * ‖b1wSlowE F θ F.a‖) (k : ℕ) :
    slowStage b1wSt k (b1wW F Dθ) q (b1wN₀ F θ) F.a 0 ≤
        cq * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k ∧
      fastStage b1wSt k (b1wW F Dθ) (b1wAdm s tr) (fun k' _ => b1wNu s k')
          (b1wGamma F.pkg.actual.lam F.η F.a θ) F.a 0 ≤
        b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k := by
  have hϖ : 0 ≤ F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_nonneg _
  have hX := b1w_stage_data_le hL F m Ks θ Dθ hval hmem hϖ k
  set X := Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖b1wW F Dθ i F.a‖ ^ 2) with hXdef
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hE : 0 < ‖b1wSlowE F θ F.a‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have hN : b1wN₀ F θ = b1wSlowE F θ F.a := rfl
  have ha : F.a + 0 = F.a := add_zero _
  refine ⟨?_, ?_⟩
  · unfold slowStage
    rw [ha, hN]
    have hs : stageNorm b1wSt k (fun i => cellComplexPair (b1wW F Dθ i F.a) (q F.a)) ≤
        ‖q F.a‖ * X :=
      sqrt_sum_sq_le_mul _ _ _ (norm_nonneg _) (fun i _ => norm_nonneg _)
        (fun i _ => (cellComplexPair_norm_le _ _).trans_eq (mul_comm _ _))
    have hcq : 0 ≤ cq := by
      by_contra hc
      push Not at hc
      have : cq * ‖b1wSlowE F θ F.a‖ < 0 := mul_neg_of_neg_of_pos hc hE
      linarith [norm_nonneg (q F.a)]
    calc stageNorm b1wSt k (fun i => cellComplexPair (b1wW F Dθ i F.a) (q F.a)) /
          ‖b1wSlowE F θ F.a‖
        ≤ ‖q F.a‖ * X / ‖b1wSlowE F θ F.a‖ := div_le_div_of_nonneg_right hs hE.le
      _ ≤ cq * ‖b1wSlowE F θ F.a‖ * X / ‖b1wSlowE F θ F.a‖ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hqa hX0) hE.le
      _ = cq * X := by rw [div_eq_iff hE.ne']; ring
      _ ≤ cq * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k :=
          mul_le_mul_of_nonneg_left hX hcq
  · unfold fastStage
    rw [ha, b1wGamma_self, one_mul]
    refine (Real.sSup_le (fun y hy => ?_) hX0).trans hX
    obtain ⟨ψ, hψ, hψ1, rfl⟩ := hy
    calc ‖∑ i ∈ stageSet b1wSt k, cellComplexPair (b1wW F Dθ i F.a) (ψ i)‖
        ≤ ∑ i ∈ stageSet b1wSt k, ‖b1wW F Dθ i F.a‖ * ‖ψ i‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => cellComplexPair_norm_le _ _)
      _ ≤ X * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ X * Real.sqrt (∑ i ∈ stageSet b1wSt k, b1wNu s k (ψ i) ^ 2) := by
          refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Finset.sum_le_sum fun i hi => ?_))
            hX0
          exact pow_le_pow_left₀ (norm_nonneg _) (b1wNu_ge s k _ (hψ i hi).1) 2
      _ ≤ X * 1 := mul_le_mul_of_nonneg_left hψ1 hX0
      _ = X := mul_one X

/-- **The fast start data for any test norm** dominating the `L²` norm on the admissible tests. -/
theorem b1w_fast_data (hL : LevelZeroDataStatement.{v}) {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ)
    (hval : ∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
        inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y)))
    (hmem : ∀ i, ∀ t ∈ Icc F.a F.b,
      MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube))
    (Adm : ℕ → ℝ → ComplexCellL2 → Prop) (ν : ℕ → ℝ → ComplexCellL2 → ℝ) (k : ℕ)
    (hνL : ∀ ψ, Adm k F.a ψ → ‖ψ‖ ≤ ν k F.a ψ) :
    fastStage b1wSt k (b1wW F Dθ) Adm ν (b1wGamma F.pkg.actual.lam F.η F.a θ) F.a 0 ≤
      b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k := by
  have hϖ : 0 ≤ F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_nonneg _
  have hX := b1w_stage_data_le hL F m Ks θ Dθ hval hmem hϖ k
  set X := Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖b1wW F Dθ i F.a‖ ^ 2) with hXdef
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have ha : F.a + 0 = F.a := add_zero _
  unfold fastStage
  rw [ha, b1wGamma_self, one_mul]
  refine (Real.sSup_le (fun y hy => ?_) hX0).trans hX
  obtain ⟨ψ, hψ, hψ1, rfl⟩ := hy
  calc ‖∑ i ∈ stageSet b1wSt k, cellComplexPair (b1wW F Dθ i F.a) (ψ i)‖
      ≤ ∑ i ∈ stageSet b1wSt k, ‖b1wW F Dθ i F.a‖ * ‖ψ i‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => cellComplexPair_norm_le _ _)
    _ ≤ X * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ X * Real.sqrt (∑ i ∈ stageSet b1wSt k, ν k F.a (ψ i) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Finset.sum_le_sum fun i hi => ?_))
          hX0
        exact pow_le_pow_left₀ (norm_nonneg _) (hνL _ (hψ i hi)) 2
    _ ≤ X * 1 := mul_le_mul_of_nonneg_left hψ1 hX0
    _ = X := mul_one X

end Frame
end

/-! # The crude pass on one frame, by parts

The crude ladder is `s₀ = d_max + 4` (`b1wCrudeS`, top `b1wCrudeTop`). With constants chosen
before the frame:
* the slow test of a frame, with representatives on the ladder (`b1w_slow_frame`, constants
  `C_s P_e^{Q_s}` of `b1wSlowTest_full` at the top);
* the crude adjoint uniform over the stages `k < M` (`b1w_adj_frame`, constant
  `(∑ C_k) P_e^{∑ Q_k}` of `b1w_crude_adjoint`). -/

section
universe u v

/-- The crude ladder, `s₀ = d_max + 4`. -/
def b1wCrudeS {Nw : ℕ} (d Ks : Fin Nw → ℕ) : ℕ → ℕ :=
  b1wLadderAt Nw (Finset.univ.sup d + 4) d Ks

/-- The top of the crude ladder. -/
def b1wCrudeTop {Nw : ℕ} (m : ℕ) (d Ks : Fin Nw → ℕ) : ℕ :=
  b1wLadderTop (Finset.univ.sup d + 4) d Ks m

/-- The jet bounds of a piece's drift, made nonnegative. -/
def b1wJets (K : ScalarConstants) : ℕ → ℝ := fun l => max (K.Cvj l) 0

/-- **The slow test of a frame** with its representatives on the crude ladder. -/
theorem b1w_slow_frame (hR : CellDriftRegularityStatement) (K : ScalarConstants) {Nw : ℕ}
    (m : ℕ) (d Ks : Fin Nw → ℕ) {ρ : ℝ} (hρ : ρ < K.ξ0) (hρlo : ρ ≤ 2 * K.ξlo) (hρ0 : 0 ≤ ρ) :
    ∃ (Cs : ℝ) (Qs : ℕ), 0 < Cs ∧
    ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}
      (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
      fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
      ∀ (V : ℝ) (hb : ∀ t x, ∑ i, F.v t x i ^ 2 ≤ V ^ 2),
      ∃ (q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve F.a F.b q qs (fun t =>
          -cellDualDerivative (cellAdjointCoefficients (b1wCoeff F θ)) F.piece.hGm V
            (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) t (qs t) 0 0) ∧
        q F.b = cellConstantCLM 1 ∧
        (∀ r ∈ Icc F.a F.b,
          cellComplexPair (b1wRow F θ r + cellConstantCLM 1) (q r) = b1wSlowE F θ r) ∧
        ‖q F.a‖ ≤ (1 + |rowConst K (4 * (ρ + K.Cw)) ρ| * ρ) * ‖b1wSlowE F θ F.a‖ ∧
        ∀ r ∈ Icc F.a F.b, ∀ k < b1wM Nw m Ks, ∃ U : TorusHk (b1wCrudeS d Ks k) ℂ,
          torusHkValueCLM U = q r ∧ ‖U‖ ≤ Cs * peFactor F.η ^ Qs * ‖b1wSlowE F θ r‖ := by
  obtain ⟨Cs, Qs, hCs, hslow⟩ := b1wSlowTest_full (K := K) hR (b1wCrudeTop m d Ks) hρ0
    (b1wJets K) (fun l => le_max_right _ _)
  refine ⟨Cs, Qs, hCs, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ D F θ hθ V hb
  have H := b1w_transverseLocalHyp F θ hρ hρlo hθ
  obtain ⟨q, qs, hqc, hqb, hqr⟩ := hslow F.η F.G F.v (planeFibreFrequency F.η θ) H F.pkg.actual
    F.piece.hη hθ F.piece.hvs (fun l t z => (F.piece.hvj l t z).trans (le_max_left _ _)) V hb
    F.ordered
  refine ⟨q, qs, hqc, hqb, fun r hr => (hqr r hr).1, ?_, fun r hr => ?_⟩
  · refine (hqr F.a ⟨le_rfl, F.ordered⟩).2.1.trans
      (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self (rowConst K (4 * (ρ + K.Cw)) ρ)) hρ0
    linarith
  · obtain ⟨w, hwq, hw⟩ := (hqr r hr).2.2
    exact b1w_slow_reps (Finset.univ.sup d + 4) m d Ks w hwq hw

/-- **The crude adjoint of a frame**, uniform over the stages `k < M`. -/
theorem b1w_adj_frame (hR : CellDriftRegularityStatement) (K : ScalarConstants) {Nw : ℕ}
    (m : ℕ) (d Ks : Fin Nw → ℕ) {ρ : ℝ} (hρ : ρ < K.ξ0) (hρlo : ρ ≤ 2 * K.ξlo) (hρ0 : 0 ≤ ρ) :
    ∃ (Ca' : ℝ) (Qa : ℕ), 0 ≤ Ca' ∧
    ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}
      (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
      fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
      ∀ (V : ℝ) (hb : ∀ t x, ∑ i, F.v t x i ^ 2 ≤ V ^ 2),
      ∀ k < b1wM Nw m Ks, ∀ T ∈ Icc F.a F.b, ∀ ψ : ComplexCellL2,
        b1wAdm (b1wCrudeS d Ks) (b1wRow F θ) k T ψ →
        ∃ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ),
          CellWeakHilbertCurve F.a T Ψv Ψs (fun r =>
            -cellDualDerivative (cellAdjointCoefficients (b1wCoeff F θ)) F.piece.hGm V
              (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) r (Ψs r) 0 0) ∧
          Ψv T = ψ ∧
          ∀ r ∈ Icc F.a T, b1wAdm (b1wCrudeS d Ks) (b1wRow F θ) k r (Ψv r) ∧
            b1wNu (b1wCrudeS d Ks) k (Ψv r) ≤ Ca' * peFactor F.η ^ Qa *
              Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) * b1wNu (b1wCrudeS d Ks) k ψ := by
  choose Ck Qk hCk hadjk using fun k => b1w_crude_adjoint (K := K) hR (b1wCrudeS d Ks) k hρ0
    (b1wJets K) (fun l => le_max_right _ _)
  have hCa'0 : 0 ≤ ∑ k ∈ Finset.range (b1wM Nw m Ks), Ck k :=
    Finset.sum_nonneg fun k _ => (hCk k).le
  refine ⟨∑ k ∈ Finset.range (b1wM Nw m Ks), Ck k, ∑ k ∈ Finset.range (b1wM Nw m Ks), Qk k,
    hCa'0, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ D F θ hθ V hb k hk T hT ψ hψ
  have H := b1w_transverseLocalHyp F θ hρ hρlo hθ
  have hP := one_le_peFactor F.η
  obtain ⟨Ψv, Ψs, h1, h2, h3⟩ := hadjk k F.η F.G F.v (planeFibreFrequency F.η θ) H F.pkg.actual
    F.piece.hη hθ F.piece.hvs (fun l t z => (F.piece.hvj l t z).trans (le_max_left _ _)) V hb
    hT.1 ψ hψ
  refine ⟨Ψv, Ψs, h1, h2, fun r hr => ⟨(h3 r hr).1, (h3 r hr).2.trans ?_⟩⟩
  have hk' : k ∈ Finset.range (b1wM Nw m Ks) := Finset.mem_range.2 hk
  have hC : Ck k * peFactor F.η ^ Qk k ≤ (∑ k ∈ Finset.range (b1wM Nw m Ks), Ck k) *
      peFactor F.η ^ (∑ k ∈ Finset.range (b1wM Nw m Ks), Qk k) :=
    mul_le_mul (Finset.single_le_sum (f := Ck) (fun k _ => (hCk k).le) hk')
      (pow_le_pow_right₀ hP (Finset.single_le_sum (f := Qk) (fun _ _ => Nat.zero_le _) hk'))
      (pow_nonneg (zero_le_one.trans hP) _) hCa'0
  have he : 0 ≤ Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) * b1wNu (b1wCrudeS d Ks) k ψ :=
    mul_nonneg (Real.exp_pos _).le (b1wNu_nonneg _ _ _)
  calc Ck k * peFactor F.η ^ Qk k * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) *
        b1wNu (b1wCrudeS d Ks) k ψ
      = Ck k * peFactor F.η ^ Qk k *
          (Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) * b1wNu (b1wCrudeS d Ks) k ψ) := by ring
    _ ≤ (∑ k ∈ Finset.range (b1wM Nw m Ks), Ck k) *
          peFactor F.η ^ (∑ k ∈ Finset.range (b1wM Nw m Ks), Qk k) *
          (Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) * b1wNu (b1wCrudeS d Ks) k ψ) :=
        mul_le_mul_of_nonneg_right hC he
    _ = _ := by ring

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The good times of a frame**: the a.e. facts of the crude pass hold together on a set of full
measure. -/
theorem b1w_good_frame {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (s : ℕ → ℕ) (n : ℕ) (B : ℝ) (src : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → ℂ)
    (Fl : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ)
    (hlit : ∀ i, ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
      src i r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralSource F θ i.1 i.2.1
        (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) i.2.2.1.1 r ∧
      Fl i r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralFlux F θ i.1 i.2.1
        (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) i.2.2.1.1 r)
    (hsl : ∀ i, ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
      MemLp (src i r) 2 (volume.restrict AVenhance.unitCube) ∧
        ∀ j : Fin 2, MemLp (fun z => Fl i r z j) 2 (volume.restrict AVenhance.unitCube))
    (hexp : ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
      ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ), ContDiff ℝ n φ →
        AVenhance.IsZ2Periodic φ →
        b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
          ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
            b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hfam : ∀ᵐ r ∂volume.restrict (Icc F.a F.b), ∀ (k k' : ℕ), k' < k →
      ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (s k) ℂ,
        ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
          (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
            =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
              ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
                star (b1wTestTransform F θ i i' r (fun y => star
                  (torusHigherClassicalValue (s k) (ψ i) y)) y)) ∧
          ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)
    (hag : ∀ᵐ t ∂volume.restrict (Icc F.a F.b), q t = torusHkValueCLM (qs t)) :
    ∃ Good : Set ℝ, (∀ᵐ t ∂volume.restrict (Icc F.a F.b), t ∈ Good) ∧
      (∀ r ∈ Good, ∀ i, MemLp (src i r) 2 (volume.restrict AVenhance.unitCube) ∧
        src i r =ᵐ[volume.restrict AVenhance.unitCube]
          amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r ∧
        (∀ j : Fin 2, MemLp (fun z => Fl i r z j) 2 (volume.restrict AVenhance.unitCube)) ∧
        Fl i r =ᵐ[volume.restrict AVenhance.unitCube]
          amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r) ∧
      (∀ r ∈ Good, ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ), ContDiff ℝ n φ →
        AVenhance.IsZ2Periodic φ →
        b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
          ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
            b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y) ∧
      (∀ r ∈ Good, ∀ (k k' : ℕ), k' < k → ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (s k) ℂ,
        ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
          (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
            =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
              ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
                star (b1wTestTransform F θ i i' r (fun y => star
                  (torusHigherClassicalValue (s k) (ψ i) y)) y)) ∧
          ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) ∧
      ∀ r ∈ Good, torusHkValueCLM (qs r) = q r := by
  refine ⟨{r | (∀ i, MemLp (src i r) 2 (volume.restrict AVenhance.unitCube) ∧
        src i r =ᵐ[volume.restrict AVenhance.unitCube]
          amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r ∧
        (∀ j : Fin 2, MemLp (fun z => Fl i r z j) 2 (volume.restrict AVenhance.unitCube)) ∧
        Fl i r =ᵐ[volume.restrict AVenhance.unitCube]
          amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r) ∧
      (∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ), ContDiff ℝ n φ →
        AVenhance.IsZ2Periodic φ →
        b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
          ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
            b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y) ∧
      (∀ (k k' : ℕ), k' < k → ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (s k) ℂ,
        ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
          (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
            =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
              ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
                star (b1wTestTransform F θ i i' r (fun y => star
                  (torusHigherClassicalValue (s k) (ψ i) y)) y)) ∧
          ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) ∧
      torusHkValueCLM (qs r) = q r}, ?_, fun r hr => hr.1, fun r hr => hr.2.1,
    fun r hr => hr.2.2.1, fun r hr => hr.2.2.2⟩
  filter_upwards [ae_all_iff.2 hlit, ae_all_iff.2 hsl, hexp, hfam, hag] with r h1 h2 h3 h4 h5
  exact ⟨fun i => ⟨(h2 i).1, (h1 i).1, (h2 i).2, (h1 i).2⟩, h3, h4, h5.symm⟩

end Frame
end

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # The block statement and the assembly of the two letter helpers

`SlBlockStmt` is the block statement (proved as `slBlockStmt`): for every pair of components and
moments, the gain family `letterGfamP true` and the zero family `letterGfamP false` of the letter
transform are realized by operators on `H^{n + d l}` (through the truncation) with
* block norm `O(ϖ)` for the gain operators,
* block mean `O(t)` and block norm on constants `O(t)` for the zero operators (`t = |ξ|`),
* block mean on constants `O(ζ²)` for the sum;
the constants carry the norm `kc = ‖const_{n + d l} 1‖` of the constants. `slOps_of_blocks`
assembles the operator families on the basis indices, and the two letter helpers
`SharpLetterGainFact` and `SharpLetterConstMeanFact` follow. -/

universe u v

open Classical in
/-- **The block statement.** The block bundle of the gain and zero families. -/
def SlBlockStmt : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ)
    (n : ℕ),
  ∃ C0 : ℝ, 0 ≤ C0 ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    n + (Finset.univ.sup d) ≤ F.J →
    fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (l : Fin Nw) (x x' : ι) (β β' : ℕ × ℕ),
    β.1 + β.2 ≤ m + ∑ l, Ks l → β'.1 + β'.2 ≤ m + ∑ l, Ks l →
      SlBlockSplit (n + d l) n (d l + 3)
        (letterGfamP true θ (F.letters l)
          (admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D (l.succ, x)
            (l.castSucc, x')) (F.ϖ * F.ηg) F.X₀ r x x' β β'
          (letterRatioReal F.π F.ϖ F.ηg F.letters l x x' β β'))
        (letterGfamP false θ (F.letters l)
          (admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D (l.succ, x)
            (l.castSucc, x')) (F.ϖ * F.ηg) F.X₀ r x x' β β'
          (letterRatioReal F.π F.ϖ F.ηg F.letters l x x' β β'))
        (C0 * F.ϖ * ((if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) β β'
            then 1 else 0) * letterCompWeight (F.letters l) x x'))
        (C0 * fibreNorm (planeFibreFrequency F.η θ) *
          ((if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) β β'
            then 1 else 0) * letterCompWeight (F.letters l) x x'))
        (C0 * fibreNorm (planeFibreFrequency F.η θ) *
          ((if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) β β'
            then 1 else 0) * letterCompWeight (F.letters l) x x') *
          ‖torusHigherConstant (n + d l) 1‖)
        (C0 * (min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹)) ^ 2 *
          ((if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) β β'
            then 1 else 0) * letterCompWeight (F.letters l) x x') *
          ‖torusHigherConstant (n + d l) 1‖)

theorem slc_sq (C C' a b S : ℝ) (hC : 0 ≤ C) (hCC : C ≤ C') (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hS : 0 ≤ S) : (C * a * b) ^ 2 * S ≤ (C' * a * b) ^ 2 * S :=
  mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (mul_nonneg (mul_nonneg hC ha) hb)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC ha) hb) 2) hS

theorem slc_const (C0 Kc kc t w P Q : ℝ) (hC : 0 ≤ C0) (hkc : kc ≤ Kc) (hkc0 : 0 ≤ kc)
    (ht : 0 ≤ t) (hw : 0 ≤ w) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (C0 * t * w * kc) ^ 2 * (P * Q) ≤ (C0 * (1 + Kc) * t * w) ^ 2 * P * Q := by
  have h1 : C0 * t * w * kc ≤ C0 * (1 + Kc) * t * w := by
    have : 0 ≤ C0 * t * w := by positivity
    calc C0 * t * w * kc ≤ C0 * t * w * (1 + Kc) :=
          mul_le_mul_of_nonneg_left (by linarith) this
      _ = _ := by ring
  have h0 : 0 ≤ C0 * t * w * kc := by positivity
  calc (C0 * t * w * kc) ^ 2 * (P * Q) ≤ (C0 * (1 + Kc) * t * w) ^ 2 * (P * Q) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) (by positivity)
    _ = _ := by ring

theorem slc_const2 (C0 Kc kc z w P Q : ℝ) (hC : 0 ≤ C0) (hkc : kc ≤ Kc) (hkc0 : 0 ≤ kc)
    (hw : 0 ≤ w) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (C0 * z ^ 2 * w * kc) ^ 2 * (P * Q) ≤ (C0 * (1 + Kc) * z ^ 2 * w) ^ 2 * P * Q :=
  slc_const C0 Kc kc (z ^ 2) w P Q hC hkc hkc0 (sq_nonneg z) hw hP hQ

theorem slConst_le_sum {Nw : ℕ} (d : Fin Nw → ℕ) (n : ℕ) (l : Fin Nw) :
    ‖torusHigherConstant (n + d l) 1‖ ≤ ∑ l, ‖torusHigherConstant (n + d l) 1‖ :=
  Finset.single_le_sum (f := fun l => ‖torusHigherConstant (n + d l) 1‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ l)

open Classical in
/-- **The gain helper `SharpLetterGainFact` from the block statement.** -/
theorem sharpLetterGainFact_of_blocks (hB : SlBlockStmt.{u, v}) : SharpLetterGainFact.{u, v} := by
  intro K Nw D m d Ks pos ρ n
  obtain ⟨C0, hC0, hk⟩ := hB K Nw D m d Ks pos ρ n
  have hKc : 0 ≤ ∑ l, ‖torusHigherConstant (n + d l) 1‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨C0 * (1 + ∑ l, ‖torusHigherConstant (n + d l) 1‖), by positivity, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  filter_upwards [hk g₁ F θ hlet hJ hρ] with r hr
  intro l N hN1 hN2
  have hdN : d l + 3 ≤ N := by
    have := Finset.le_sup (f := d) (Finset.mem_univ l)
    omega
  obtain ⟨Tg, T0, hv, hb⟩ := slOps_of_blocks F θ r l n N (n + d l) (d l + 3) hN1 hdN
    (m + ∑ l, Ks l) stage_mom_le _ _ _ _ (fun x x' β β' hβ hβ' => hr l x x' β β' hβ hβ')
  refine ⟨Tg, T0, hv, fun S S' x x' β β' hS hS' => ?_⟩
  intro w0
  obtain ⟨b1, b2, b3, -⟩ := hb S S' x x' β β' hS hS'
  have hw0 : 0 ≤ w0 := mul_nonneg (by split_ifs <;> simp)
    (letterCompWeight_nonneg (F.piece.hlet l) x x')
  have hx0 := fibreNorm_nonneg (planeFibreFrequency F.η θ)
  obtain ⟨hv0, -⟩ := sl80_varpi F θ
  have hkc := slConst_le_sum d n l
  have hS0 : ∀ f : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
      0 ≤ ∑ i ∈ S, ‖truncateTorusHk hN1 (f i)‖ ^ 2 := fun f => Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨fun f => (b1 f).trans (slc_sq C0 _ F.ϖ w0 _ hC0 ?_ hv0 hw0 (hS0 f)),
    fun f => (b2 f).trans (slc_sq C0 _ _ w0 _ hC0 ?_ hx0 hw0 (Finset.sum_nonneg fun _ _ => by positivity)),
    fun E b => ?_⟩
  · nlinarith
  · nlinarith
  · refine (b3 E b).trans ?_
    have := slc_const C0 (∑ l, ‖torusHigherConstant (n + d l) 1‖) _ _ w0 (‖E‖ ^ 2)
      (∑ i ∈ S, ‖b i‖ ^ 2) hC0 hkc (norm_nonneg _) hx0 hw0 (sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => by positivity)
    exact this.trans (le_of_eq (by ring))

open Classical in
/-- **The constant mean helper `SharpLetterConstMeanFact` from the block statement.** -/
theorem sharpLetterConstMeanFact_of_blocks (hB : SlBlockStmt.{u, v}) :
    SharpLetterConstMeanFact.{u, v} := by
  intro K Nw D m d Ks pos ρ n
  obtain ⟨C0, hC0, hk⟩ := hB K Nw D m d Ks pos ρ n
  have hKc : 0 ≤ ∑ l, ‖torusHigherConstant (n + d l) 1‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨C0 * (1 + ∑ l, ‖torusHigherConstant (n + d l) 1‖), by positivity, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  filter_upwards [hk g₁ F θ hlet hJ hρ] with r hr
  intro l N hN1 hN2 T hT S S' x x' β β' hS hS' w0 ζ E b
  have hdN : d l + 3 ≤ N := by
    have := Finset.le_sup (f := d) (Finset.mem_univ l)
    omega
  obtain ⟨Tg, T0, hv, hb⟩ := slOps_of_blocks F θ r l n N (n + d l) (d l + 3) hN1 hdN
    (m + ∑ l, Ks l) stage_mom_le _ _ _ _ (fun x x' β β' hβ hβ' => hr l x x' β β' hβ hβ')
  obtain ⟨-, -, -, b4⟩ := hb S S' x x' β β' hS hS'
  have hw0 : 0 ≤ w0 := mul_nonneg (by split_ifs <;> simp)
    (letterCompWeight_nonneg (F.piece.hlet l) x x')
  have hkc := slConst_le_sum d n l
  have hζ : 0 ≤ ζ := le_min zero_le_one (by
    have := fibreNorm_nonneg (planeFibreFrequency F.η θ)
    have : 0 ≤ (Real.sqrt F.S)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    linarith)
  have hsplit : ∀ i' ∈ S', ∑ i ∈ S, T i i' (torusHigherScalarCLM N (b i) (torusHigherConstant N E)) =
      ∑ i ∈ S, (Tg i i' + T0 i i') (torusHigherScalarCLM N (b i) (torusHigherConstant N E)) := by
    intro i' hi'
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [sl80_split (T := T) (Tg := Tg) (T0 := T0) hT hv i i' (hS i hi).1 (hS' i' hi').1]
    rfl
  rw [Finset.sum_congr rfl fun i' hi' => by rw [hsplit i' hi']]
  refine (b4 E b).trans ?_
  have := slc_const2 C0 (∑ l, ‖torusHigherConstant (n + d l) 1‖) _ ζ w0 (‖E‖ ^ 2)
    (∑ i ∈ S, ‖b i‖ ^ 2) hC0 hkc (norm_nonneg _) hw0 (sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => by positivity)
  exact this.trans (le_of_eq (by ring))

/-- `SharpLetterAEStatement` from the block statement. -/
theorem sharpLetterAE_of_blocks (hB : SlBlockStmt.{u, v}) : SharpLetterAEStatement.{u, v} :=
  sharpLetterAE_of_helpers (sharpLetterGainFact_of_blocks hB) (sharpLetterConstMeanFact_of_blocks hB)

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # The objects of the crude pass for one frame

From the inputs of the word fibre facts (the measurable fibre clause and the moments of the
amplitude identification, letterBloch, the stage expansion, the transform bounds, the cell drift
regularity, the level-0 data identity), with constants chosen before the frame (the transform
constant `B`, the slow test's `C_s P_e^{Q_s}`, the crude adjoint's `C_k P_e^{Q_k}` for the stages
`k < M`), every frame at a frequency of the disc has the objects of the crude pass
(`b1w_crude_objects`):
* the stage curves `W_i = c_i Dθ_i` with the forcing set to `0` off the good times;
* the slow test `q` from `1` at `b`;
* the start data, `slowStage(k, 0) ≤ c_q b1wDd_k`;
* the crude source bound `‖∑ β_i src_i(q(r))‖ ≤ ‖N₀‖ ε_k ‖β‖` at every time (`b1w_crude_pass`);
* the budget `ε_k (b − a) ≤ C₂ P_e^{Q₂} (1 + S)^{Q₂} b1wDd_k` (`crude_eps_le`).

The ladder is `s₀ = d_max + 4`, and the tests are `C^{d_max+1}`. -/

universe u v

/-- **The objects of the crude pass for one frame.** -/
theorem b1w_crude_objects (hR : CellDriftRegularityStatement) (hL : LevelZeroDataStatement.{v})
    (hSL : SameLevelTransformBoundStatement.{u, v})
    (hLT : LetterTransformBoundAEStatement.{u, v}) (hLB : LetterBlochStatement.{u, v})
    (hExp : StageExpansionStatement.{u, v}) (hEarly : StageTransformEarlierStatement.{u, v})
    (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ)
    (hρ : ρ < K.ξ0) (hρlo : ρ ≤ 2 * K.ξlo) (hρ0 : 0 ≤ ρ) :
    ∃ (Q₂ Q₃ : ℕ), ∀ CH : ℝ, 0 ≤ CH →
    ∃ (C₂ cq C₃ : ℝ), 0 ≤ C₂ ∧ 0 ≤ cq ∧ 0 ≤ C₃ ∧
    ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
      (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
        (F.letters l).positive = pos l) →
      b1wLadderTop (Finset.univ.sup d + 4) d Ks m + Finset.univ.sup d ≤ F.J →
      fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
      F.b - F.a ≤ CH * F.S →
      AmplitudeIdMoments F →
      (∀ (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ),
        ∃ (Dθ : ℝ → RawJet2 1 ℂ) (src : ℝ → Vec 2 → ℂ)
          (Fl : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)),
          MemLp (Function.uncurry src) 2
            ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube)) ∧
          (∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Fl p.1 p.2 k) 2
            ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube))) ∧
          (∀ᵐ r ∂volume.restrict (Icc F.a F.b),
            src r =ᵐ[volume.restrict AVenhance.unitCube]
              amplitudeIdLiteralSource F θ j x e β r ∧
            Fl r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralFlux F θ j x e β r) ∧
          IsCellSolution (Icc F.a F.b)
            (fibreCoefficients F.η F.G F.v (planeFibreFrequency F.η θ) (fun _ => 0)) src Fl Dθ ∧
          ∀ t ∈ Icc F.a F.b, cellValue Dθ t =ᵐ[volume.restrict AVenhance.unitCube]
            planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x t) y))) →
      ∃ (V : ℝ) (hb : ∀ t x, ∑ i, F.v t x i ^ 2 ≤ V ^ 2)
        (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ)
        (src : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → ℂ)
        (Fl : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (Good : Set ℝ)
        (q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ) (εs : ℕ → ℝ),
        (∀ i, CellWeakHilbertCurve F.a F.b (b1wW F Dθ i) (b1wWs F Dθ i) (fun t =>
          cellDualDerivative (b1wCoeff F θ) F.piece.hGm V F.piece.hv.1 hb t (b1wWs F Dθ i t)
            (b1wSr F src Good i t) (b1wFl F Fl Good i t))) ∧
        CellWeakHilbertCurve F.a F.b q qs (fun t =>
          -cellDualDerivative (cellAdjointCoefficients (b1wCoeff F θ)) F.piece.hGm V
            (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) t (qs t) 0 0) ∧
        q F.b = cellConstantCLM 1 ∧
        (∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
          planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
            inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y))) ∧
        (∀ i, ∀ t ∈ Icc F.a F.b,
          MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube)) ∧
        (∀ k, slowStage b1wSt k (b1wW F Dθ) q (b1wN₀ F θ) F.a 0 ≤
          cq * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k) ∧
        Monotone εs ∧ (∀ k, 0 ≤ εs k) ∧
        (∀ r ∈ Icc F.a F.b, ∀ k < b1wM Nw m Ks, ∀ β : B1WIndex ι h Nw m Ks → ℂ,
          ‖∑ i ∈ stageSet b1wSt k, β i * cellComplexSource (b1wCoeff F θ).θ
              (b1wSr F src Good i r) (b1wFl F Fl Good i r) (qs r)‖ ≤
            ‖b1wN₀ F θ‖ * εs k * stageNorm b1wSt k β) ∧
        (∀ k ≤ b1wM Nw m Ks, εs k * (F.b - F.a) ≤
          C₂ * peFactor F.η ^ Q₂ * (1 + F.S) ^ Q₂ *
            b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k) ∧
        ∀ k < b1wM Nw m Ks, ∀ t ∈ Icc 0 (F.b - F.a),
          slowStage b1wSt k (b1wW F Dθ) q (b1wN₀ F θ) F.a t ≤
              C₃ * peFactor F.η ^ Q₃ * (1 + F.S) ^ Q₃ *
                b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k ∧
            fastStage b1wSt k (b1wW F Dθ) (b1wAdm (b1wCrudeS d Ks) (b1wRow F θ))
                (fun k' _ => b1wNu (b1wCrudeS d Ks) k')
                (b1wGamma F.pkg.actual.lam F.η F.a θ) F.a t ≤
              C₃ * peFactor F.η ^ Q₃ * (1 + F.S) ^ Q₃ *
                b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k := by
  classical
  obtain ⟨B, hB0, hprov⟩ := b1w_family_provider hSL hLT K Nw D m d Ks pos ρ
    (Finset.univ.sup d + 4) (by omega)
  obtain ⟨Cs, Qs, hCs, hslowF⟩ := b1w_slow_frame.{u, v} hR K m d Ks hρ hρlo hρ0
  obtain ⟨Ca', Qa, hCa'0, hadjF⟩ := b1w_adj_frame.{u, v} hR K m d Ks hρ hρlo hρ0
  obtain ⟨cq, hcq⟩ : ∃ cq : ℝ, cq = 1 + |rowConst K (4 * (ρ + K.Cw)) ρ| * ρ := ⟨_, rfl⟩
  have hcq0 : 0 ≤ cq := by rw [hcq]; positivity
  refine ⟨2 * Qs + (2 * Qs + Qa) * b1wM Nw m Ks + Qa + b1wM Nw m Ks + 1,
    (2 * Qs + Qa) * b1wM Nw m Ks + Qa + b1wM Nw m Ks, fun CH hCH => ?_⟩
  refine ⟨3 * (B * (1 + Cs) ^ 2 * (1 + (|K.Cg| * ρ + 1))) * (cq + Ca') * b1wM Nw m Ks *
      (1 + B * (1 + Cs) ^ 2 * (1 + (|K.Cg| * ρ + 1)) * (1 + Ca') * b1wM Nw m Ks *
        (2 + 2 / (Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16))) ^ b1wM Nw m Ks *
      (1 + CH) ^ (b1wM Nw m Ks + 1), cq,
    3 * (cq + Ca') * (1 + B * (1 + Cs) ^ 2 * (1 + (|K.Cg| * ρ + 1)) * (1 + Ca') * b1wM Nw m Ks *
        (2 + 2 / (Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16))) ^ b1wM Nw m Ks *
      (1 + CH) ^ b1wM Nw m Ks, ?_, hcq0, ?_, ?_⟩
  · have hc₁ : 0 ≤ 2 + 2 / (Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16) := by
      have : 0 < Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16 := by
        have : 0 < Real.pi ^ 2 := by positivity
        linarith
      positivity
    have := hCs.le
    positivity
  · have hc₁ : 0 ≤ 2 + 2 / (Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16) := by
      have : 0 < Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16 := by
        have : 0 < Real.pi ^ 2 := by positivity
        linarith
      positivity
    have := hCs.le
    positivity
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJF hθ hT hmom hmeas
  have hP : 1 ≤ peFactor F.η := one_le_peFactor F.η
  have hP0 : 0 ≤ peFactor F.η := zero_le_one.trans hP
  have hϖ : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
  have hCg : 0 < K.Cg := F.pkg.consts_pos.2.2.2.1
  obtain ⟨V, hb⟩ := F.piece.hv.2.1
  obtain ⟨q, qs, hqc, hqb, hE, hqa, hrep⟩ := hslowF g₁ F θ hθ V hb
  have hadj := hadjF g₁ F θ hθ V hb
  obtain ⟨Dθ, src, Fl, hcur, hval, hlit, hmem, hsl⟩ := b1w_stage_curves F m Ks θ hmeas V hb
    (b1wScale F.π F.ϖ F.ηg F.letters)
  -- the a.e. facts and the good times
  have hdl : ∀ l, d l ≤ Finset.univ.sup d := fun l => Finset.le_sup (f := d) (Finset.mem_univ l)
  have hord : ∀ l, (F.letters l).order ≤ F.J := fun l => by
    rw [(hlet l).1]
    have := hdl l
    omega
  have hsup : (Finset.univ.sup fun l => (F.letters l).order) = Finset.univ.sup d := by
    congr 1
    funext l
    exact (hlet l).1
  have hexp : ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
      ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ), ContDiff ℝ (Finset.univ.sup d + 1) φ →
        AVenhance.IsZ2Periodic φ →
        b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
          ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
            b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y := by
    filter_upwards [hExp K g₁ F θ m Ks (fun l => (hlet l).2.1) hord hLB hmom] with r hr i φ hφ hper
    refine hr i φ ?_ hper
    rw [hsup]
    exact_mod_cast hφ
  obtain ⟨Good, hGfull, hG1, hG2, hG3, hG4⟩ := b1w_good_frame F θ (b1wCrudeS d Ks)
    (Finset.univ.sup d + 1) B src Fl q qs hlit hsl hexp (hprov g₁ F θ hlet hJF hθ) hqc.agrees
  -- the start data
  have hqa' : ‖q F.a‖ ≤ cq * ‖b1wSlowE F θ F.a‖ := by rw [hcq]; exact hqa
  have hdata := fun k => b1w_crude_data hL F θ (b1wCrudeS d Ks) (b1wRow F θ) Dθ hval hmem q cq
    hqa' (Ks := Ks) k
  have hbd0 : ∀ k, 0 ≤ b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k :=
    b1wDd_nonneg _ _ _ hϖ.le _ _ zero_le_one
  have hbdm : Monotone (b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1) :=
    b1wDd_mono _ _ _ hϖ.le _ _ zero_le_one
  have hCa0 : 0 ≤ Ca' * peFactor F.η ^ Qa := mul_nonneg hCa'0 (pow_nonneg hP0 _)
  -- the crude pass
  have hpass := b1w_crude_pass F θ hρ hρlo hθ F.piece.hπ hϖ (b1wCrudeS d Ks)
    (Finset.univ.sup d + 1) (fun k => by unfold b1wCrudeS b1wLadderAt; omega) (b1wM Nw m Ks) V hb
    Dθ src Fl hcur hval hmem Good hGfull hG1 hG2
    (fun i i' hii r φ => hEarly K g₁ F θ m Ks (fun l => (hlet l).2.1) i i' hii r φ) B hB0 hG3
    q qs hqc hG4 hE (Cs * peFactor F.η ^ Qs) (mul_nonneg hCs.le (pow_nonneg hP0 _)) hrep
    (Ca' * peFactor F.η ^ Qa) hCa0 hadj
    (fun k => (cq + Ca' * peFactor F.η ^ Qa) *
      b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k)
    (fun k => Ca' * peFactor F.η ^ Qa * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k)
    (fun k k' hk => mul_le_mul_of_nonneg_left (hbdm hk) (by positivity))
    (fun k k' hk => mul_le_mul_of_nonneg_left (hbdm hk) hCa0)
    (fun k => mul_nonneg (by positivity) (hbd0 k)) (fun k => mul_nonneg hCa0 (hbd0 k))
    (fun k => mul_le_mul_of_nonneg_right (by linarith) (hbd0 k))
    (fun k _ => (hdata k).1.trans (mul_le_mul_of_nonneg_right (by linarith) (hbd0 k)))
    (fun k _ => mul_le_mul_of_nonneg_left (hdata k).2 hCa0)
  have hcRe : K.Cg * ρ + ‖(cellConstantCLM 1 : ComplexCellL2)‖ = |K.Cg| * ρ + 1 := by
    rw [cellConstantCLM_norm, norm_one, abs_of_pos hCg]
  rw [hcRe] at hpass
  obtain ⟨hstages, hpass⟩ := hpass
  have hterm0 : ∀ k', 0 ≤ (1 + b1wCrudeΘ B (Cs * peFactor F.η ^ Qs) (|K.Cg| * ρ + 1) *
      max 1 (Ca' * peFactor F.η ^ Qa) * (b1wM Nw m Ks : ℝ) *
        (2 + 2 / (Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16))) ^ k' * (1 + (F.b - F.a)) ^ k' *
      (2 * ((cq + Ca' * peFactor F.η ^ Qa) *
        b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k') +
        Ca' * peFactor F.η ^ Qa * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k') :=
    fun k' => by
      have hT0 : 0 ≤ F.b - F.a := sub_nonneg.2 F.ordered
      have hΘ0 : 0 ≤ b1wCrudeΘ B (Cs * peFactor F.η ^ Qs) (|K.Cg| * ρ + 1) := by
        unfold b1wCrudeΘ
        have := hCs.le
        positivity
      have hc₁ : 0 ≤ 2 + 2 / (Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16) := by
        have : 0 < Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16 := by
          have : 0 < Real.pi ^ 2 := by positivity
          linarith
        positivity
      have hm : 0 ≤ max 1 (Ca' * peFactor F.η ^ Qa) := le_max_of_le_left zero_le_one
      have := hbd0 k'
      positivity
  have hΘ0 : 0 ≤ b1wCrudeΘ B (Cs * peFactor F.η ^ Qs) (|K.Cg| * ρ + 1) := by
    unfold b1wCrudeΘ
    have := hCs.le
    positivity
  refine ⟨V, hb, Dθ, src, Fl, Good, q, qs, fun k =>
    b1wCrudeΘ B (Cs * peFactor F.η ^ Qs) (|K.Cg| * ρ + 1) * ∑ k' ∈ Finset.range k,
      (1 + b1wCrudeΘ B (Cs * peFactor F.η ^ Qs) (|K.Cg| * ρ + 1) *
        max 1 (Ca' * peFactor F.η ^ Qa) * (b1wM Nw m Ks : ℝ) *
          (2 + 2 / (Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16))) ^ k' * (1 + (F.b - F.a)) ^ k' *
      (2 * ((cq + Ca' * peFactor F.η ^ Qa) *
        b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k') +
        Ca' * peFactor F.η ^ Qa * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k'),
    fun i => cellWeakHilbertCurve_indicator_forcing (b1wCoeff F θ) F.piece.hGm V F.piece.hv hb
      (hcur i) Good hGfull, hqc, hqb, hval, hmem, fun k => (hdata k).1, ?_, ?_, hpass, ?_, ?_⟩
  · intro k k' hk
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hk) fun k'' _ _ => hterm0 k'') hΘ0
  · exact fun k => mul_nonneg hΘ0 (Finset.sum_nonneg fun k' _ => hterm0 k')
  · intro k hk
    have h := crude_eps_budget (B := B) (Cs := Cs) (cR := |K.Cg| * ρ + 1) (Ca' := Ca') (cq := cq)
      (Qs := Qs) (Qa := Qa) (M := b1wM Nw m Ks)
      (b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1) hB0 hCs.le (by positivity) hCa'0
      hcq0 hP (zero_le_one.trans F.piece.hS) (sub_nonneg.2 F.ordered) hT hCH hbd0 hbdm hk
    unfold b1wCrudeΘ
    exact h
  · -- the crude stage bounds, polynomial
    intro k hk t ht
    have hc₁ : 0 ≤ 2 + 2 / (Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16) := by
      have : 0 < Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16 := by
        have : 0 < Real.pi ^ 2 := by positivity
        linarith
      positivity
    obtain ⟨-, hL1, hLle⟩ := crude_constants_le (M := b1wM Nw m Ks) hB0 hCs.le
      (by positivity : (0 : ℝ) ≤ |K.Cg| * ρ + 1) hCa0 le_rfl hP hc₁ (Qs := Qs) (Ca' := Ca')
    have hPa : 1 ≤ peFactor F.η ^ Qa := one_le_pow₀ hP
    have hDle : (cq + Ca' * peFactor F.η ^ Qa) *
        b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k ≤
        (cq + Ca') * peFactor F.η ^ Qa * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k := by
      refine mul_le_mul_of_nonneg_right ?_ (hbd0 k)
      have : cq ≤ cq * peFactor F.η ^ Qa := le_mul_of_one_le_right hcq0 hPa
      nlinarith
    have hDple : Ca' * peFactor F.η ^ Qa * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k ≤
        (cq + Ca') * peFactor F.η ^ Qa * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k := by
      refine mul_le_mul_of_nonneg_right ?_ (hbd0 k)
      have : 0 ≤ cq * peFactor F.η ^ Qa := mul_nonneg hcq0 (pow_nonneg hP0 _)
      nlinarith
    have hpoly := crude_stage_poly (c := cq + Ca') (CH := CH) (M := b1wM Nw m Ks)
      (fun k => (cq + Ca' * peFactor F.η ^ Qa) *
        b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k)
      (fun k => Ca' * peFactor F.η ^ Qa * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k)
      (b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1) hP (zero_le_one.trans F.piece.hS)
      (sub_nonneg.2 F.ordered) hT hCH hL1 hLle (by positivity) (hbd0 k)
      (mul_nonneg (by positivity) (hbd0 k)) (mul_nonneg hCa0 (hbd0 k)) hDle hDple hk.le
    have hfin : ∀ X : ℝ, X ≤ 3 * (cq + Ca') *
        (1 + B * (1 + Cs) ^ 2 * (1 + (|K.Cg| * ρ + 1)) * (1 + Ca') * b1wM Nw m Ks *
          (2 + 2 / (Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16))) ^ b1wM Nw m Ks *
        (1 + CH) ^ b1wM Nw m Ks * peFactor F.η ^ ((2 * Qs + Qa) * b1wM Nw m Ks + Qa) *
        (1 + F.S) ^ ((2 * Qs + Qa) * b1wM Nw m Ks + Qa + b1wM Nw m Ks) *
          b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k →
        X ≤ 3 * (cq + Ca') *
          (1 + B * (1 + Cs) ^ 2 * (1 + (|K.Cg| * ρ + 1)) * (1 + Ca') * b1wM Nw m Ks *
            (2 + 2 / (Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16))) ^ b1wM Nw m Ks *
          (1 + CH) ^ b1wM Nw m Ks *
          peFactor F.η ^ ((2 * Qs + Qa) * b1wM Nw m Ks + Qa + b1wM Nw m Ks) *
          (1 + F.S) ^ ((2 * Qs + Qa) * b1wM Nw m Ks + Qa + b1wM Nw m Ks) *
            b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k := by
      intro X hX
      refine hX.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP (by omega)) ?_) ?_) (hbd0 k))
      · have := hCs.le
        positivity
      · exact pow_nonneg (by linarith [F.piece.hS]) _
    obtain ⟨hs, hf⟩ := hstages k hk t ht
    exact ⟨hfin _ (hs.trans hpoly), hfin _ (hf.trans hpoly)⟩

end AVRegularity.CycleWords.Assembly
end
