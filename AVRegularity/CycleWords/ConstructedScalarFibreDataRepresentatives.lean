-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.InteriorPulseRawFastZeroOrderDecayPrice
import AVRegularity.CycleWords.ConstructedRawFastPeriodicDecayPrice
import AVRegularity.CycleWords.InteriorPulseRawAdjointFastPeriodicDecay
import AVRegularity.CycleWords.InteriorPulseCanonicalFastPeriodicDecay
import AVRegularity.CycleWords.ConstructedCanonicalFastRoughSmoothing
import AVRegularity.CycleWords.InteriorPulseReflectedActualWeakAllNativeOrders
public import AVRegularity.CycleWords.ConstructedScalarFibreConstants
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The full forward producer in the original raw fast-part notation. -/

theorem constructedRawAdjointFast_all_time_periodic_decay (J : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x j : ℂ)) = 0)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {a b : ℝ} (hab : a ≤ b)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc (-b) (-a))
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) (fun τ => G (-τ))
        (fun τ x => -ocCellDrift α q Λ ζ m ν y₀ (-τ) x) (fun i => -ξ i) 0) (fun _ _ => 0) (fun _ _ => 0) D)
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀)
    (hi : cellValue D (-b) =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedAdjointDecayPrice J R Cw * peFactor η ^ (2 * J) *
          Real.exp (-(3 * Real.pi ^ 2) * (b - a))) * cellSobolevNorm J g₀ := by
  by_cases heq : a = b
  · subst b
    have hmem := (hD.2.2.1 (-a) ⟨le_rfl, le_rfl⟩).1
    have h := constructedRawAdjointFast_same_time_decay_price J hΛ hζ hν hr y₀ hv V hb G hG
      Cw hCw hw ξ R hR hξ hθ hη0 hη hm hdisc g₀ hg₀ hp₀ a D hmem hi
    simpa only [sub_self, mul_zero, Complex.exp_zero, Real.exp_zero, mul_one] using h
  · have hlt : a < b := lt_of_le_of_ne hab heq
    by_cases hzero : J = 0
    · subst J
      have h := constructedRawAdjointFast_zero_order_decay_price hΛ hζ hν hr y₀ hv V hb G hG
        Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall hdisc hfreq hlt g₀ hg₀.continuous D hD hi
      simpa only [Nat.mul_zero, Nat.cast_zero, pow_zero, mul_one] using h
    · exact constructedRawAdjointFast_periodic_entrance_decay_price J (by omega) hΛ hζ hν hr
        y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
        hdisc hfreq hlt D hD g₀ hg₀ hp₀ hi

theorem interiorPulseRawAdjointFast_zero_order_decay_price
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {a b : ℝ} (hab : a < b)
    (g₀ : Vec 2 → ℂ) (hg₀ : Continuous g₀)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc (-b) (-a))
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) (fun s => G (-s))
        (fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x) (fun i => -ξ i) 0) (fun _ _ => 0) (fun _ _ => 0) D)

    (hi : cellValue D (-b) =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (0 : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm 0 g₁ ≤
        ENNReal.ofReal (constructedAdjointDecayPrice 0 R Cw *
          Real.exp (-(3 * Real.pi ^ 2) * (b - a))) * cellSobolevNorm 0 g₀ := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseRawAdjointFast_zero_order_decay
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab g₀ hg₀ D hD hi
  refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, hb₁.trans ?_⟩
  rw [nativeSobolevWordPrice_mul_ofReal]
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = constructedAdjointZeroDecayPrice R Cw * Real.exp (-(3 * Real.pi ^ 2) * (b - a)) := by
      have hexp : -(6 * Real.pi ^ 2) * (b - a) / 2 = -(3 * Real.pi ^ 2) * (b - a) := by ring
      rw [hexp]
      simp only [pow_zero, mul_one, neg_zero, zero_div, Real.rpow_zero]
      dsimp only [constructedAdjointZeroDecayPrice]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (constructedAdjointZeroDecayPrice_le 0 R Cw)
      (Real.exp_nonneg _)

/-! The full forward producer in the original raw fast-part notation. -/

theorem interiorPulseRawAdjointFast_periodic_entrance_decay_price (J : ℕ) (hJ : 1 ≤ J)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {a b : ℝ} (hab : a < b)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc (-b) (-a))
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) (fun s => G (-s))
        (fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x) (fun i => -ξ i) 0) (fun _ _ => 0) (fun _ _ => 0) D)
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀)
    (hi : cellValue D (-b) =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedAdjointDecayPrice J R Cw * peFactor η ^ (2 * J) *
          Real.exp (-(3 * Real.pi ^ 2) * (b - a))) * cellSobolevNorm J g₀ := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseRawAdjointFast_periodic_entrance_decay J hJ
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab D hD g₀ hg₀ hp₀ hi
  refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, hb₁.trans ?_⟩
  rw [nativeSobolevReadoutPrice_ofReal]
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  let η := ν / ocMeanFlux α q Λ ζ m ν
  have hpe : 0 ≤ peFactor η ^ (2 * J) := pow_nonneg
    ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)) _
  calc
    _ = constructedAdjointHigherDecayPrice J R Cw * peFactor η ^ (2 * J) *
        Real.exp (-(3 * Real.pi ^ 2) * (b - a)) := by
      have hexp : -(6 * Real.pi ^ 2) * (b - a) / 2 = -(3 * Real.pi ^ 2) * (b - a) := by ring
      rw [hexp]
      dsimp only [constructedAdjointHigherDecayPrice]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (constructedAdjointHigherDecayPrice_le J R Cw) hpe)
      (Real.exp_nonneg _)

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.CycleWords

/-- **Weighted finite Taylor comparison** (error bound), for every pair of chain families. -/
theorem cycle_geometry_error_proof (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ (D H K J n Kmax qJ : ℕ), 2 ≤ D → 1 ≤ K → K + 1 + Kmax ≤ qJ →
      ∀ (Cenv CG : ℕ → ℝ) (Cb CT g0 : ℝ), g0 ≤ 1 / 4 →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ x, 0 < π x) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (Φ : ℕ → ℝ → Vec 2 → ℝ) (_hΦ : IsOCStreamSeq α q Λ ζ Φ)
        (M' : ℕ) (κ' : ℕ → ℝ) (_hband : IsOCBandChain α q Λ ζ M' κ')
        (m : ℕ) (_hm2 : 2 ≤ m) (_hmM : m ≤ M') (ν B : ℝ) (_hν : κ' m = ν) (_hB : κ' (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (ta T ρs g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (_cov : IsGeometryCover α q Λ m ζ Φ hφ ν B T ta ρs g g0 a B₀ lam Cb CT qJ Kmax CG l₀ P y₀)
        {P' : Type*} {Ctx : P' → Type*} (Fam : ChartedFamily ι h D P' Ctx)
        (pc : Fin P → P') (ctx : ∀ i, Ctx (pc i)) (dom : Fam.Domain)
        (_hlabel : ∀ i : Fin P, (Fam.piece (pc i)).label = l₀ + i)
        (_hmat : ∀ (i : Fin P) t y, (Fam.piece (pc i)).material t y =
          ocChart α q Λ m (Φ (m - 1)) hφ (l₀ + i) t y)
        (_hout : ∀ i : Fin P,
          Set.Icc (ocEll q Λ m ν ^ 2 * ocPieceStart α q Λ m ν ta (l₀ + i))
            (ocEll q Λ m ν ^ 2 * ocPieceEnd α q Λ m ν ta T (l₀ + i)) ⊆ (Fam.piece (pc i)).output)
        (_hdom : ∀ i : Fin P,
          Set.Icc (ocEll q Λ m ν ^ 2 * ocPieceStart α q Λ m ν ta (l₀ + i))
            (ocEll q Λ m ν ^ 2 * ocPieceEnd α q Λ m ν ta T (l₀ + i)) ×ˢ Set.univ ⊆
              dom (pc i) (ctx i))
        (_hdepth : Fam.HasDepthAtMost H) (_hdesc : Fam.IsDescending Kslot)
        (b : ι → ι → ℝ) (Θ : ℝ) (_hΘ : Θ ≤ 1) (_hb : ∀ x y, 0 ≤ b x y)
        (_hrow : ∀ x, ∑ y, b x y ≤ Θ) (_hcol : ∀ y, ∑ x, b x y ≤ Θ)
        (_henv : IsMolecularEnvelope Fam π Kslot dom ν
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρs Cenv (K + 1) b)
        (_hmeas : Fam.IsTimeMeasurable)
        (ϖ ζr rstar : ℝ) (_hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (B * T))
        (_hζr : ζr = Real.sqrt (B * T) / ocEpsilon q Λ (m - 1))
        (_hrstar : rstar = ρs / ocEpsilon q Λ m)
        (M : ℕ) (_hM : M = n + (J + H + 2) * (K + 1)) (_hCg : C * g * ζr ≤ 1 / 2)
        (F : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
        (fU : ∀ (_ : Fin P) (x : ι), PlaneHk Set.univ (Kslot x) (h x))
        (U : ∀ (_ : Fin P) (_ : Fin 1) (x : ι), ℝ → PlaneHk Set.univ (Kslot x) (h x))
        (Uw : ∀ (_ : Fin P) (_ : Fin 1) (x : ι), ℝ → PlaneHk Set.univ (Kslot x + 1) (h x))
        (fZ : ∀ (_ : Fin P) (_ : Fin (J + 1)) (x : ι), PlaneHk Set.univ (Kslot x) (h x))
        (Z : ∀ (_ : Fin P) (_ : Fin (J + 1)) (x : ι), ℝ → PlaneHk Set.univ (Kslot x) (h x))
        (Zw : ∀ (_ : Fin P) (_ : Fin (J + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (Kslot x + 1) (h x))
        (_hU : ∀ i : Fin P, IsPlaneChainFrom
          (geometryActualData (ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
            (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
            (ocCellFiber Fam q Λ m ν (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) (pc i) (ctx i))
            ((ocEpsilon q Λ (m - 1))⁻¹ • ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)
            (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)))
          (fun _ x => Kslot x) (ocPieceStart α q Λ m ν ta (l₀ + i))
          (ocPieceEnd α q Λ m ν ta T (l₀ + i))
          (ocCellDrift α q Λ ζ m ν (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
          (fun _ x => fU i x) (fun _ _ _ => 0) (U i) (Uw i))
        (_hZ : ∀ i : Fin P, IsPlaneChainFrom
          (geometryResponseData J K (ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
            (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)) 0
            (ocCellFiber Fam q Λ m ν (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) (pc i) (ctx i))
            ((ocEpsilon q Λ (m - 1))⁻¹ • ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)
            (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)))
          (fun _ x => Kslot x) (ocPieceStart α q Λ m ν ta (l₀ + i))
          (ocPieceEnd α q Λ m ν ta T (l₀ + i))
          (ocCellDrift α q Λ ζ m ν (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
          (fun j x => fZ i j x) (fun _ _ _ => 0) (Z i) (Zw i))
        (_hfU0 : ∀ i : Fin P, i.val = 0 → fU i = F)
        (_hfZ0 : ∀ i : Fin P, i.val = 0 → ∀ j x, fZ i j x = if j = 0 then F x else 0)
        (_hfU : ∀ i i' : Fin P, i'.val = i.val + 1 → ∀ x, planeValue (fU i' x) =ᵐ[volume]
          fun z => planeValue (U i 0 x (ocPieceEnd α q Λ m ν ta T (l₀ + i)))
            (ocCellTransition α q Λ m (Φ (m - 1)) hφ (l₀ + i)
              (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)
              (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i') z))
        (_hfZ : ∀ i i' : Fin P, i'.val = i.val + 1 → ∀ j x, planeValue (fZ i' j x) =ᵐ[volume]
          fun z => planeValue (Z i j x (ocPieceEnd α q Λ m ν ta T (l₀ + i)))
            (ocCellTransition α q Λ m (Φ (m - 1)) hφ (l₀ + i)
              (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)
              (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i') z)),
      ∀ i : Fin P,
        geometryEnergyNorm π Kslot n ϖ 0 rstar (ocPieceStart α q Λ m ν ta (l₀ + i))
            (ocPieceEnd α q Λ m ν ta T (l₀ + i))
            (fun x t => U i 0 x t - ∑ j, Z i j x t)
            (fun x t => Uw i 0 x t - ∑ j, Zw i j x t) ≤
          ENNReal.ofReal (C * (ζr ^ (K + 1) + (C * g * ζr) ^ (J + 1))) *
            geometryDataNorm π Kslot M ϖ 0 rstar F := by
  classical
  obtain ⟨Cw, Λ₀, hΛ₀, hw⟩ := geometryCover_uniform_adjoint_weights hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ D H K J n Kmax qJ hD hK hqJ Cenv CG Cb CT g0 hg0
  have hΛ128 : 128 ≤ Λ := hΛ₀.trans hΛ
  obtain ⟨Cmass, hCm, hm⟩ := geometryError_cover_mass_budget_from_weights
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ128 D H K J n Kmax qJ hD hK hqJ
    Cenv CG Cw Cb CT g0 hg0
  let C := 1 + Cmass
  have hC : 1 ≤ C := le_add_of_nonneg_right (zero_le_one.trans hCm)
  have hCmC : Cmass ≤ C ^ 2 := by dsimp [C]; nlinarith [sq_nonneg Cmass]
  refine ⟨C, zero_le_one.trans hC, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hKslot Φ hΦ M' κ' hband m hm2 hmM ν B hν hB hφ
    ta T ρs g a B₀ lam l₀ P y₀ cov P' Ctx Fam pc ctx dom _hlabel _hmat _hout hdom hdepth hdesc
    b Θ hΘ hb hrow hcol henv hmeas ϖ ζr rstar hϖ hζr hrstar M hM _hCg F
    fU U Uw fZ Z Zw hU hZ hfU0 hfZ0 hfU hfZ
  subst M
  have hΛ1 : 1 ≤ Λ := by omega
  have hE := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ1
  have hRT : 0 < Real.sqrt (B * T) := Real.sqrt_pos.mpr (mul_pos cov.pos.2.1 cov.pos.2.2.1)
  have hζpos : 0 < ζr := by rw [hζr]; exact div_pos hRT hE
  have hgζ : 0 ≤ g * ζr := mul_nonneg cov.g_range.1 hζpos.le
  have hpower : (g * ζr) ^ (J + 1) ≤ (C * g * ζr) ^ (J + 1) := by
    apply pow_le_pow_left₀ hgζ
    have hh := mul_le_mul_of_nonneg_right hC hgζ
    simpa only [one_mul, mul_assoc] using hh
  let Ddata := ∑ x, ENNReal.ofReal ((π x)⁻¹) *
    weightedFactorialNormSq (n + (J + H + 2) * (K + 1)) ϖ 0 rstar (Kslot x) (F x)
  by_cases hfinite : geometryDataNorm π Kslot (n + (J + H + 2) * (K + 1)) ϖ 0 rstar F = ⊤
  · intro i
    rw [hfinite]
    have hp : 0 < C * (ζr ^ (K + 1) + (C * g * ζr) ^ (J + 1)) :=
      mul_pos (zero_lt_one.trans_le hC) (add_pos_of_pos_of_nonneg (pow_pos hζpos _)
        (pow_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans hC) cov.g_range.1) hζpos.le) _))
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.mpr hp).ne']
    exact le_top
  have hDf : Ddata ≠ ⊤ := finiteError_mass_finite_of_root hfinite
  have hweights : ∀ i : Fin P, ∀ frozen : Bool, ∀ N : ℕ, Nonempty (ChartWeights
      (if frozen then (fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) t 0) else
        ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
      (ocCellDrift α q Λ ζ m ν (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
      (ta / ocEll q Λ m ν ^ 2) (T / ocEll q Λ m ν ^ 2) ϖ 0 N Cw) := by
    intro i frozen N
    cases frozen
    · simpa only [Bool.false_eq_true, ite_false, hϖ] using
        hw Λ hΛ Φ M' κ' hband m hm2 hmM ν B hν hB hφ T ta ρs g g0 a B₀ lam Cb CT
          qJ Kmax CG l₀ P y₀ cov hg0 i
          (ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
            (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)) (Or.inl rfl) N
    · simpa only [ite_true, hϖ] using
        hw Λ hΛ Φ M' κ' hband m hm2 hmM ν B hν hB hφ T ta ρs g g0 a B₀ lam Cb CT
          qJ Kmax CG l₀ P y₀ cov hg0 i
          (fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
            (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) t 0) (Or.inr rfl) N
  have hmass := hm π hπ Kslot hKslot Φ hΦ M' κ' hband m hm2 hmM ν B hν hB hφ
    ta T ρs g a B₀ lam l₀ P y₀ cov Fam pc ctx dom hdom hdepth hdesc b Θ hΘ hb hrow hcol
    henv hmeas ϖ ζr rstar hϖ hζr hrstar hweights F hDf fU U Uw fZ Z Zw hU hZ hfU0 hfZ0 hfU hfZ
  intro i
  have hb := hmass i
  rw [finiteError_response_square (g * ζr) hgζ J] at hb
  have hr := finiteError_root_budget Cmass C (ζr ^ (K + 1)) ((g * ζr) ^ (J + 1))
    (zero_le_one.trans hCm) (zero_le_one.trans hC) (pow_nonneg hζpos.le _) (pow_nonneg hgζ _)
    hCmC _ Ddata hb
  change geometryEnergyNorm π Kslot n ϖ 0 rstar
      (ocPieceStart α q Λ m ν ta (l₀ + i)) (ocPieceEnd α q Λ m ν ta T (l₀ + i))
      (fun x t => U i 0 x t - ∑ j, Z i j x t) (fun x t => Uw i 0 x t - ∑ j, Zw i j x t) ≤
    ENNReal.ofReal (C * (ζr ^ (K + 1) + (C * g * ζr) ^ (J + 1))) * Ddata ^ (1 / 2 : ℝ)
  exact hr.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hpower) (zero_le_one.trans hC))) _)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Full rough smoothing for the chosen smooth graph and row, with the common scalar price. -/

theorem interiorPulseSmoothAdjointFast_rough_smoothing (J : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {a b : ℝ} (hab : a < b)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc (-b) (-a))
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) (fun s => G (-s))
        (fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x) (fun i => -ξ i) 0) (fun _ _ => 0) (fun _ _ => 0) D)

    (ρ : ℝ) (r' : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (ell' : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (her : ∀ p t, cellValue (r' p) t =ᵐ[volume.restrict AVenhance.unitCube]
      cellValue (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p) t)
    (heell : ∀ p t, ell' p t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p t) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r' lam ell' ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedScalarJetPrice J R Cw ρ * peFactor η ^ (2 * J) *
          (1 + (b - a) ^ (-(J : ℝ) / 2)) * Real.exp (-(3 * Real.pi ^ 2) * (b - a))) *
          cellL2Norm (cellValue D (-b)) := by
  dsimp only
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseRawAdjointFast_rough_smoothing_price J
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm
    hg hgsmall hdisc hfreq hab D hD
  have hgraph := fibreAdjointFastPart_graph_congr_ae
    (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) r'
    (fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
      (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot)
      (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw))
    (fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw)
    (fun p t => (her p t).symm) ξ D a b
  have hrow := fibreAdjointFastPart_row_congr_ae r'
    (fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
      (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot)
      (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw))
    (fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) ell'
    (fun p t => (heell p t).symm) ξ D a b
  refine ⟨g₁, hg₁, hp₁, (hgraph.trans hrow).symm.trans he₁, hb₁.trans ?_⟩
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  have ht : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hp : 0 ≤ 1 + (b - a) ^ (-(J : ℝ) / 2) :=
    add_nonneg (by norm_num) (Real.rpow_nonneg ht _)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (constructedSmoothingPrice_le_scalar J R Cw ρ)
        (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans
          (one_le_peFactor (ν / ocMeanFlux α q Λ ζ m ν))) _)) hp) (Real.exp_pos _).le

/-! Full periodic decay for the chosen smooth graph and row, with the common scalar price. -/

theorem constructedSmoothAdjointFast_all_time_periodic_decay (J : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x j : ℂ)) = 0)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {a b : ℝ} (hab : a ≤ b)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc (-b) (-a))
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) (fun τ => G (-τ))
        (fun τ x => -ocCellDrift α q Λ ζ m ν y₀ (-τ) x) (fun i => -ξ i) 0) (fun _ _ => 0) (fun _ _ => 0) D)
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀)
    (hi : cellValue D (-b) =ᵐ[volume.restrict AVenhance.unitCube] g₀)
    (ρ : ℝ) (r' : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (ell' : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (her : ∀ p t, cellValue (r' p) t =ᵐ[volume.restrict AVenhance.unitCube]
      cellValue (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p) t)
    (heell : ∀ p t, ell' p t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p t) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r' lam ell' ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedScalarJetPrice J R Cw ρ * peFactor η ^ (2 * J) *
          Real.exp (-(3 * Real.pi ^ 2) * (b - a))) * cellSobolevNorm J g₀ := by
  dsimp only
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedRawAdjointFast_all_time_periodic_decay J
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm
    hg hgsmall hdisc hfreq hab D hD g₀ hg₀ hp₀ hi
  have hgraph := fibreAdjointFastPart_graph_congr_ae
    (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) r'
    (fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
      (ocCellDrift α q Λ ζ m ν y₀)
      (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw))
    (fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw)
    (fun p t => (her p t).symm) ξ D a b
  have hrow := fibreAdjointFastPart_row_congr_ae r'
    (fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
      (ocCellDrift α q Λ ζ m ν y₀)
      (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw))
    (fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) ell'
    (fun p t => (heell p t).symm) ξ D a b
  refine ⟨g₁, hg₁, hp₁, (hgraph.trans hrow).symm.trans he₁, hb₁.trans ?_⟩
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (constructedAdjointDecayPrice_le_scalar J R Cw ρ) (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans
      (one_le_peFactor (ν / ocMeanFlux α q Λ ζ m ν))) _))
    (Real.exp_pos _).le

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Joint literal graph and row representatives with every scalar spatial jet bound. -/

theorem interiorPulseCanonicalGraphRow_smooth_scalar_jets
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < fibreCoefficientMajorantRadius Cw) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    ∃ R : ℕ × ℕ → ℝ → RawJet2 1 ℂ, ∃ ell : ℕ × ℕ → ℝ → Vec 2 → ℂ,
      IsFibreGraph η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot)
        (fibreCoefficientMajorantRadius Cw) (fibreCoefficientGraphBound Cw) R lam ∧
      (∀ p t a, R p t a =ᵐ[volume.restrict AVenhance.unitCube] r p t a) ∧
      (∀ p t, ell p t =ᵐ[volume.restrict AVenhance.unitCube]
        fibreAdjointRowCoefficients η Cw hη G hG hv hw p t) ∧
      ∀ ξ : Fin 2 → ℂ, fibreNorm ξ ≤ constructedScalarCommonRadius Cw (ρ : ℝ) →
        ∀ t : ℝ,
          ContDiff ℝ (⊤ : ℕ∞) (cellValue (fibreSeriesJet R ξ) t) ∧
          AVenhance.IsZ2Periodic (cellValue (fibreSeriesJet R ξ) t) ∧
          ContDiff ℝ (⊤ : ℕ∞) (fun x => fibreSeriesFun ell ξ t x - 1) ∧
          AVenhance.IsZ2Periodic (fibreSeriesFun ell ξ t) ∧
          ∀ J : ℕ,
            cellSobolevNorm J (cellValue (fibreSeriesJet R ξ) t) ≤
              ENNReal.ofReal (constructedScalarJetPrice J
                (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cw (ρ : ℝ) *
                peFactor η ^ (2 * J) * fibreNorm ξ) ∧
            cellSobolevNorm J (fun x => fibreSeriesFun ell ξ t x - 1) ≤
              ENNReal.ofReal (constructedScalarJetPrice J
                (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cw (ρ : ℝ) *
                peFactor η ^ (2 * J) * fibreNorm ξ) := by
  dsimp only
  obtain ⟨R, hg, heR, hsR, hpR⟩ := interiorPulseCanonicalGraph_smooth_value_replacement
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw hη0 hη hm ρ hρ hband
  obtain ⟨ell, _, _, hpell, hsell, heell⟩ :=
    interiorPulseCanonicalRow_coefficients_smooth_series_replacement
      hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw hη0 hη hm ρ hρ hband
  refine ⟨R, ell, hg, heR, heell, ?_⟩
  intro ξ hξ t
  obtain ⟨_, hsmall, hnorm, hseries, _⟩ :=
    constructedScalarCommonDisc_bounds hCw hρ ξ hξ
  have hball : ξ ∈ Metric.ball 0 ((ρ : ℝ) / 2) := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hnorm
  have hsg := hsR ξ t hseries
  have hse : ContDiff ℝ (⊤ : ℕ∞) (fun x => fibreSeriesFun ell ξ t x - 1) :=
    (hsell ξ t hseries hsmall).sub contDiff_const
  refine ⟨hsg, hpR ξ t, hse, hpell ξ t, ?_⟩
  intro J
  refine ⟨?_, ?_⟩
  · exact interiorPulseFibreGraph_scalar_jet_bound hΛ hζ hν hr y₀ hslot hv V hb G hG
      Cw hCw hw hη0 hη hm (fibreCoefficientMajorantRadius Cw) R
      (fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
        (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot)
        (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw)) hg
      ρ hρ hband t J ξ hball _ (hsg.of_le (by simp)) (Filter.Eventually.of_forall (fun _ => rfl))
  · apply interiorPulseCanonicalRow_scalar_jet_bound hΛ hζ hν hr y₀ hslot hv V hb G hG
      Cw hCw hw hη0 hη hm ρ hρ hband t J ξ hball hsmall _ (hse.of_le (by simp))
    filter_upwards [fibreSeriesFun_congr_ae ell _ heell ξ t] with x hx
    rw [hx]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Full periodic decay for the chosen smooth graph and row, with the common scalar price. -/

theorem interiorPulseSmoothFast_all_time_periodic_decay (J : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {a b : ℝ} (hab : a ≤ b)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b)
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
        (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) ξ 0) (fun _ _ => 0) (fun _ _ => 0) D)
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] g₀)
    (ρ : ℝ) (r' : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (ell' : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (her : ∀ p t, cellValue (r' p) t =ᵐ[volume.restrict AVenhance.unitCube]
      cellValue (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p) t)
    (heell : ∀ p t, ell' p t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p t) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreFastPart r' lam ell' ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedScalarJetPrice J R Cw ρ * peFactor η ^ (2 * J) *
          Real.exp (-(3 * Real.pi ^ 2) * (b - a))) * cellSobolevNorm J g₀ := by
  dsimp only
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseRawFast_all_time_periodic_decay J
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm
    hg hgsmall hdisc hfreq hab D hD g₀ hg₀ hp₀ hi
  have hgraph := fibreFastPart_graph_congr_ae
    (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) r'
    (fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
      (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot)
      (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw))
    (fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw)
    (fun p t => (her p t).symm) ξ D a b
  have hrow := fibreFastPart_row_congr_ae r'
    (fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
      (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot)
      (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw))
    (fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) ell'
    (fun p t => (heell p t).symm) ξ D a b
  refine ⟨g₁, hg₁, hp₁, (hgraph.trans hrow).symm.trans he₁, hb₁.trans ?_⟩
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (constructedForwardDecayPrice_le_scalar J R Cw ρ) (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans
      (one_le_peFactor (ν / ocMeanFlux α q Λ ζ m ν))) _))
    (Real.exp_pos _).le

/-! The full forward producer in the original raw fast-part notation. -/

theorem interiorPulseRawAdjointFast_all_time_periodic_decay (J : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {a b : ℝ} (hab : a ≤ b)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc (-b) (-a))
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) (fun τ => G (-τ))
        (fun τ x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-τ) x) (fun i => -ξ i) 0) (fun _ _ => 0) (fun _ _ => 0) D)
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀)
    (hi : cellValue D (-b) =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedAdjointDecayPrice J R Cw * peFactor η ^ (2 * J) *
          Real.exp (-(3 * Real.pi ^ 2) * (b - a))) * cellSobolevNorm J g₀ := by
  by_cases heq : a = b
  · subst b
    have hmem := (hD.2.2.1 (-a) ⟨le_rfl, le_rfl⟩).1
    have h := interiorPulseRawAdjointFast_same_time_decay_price J hΛ hζ hν hr y₀ hslot hv V hb G hG
      Cw hCw hw ξ R hR hξ hθ hη0 hη hm hdisc g₀ hg₀ hp₀ a D hmem hi
    simpa only [sub_self, mul_zero, Complex.exp_zero, Real.exp_zero, mul_one] using h
  · have hlt : a < b := lt_of_le_of_ne hab heq
    by_cases hzero : J = 0
    · subst J
      have h := interiorPulseRawAdjointFast_zero_order_decay_price hΛ hζ hν hr y₀ hslot hv V hb G hG
        Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall hdisc hfreq hlt g₀ hg₀.continuous D hD hi
      simpa only [Nat.mul_zero, Nat.cast_zero, pow_zero, mul_one] using h
    · exact interiorPulseRawAdjointFast_periodic_entrance_decay_price J (by omega) hΛ hζ hν hr
        y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
        hdisc hfreq hlt D hD g₀ hg₀ hp₀ hi

/-! Full periodic decay for the chosen smooth graph and row, with the common scalar price. -/

theorem interiorPulseSmoothAdjointFast_all_time_periodic_decay (J : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {a b : ℝ} (hab : a ≤ b)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc (-b) (-a))
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) (fun τ => G (-τ))
        (fun τ x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-τ) x) (fun i => -ξ i) 0) (fun _ _ => 0) (fun _ _ => 0) D)
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀)
    (hi : cellValue D (-b) =ᵐ[volume.restrict AVenhance.unitCube] g₀)
    (ρ : ℝ) (r' : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (ell' : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (her : ∀ p t, cellValue (r' p) t =ᵐ[volume.restrict AVenhance.unitCube]
      cellValue (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p) t)
    (heell : ∀ p t, ell' p t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p t) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r' lam ell' ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedScalarJetPrice J R Cw ρ * peFactor η ^ (2 * J) *
          Real.exp (-(3 * Real.pi ^ 2) * (b - a))) * cellSobolevNorm J g₀ := by
  dsimp only
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseRawAdjointFast_all_time_periodic_decay J
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm
    hg hgsmall hdisc hfreq hab D hD g₀ hg₀ hp₀ hi
  have hgraph := fibreAdjointFastPart_graph_congr_ae
    (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) r'
    (fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
      (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot)
      (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw))
    (fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw)
    (fun p t => (her p t).symm) ξ D a b
  have hrow := fibreAdjointFastPart_row_congr_ae r'
    (fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
      (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot)
      (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw))
    (fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) ell'
    (fun p t => (heell p t).symm) ξ D a b
  refine ⟨g₁, hg₁, hp₁, (hgraph.trans hrow).symm.trans he₁, hb₁.trans ?_⟩
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (constructedAdjointDecayPrice_le_scalar J R Cw ρ) (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans
      (one_le_peFactor (ν / ocMeanFlux α q Λ ζ m ν))) _))
    (Real.exp_pos _).le

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! The actual smooth scalar fibre data under explicit numerical choices of constants. -/

theorem constructedSmoothFibreScalarData_with_representatives
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x j : ℂ)) = 0)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < fibreCoefficientMajorantRadius Cw)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (K : ScalarConstants)
    (hKξ : K.ξ0 = constructedScalarCommonRadius Cw (ρ : ℝ))
    (hKCg : K.Cg = constructedScalarGraphPrice Cw)
    (hKCj : ∀ J, K.Cj J = constructedScalarJetPrice J
      (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cw (ρ : ℝ))
    (hKcj : ∀ J, K.cj J = 3 * Real.pi ^ 2)
    (hKQj : ∀ J, K.Qj J = 2 * J) (t₀ S : ℝ) :
    ∃ d : FibreScalarData K (ν / ocMeanFlux α q Λ ζ m ν) G
      (ocCellDrift α q Λ ζ m ν y₀) t₀ S,
      (∀ p t a, d.r p t a =ᵐ[volume.restrict AVenhance.unitCube]
        fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p t a) ∧
      d.lam = fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
        (ocCellDrift α q Λ ζ m ν y₀) (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) ∧
      (∀ p t, d.ell p t =ᵐ[volume.restrict AVenhance.unitCube]
        fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p t) ∧
      ∀ ξ : Fin 2 → ℂ, fibreNorm ξ < K.ξ0 → ∀ t,
        AVenhance.IsZ2Periodic (cellValue (fibreSeriesJet d.r ξ) t) ∧
        AVenhance.IsZ2Periodic (fibreSeriesFun d.ell ξ t) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r₀ := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r₀
  let R₀ := fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))
  have hδ : 0 < K.ξ0 := by
    rw [hKξ]
    exact constructedScalarCommonRadius_pos hCw hρ
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hδR : K.ξ0 ≤ fibreCoefficientMajorantRadius Cw / 16 := by
    rw [hKξ]
    have h := min_le_left (fibreCoefficientMajorantRadius Cw / 2048) ((ρ : ℝ) / 4)
    change min _ _ ≤ _
    linarith
  have hδold : K.ξ0 ≤ fibreCoefficientMajorantRadius Cw := by linarith
  have hCg : 0 ≤ fibreCoefficientGraphBound Cw := by
    unfold fibreCoefficientGraphBound
    positivity
  have hR₀ : 0 ≤ R₀ := fibreNorm_nonneg _
  have hρR₀ : (ρ : ℝ) ≤ R₀ := by
    have h := fibreNorm_coordinate_le (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) 0
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ρ.coe_nonneg] using h
  have hδρ : K.ξ0 ≤ (ρ : ℝ) := by
    rw [hKξ]
    have h := min_le_right (fibreCoefficientMajorantRadius Cw / 2048) ((ρ : ℝ) / 4)
    change min _ _ ≤ _
    linarith [ρ.coe_nonneg]
  obtain ⟨r, ell, hgraph, her, heell, hjets⟩ :=
    constructedCanonicalGraphRow_smooth_scalar_jets hΛ hζ hν hr y₀ hv V hb G hG
      Cw hCw hw hη0 hη hm ρ hρ hband
  have herv : ∀ p t, cellValue (r p) t =ᵐ[volume.restrict AVenhance.unitCube]
      cellValue (r₀ p) t := fun p t => her p t (valueIndex2 1)
  have hs (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < K.ξ0) :=
    constructedScalarCommonDisc_bounds hCw hρ ξ (hξ.le.trans_eq hKξ)
  have hxR (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < K.ξ0) : fibreNorm ξ ≤ R₀ :=
    hξ.le.trans (hδρ.trans hρR₀)
  have hxθ (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < K.ξ0) (i : Fin 2) :
      ‖(Real.sqrt η : ℂ) * ξ i‖ ≤ R₀ :=
    (normalizedFrequency_coordinate_le hη ξ i).trans (hxR ξ hξ)
  refine ⟨{
    r := r
    lam := lam
    ell := ell
    graph := ?_
    row_summable := ?_
    row_mean := ?_
    row_taylor := ?_
    real_ratio := ?_
    graph_jets := ?_
    row_jets := ?_
    fast_decay := ?_
    fast_smoothing := ?_
    adjoint_decay := ?_
    adjoint_smoothing := ?_ }, her, rfl, heell, ?_⟩
  · apply isFibreGraph_radius_restriction hgraph hδ hδold hCg
    rw [hKCg]
    exact constructedScalarGraphPrice_graph Cw
  · intro ξ hξ
    exact constructedScalarRow_summable η Cw hη hCw G hG hv hw ell heell ξ
      (hξ.le.trans hδR)
  · intro ξ hξ t
    obtain ⟨hi, hn⟩ := constructedScalarGraphRow_normalization η Cw hη hCw G hG hv hw
      r her ell heell ξ (hξ.le.trans hδR) t
    refine ⟨hi, hn, ?_⟩
    rw [hKCg]
    exact constructedScalarRow_sub_one_bound η Cw hη hCw G hG hv hw ell heell ξ
      (hξ.le.trans hδR) t
  · intro n ξ t
    rw [hKCg]
    exact constructedScalarRow_taylor_bound η Cw hη hCw G hG hv hw ell heell hδ hδR n ξ t
  · intro ξ hreal hξ s t hst
    rw [hKCg]
    exact constructedScalarGraph_real_ratio η Cw hη hCw G hG hv hw r her hη0 hm V hb
      ξ hreal (hξ.le.trans hδold) hst
  · intro J ξ _ hξ t
    have hj := hjets ξ (hξ.le.trans_eq hKξ) t
    refine ⟨hj.1.of_le (by simp), ?_⟩
    rw [hKCj J, hKQj J]
    exact (hj.2.2.2.2 J).1
  · intro J ξ _ hξ t
    have hj := hjets ξ (hξ.le.trans_eq hKξ) t
    refine ⟨hj.2.2.1.of_le (by simp), ?_⟩
    rw [hKCj J, hKQj J]
    exact (hj.2.2.2.2 J).2
  · intro J ξ _ hξ a b _ hab _ D hD g₀ hg₀ hp₀ hi
    have h := constructedSmoothFast_all_time_periodic_decay J hΛ hζ hν hr y₀ hv V hb
      G hG Cw hCw hw ξ R₀ hR₀ (hxR ξ hξ) (hxθ ξ hξ) hη0 hη hm hg hgsmall
      (hs ξ hξ).1 (hs ξ hξ).2.2.2.2 hab D hD g₀ hg₀ hp₀ hi (ρ : ℝ) r ell herv heell
    obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := h
    refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, ?_⟩
    rw [hKCj J, hKQj J, hKcj J]
    exact hb₁
  · intro J ξ _ hξ a b _ hab _ D hD
    have h := constructedSmoothFast_rough_smoothing J hΛ hζ hν hr y₀ hv V hb
      G hG Cw hCw hw ξ R₀ hR₀ (hxR ξ hξ) (hxθ ξ hξ) hη0 hη hm hg hgsmall
      (hs ξ hξ).1 (hs ξ hξ).2.2.2.2 hab D hD (ρ : ℝ) r ell herv heell
    obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := h
    refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, ?_⟩
    rw [hKCj J, hKQj J, hKcj J]
    exact hb₁
  · intro J ξ _ hξ a b _ hab _ D hD g₀ hg₀ hp₀ hi
    have h := constructedSmoothAdjointFast_all_time_periodic_decay J hΛ hζ hν hr y₀ hv V hb
      G hG Cw hCw hw ξ R₀ hR₀ (hxR ξ hξ) (hxθ ξ hξ) hη0 hη hm hg hgsmall
      (hs ξ hξ).1 (hs ξ hξ).2.2.2.2 hab D hD g₀ hg₀ hp₀ hi (ρ : ℝ) r ell herv heell
    obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := h
    refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, ?_⟩
    rw [hKCj J, hKQj J, hKcj J]
    exact hb₁
  · intro J ξ _ hξ a b _ hab _ D hD
    have h := constructedSmoothAdjointFast_rough_smoothing J hΛ hζ hν hr y₀ hv V hb
      G hG Cw hCw hw ξ R₀ hR₀ (hxR ξ hξ) (hxθ ξ hξ) hη0 hη hm hg hgsmall
      (hs ξ hξ).1 (hs ξ hξ).2.2.2.2 hab D hD (ρ : ℝ) r ell herv heell
    obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := h
    refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, ?_⟩
    rw [hKCj J, hKQj J, hKcj J]
    exact hb₁

  · intro ξ hξ t
    have hj := hjets ξ (hξ.le.trans_eq hKξ) t
    exact ⟨hj.2.1, hj.2.2.2.1⟩

/-! Full scalar fibre data with numerical constants fixed only by the scaled drift bound. -/

theorem constructedSmoothFibreScalarData_representatives
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x j : ℂ)) = 0)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (seed : ScalarConstants) (t₀ S : ℝ) :
    ∃ d : FibreScalarData (constructedScalarFibreConstants seed Cw hCw)
      (ν / ocMeanFlux α q Λ ζ m ν) G (ocCellDrift α q Λ ζ m ν y₀) t₀ S,
      (∀ p t a, d.r p t a =ᵐ[volume.restrict AVenhance.unitCube]
        fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p t a) ∧
      d.lam = fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
        (ocCellDrift α q Λ ζ m ν y₀) (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) ∧
      (∀ p t, d.ell p t =ᵐ[volume.restrict AVenhance.unitCube]
        fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p t) ∧
      ∀ ξ : Fin 2 → ℂ, fibreNorm ξ < (constructedScalarFibreConstants seed Cw hCw).ξ0 → ∀ t,
        AVenhance.IsZ2Periodic (cellValue (fibreSeriesJet d.r ξ) t) ∧
        AVenhance.IsZ2Periodic (fibreSeriesFun d.ell ξ t) := by
  apply constructedSmoothFibreScalarData_with_representatives hΛ hζ hν hr y₀ hv V hb G hG Cw hCw
    hw hη0 hη hm (constructedScalarNativeRadius Cw hCw)
    (constructedScalarNativeRadius_pos Cw hCw) (constructedScalarNativeRadius_band Cw hCw)
    hg hgsmall (constructedScalarFibreConstants seed Cw hCw)
  · exact (constructedScalarCommonRadius_native Cw hCw).symm
  · rfl
  · intro J
    rfl
  · intro J
    rfl
  · intro J
    rfl

end AVRegularity.CycleWords
end
