-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.InteriorPulseCanonicalFastPeriodicDecay
import AVRegularity.CycleWords.GeometryErrorPieceMassBudget
import AVRegularity.CycleWords.InteriorPulseRawFastZeroOrderDecayPrice
public import AVRegularity.CycleWords.ConstructedReflectedFibreGraphNativeLinearGain
import AVRegularity.CycleWords.ConstructedCanonicalRowPeriodicRepresentative
import AVRegularity.CycleWords.ConstructedRawFastPeriodicDecayPrice
import AVRegularity.CycleWords.CanonicalGraphCommonDriftWindowDifferenceDecay
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Actual error energy glued through the full cover. -/

theorem geometryError_cover_mass_budget_from_weights
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (Λ : ℕ) (hΛ : 128 ≤ Λ) (D H K J n Kmax qJ : ℕ) (hD : 2 ≤ D)
    (hK : 1 ≤ K) (hqJ : K + 1 + Kmax ≤ qJ)
    (Cenv CG Cw : ℕ → ℝ) (Cb CT g0 : ℝ) (hg0 : g0 ≤ 1 / 4) :
    ∃ C : ℝ, 1 ≤ C ∧
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
        (_hweights : ∀ i : Fin P, ∀ frozen : Bool, ∀ N : ℕ, Nonempty (ChartWeights
          (if frozen then (fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
            (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) t 0) else
            ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
            (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
          (ocCellDrift α q Λ ζ m ν (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
          (ta / ocEll q Λ m ν ^ 2) (T / ocEll q Λ m ν ^ 2) ϖ 0 N Cw))
        (F : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
        (_hfinite : (∑ x, ENNReal.ofReal ((π x)⁻¹) *
          weightedFactorialNormSq (n + (J + H + 2) * (K + 1)) ϖ 0 rstar (Kslot x) (F x)) ≠ ⊤)
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
        (∑ x, ENNReal.ofReal ((π x)⁻¹) * nativeComponentEnergy n ϖ rstar
          (ocPieceStart α q Λ m ν ta (l₀ + i)) (ocPieceEnd α q Λ m ν ta T (l₀ + i))
          (nativeErrorCurve (U i 0 x) (fun j => Z i j x))
          (nativeErrorCurve (Uw i 0 x) (fun j => Zw i j x))) ≤
        ENNReal.ofReal C * (ENNReal.ofReal ((ζr ^ (K + 1)) ^ 2) +
          (ENNReal.ofReal ((g * ζr) ^ 2)) ^ (J + 1)) *
        ∑ x, ENNReal.ofReal ((π x)⁻¹) *
          weightedFactorialNormSq (n + (J + H + 2) * (K + 1)) ϖ 0 rstar (Kslot x) (F x) := by
  classical
  obtain ⟨Cforce, hCf, hf⟩ := geometryError_cover_remainder_from_weights
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ D H K J n Kmax qJ hD hK hqJ
    Cenv CG Cw Cb CT g0 hg0
  obtain ⟨A, hA, hp⟩ := geometryError_piece_mass_budget_uniform H n Kmax CG Cw Cenv
  let L := cellTransitionMomentBudget Kmax n
  have hL : 1 ≤ L := cellTransitionMomentBudget_ge_one Kmax n
  let Bprice := 1 + A * (L + 1)
  have hBp : 1 ≤ Bprice := le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans hA) (by positivity))
  have hAB : A ≤ Bprice := by dsimp [Bprice]; nlinarith [mul_nonneg (zero_le_one.trans hA) (zero_le_one.trans hL)]
  have hALB : A * L + A ≤ Bprice := by dsimp [Bprice]; nlinarith
  let N := Nat.ceil (CT + 2)
  let C := Bprice ^ N * Cforce
  have hC : 1 ≤ C := by
    simpa only [C, one_mul] using mul_le_mul (one_le_pow₀ hBp) hCf zero_le_one
      (zero_le_one.trans (one_le_pow₀ hBp))
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hKslot Φ hΦ M' κ' hband m hm2 hmM ν B hν hB hφ
    ta T ρs g a B₀ lam l₀ P y₀ cov P' Ctx Fam pc ctx dom hdom hdepth hdesc
    b Θ hΘ hb hrow hcol henv hmeas ϖ ζr rstar hϖ hζr hrstar hweights F hfinite
    fU U Uw fZ Z Zw hU hZ hfU0 hfZ0 hfU hfZ
  let left := fun i : Fin P => ocPieceStart α q Λ m ν ta (l₀ + i)
  let right := fun i : Fin P => ocPieceEnd α q Λ m ν ta T (l₀ + i)
  let yc := fun i : Fin P => ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i
  let G := fun i : Fin P => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν (yc i)
  let Ddata := ∑ x, ENNReal.ofReal ((π x)⁻¹) *
    weightedFactorialNormSq (n + (J + H + 2) * (K + 1)) ϖ 0 rstar (Kslot x) (F x)
  let Force := ENNReal.ofReal Cforce * (ENNReal.ofReal ((ζr ^ (K + 1)) ^ 2) +
    (ENNReal.ofReal ((g * ζr) ^ 2)) ^ (J + 1)) * Ddata
  have hex := hf π hπ Kslot hKslot Φ hΦ M' κ' hband m hm2 hmM ν B hν hB hφ
    ta T ρs g a B₀ lam l₀ P y₀ cov Fam pc ctx dom hdom hdepth hdesc b Θ hΘ hb hrow hcol
    henv hmeas ϖ ζr rstar hϖ hζr hrstar F hfinite
    (by simpa only [ite_true] using fun i N => hweights i true N)
    fZ Z Zw hZ hfZ0 hfZ
  choose R hR hRv hRb using hex
  have hΛ1 : 1 ≤ Λ := by omega
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ1
  have hE := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ1
  have hRT : 0 < Real.sqrt (B * T) := Real.sqrt_pos.mpr (mul_pos cov.pos.2.1 cov.pos.2.2.1)
  have hϖpos : 0 < ϖ := by rw [hϖ]; exact div_pos he hRT
  have hr : 0 < rstar := by rw [hrstar]; exact div_pos cov.pos.2.2.2 he
  have hr1 : rstar ≤ 1 := by rw [hrstar]; exact (div_le_one he).mpr cov.rho_e
  have hell : 0 < ocEll q Λ m ν ^ 2 := by
    unfold ocEll
    exact sq_pos_of_pos (div_pos he (Real.sqrt_pos.mpr cov.pos.1))
  have hcount : P ≤ N := by
    have hh := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ1
    have hbP := renewal_piece_count_bound (ocTauPP α q Λ m) ta T CT l₀ P hh
      cov.window.2.1 cov.window.2.2.1 cov.comparable.1
    exact_mod_cast hbP.le.trans (Nat.le_ceil (CT + 2))
  have hpiece (i : Fin P) :
      (∑ x, ENNReal.ofReal ((π x)⁻¹) * nativeComponentEnergy n ϖ rstar (left i) (right i)
        (nativeErrorCurve (U i 0 x) (fun j => Z i j x))
        (nativeErrorCurve (Uw i 0 x) (fun j => Zw i j x))) ≤
      ENNReal.ofReal A * ((∑ x, ENNReal.ofReal ((π x)⁻¹) * weightedFactorialNormSq n ϖ 0 rstar (Kslot x)
        (nativeErrorDatum (fU i x) (fun j => fZ i j x))) + Force) := by
    have HC := geometryCover_piece_scalar_inputs Kmax CG hΛ1 hζ hφ (by omega) cov hg0 i (G i) (Or.inl rfl)
    let Gc := metricClamp (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2) (G i)
    have hsub := ocPiece_interval_subset α q Λ m ν ta T (l₀ + i) hell
    have hc : ∀ t ∈ Set.Icc (left i) (right i), Gc t = G i t :=
      fun t ht => metricClamp_of_mem (G i) (hsub ht)
    have hTaylor (lo : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (left i) (right i)) (z : Vec 2) :
        metricTaylor lo K Gc t 0 z = metricTaylor lo K (G i) t 0 z := by
      unfold metricTaylor
      rw [hc t ht]
    let W0 := Classical.choice (hweights i false n)
    let W : ChartWeights Gc (ocCellDrift α q Λ ζ m ν (yc i))
        (ta / ocEll q Λ m ν ^ 2) (T / ocEll q Λ m ν ^ 2) ϖ 0 n Cw :=
      chartWeightsOfEqOn (by simpa only [Bool.false_eq_true, ite_false] using W0)
        (fun t ht => metricClamp_of_mem (G i) (by simpa only [add_div] using ht))
    have hwin : ∀ t ∈ Set.Icc (left i) (right i), ∀ Y : Vec 2,
        (ocEll q Λ m ν ^ 2 * t, Y) ∈ dom (pc i) (ctx i) := by
      intro t ht Y
      apply hdom i
      exact ⟨⟨mul_le_mul_of_nonneg_left ht.1 hell.le, mul_le_mul_of_nonneg_left ht.2 hell.le⟩, Set.mem_univ Y⟩
    have hu : IsPlaneChainFrom (geometryActualData (G i)
        (Fam.cellFiber (ocEll q Λ m ν ^ 2) ((ocEpsilon q Λ m)⁻¹ • yc i) (pc i) (ctx i))
        ((ocEpsilon q Λ (m - 1))⁻¹ • yc i) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)))
        (fun _ x => Kslot x) (left i) (right i)
        (ocCellDrift α q Λ ζ m ν (yc i)) (fun _ x => fU i x) (fun _ _ _ => 0)
        (fun _ x => U i 0 x) (fun _ x => Uw i 0 x) := by
      have hUU : (fun (_ : Fin 1) x => U i 0 x) = U i := by
        funext j x
        rw [Fin.eq_zero j]
      have hUW : (fun (_ : Fin 1) x => Uw i 0 x) = Uw i := by
        funext j x
        rw [Fin.eq_zero j]
      simpa only [G, yc, left, right, ocCellFiber, hUU, hUW] using hU i
    have huc : IsPlaneChainFrom (geometryActualData Gc
        (Fam.cellFiber (ocEll q Λ m ν ^ 2) ((ocEpsilon q Λ m)⁻¹ • yc i) (pc i) (ctx i))
        ((ocEpsilon q Λ (m - 1))⁻¹ • yc i) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)))
        (fun _ x => Kslot x) (left i) (right i)
        (ocCellDrift α q Λ ζ m ν (yc i)) (fun _ x => fU i x) (fun _ _ _ => 0)
        (fun _ x => U i 0 x) (fun _ x => Uw i 0 x) := by
      unfold IsPlaneChainFrom
      apply isCoupledWeakSolutionPlane_congr_coeff (hsol := hu)
      intro j j' d t ht
      funext z
      simp only [planeChainCoefficient, geometryActualData, hc t ht]
    have hzc : IsPlaneChainFrom (geometryResponseData J K Gc 0
        (ocCellFiber Fam q Λ m ν (yc i) (pc i) (ctx i))
        ((ocEpsilon q Λ (m - 1))⁻¹ • yc i) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)))
        (fun _ x => Kslot x) (left i) (right i)
        (ocCellDrift α q Λ ζ m ν (yc i)) (fZ i) (fun _ _ _ => 0) (Z i) (Zw i) := by
      unfold IsPlaneChainFrom
      apply isCoupledWeakSolutionPlane_congr_coeff (hsol := hZ i)
      intro j j' d t ht
      funext z
      simp only [planeChainCoefficient, geometryResponseData, hc t ht, hTaylor 1 t ht z]
      rfl
    have hRc : ∀ x, ∀ᵐ t ∂volume.restrict (Set.Icc (left i) (right i)),
        planeValue (R i x t) =ᵐ[volume]
          geometryErrorRemainderFlux Fam J K Kslot (pc i) (ctx i) Gc
            (ocEll q Λ m ν ^ 2) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1))
            ((ocEpsilon q Λ (m - 1))⁻¹ • yc i) ((ocEpsilon q Λ m)⁻¹ • yc i)
            (fun j u => Zw i j u t) x t := by
      intro x
      filter_upwards [hRv i x, ae_restrict_mem measurableSet_Icc] with t ht hmem
      have heq : geometryErrorRemainderFlux Fam J K Kslot (pc i) (ctx i) Gc
          (ocEll q Λ m ν ^ 2) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1))
          ((ocEpsilon q Λ (m - 1))⁻¹ • yc i) ((ocEpsilon q Λ m)⁻¹ • yc i)
          (fun j u => Zw i j u t) x t =
            geometryErrorRemainderFlux Fam J K Kslot (pc i) (ctx i) (G i)
              (ocEll q Λ m ν ^ 2) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1))
              ((ocEpsilon q Λ (m - 1))⁻¹ • yc i) ((ocEpsilon q Λ m)⁻¹ • yc i)
              (fun j u => Zw i j u t) x t := by
        funext z
        simp only [geometryErrorRemainderFlux, hc t hmem, hTaylor 0 t hmem z, hTaylor 1 t hmem z]
      rw [heq]
      exact ht
    have hh := hp Fam hD hdepth J K π hπ Kslot hKslot hdesc dom ν (ocEpsilon q Λ m)
      (ocEpsilon q Λ (m - 1)) ρs cov.pos.1 he hE cov.pos.2.2.2 (K + 1) b henv hmeas hb
      (fun x => (hrow x).trans hΘ) (fun x => (hcol x).trans hΘ)
      (pc i) (ctx i) (left i) (right i) (ocEll q Λ m ν ^ 2) ϖ g hell.ne' hϖpos
      ((ocEpsilon q Λ (m - 1))⁻¹ • yc i) ((ocEpsilon q Λ m)⁻¹ • yc i) hwin
      (ocCellDrift α q Λ ζ m ν (yc i)) Gc a B₀ lam HC
      (ta / ocEll q Λ m ν ^ 2) (T / ocEll q Λ m ν ^ 2)
      (ocPieceStart_global_lower α q Λ m ν ta (l₀ + i) hell)
      (by simpa only [add_div] using ocPieceEnd_global_upper α q Λ m ν ta T (l₀ + i) hell)
      W
      (fU i) (U i 0) (Uw i 0) (fZ i) (Z i) (Zw i) (R i) huc hzc (hR i) hRc
    have hh' : (∑ x, ENNReal.ofReal ((π x)⁻¹) * nativeComponentEnergy n ϖ rstar (left i) (right i)
        (nativeErrorCurve (U i 0 x) (fun j => Z i j x))
        (nativeErrorCurve (Uw i 0 x) (fun j => Zw i j x))) ≤
      ENNReal.ofReal A * ((∑ x, ENNReal.ofReal ((π x)⁻¹) * weightedFactorialNormSq n ϖ 0 rstar (Kslot x)
        (nativeErrorDatum (fU i x) (fun j => fZ i j x))) +
       ∑ x, ENNReal.ofReal ((π x)⁻¹) * ∫⁻ t in Set.Icc (left i) (right i),
         weightedFactorialNormSq n ϖ 0 rstar (Kslot x) (R i x t)) := by
      simpa only [← hrstar] using hh
    exact hh'.trans (mul_le_mul_right (add_le_add le_rfl (hRb i)) _)
  have hzero : ∀ i : Fin P, i.val = 0 → ∀ x, nativeErrorDatum (fU i x) (fun j => fZ i j x) = 0 := by
    intro i hi x
    rw [hfU0 i hi]
    exact nativeErrorDatum_initial_zero (F x) (fun j => fZ i j x) (fun j => hfZ0 i hi j x)
  have hjoin : ∀ i i' : Fin P, i'.val = i.val + 1 → ∀ x,
      weightedFactorialNormSq n ϖ 0 rstar (Kslot x) (nativeErrorDatum (fU i' x) (fun j => fZ i' j x)) ≤
      ENNReal.ofReal L * nativeComponentEnergy n ϖ rstar (left i) (right i)
        (nativeErrorCurve (U i 0 x) (fun j => Z i j x))
        (nativeErrorCurve (Uw i 0 x) (fun j => Zw i j x)) := by
    intro i i' hi x
    have hc : yc i' = ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ (i.val + 1) := by
      dsimp only [yc]
      rw [hi]
    have hx := cellTransition_measurePreserving α q Λ m hφ (l₀ + i) (yc i) (yc i') he.ne'
    have hv := nativeErrorDatum_pullback _ hx.quasiMeasurePreserving
      (U i 0 x (right i)) (fU i' x) (fun j => Z i j x (right i)) (fun j => fZ i' j x)
      (hfU i i' hi x) (fun j => hfZ i i' hi j x)
    have hpull := cellTransition_polynomial_factorial_energy_reserved α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ
      Φ hΦ m (by omega) hφ l₀ y₀ i.val ϖ n n le_rfl (hKslot x)
      (nativeErrorDatum (U i 0 x (right i)) (fun j => Z i j x (right i)))
      (nativeErrorDatum (fU i' x) (fun j => fZ i' j x)) rstar hr.le hr1
      (by simpa only [yc, hc] using hv)
    have ht : right i ∈ Set.Icc (left i) (right i) := ⟨geometryCover_piece_nonempty hΛ1 cov i, le_rfl⟩
    have hend : weightedFactorialNormSq n ϖ 0 rstar (Kslot x)
        (nativeErrorDatum (U i 0 x (right i)) (fun j => Z i j x (right i))) ≤
      nativeComponentEnergy n ϖ rstar (left i) (right i)
        (nativeErrorCurve (U i 0 x) (fun j => Z i j x))
        (nativeErrorCurve (Uw i 0 x) (fun j => Zw i j x)) := by
      unfold nativeComponentEnergy
      apply le_add_right
      exact le_iSup₂_of_le (right i) ht le_rfl
    exact hpull.trans (mul_le_mul_right hend _)
  have hh := nativeError_renewal_mass_budget hcount π Kslot n ϖ rstar left right fU fZ
    (fun i x => U i 0 x) (fun i x => Uw i 0 x) Z Zw (ENNReal.ofReal A) (ENNReal.ofReal L)
    (ENNReal.ofReal Bprice) Force
    (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hBp)
    (ENNReal.ofReal_le_ofReal hAB)
    (by rw [← ENNReal.ofReal_mul (zero_le_one.trans hA),
            ← ENNReal.ofReal_add (by positivity : 0 ≤ A * L) (zero_le_one.trans hA)]
        exact ENNReal.ofReal_le_ofReal hALB)
    hzero hjoin hpiece
  have hcoef : (ENNReal.ofReal Bprice) ^ N * ENNReal.ofReal Cforce = ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_pow (zero_le_one.trans hBp), ← ENNReal.ofReal_mul (by positivity)]
  intro i
  have hb := hh i
  simpa only [Force, Ddata, ← mul_assoc, hcoef, left, right] using hb

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Full rough smoothing for the chosen smooth graph and row, with the common scalar price. -/

theorem constructedSmoothAdjointFast_rough_smoothing (J : ℕ)
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
    {a b : ℝ} (hab : a < b)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc (-b) (-a))
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) (fun s => G (-s))
        (fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x) (fun i => -ξ i) 0) (fun _ _ => 0) (fun _ _ => 0) D)

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
          (1 + (b - a) ^ (-(J : ℝ) / 2)) * Real.exp (-(3 * Real.pi ^ 2) * (b - a))) *
          cellL2Norm (cellValue D (-b)) := by
  dsimp only
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedRawAdjointFast_rough_smoothing_price J
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm
    hg hgsmall hdisc hfreq hab D hD
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
  have ht : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hp : 0 ≤ 1 + (b - a) ^ (-(J : ℝ) / 2) :=
    add_nonneg (by norm_num) (Real.rpow_nonneg ht _)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (constructedSmoothingPrice_le_scalar J R Cw ρ)
        (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans
          (one_le_peFactor (ν / ocMeanFlux α q Λ ζ m ν))) _)) hp) (Real.exp_pos _).le

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Joint literal graph and row representatives with every scalar spatial jet bound. -/

theorem constructedCanonicalGraphRow_smooth_scalar_jets
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
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < fibreCoefficientMajorantRadius Cw) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    ∃ R : ℕ × ℕ → ℝ → RawJet2 1 ℂ, ∃ ell : ℕ × ℕ → ℝ → Vec 2 → ℂ,
      IsFibreGraph η G (ocCellDrift α q Λ ζ m ν y₀)
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
  obtain ⟨R, hg, heR, hsR, hpR⟩ := constructedCanonicalGraph_smooth_value_replacement
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw hη0 hη hm ρ hρ hband
  obtain ⟨ell, _, _, hpell, hsell, heell⟩ :=
    constructedCanonicalRow_coefficients_smooth_series_replacement
      hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw hη0 hη hm ρ hρ hband
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
  · exact constructedFibreGraph_scalar_jet_bound hΛ hζ hν hr y₀ hv V hb G hG
      Cw hCw hw hη0 hη hm (fibreCoefficientMajorantRadius Cw) R
      (fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
        (ocCellDrift α q Λ ζ m ν y₀)
        (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw)) hg
      ρ hρ hband t J ξ hball _ (hsg.of_le (by simp)) (Filter.Eventually.of_forall (fun _ => rfl))
  · apply constructedCanonicalRow_scalar_jet_bound hΛ hζ hν hr y₀ hv V hb G hG
      Cw hCw hw hη0 hη hm ρ hρ hband t J ξ hball hsmall _ (hse.of_le (by simp))
    filter_upwards [fibreSeriesFun_congr_ae ell _ heell ξ t] with x hx
    rw [hx]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Full rough fast smoothing in the literal raw notation, with periodic outputs. -/

theorem interiorPulseRawAdjointFast_rough_smoothing (J : ℕ)
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
 :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    let B := Real.exp (6 * Real.pi ^ 2) * constructedGapSmoothingBasePrice J R 0 Cw *
      Real.exp (constructedAllOrderPrice 0 R 0 Cw)
    let C := 13 * ((Real.sqrt B * peFactor η ^ J * Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) *
      (1 + (b - a) ^ (-(J : ℝ) / 2)))
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ((∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal C) * cellL2Norm (cellValue D (-b)) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
  let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
  have hraw := cellRawHomogeneous_to_Hilbert (by linarith : -b ≤ -a)
    (fun s _ => G (-s)) (cellMetric_timeReverse hG)
    (fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x) V (cellDrift_timeReverse hv).1
    (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x)
    (fun i => (Real.sqrt η : ℂ) * -ξ i) D (by
      simpa only [fibreCoefficients, Pi.zero_apply, neg_zero,
        show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl] using hD)
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseCanonicalAdjointFast_rough_smoothing
    J hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab (cellRawTrace D) (cellH1Slice D) hraw
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith only [hdisc, hrad]
  have hξ16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by linarith only [hdisc, hrad]
  have hgraph := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξR
  have hrow := (fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hv hw ξ hξ16 a).1
  have he := fibreAdjointFast_native_class_ae r lam ell ξ D a b
    (hD.2.2.1 (-b) ⟨le_rfl, by linarith⟩).1
    (hD.2.2.1 (-a) ⟨by linarith, le_rfl⟩).1
    (hgraph.1.2.2.1 b (mem_univ b)).1 hrow
  refine ⟨g₁, hg₁, hp₁, he.symm.trans he₁, ?_⟩
  rw [cellL2Norm_eq_of_class _ (cellRawTrace D (-b))
    (cellRawTrace_ae D (-b) (hD.2.2.1 (-b) ⟨le_rfl, by linarith⟩).1)]
  exact hb₁

theorem interiorPulseRawAdjointFast_zero_order_decay
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
    let B := Real.exp (6 * Real.pi ^ 2) * constructedGapSmoothingBasePrice 0 R 0 Cw *
      Real.exp (constructedAllOrderPrice 0 R 0 Cw)
    let C := 13 * ((Real.sqrt B * peFactor η ^ 0 * Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) *
      (1 + (b - a) ^ (-(0 : ℝ) / 2)))
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm 0 g₁ ≤
        ((∑ l ∈ Finset.range (0 + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal C) * cellSobolevNorm 0 g₀ := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseRawAdjointFast_rough_smoothing
    0 hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab D hD
  refine ⟨g₁, hg₁, hp₁, he₁, ?_⟩
  rw [cellSobolevNorm_zero_eq g₀ hg₀]
  have hn : cellL2Norm (cellValue D (-b)) = cellL2Norm g₀ := by
    exact eLpNorm_congr_ae hi
  rw [hn] at hb₁
  simpa only [Nat.cast_zero] using hb₁

/-! Full rough smoothing for the chosen smooth graph and row, with the common scalar price. -/

theorem interiorPulseSmoothFast_rough_smoothing (J : ℕ)
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
    (hD : IsCellSolution (Icc a b)
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
        (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) ξ 0) (fun _ _ => 0) (fun _ _ => 0) D)

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
          (1 + (b - a) ^ (-(J : ℝ) / 2)) * Real.exp (-(3 * Real.pi ^ 2) * (b - a))) *
          cellL2Norm (cellValue D a) := by
  dsimp only
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseRawFast_rough_smoothing_price J
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm
    hg hgsmall hdisc hfreq hab D hD
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
  have ht : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hp : 0 ≤ 1 + (b - a) ^ (-(J : ℝ) / 2) :=
    add_nonneg (by norm_num) (Real.rpow_nonneg ht _)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (constructedSmoothingPrice_le_scalar J R Cw ρ)
        (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans
          (one_le_peFactor (ν / ocMeanFlux α q Λ ζ m ν))) _)) hp) (Real.exp_pos _).le

/-! Full periodic decay for the chosen smooth graph and row, with the common scalar price. -/

theorem constructedSmoothFast_all_time_periodic_decay (J : ℕ)
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
    (hD : IsCellSolution (Icc a b)
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
        (ocCellDrift α q Λ ζ m ν y₀) ξ 0) (fun _ _ => 0) (fun _ _ => 0) D)
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
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreFastPart r' lam ell' ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedScalarJetPrice J R Cw ρ * peFactor η ^ (2 * J) *
          Real.exp (-(3 * Real.pi ^ 2) * (b - a))) * cellSobolevNorm J g₀ := by
  dsimp only
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedRawFast_all_time_periodic_decay J
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm
    hg hgsmall hdisc hfreq hab D hD g₀ hg₀ hp₀ hi
  have hgraph := fibreFastPart_graph_congr_ae
    (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) r'
    (fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
      (ocCellDrift α q Λ ζ m ν y₀)
      (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw))
    (fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw)
    (fun p t => (her p t).symm) ξ D a b
  have hrow := fibreFastPart_row_congr_ae r'
    (fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
      (ocCellDrift α q Λ ζ m ν y₀)
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

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Full two-orientation fast decay with a periodic entrance and periodic output. -/

theorem interiorPulseCanonicalAdjointFast_periodic_entrance_decay (J : ℕ) (hJ : 1 ≤ J)
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
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve (-b) (-a) U slice (fun t => cellDualDerivative
      ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * -ξ i, 0⟩
      (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀)
    (hi : (U (-b) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    let c := cellComplexPair (U (-b))
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
        (cellRawTrace (fibreSeriesJet r ξ) b + cellConstantCLM 1))
    let phase := Complex.exp (∫ τ in a..b, fibreSeriesC lam ξ τ)
    let A := 1 + 3 * (2 * Real.sqrt (constructedReflectedGraphNativeSquareBudget J R
      (fibreCoefficientGraphBound Cw) Cw η))
    let C := (Real.sqrt (constructedNativeGapBasePrice J R 0 Cw (6 * Real.pi ^ 2)) *
      peFactor η ^ J * Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) * A
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      ((U (-a) - cellScalarCLM c (cellScalarCLM phase
        (cellSourceSlice ell a)) : ComplexCellL2) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ((∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal C * (Fintype.card (JetIndex2 J) : ℝ≥0∞)) * cellSobolevNorm J g₀ := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  let c := cellComplexPair (U (-b)) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
    (cellRawTrace (fibreSeriesJet r ξ) b + cellConstantCLM 1))
  let A := 1 + 3 * (2 * Real.sqrt (constructedReflectedGraphNativeSquareBudget J R
    (fibreCoefficientGraphBound Cw) Cw η))
  let B := constructedNativeGapBasePrice J R 0 Cw (6 * Real.pi ^ 2)
  let C := (Real.sqrt B * peFactor η ^ J *
    Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) * A
  let initial := finiteSmoothPeriodicHk J g₀ hg₀ hp₀
  have hiv : U (-b) = torusHkValueCLM initial := by
    apply Lp.ext
    exact hi.trans (finiteSmoothPeriodicHk_value_ae J g₀ hg₀ hp₀).symm
  obtain ⟨I, hIv, hIb⟩ := interiorPulseCanonicalAdjointFast_native_entrance J hΛ hζ hν hr
    y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hdisc initial b
  have hI : U (-b) - cellScalarCLM c (cellSourceSlice ell b) = torusHkValueCLM I := by
    simpa only [← hiv] using hIv.symm
  obtain ⟨W, hwv, hwb⟩ := interiorPulseCanonicalAdjointFast_native_decay J hJ hΛ hζ hν hr
    y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall hdisc hfreq
    hab U slice hU I hI
  have hneg : fibreNorm (fun i => -ξ i) ≤ R := by simpa only [fibreNorm_neg] using hξ
  have hθneg : ∀ i, ‖(Real.sqrt η : ℂ) * -ξ i‖ ≤ R := by
    intro i
    simpa only [mul_neg, norm_neg] using hθ i
  have hprice := constructedNativeGap_polynomial_price J R 0 Cw η (6 * Real.pi ^ 2)
    hR le_rfl hCw (fun i => -ξ i) hneg hθneg
  have hB := constructedNativeGapBasePrice_nonneg J R 0 Cw (6 * Real.pi ^ 2) hR le_rfl hCw
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hp : 0 ≤ peFactor η := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hIb2 : ‖I‖ ^ 2 ≤ A ^ 2 * ‖initial‖ ^ 2 := by
    have hh := (sq_le_sq₀ (norm_nonneg I) (mul_nonneg hA (norm_nonneg initial))).mpr hIb
    simpa only [mul_pow] using hh
  have hW : ‖W‖ ^ 2 ≤ C ^ 2 * ‖initial‖ ^ 2 := by
    have hb := hwb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hprice (Real.exp_pos _).le) (sq_nonneg ‖I‖))
    have hh := hb.trans (mul_le_mul_of_nonneg_left hIb2
      (mul_nonneg (mul_nonneg hB (pow_nonneg hp _)) (Real.exp_pos _).le))
    dsimp only [C]
    rw [mul_pow, polynomial_decay_square_price _ _ _ _ _ hB]
    convert hh using 1
    ring
  obtain ⟨g₁, hg₁, hp₁, he₁, _⟩ := interiorPulseCanonicalAdjointFast_rough_smoothing
    J hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab U slice hU
  refine ⟨g₁, hg₁, hp₁, he₁, ?_⟩
  exact torusHigher_periodic_entrance_sobolev_transfer J g₀ g₁ hg₀ hp₀
    (hg₁.of_le (by simp)) W (by rw [hwv]; exact he₁) C hC hW

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Full rough fast smoothing in the literal raw notation, with periodic outputs. -/

theorem interiorPulseRawAdjointFast_rough_smoothing_price (J : ℕ)
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
 :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedSmoothingPrice J R Cw * peFactor η ^ (2 * J) *
          (1 + (b - a) ^ (-(J : ℝ) / 2)) * Real.exp (-(3 * Real.pi ^ 2) * (b - a))) *
          cellL2Norm (cellValue D (-b)) := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseRawAdjointFast_rough_smoothing J hΛ hζ hν hr y₀ hslot hv V hb G hG
    Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall hdisc hfreq hab D hD
  refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, hb₁.trans ?_⟩
  rw [nativeSobolevWordPrice_mul_ofReal]
  apply mul_le_mul_left
  exact ENNReal.ofReal_le_ofReal (constructedSmoothingPrice_bound J R Cw
    (ν / ocMeanFlux α q Λ ζ m ν) (b - a) (sub_nonneg.mpr hab.le))

/-! The full forward producer in the original raw fast-part notation. -/

theorem interiorPulseRawFast_all_time_periodic_decay (J : ℕ)
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
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedForwardDecayPrice J R Cw * peFactor η ^ (2 * J) *
          Real.exp (-(3 * Real.pi ^ 2) * (b - a))) * cellSobolevNorm J g₀ := by
  by_cases heq : a = b
  · subst b
    have hmem := (hD.2.2.1 a ⟨le_rfl, le_rfl⟩).1
    have h := interiorPulseRawFast_same_time_decay_price J hΛ hζ hν hr y₀ hslot hv V hb G hG
      Cw hCw hw ξ R hR hξ hθ hη0 hη hm hdisc g₀ hg₀ hp₀ a D hmem hi
    simpa only [sub_self, mul_zero, Complex.exp_zero, Real.exp_zero, mul_one] using h
  · have hlt : a < b := lt_of_le_of_ne hab heq
    by_cases hzero : J = 0
    · subst J
      have h := interiorPulseRawFast_zero_order_decay_price hΛ hζ hν hr y₀ hslot hv V hb G hG
        Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall hdisc hfreq hlt g₀ hg₀.continuous D hD hi
      simpa only [Nat.mul_zero, Nat.cast_zero, pow_zero, mul_one] using h
    · exact interiorPulseRawFast_periodic_entrance_decay_price J (by omega) hΛ hζ hν hr
        y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
        hdisc hfreq hlt D hD g₀ hg₀ hp₀ hi

/-! The full forward producer in the original raw fast-part notation. -/

theorem interiorPulseRawAdjointFast_periodic_entrance_decay (J : ℕ) (hJ : 1 ≤ J)
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
    let C := Real.sqrt (constructedNativeGapBasePrice J R 0 Cw (6 * Real.pi ^ 2)) *
      (1 + 6 * Real.sqrt (constructedGraphNativeBaseSquareBudget J R
        (fibreCoefficientGraphBound Cw) Cw))
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ((∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal (C * peFactor η ^ (2 * J) * Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) *
            (Fintype.card (JetIndex2 J) : ℝ≥0∞)) * cellSobolevNorm J g₀ := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
  let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
  have hraw := cellRawHomogeneous_to_Hilbert (by linarith : -b ≤ -a)
    (fun s _ => G (-s)) (cellMetric_timeReverse hG)
    (fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x) V (cellDrift_timeReverse hv).1
    (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x)
    (fun i => (Real.sqrt η : ℂ) * -ξ i) D (by
      simpa only [fibreCoefficients, Pi.zero_apply, neg_zero,
        show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl] using hD)
  have hi' := (cellRawTrace_ae D (-b) (hD.2.2.1 (-b) ⟨le_rfl, by linarith⟩).1).trans hi
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseCanonicalAdjointFast_periodic_entrance_decay
    J hJ hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab (cellRawTrace D) (cellH1Slice D) hraw g₀ hg₀ hp₀ hi'
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith only [hdisc, hrad]
  have hξ16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by linarith only [hdisc, hrad]
  have hgraph := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξR
  have hrow := (fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hv hw ξ hξ16 a).1
  have he := fibreAdjointFast_native_class_ae r lam ell ξ D a b
    (hD.2.2.1 (-b) ⟨le_rfl, by linarith⟩).1
    (hD.2.2.1 (-a) ⟨by linarith, le_rfl⟩).1
    (hgraph.1.2.2.1 b (mem_univ b)).1 hrow
  have hprice := constructedAdjointFastNativeDecay_polynomial_price
    J R (fibreCoefficientGraphBound Cw) Cw η (6 * Real.pi ^ 2) (b - a)
  have hc := ENNReal.ofReal_le_ofReal hprice
  simp only [show ∀ x : ℝ, 3 * (2 * x) = 6 * x by intro x; ring] at hb₁
  refine ⟨g₁, hg₁, hp₁, he.symm.trans he₁, hb₁.trans ?_⟩
  exact mul_le_mul_left
    (mul_le_mul_left (mul_le_mul_right hc
      (∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)))
      (Fintype.card (JetIndex2 J) : ℝ≥0∞)) (cellSobolevNorm J g₀)

end AVRegularity.CycleWords
end
