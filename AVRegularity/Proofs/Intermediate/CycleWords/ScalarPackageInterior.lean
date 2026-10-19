-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.ConstructedScalarFibreDataRepresentatives
import AVRegularity.CycleWords.Assembly.MixedWordsB1SharpBlocks
import AVRegularity.CycleWords.Interior.NegativeAdjoint
public import AVRegularity.Definitions.CycleWords.ScalarPackage
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleEvolution.IsMetricNearIdentity
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyHasDepthAtMost
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTimeMeasurable
public import AVRegularity.Statements.Intermediate.Families.FamilyEdges
public import AVRegularity.Statements.Intermediate.Families.IsMolecularEnvelope

section
/-! The cycle mixed words statement. This module is currently empty. -/
end

section
/-! The cycle seam statement. This module is currently empty. -/
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Providers

/-! Weighted scalar geometry energy on the full renewal cover. -/

/-- **Weighted finite Taylor comparison**. -/
theorem cycle_geometry_energy (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ (D n Kmax qJ : ℕ), 2 ≤ D → Kmax + 1 ≤ qJ →
      ∀ (CG : ℕ → ℝ) (Cb CT g0 : ℝ), g0 ≤ 1 / 4 →
      ∃ Cn : ℝ, 0 ≤ Cn ∧
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
        (ϖ rstar : ℝ) (_hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (B * T))
        (_hrstar : rstar = ρs / ocEpsilon q Λ m)
        (Gs : Fin P → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
        (_hGs : ∀ i : Fin P,
          Gs i = ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
              (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) ∨
            Gs i = fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
              (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) t 0)
        (V₀ : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
        (Fl : ∀ (_ : Fin P) (x : ι), ℝ →
          PlaneHk Set.univ (Kslot x) (PiLp 2 (fun _ : Fin 2 => h x)))
        (fV : ∀ (_ : Fin P) (x : ι), PlaneHk Set.univ (Kslot x) (h x))
        (V : ∀ (_ : Fin P) (_ : Fin 1) (x : ι), ℝ → PlaneHk Set.univ (Kslot x) (h x))
        (Vw : ∀ (_ : Fin P) (_ : Fin 1) (x : ι), ℝ → PlaneHk Set.univ (Kslot x + 1) (h x))
        (_hV : ∀ i : Fin P, IsPlaneChainFrom (geometryScalarData D (Gs i)) (fun _ x => Kslot x)
          (ocPieceStart α q Λ m ν ta (l₀ + i)) (ocPieceEnd α q Λ m ν ta T (l₀ + i))
          (ocCellDrift α q Λ ζ m ν (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
          (fun _ x => fV i x) (fun _ x => Fl i x) (V i) (Vw i))
        (_hfV0 : ∀ i : Fin P, i.val = 0 → fV i = V₀)
        (_hfV : ∀ i i' : Fin P, i'.val = i.val + 1 → ∀ x, planeValue (fV i' x) =ᵐ[volume]
          fun z => planeValue (V i 0 x (ocPieceEnd α q Λ m ν ta T (l₀ + i)))
            (ocCellTransition α q Λ m (Φ (m - 1)) hφ (l₀ + i)
              (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)
              (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i') z)),
      ∀ i : Fin P,
        geometryEnergyNorm π Kslot n ϖ 0 rstar (ocPieceStart α q Λ m ν ta (l₀ + i))
            (ocPieceEnd α q Λ m ν ta T (l₀ + i)) (fun x => V i 0 x) (fun x => Vw i 0 x) ≤
          ENNReal.ofReal Cn *
            (geometryDataNorm π Kslot n ϖ 0 rstar V₀ +
              ∑ i' : Fin P, geometryFluxNorm π Kslot n ϖ 0 rstar
                (ocPieceStart α q Λ m ν ta (l₀ + i')) (ocPieceEnd α q Λ m ν ta T (l₀ + i'))
                (Fl i')) := by
  exact AVRegularity.CycleWords.cycle_geometry_energy_proof α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-! Weighted finite Taylor comparison on the actual geometry cover. -/

/-- **Weighted finite Taylor comparison**. -/
theorem cycle_geometry_error (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
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
            geometryDataNorm π Kslot M ϖ 0 rstar F :=
  AVRegularity.CycleWords.cycle_geometry_error_proof α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.Providers
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers

/-! Proof of `scalar_package_interior`:
the assembly `scalar_package_interior_of_ingredients` with its five proved ingredients (drift scale,
quiet gap, high smoothing, chart weights, negative-weight adjoint). -/

/-- **The interior construction provides the scalar package**. -/
theorem scalar_package_interior (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ ξ₀ ξmax c Cg : ℝ, 0 < g₀ ∧ 0 < ξmax ∧
      ξmax < ξ₀ ∧ 0 < c ∧ 0 < Cg ∧
      ∀ ξlo : ℝ, 0 < ξlo → 2 * ξlo ≤ ξmax →
      ∃ (K : ScalarConstants) (Θ₀ : ℝ), K.ξlo = ξlo ∧ K.g0 = g₀ ∧ K.ξ0 = ξ₀ ∧ K.Cg = Cg ∧
        K.cGauss = c ∧ 1 ≤ Θ₀ ∧
        ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
          ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
          ∀ y₀ : Vec 2, ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ),
            IsCellMetric (fun t _ => G t) → 0 ≤ g → g ≤ K.g0 →
            IsMetricNearIdentity (fun t _ => G t) g →
            IsCellDrift (ocCellDrift α q Λ ζ m ν y₀) ∧
            (∀ t (k : Fin 2),
              cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x k : ℂ)) = 0) ∧
            (∀ t, ContDiff ℝ (⊤ : ℕ∞) (ocCellDrift α q Λ ζ m ν y₀ t)) ∧
            (∀ t x, Real.sqrt (ν / B) *
              Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ K.Cw) ∧
            (∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j
              (fun z' => Real.sqrt (ν / B) • ocCellDrift α q Λ ζ m ν y₀ t z') z‖ ≤ K.Cvj j) ∧
            ∀ ta T : ℝ, IsOCAdmissibleInterval α q Λ ζ m ν B Θ₀ K.θs ta T →
              ∃ reg : BlockRegions,
                (∀ t ∈ Set.Icc (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2),
                  t ∈ reg.quiet ↔
                    ∀ s ∈ Set.Icc (t - ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2))
                        (t + ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2)),
                      ∀ z, ocCellDrift α q Λ ζ m ν y₀ s z = 0) ∧
                (∀ p, ∃ k : ℤ, Odd k ∧
                  (∀ t ∈ Set.Icc (reg.lo p) (reg.hi p),
                    |ocEll q Λ m ν ^ 2 * t - k * ocTau α q Λ m| ≤ 3 / 4 * ocTau α q Λ m) ∧
                  reg.orient p = (if k % 4 = 3 then 0 else 1)) ∧
                ((∀ t ∈ Set.Icc (ta / ocEll q Λ m ν ^ 2 - ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2))
                      (ta / ocEll q Λ m ν ^ 2 + 7 * ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2)) ∪
                    Set.Icc ((ta + T) / ocEll q Λ m ν ^ 2 - 7 * ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2))
                      ((ta + T) / ocEll q Λ m ν ^ 2 + ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2)),
                    ∀ z, ocCellDrift α q Λ ζ m ν y₀ t z = 0) →
                  min (ocTau α q Λ m / (4 * ocEll q Λ m ν ^ 2)) (T / ocEll q Λ m ν ^ 2) ≤
                    reg.buffer) ∧
                (reg.joins : ℝ) ≤ T / ocTau α q Λ m + 4 ∧
                Nonempty (ScalarPackage K (ν / B) G (ocCellDrift α q Λ ζ m ν y₀)
                  (ta / ocEll q Λ m ν ^ 2) (T / ocEll q Λ m ν ^ 2)
                  (Real.sqrt ((ν / B) / (T / ocEll q Λ m ν ^ 2))) reg) :=
  CycleWords.Assembly.scalar_package_interior_of_ingredients CycleWords.Interior.interiorDriftScale
    CycleWords.Interior.cellQuietGap CycleWords.Interior.interiorHighSmoothing
    CycleWords.Interior.cellChartWeights CycleWords.Interior.cellNegativeAdjoint
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.Providers
end
end
