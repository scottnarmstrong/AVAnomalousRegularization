-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleEvolution.CellInverseJetFactorialBound
import AVRegularity.CycleDamping.ConstructedCanonicalGraph
import AVRegularity.CycleEvolution.FibreWordHomogeneousJets
public import AVRegularity.Definitions.CycleEvolution.IsFibreGraph
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Intermediate.CycleEvolution.IsMetricNearIdentity
public import AVRegularity.Statements.Intermediate.CycleEvolution.OcCellDrift
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.ChartTestTransport
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.Providers

/-! Cell/fibre existence, uniqueness, and energy from the actual Fourier Galerkin construction.
It covers arbitrary L² initial traces and singleton intervals. -/

/-- **Cell/fibre energy estimate**. -/
theorem cell_fibre_energy :
    ∃ Λ₀ c₀ C₀ : ℝ, 0 < Λ₀ ∧ 0 < c₀ ∧ 0 < C₀ ∧
    ∀ (t₀ t₁ : ℝ) (_ht : t₀ ≤ t₁) (C : CellCoefficients)
    (_hG : IsCellMetric C.G) (V : ℝ)
    (_hv_meas : Measurable fun p : ℝ × Vec 2 => C.v p.1 p.2)
    (_hv_bdd : ∀ t z, ∑ i, C.v t z i ^ 2 ≤ V ^ 2)
    (k : ℝ) (_hκ_meas : Measurable C.κ) (_hκ_bdd : ∀ t, ‖C.κ t‖ ≤ k)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (_hsrc_meas : Measurable fun p : ℝ × Vec 2 => src p.1 p.2)
    (_hF_meas : Measurable fun p : ℝ × Vec 2 => F p.1 p.2)
    (_hsrc : ∫⁻ τ in Set.Icc t₀ t₁, cellL2Norm (src τ) ^ 2 < ⊤)
    (_hF : ∫⁻ τ in Set.Icc t₀ t₁, cellL2Norm (F τ) ^ 2 < ⊤)
    (u₀ : Vec 2 → ℂ)
    (_hu₀_meas : AEStronglyMeasurable u₀ (volume.restrict AVenhance.unitCube))
    (_hu₀ : cellL2Norm u₀ < ⊤),
    (∃ D : ℝ → RawJet2 1 ℂ, IsCellSolution (Set.Icc t₀ t₁) C src F D ∧
      cellValue D t₀ =ᵐ[volume.restrict AVenhance.unitCube] u₀) ∧
    (∀ D D' : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc t₀ t₁) C src F D →
      IsCellSolution (Set.Icc t₀ t₁) C src F D' →
      cellValue D t₀ =ᵐ[volume.restrict AVenhance.unitCube] u₀ →
      cellValue D' t₀ =ᵐ[volume.restrict AVenhance.unitCube] u₀ →
      ∀ t ∈ Set.Icc t₀ t₁,
        cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] cellValue D' t) ∧
    (∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc t₀ t₁) C src F D →
      cellValue D t₀ =ᵐ[volume.restrict AVenhance.unitCube] u₀ →
      ∀ t ∈ Set.Icc t₀ t₁,
        cellL2Norm (cellValue D t) ^ 2 +
            ENNReal.ofReal c₀ * ∫⁻ τ in Set.Icc t₀ t, cellL2Norm (cellGradient (D τ)) ^ 2
          ≤ ENNReal.ofReal (Real.exp (Λ₀ * (1 + ∑ i, ‖C.θ i‖ ^ 2 + V ^ 2 + k) * (t - t₀))) *
              (cellL2Norm u₀ ^ 2 + (∫⁻ τ in Set.Icc t₀ t, cellL2Norm (src τ) ^ 2)
                + ENNReal.ofReal C₀ * (∫⁻ τ in Set.Icc t₀ t, cellL2Norm (F τ) ^ 2))) := by
  refine ⟨300, 1 / 2, 9, by norm_num, by norm_num, by norm_num, ?_⟩
  intro a b hab C hG V hv hvb k hκ hκb src F hsrcm hFm hsrc hF u₀ _ hu₀
  have hsrcP := cellSource_memLp_product (Set.Icc a b) src hsrcm hsrc
  have hFP := cellSource_memLp_product (Set.Icc a b) F hFm hF
  have hu₀P : MemLp u₀ 2 (volume.restrict AVenhance.unitCube) := by
    change eLpNorm u₀ 2 _ < ⊤
    exact hu₀
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨D, hD, hi⟩ := cellActual_exists_raw hab C hG V k hv hvb hκ hκb
      src F hsrcm hFm hsrc hF (hu₀P.toLp u₀)
    exact ⟨D, hD, hi.trans hu₀P.coeFn_toLp⟩
  · intro D D' hD hD' hi hi'
    exact cellActual_unique_raw hab C hG V k hv hvb hκ hκb src F hsrcP hFP
      D D' hD hD' (hi.trans hi'.symm)
  · intro D hD hi t ht
    exact cellActual_raw_energy hab C hG V k hv hvb hκ hκb src F hsrcP hFP D hD u₀ hi t ht

end AVRegularity.Providers
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.Providers

/-! The complete cell-inverse statement, including finite-past data, decay, and factorial parameter
jets. -/

/-- **Cell inverse, slow mode**. Lemma 11.3 of the paper follows from it. -/
theorem cycle_cell_inverse :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      (∀ (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2),
        IsCellMetric G → IsCellDrift v →
        (∀ (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)),
          Measurable (fun p : ℝ × Vec 2 => f p.1 p.2) →
          Measurable (fun p : ℝ × Vec 2 => F p.1 p.2) →
          cellUlNorm Set.univ f < ⊤ → cellUlNorm Set.univ F < ⊤ →
          ∃ D : ℝ → RawJet2 1 ℂ,
            IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F D ∧
            cellEnergyNorm Set.univ D ≤
              ENNReal.ofReal C₀ * (cellUlNorm Set.univ f + cellUlNorm Set.univ F) ∧
            ∀ D' : ℝ → RawJet2 1 ℂ,
              IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F D' →
              ∀ t, cellValue D' t =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) ∧
        (∀ (s : ℝ) (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)),
          Measurable (fun p : ℝ × Vec 2 => f p.1 p.2) →
          Measurable (fun p : ℝ × Vec 2 => F p.1 p.2) →
          cellUlNorm (Set.Ici s) f < ⊤ → cellUlNorm (Set.Ici s) F < ⊤ →
          ∀ c₀ : Vec 2 → ℂ, AEStronglyMeasurable c₀ (volume.restrict AVenhance.unitCube) →
          cellL2Norm c₀ < ⊤ → cellMean c₀ = 0 →
          ∃ D : ℝ → RawJet2 1 ℂ,
            IsCellSolution (Set.Ici s) ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F D ∧
            (∀ t, s ≤ t → cellMean (cellValue D t) = 0) ∧
            cellValue D s =ᵐ[volume.restrict AVenhance.unitCube] c₀ ∧
            cellEnergyNorm (Set.Ici s) D ≤
              ENNReal.ofReal C₀ * (cellUlNorm (Set.Ici s) f + cellUlNorm (Set.Ici s) F
                + cellL2Norm c₀)) ∧
        (∀ (s : ℝ) (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
            (D D' : ℝ → RawJet2 1 ℂ),
          IsCellSolution (Set.Ici s) ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F D →
          IsCellSolution (Set.Ici s) ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F D' →
          (∀ t, s ≤ t → cellMean (cellValue D t) = 0) →
          (∀ t, s ≤ t → cellMean (cellValue D' t) = 0) →
          ∀ t, s ≤ t →
            cellL2Norm (fun x => cellValue D t x - cellValue D' t x) ≤
              ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (t - s) / 2)) *
                cellL2Norm (fun x => cellValue D s x - cellValue D' s x))) ∧
      (∀ (v : ℝ → Vec 2 → Vec 2), IsCellDrift v →
        ∀ (K : ℕ) (Gj : ℕ × ℕ → Vec 2 → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
          (fj : ℕ × ℕ → Vec 2 → ℝ → Vec 2 → ℂ)
          (Fj : ℕ × ℕ → Vec 2 → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)),
        (∀ Y, IsCellMetric (Gj 0 Y)) →
        (∀ α : ℕ × ℕ, α.1 + α.2 ≤ K → ∀ Y,
          cellMetricSupNorm (Gj α Y) < ⊤ ∧
          Measurable (fun p : ℝ × Vec 2 => Gj α Y p.1 p.2) ∧
          (∀ t, AVenhance.IsZ2Periodic (Gj α Y t)) ∧
          cellUlNorm Set.univ (fj α Y) < ⊤ ∧ cellUlNorm Set.univ (Fj α Y) < ⊤ ∧
          Measurable (fun p : ℝ × Vec 2 => fj α Y p.1 p.2) ∧
          Measurable (fun p : ℝ × Vec 2 => Fj α Y p.1 p.2)) →
        IsNormJetFamily (𝕜 := ℝ) cellMetricSupNorm K Set.univ Gj →
        IsNormJetFamily (𝕜 := ℝ) (cellUlNorm Set.univ) K Set.univ fj →
        IsNormJetFamily (𝕜 := ℝ) (cellUlNorm Set.univ) K Set.univ Fj →
        ∃ cj : ℕ × ℕ → Vec 2 → ℝ → RawJet2 1 ℂ,
          IsNormJetFamily (𝕜 := ℝ) (cellEnergyNorm Set.univ) K Set.univ cj ∧
          (∀ Y, ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K →
            IsCellInverseValue ⟨Gj 0 Y, v, 0, 0⟩ (fun t => cellQ0 (fj α Y t))
              (fun t x => Fj α Y t x
                + cellMetricJetFlux (fun β => Gj β Y) (fun β => cj β Y) α t x)
              (cj α Y)) ∧
          (∀ (Y : Vec 2) (ρ : ℝ), 0 < ρ →
            ENNReal.ofReal C₀ * factorialJetSum ((jetIndices K).erase 0) ρ
                (fun β => cellMetricSupNorm (Gj β Y)) ≤ 1 / 2 →
            factorialJetSum (jetIndices K) ρ (fun α => cellEnergyNorm Set.univ (cj α Y)) ≤
              ENNReal.ofReal (2 * C₀) * factorialJetSum (jetIndices K) ρ
                (fun α => cellUlNorm Set.univ (fj α Y) + cellUlNorm Set.univ (Fj α Y))) ∧
          (∀ (Y : Vec 2) (M a : ℝ), 0 ≤ M → 0 < a →
            (∀ β : ℕ × ℕ, β.1 + β.2 ≤ K → cellMetricSupNorm (Gj β Y) ≤
              ENNReal.ofReal (M * ((β.1.factorial : ℝ) * (β.2.factorial : ℝ)) *
                a ^ (β.1 + β.2))) →
            factorialJetSum (jetIndices K) ((16 * (1 + C₀ * M) * a)⁻¹)
                (fun α => cellEnergyNorm Set.univ (cj α Y)) ≤
              ENNReal.ofReal (2 * C₀) * factorialJetSum (jetIndices K)
                ((16 * (1 + C₀ * M) * a)⁻¹)
                (fun α => cellUlNorm Set.univ (fj α Y) + cellUlNorm Set.univ (Fj α Y)))) := by
  refine ⟨100, by norm_num, ?_, ?_⟩
  · intro G v hG hv
    refine ⟨?_, ?_, ?_⟩
    · intro f F hfm hFm hf hF
      obtain ⟨D, hD, hb, hu⟩ := cellAllTimeInverse_exists_unique hG hv f F hfm hFm hf hF
      refine ⟨D, hD, hb.trans ?_, hu⟩
      gcongr
      norm_num
    · intro s f F hfm hFm hf hF c0 hmi h0 hm0
      obtain ⟨D, hD, hm, hi, hb⟩ := cellFinitePast_exists_bound s hG hv f F hfm hFm hf hF c0 hmi h0 hm0
      refine ⟨D, hD, hm, hi, hb.trans ?_⟩
      gcongr
      norm_num
    · intro s f F D D' hD hD' hm hm'
      exact cellFinitePast_decay s hG hv (fun t => cellQ0 (f t)) F D D' hD hD' hm hm'
  · intro v hv K Gj fj Fj hG0 hdata hGj hfj hFj
    have hd (α : ℕ × ℕ) (hα : α.1 + α.2 ≤ K) Y :
        cellMetricSupNorm (Gj α Y) < ⊤ ∧ Measurable (Function.uncurry (Gj α Y)) ∧
        cellUlNorm Set.univ (fj α Y) < ⊤ ∧ cellUlNorm Set.univ (Fj α Y) < ⊤ ∧
        AEStronglyMeasurable (Function.uncurry (fj α Y))
          ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) ∧
        AEStronglyMeasurable (Function.uncurry (Fj α Y))
          ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) :=
      ⟨(hdata α hα Y).1, (hdata α hα Y).2.1,
        (hdata α hα Y).2.2.2.1, (hdata α hα Y).2.2.2.2.1,
        (hdata α hα Y).2.2.2.2.2.1.aestronglyMeasurable,
        (hdata α hα Y).2.2.2.2.2.2.aestronglyMeasurable⟩
    obtain ⟨cj, hcj, hsol⟩ := cellInverse_normJetFamily_exists K Gj fj Fj hv hG0 hd hGj hfj hFj
    refine ⟨cj, hcj, hsol, ?_, ?_⟩
    · intro Y ρ hρ hsmall
      norm_num only [show (2 * (100 : ℝ)) = 200 by norm_num]
      exact cellInverse_jet_factorial_bound K (fun β => Gj β Y) (fun α => fj α Y)
        (fun α => Fj α Y) (fun α => cj α Y) (hG0 Y) hv
        (fun α ha => hd α ha Y) (fun α ha => hsol Y α ha) hρ hsmall
    · intro Y M a hM ha hgrowth
      have hsmall := factorialJetRadius_small K (fun β => cellMetricSupNorm (Gj β Y))
        100 M a (by norm_num) hM ha hgrowth
      have hr := (factorialRadius_algebra 100 M a (by norm_num) hM ha).1
      norm_num only [show (2 * (100 : ℝ)) = 200 by norm_num]
      exact cellInverse_jet_factorial_bound K (fun β => Gj β Y) (fun α => fj α Y)
        (fun α => Fj α Y) (fun α => cj α Y) (hG0 Y) hv
        (fun α ha => hd α ha Y) (fun α ha => hsol Y α ha) hr hsmall

end AVRegularity.Providers
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleDamping
namespace AVRegularity.Providers

/-! The damping bridge for the constructed cycle. -/

/-- **Damping bridge**. Proposition 11.5(a) of the paper follows from it. -/
theorem cycle_damping_bridge (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∃ g₀ ξ₀ Cg C : ℝ, 0 < g₀ ∧ 0 < ξ₀ ∧ 0 < Cg ∧ 0 < C ∧
        ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
        ∀ y₀ : Vec 2, ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ),
          IsCellMetric (fun t _ => G t) → 0 ≤ g → g ≤ g₀ →
          IsMetricNearIdentity (fun t _ => G t) g →
          ∃ (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ),
            IsFibreGraph (ν / B) G (ocCellDrift α q Λ ζ m ν y₀) ξ₀ Cg r lam ∧
            ∀ χ : Fin 2 → ℝ → RawJet2 1 ℂ,
              (∀ j : Fin 2, IsCellInverseValue
                ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩
                (fun t => cellQ0 (fun x =>
                  ((Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t x j : ℝ) : ℂ)))
                (fun _ _ => 0) (χ j)) →
              ∀ t : ℝ,
                (∀ ξ : Fin 2 → ℂ, fibreHomogeneous lam ξ 2 t =
                  -(∑ i, ∑ j, ξ i *
                    fibreBridgeMatrix (ν / B) G (ocCellDrift α q Λ ζ m ν y₀) χ t i j * ξ j)) ∧
                ∀ i j : Fin 2,
                  ‖fibreBridgeMatrix (ν / B) G (ocCellDrift α q Λ ζ m ν y₀) χ t i j
                      - ((ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) i j / B : ℝ) : ℂ)‖ ≤
                    C * (g + ocEll q Λ m ν ^ 2 / ocTau α q Λ m *
                      Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)))  := by
  obtain ⟨L, hL, hr⟩ := bandChain_relaxation_large hα₀ hα₁ hs₀ hs₁ hq hζ 6 (by norm_num)
  obtain ⟨K, hK, C, hC, hb⟩ := bandChain_bridge_error hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max L K, hL.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ
  refine ⟨1, constructedGraphRadius, constructedGraphBound, C, by norm_num,
    constructedGraphRadius_pos, constructedGraphBound_pos, hC, ?_⟩
  intro M κ hκ m hm hmM ν B hνeq hBeq y₀ G g hG hg _ hnear
  have hΛL := (le_max_left L K).trans hΛ
  have hΛK := (le_max_right L K).trans hΛ
  have hΛ1 : 1 ≤ Λ := by omega
  have hν : 0 < ν := hνeq ▸ CycleReference.bandChain_pos hΛ1 hζ hκ hmM
  have hB : B = ocMeanFlux α q Λ ζ m ν := by
    rw [← hBeq, hκ.2 m (by omega) hmM, hνeq]
  obtain ⟨r, lam, hgraph, _, hid⟩ := constructed_canonical_graph hΛ1 hζ hν
    (hνeq ▸ hr Λ hΛL M κ hκ m hm hmM) y₀ G hG
  rw [← hB] at hgraph hid
  refine ⟨r, lam, hgraph, ?_⟩
  intro χ hχ t
  exact ⟨fun ξ => hid χ hχ ξ t,
    fun i j => hb Λ hΛK M κ hκ m hm hmM ν B hνeq hBeq y₀ G hG g hg hnear χ hχ t i j⟩

end AVRegularity.Providers
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.Providers

/-! The complete cell fibre graph statement, with literal constructed Taylor families. -/

/-- **Fibre graph, decomposition and stability** (Proposition 11.4(a)–(d) of the paper, under the
standing hypotheses (11.3)). -/
theorem cycle_fibre_graph (Cw : ℝ) (hCw : 0 < Cw) :
    ∃ g₀ ξ₀ ξ₁ C : ℝ, 0 < g₀ ∧ 0 < ξ₀ ∧ 0 < ξ₁ ∧ ξ₁ ≤ ξ₀ ∧ 0 < C ∧
      ∀ (η : ℝ), 0 < η → η ≤ 1 →
      ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ),
        IsCellMetric (fun t _ => G t) → IsCellDrift v →
        (∀ t (k : Fin 2), cellMean (fun x => (v t x k : ℂ)) = 0) →
        (∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) →
        0 ≤ g → g ≤ g₀ → IsMetricNearIdentity (fun t _ => G t) g →
        ∃ (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
          (ell : ℕ × ℕ → ℝ → Vec 2 → ℂ),
          IsFibreGraph η G v ξ₀ C r lam ∧
          (∀ ξ : Fin 2 → ℂ, fibreNorm ξ < ξ₀ →
            ∑' p, ENNReal.ofReal ‖fibreMonomial ξ p‖ * ⨆ s, cellL2Norm (ell p s) < ⊤) ∧
          (∀ ξ : Fin 2 → ℂ, fibreNorm ξ < ξ₀ → ∀ s : ℝ,
            Integrable (fun x => fibreSeriesFun ell ξ s x * (1 + cellValue (fibreSeriesJet r ξ) s x))
              (volume.restrict AVenhance.unitCube) ∧
            (∫ x in AVenhance.unitCube,
              fibreSeriesFun ell ξ s x * (1 + cellValue (fibreSeriesJet r ξ) s x)) = 1 ∧
            cellL2Norm (fun x => fibreSeriesFun ell ξ s x - 1) ≤
              ENNReal.ofReal (C * fibreNorm ξ)) ∧
          (∀ (n : ℕ) (ξ : Fin 2 → ℂ) (s : ℝ),
            cellL2Norm (fibreHomogeneous ell ξ n s) ≤
              ENNReal.ofReal (C * (2 / ξ₀) ^ n * fibreNorm ξ ^ n)) ∧
          (∀ ξ : Fin 2 → ℂ, fibreNorm ξ < ξ₀ → ∀ s t : ℝ, s ≤ t →
            ∀ D : ℝ → RawJet2 1 ℂ,
              IsCellSolution (Set.Icc s t) (fibreCoefficients η G v ξ (fun _ => 0))
                (fun _ _ => 0) (fun _ _ => 0) D →
              cellL2Norm (fun x => cellValue D t x
                  - (1 + cellValue (fibreSeriesJet r ξ) t x)
                    * Complex.exp (∫ τ in s..t, fibreSeriesC lam ξ τ)
                    * ∫ y in AVenhance.unitCube, fibreSeriesFun ell ξ s y * cellValue D s y) ≤
                ENNReal.ofReal (C * Real.exp (-(2 * Real.pi ^ 2) * (t - s))) *
                  cellL2Norm (cellValue D s)) ∧
          (∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0) → fibreNorm ξ < ξ₀ → ∀ s t : ℝ, s ≤ t →
            ENNReal.ofReal ‖Complex.exp (∫ τ in s..t, fibreSeriesC lam ξ τ)‖ *
                cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) t x) ≤
              cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) s x) ∧
            cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) s x) ≤
              ENNReal.ofReal C * cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) t x)) ∧
          (∀ ξ : Fin 2 → ℂ, fibreNorm ξ < ξ₀ → ∀ t : ℝ,
            (∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
              cellValue (fibreSeriesJet r (fun i => -(starRingEnd ℂ) (ξ i))) t x
                = (starRingEnd ℂ) (cellValue (fibreSeriesJet r ξ) t x)) ∧
            fibreSeriesC lam (fun i => -(starRingEnd ℂ) (ξ i)) t
              = (starRingEnd ℂ) (fibreSeriesC lam ξ t)) ∧
          (∀ x y : Vec 2, fibreNorm (fun i => (x i : ℂ) + Complex.I * (y i : ℂ)) < ξ₁ → ∀ t : ℝ,
            |(fibreSeriesC lam (fun i => (x i : ℂ) + Complex.I * (y i : ℂ)) t
                - fibreSeriesC lam (fun i => (x i : ℂ)) t).re| ≤
              C * (Real.sqrt (∑ i, y i ^ 2) * ∑ i, x i ^ 2 + ∑ i, y i ^ 2)) ∧
          (∀ (r' : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam' : ℕ × ℕ → ℝ → ℂ),
            IsFibreGraph η (fun _ => 1) v ξ₀ C r' lam' →
            ∀ ξ : Fin 2 → ℂ, fibreNorm ξ < ξ₀ →
              cellEnergyNorm Set.univ (fibreSeriesJet r ξ - fibreSeriesJet r' ξ) ≤
                ENNReal.ofReal (C * g * fibreNorm ξ) ∧
              ∀ t : ℝ, ‖fibreSeriesC lam ξ t - fibreSeriesC lam' ξ t‖ ≤
                C * g * fibreNorm ξ ^ 2) ∧
          (∀ (ξ : Fin 2 → ℂ) (s a : ℝ), fibreNorm ξ < ξ₀ → 0 ≤ a →
            ((∀ τ ∈ Set.Icc (s - a) s, ∀ x, v τ x = 0) →
              cellL2Norm (cellValue (fibreSeriesJet r ξ) s) ≤
                ENNReal.ofReal (C * fibreNorm ξ * Real.exp (-(2 * Real.pi ^ 2) * a))) ∧
            ((∀ τ ∈ Set.Icc s (s + a), ∀ x, v τ x = 0) →
              cellL2Norm (fun x => fibreSeriesFun ell ξ s x - 1) ≤
                ENNReal.ofReal (C * fibreNorm ξ * Real.exp (-(Real.pi ^ 2) * a)))) := by
  let R := fibreCoefficientMajorantRadius Cw
  let ρ := fibreEvolutionRadius Cw
  let C := fibreEvolutionBound Cw
  have hw0 : 0 ≤ Cw := hCw.le
  have hR : 0 < R := fibreCoefficientMajorantRadius_pos hw0
  have hρ : 0 < ρ := fibreEvolutionRadius_pos hw0
  have hc := fibreEvolutionBound_bounds hw0
  have hC100 : 100 ≤ C := hc.1
  have hCfg : fibreCoefficientGraphBound Cw ≤ C := hc.2.1
  have hCpart : fibreCoefficientRealPartBound Cw ≤ C := hc.2.2.1
  have hCE : 312 / R ≤ C := hc.2.2.2.1
  have hCS : 4 + Cw * (312 / R) ≤ C := hc.2.2.2.2.1
  have hCL : 64 / R ≤ C := hc.2.2.2.2.2
  have hC0 : 0 < C := by linarith
  have hρ1024 : ρ ≤ R / 1024 := fibreEvolutionRadius_le_majorant
  have hρ16 : ρ ≤ R / 16 := by linarith
  have hρR : ρ ≤ R := by linarith
  have hρ2 : ρ ≤ R / 2 := by linarith
  have hρ1 : ρ ≤ 1 := by have hr := fibreCoefficientMajorantRadius_le_one hw0; linarith
  have hC13 : 13 ≤ C := by linarith
  have hC3 : 3 ≤ C := by linarith
  have hC4 : 4 ≤ C := by linarith
  have hCfg0 : 0 ≤ fibreCoefficientGraphBound Cw := by
    unfold fibreCoefficientGraphBound
    positivity
  have h8 : 8 / R ≤ 64 / R := by
    gcongr
    norm_num
  have h2 : 2 / R ≤ 64 / R := by
    gcongr
    norm_num
  have hCquiet : 8 / R ≤ C := h8.trans hCL
  have hC2 : 2 / R ≤ C := h2.trans hCL
  refine ⟨1 / 16, ρ, ρ, C, by norm_num, hρ, hρ, le_rfl, hC0, ?_⟩
  intro η hη0 hη G v g hG hv hm hw hg0 hgsmall hg
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G v r
  let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
  have hdisc (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < ρ) : fibreNorm ξ ≤ R / 1024 :=
    hξ.le.trans hρ1024
  have hdisc16 (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < ρ) : fibreNorm ξ ≤ R / 16 :=
    hξ.le.trans hρ16
  have hdiscR (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < ρ) : fibreNorm ξ ≤ R :=
    hξ.le.trans hρR
  refine ⟨r, lam, ell, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isFibreGraph_radius_restriction
      (fibreCoefficientFamily_isFibreGraph η Cw hη0.le hη hw0 G hG hv hw) hρ hρR hCfg0 hCfg
  · intro ξ hξ
    have hb := (fibreMonomial_weighted_energy_le (R / 16) ξ (hdisc16 ξ hξ)
      (fun p => ⨆ s, cellL2Norm (ell p s))).trans
      (fibreAdjointRowCoefficients_weighted_le_four η Cw hη hw0 G hG hv hw)
    exact hb.trans_lt (by norm_num : (4 : ℝ≥0∞) < ⊤)
  · intro ξ hξ s
    have hn := fibreAdjointRowCoefficients_normalization η Cw hη hw0 G hG hv hw ξ (hdisc16 ξ hξ) s
    refine ⟨hn.1, hn.2, ?_⟩
    apply (fibreAdjointRowCoefficients_sub_one_le η Cw hη hw0 G hG hv hw ξ (hdisc16 ξ hξ) s).trans
    apply ENNReal.ofReal_le_ofReal
    have he : 4 / (R / 16) = 64 / R := by
      field_simp
      norm_num
    change (4 / (R / 16)) * fibreNorm ξ ≤ C * fibreNorm ξ
    rw [he]
    exact mul_le_mul_of_nonneg_right hCL (fibreNorm_nonneg ξ)
  · intro n ξ s
    apply (fibreAdjointRowCoefficients_homogeneous_le η Cw hη hw0 G hG hv hw n ξ s).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (fibreNorm_nonneg ξ) n)
    exact mul_le_mul hC4 (pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_left (by norm_num) hρ hρ16) n) (by positivity) hC0.le
  · intro ξ hξ s t hst D hD
    apply (fibreGraph_raw_remainder_norm hst η Cw hη0.le hη hw0 G hG hg hgsmall
      hv hm hw ξ (hdisc ξ hξ) D hD).trans
    apply mul_le_mul' _ le_rfl
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC13 (Real.exp_pos _).le)
  · intro ξ hreal hξ s t hst
    obtain ⟨V, hb⟩ := hv.2.1
    refine ⟨fibreCoefficientFamily_graph_real_ratio η Cw hη0.le hη hw0 G hG hv hm hw
      V hb ξ hreal (hdiscR ξ hξ) hst, ?_⟩
    apply (fibreCoefficientFamily_graph_mode_ratio η Cw hη hw0 G hG hv hw ξ (hdiscR ξ hξ) s t).trans
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hC3) le_rfl
  · intro ξ _ t
    exact ⟨fibreCoefficientFamily_graph_reality η Cw hη G hG hv hw ξ t,
      fibreCoefficientFamily_symbol_series_reality η Cw hη G hG hv hw ξ t⟩
  · intro x y hxy t
    apply (fibreCoefficientFamily_symbol_real_part_bound η Cw hη0.le hη hw0 G hG hv hw
      x y (hxy.le.trans hρ2) t).trans
    exact mul_le_mul_of_nonneg_right hCpart (by positivity)
  · intro r' lam' hgraph ξ hξ
    have hsmall := fibreEvolution_frequency_small hw0 hξ.le
    have hs := fibreCoefficientFamily_metric_stability η Cw hη0.le hη hw0 G hG hv hw
      g hg0 hg ρ C r' lam' hgraph ξ hξ (hξ.le.trans hρ2) (hξ.le.trans hρ1) hsmall.1 hsmall.2
    refine ⟨hs.1.trans (ENNReal.ofReal_le_ofReal ?_), fun t => (hs.2 t).trans ?_⟩
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCE hg0) (fibreNorm_nonneg ξ)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCS hg0)
        (sq_nonneg (fibreNorm ξ))
  · intro ξ s a hξ ha
    constructor
    · intro hquiet
      apply (fibreCoefficientFamily_quiet_past η Cw hη hw0 G hG hg hgsmall hv hw
        ξ (hdisc ξ hξ) s a ha hquiet).trans
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC2 (fibreNorm_nonneg ξ)) (Real.exp_pos _).le)
    · intro hquiet
      apply (fibreAdjointRow_quiet_future η Cw hη hw0 G hG hg hgsmall hv hw
        ξ (hdisc ξ hξ) s a ha hquiet).trans
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCquiet (fibreNorm_nonneg ξ)) (Real.exp_pos _).le)

end AVRegularity.Providers
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleDamping
namespace AVRegularity.Providers

/-! The low- and high-frequency damping theorem for the constructed cycle. -/

/-- **Cycle damping**. -/
theorem cycle_damping (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∃ g₀ ξ₀ ξmax c Cg : ℝ, 0 < g₀ ∧ 0 < ξmax ∧ ξmax < ξ₀ ∧ 0 < c ∧ 0 < Cg ∧
        ∀ ξlo : ℝ, 0 < ξlo →
          ∃ cStar θs Θ₀ : ℝ, 0 < cStar ∧ 0 < θs ∧ 1 ≤ Θ₀ ∧
            (∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
              ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
              ∀ y₀ : Vec 2, ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ),
                IsCellMetric (fun t _ => G t) → 0 ≤ g → g ≤ g₀ →
                IsMetricNearIdentity (fun t _ => G t) g →
                ∃ (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ),
                  IsFibreGraph (ν / B) G (ocCellDrift α q Λ ζ m ν y₀) ξ₀ Cg r lam ∧
                  ∀ ta T : ℝ, IsOCAdmissibleInterval α q Λ ζ m ν B Θ₀ θs ta T →
                    (ξlo ≤ ξmax → ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0) → fibreNorm ξ ≤ ξlo →
                      (∫ τ in (ta / ocEll q Λ m ν ^ 2)..((ta + T) / ocEll q Λ m ν ^ 2),
                          fibreSeriesC lam ξ τ).re
                        ≤ -c * (T / ocEll q Λ m ν ^ 2) * fibreNorm ξ ^ 2 ∧
                      ∀ N : ℕ, 2 ≤ N →
                        (∫ τ in (ta / ocEll q Λ m ν ^ 2)..((ta + T) / ocEll q Λ m ν ^ 2),
                            ∑ n ∈ Finset.range (N + 1), fibreHomogeneous lam ξ n τ).re
                          ≤ -c * (T / ocEll q Λ m ν ^ 2) * fibreNorm ξ ^ 2) ∧
                    (∀ ξ : Vec 2, (∀ k, |ξ k| ≤ Real.pi / Real.sqrt (ν / B)) →
                      ξlo ≤ Real.sqrt (∑ k, ξ k ^ 2) →
                      ∀ D : ℝ → RawJet2 1 ℂ,
                        IsCellSolution
                          (Set.Icc (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2))
                          (fibreCoefficients (ν / B) G (ocCellDrift α q Λ ζ m ν y₀)
                            (fun k => (ξ k : ℂ)) (fun _ => 0))
                          (fun _ _ => 0) (fun _ _ => 0) D →
                        cellL2Norm (cellValue D ((ta + T) / ocEll q Λ m ν ^ 2)) ≤
                          ENNReal.ofReal (Real.exp (-cStar * (T / ocEll q Λ m ν ^ 2))) *
                            cellL2Norm (cellValue D (ta / ocEll q Λ m ν ^ 2)))) ∧
            ∃ mStar : ℕ, ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
              ∀ m : ℕ, 2 ≤ m → mStar ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
              ∀ l : ℤ, IsOCAdmissibleInterval α q Λ ζ m ν B Θ₀ θs
                (((l : ℝ) - 1 / 2) * ocTauPP α q Λ m) (ocTauPP α q Λ m)  := by
  obtain ⟨L, hL, g₀, hg₀, hquad⟩ := bandChain_quadratic_damping hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨H, hH, hhigh⟩ := bandChain_high_decay hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨R, hR, hrel⟩ := bandChain_relaxation_large hα₀ hα₁ hs₀ hs₁ hq hζ 6 (by norm_num)
  obtain ⟨A, hA, had⟩ := bandChain_eventual_block_admissibility hα₀ hα₁ hs₀ hs₁ hq hζ
  let cadm : ℝ := (1 - Real.exp (-2)) / 288
  have hcadm : 0 < cadm := div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))) (by norm_num)
  obtain ⟨ξmax, hxmax, hxR, hxR4, hxsmall⟩ := low_radius_budget
    constructedGraphRadius constructedGraphBound cadm constructedGraphRadius_pos
      constructedGraphBound_pos hcadm
  refine ⟨max L (max H (max R A)), hL.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ
  have hΛL := (le_max_left L (max H (max R A))).trans hΛ
  have hΛH := (le_max_left H (max R A)).trans ((le_max_right L (max H (max R A))).trans hΛ)
  have hΛRA := (le_max_right H (max R A)).trans ((le_max_right L (max H (max R A))).trans hΛ)
  have hΛR := (le_max_left R A).trans hΛRA
  have hΛA := (le_max_right R A).trans hΛRA
  have hΛ1 : 1 ≤ Λ := by omega
  refine ⟨g₀, constructedGraphRadius, ξmax, cadm / 2, constructedGraphBound,
    hg₀, hxmax, hxR, by positivity, constructedGraphBound_pos, ?_⟩
  intro ξlo hlo
  obtain ⟨d, cStar, hd, hcStar, hdec⟩ := hhigh Λ hΛH ξlo hlo
  let Θ : ℝ := max 1 (3 * d)
  have hΘ : 1 ≤ Θ := le_max_left _ _
  have hdΘ : 3 * d ≤ Θ := le_max_right _ _
  refine ⟨cStar, d, Θ, hcStar, hd, hΘ, ?_, had Λ hΛA Θ d hΘ hd hdΘ⟩
  intro M κ hκ m hm hmM ν B hνeq hBeq y₀ G g hG hg hgg hnear
  have hν : 0 < ν := hνeq ▸ CycleReference.bandChain_pos hΛ1 hζ hκ hmM
  have hB : B = ocMeanFlux α q Λ ζ m ν := by
    rw [← hBeq, hκ.2 m (by omega) hmM, hνeq]
  have hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m := hνeq ▸ hrel Λ hΛR M κ hκ m hm hmM
  have hv := ocCellDrift_isCellDrift (α := α) (q := q) (m := m) hΛ1 hζ ν y₀
  obtain ⟨r, lam, hgraph, hlam, hid⟩ := constructed_canonical_graph hΛ1 hζ hν hr y₀ G hG
  obtain ⟨χ, hχ⟩ := constructed_correctors hΛ1 hζ hν hr y₀ G hG
  rw [← hB] at hgraph hid hχ
  refine ⟨r, lam, hgraph, ?_⟩
  intro ta T hI
  constructor
  · intro hlow ξ hreal hξ
    have hξmax := hξ.trans hlow
    have hξR4 := hξmax.trans hxR4
    have hlen : 0 < ocEll q Λ m ν ^ 2 := by
      rw [CycleReference.ocEll_sq_eq hν]
      have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ1
      positivity
    have hS : 0 ≤ T / ocEll q Λ m ν ^ 2 := (by linarith : 0 ≤ Θ).trans hI.2.1
    have hab : ta / ocEll q Λ m ν ^ 2 ≤ (ta + T) / ocEll q Λ m ν ^ 2 := by
      have he : (ta + T) / ocEll q Λ m ν ^ 2 - ta / ocEll q Λ m ν ^ 2 =
          T / ocEll q Λ m ν ^ 2 := by ring
      linarith only [he, hS]
    have heS : (ta + T) / ocEll q Λ m ν ^ 2 - ta / ocEll q Λ m ν ^ 2 =
        T / ocEll q Λ m ν ^ 2 := by ring
    have hq := hquad Λ hΛL M κ hκ m hm hmM ν B hνeq hBeq y₀ G hG g hg hgg hnear
      χ hχ Θ d ta T (by linarith) hI (fun i => (ξ i).re)
    have heq : (fun t => fibreHomogeneous lam ξ 2 t) =
        fun t => -(∑ i, ∑ j, ((ξ i).re : ℂ) *
          fibreBridgeMatrix (ν / B) G (ocCellDrift α q Λ ζ m ν y₀) χ t i j * ((ξ j).re : ℂ)) := by
      funext t
      rw [hid χ hχ ξ t]
      congr 1
      exact congrArg (fun z : Fin 2 → ℂ => ∑ i, ∑ j,
        z i * fibreBridgeMatrix (ν / B) G (ocCellDrift α q Λ ζ m ν y₀) χ t i j * z j)
        (real_frequency_eq ξ hreal)
    have hq' : (∫ t in (ta / ocEll q Λ m ν ^ 2)..((ta + T) / ocEll q Λ m ν ^ 2),
        fibreHomogeneous lam ξ 2 t).re ≤ -(3 * cadm / 4) *
          (((ta + T) / ocEll q Λ m ν ^ 2) - ta / ocEll q Λ m ν ^ 2) * fibreNorm ξ ^ 2 := by
      rw [heq, heS, real_frequency_norm_sq ξ hreal]
      exact hq
    have hh := low_full_finite_damping_of_graph hG hv hgraph constructedGraphRadius_pos
      constructedGraphBound_pos.le hlam ξ hξR4 (ta / ocEll q Λ m ν ^ 2)
      ((ta + T) / ocEll q Λ m ν ^ 2) cadm hab (hxsmall _ hξmax) hq'
    simpa only [heS] using hh
  · exact hdec M κ hκ m hm hmM ν B hνeq hBeq y₀ G hG Θ ta T hΘ hI

end AVRegularity.Providers
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.Providers

/-! Actual normalized fibre word operators and their quantitative complex norm jets. -/

/-- **Word-operator bounds**. -/
theorem cycle_word_operators (Cw : ℝ) (hCw : 0 < Cw) :
    ∃ (g₀ ξ₀ ξ₂ C : ℝ) (Cj : ℕ → ℝ), 0 < g₀ ∧ 0 < ξ₀ ∧ 0 < ξ₂ ∧ ξ₂ ≤ ξ₀ ∧ 0 < C ∧
      (∀ n, 0 < Cj n) ∧
      ∀ (η : ℝ), 0 < η → η ≤ 1 →
      ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ),
        IsCellMetric (fun t _ => G t) → IsCellDrift v →
        (∀ t (k : Fin 2), cellMean (fun x => (v t x k : ℂ)) = 0) →
        (∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) →
        0 ≤ g → g ≤ g₀ → IsMetricNearIdentity (fun t _ => G t) g →
        ∃ (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ),
          IsFibreGraph η G v ξ₀ C r lam ∧
          ∀ (S : ℝ), 1 ≤ S → ∀ s₀ a b : ℝ, s₀ ≤ a → a ≤ b → b ≤ s₀ + S →
            (∀ ξ : Fin 2 → ℂ, fibreNorm ξ < ξ₂ →
              (∀ D : ℝ → RawJet2 1 ℂ,
                IsCellSolution (Set.Icc s₀ b)
                  (fibreCoefficients η G v ξ (fibreSeriesC lam ξ)) (fun _ _ => 0)
                  (fun _ _ => 0) D →
                fibreXNorm (fibreCoefficients η G v ξ (fibreSeriesC lam ξ)).θ (Set.Icc a b) D ≤
                  ENNReal.ofReal (C * (1 + Real.sqrt S * fibreNorm ξ)) *
                    cellL2Norm (cellValue D s₀)) ∧
              (∀ (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (D : ℝ → RawJet2 1 ℂ),
                MemLp (Function.uncurry F) 2 ((volume.restrict (Set.Icc s₀ b)).prod
                  (volume.restrict AVenhance.unitCube)) →
                IsCellSolution (Set.Icc s₀ b)
                  (fibreCoefficients η G v ξ (fibreSeriesC lam ξ)) (fun _ _ => 0) F D →
                cellValue D s₀ =ᵐ[volume.restrict AVenhance.unitCube] 0 →
                fibreXNorm (fibreCoefficients η G v ξ (fibreSeriesC lam ξ)).θ (Set.Icc a b) D ≤
                  ENNReal.ofReal (C * (1 + Real.sqrt S * fibreNorm ξ) ^ 2) *
                    (∫⁻ τ in Set.Icc s₀ b, cellL2Norm (F τ) ^ 2) ^ (1 / 2 : ℝ))) ∧
            (∀ (K : ℕ) (h₀ : Vec 2 → ℂ),
              AEStronglyMeasurable h₀ (volume.restrict AVenhance.unitCube) → cellL2Norm h₀ < ⊤ →
              ∃ J : ℕ × ℕ → (Fin 2 → ℂ) → ℝ → RawJet2 1 ℂ,
                IsNormJetFamily (𝕜 := ℂ) (cellEnergyNorm (Set.Icc s₀ b)) K
                  {ξ | fibreNorm ξ < ξ₂} J ∧
                (∀ ξ : Fin 2 → ℂ, fibreNorm ξ < ξ₂ →
                  IsCellSolution (Set.Icc s₀ b)
                    (fibreCoefficients η G v ξ (fibreSeriesC lam ξ)) (fun _ _ => 0)
                    (fun _ _ => 0) (J (0, 0) ξ) ∧
                  cellValue (J (0, 0) ξ) s₀ =ᵐ[volume.restrict AVenhance.unitCube] h₀) ∧
                ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K → ∀ ξ : Fin 2 → ℂ, fibreNorm ξ < ξ₂ →
                  fibreXNorm (fibreCoefficients η G v ξ (fibreSeriesC lam ξ)).θ (Set.Icc a b)
                      (J α ξ) ≤
                    ENNReal.ofReal (Cj K * Real.sqrt S ^ (α.1 + α.2) *
                      (1 + Real.sqrt S * fibreNorm ξ)) * cellL2Norm h₀) ∧
            (∀ (K : ℕ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)),
              Measurable (fun p : ℝ × Vec 2 => F p.1 p.2) →
              (∫⁻ τ in Set.Icc s₀ b, cellL2Norm (F τ) ^ 2) < ⊤ →
              ∃ J : ℕ × ℕ → (Fin 2 → ℂ) → ℝ → RawJet2 1 ℂ,
                IsNormJetFamily (𝕜 := ℂ) (cellEnergyNorm (Set.Icc s₀ b)) K
                  {ξ | fibreNorm ξ < ξ₂} J ∧
                (∀ ξ : Fin 2 → ℂ, fibreNorm ξ < ξ₂ →
                  IsCellSolution (Set.Icc s₀ b)
                    (fibreCoefficients η G v ξ (fibreSeriesC lam ξ)) (fun _ _ => 0) F
                    (J (0, 0) ξ) ∧
                  cellValue (J (0, 0) ξ) s₀ =ᵐ[volume.restrict AVenhance.unitCube] 0) ∧
                ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K → ∀ ξ : Fin 2 → ℂ, fibreNorm ξ < ξ₂ →
                  fibreXNorm (fibreCoefficients η G v ξ (fibreSeriesC lam ξ)).θ (Set.Icc a b)
                      (J α ξ) ≤
                    ENNReal.ofReal (Cj K * Real.sqrt S ^ (α.1 + α.2) *
                      (1 + Real.sqrt S * fibreNorm ξ) ^ 2) *
                      (∫⁻ τ in Set.Icc s₀ b, cellL2Norm (F τ) ^ 2) ^ (1 / 2 : ℝ)) ∧
            ∀ (n : ℕ) (j : Fin n → Fin 2) (ξ : Fin 2 → ℂ), 1 ≤ n → fibreNorm ξ < ξ₂ →
              ∀ s t : ℝ, s₀ ≤ s → s ≤ t → t ≤ s₀ + S →
                ‖iteratedFDeriv ℂ n (fun ξ' : Fin 2 → ℂ => ∫ τ in s..t, fibreSeriesC lam ξ' τ) ξ
                    (fun i => Pi.single (j i) (1 : ℂ))‖ ≤
                  Cj n * Real.sqrt S ^ n *
                    (if n = 1 then Real.sqrt S * fibreNorm ξ else 1) :=
by
  let ξ₀ := fibreWordRadius Cw
  let ξ₂ := ξ₀ / 4
  let C := fibreWordGateConstant Cw
  have hw0 := hCw.le
  have hW := fibreWordRadius_pos hw0
  have hR := fibreCoefficientMajorantRadius_pos hw0
  have hWR := (fibreWordRadius_le_graph Cw).trans (fibreEvolutionRadius_le_majorant (Cw := Cw))
  have hC := fibreWordGateConstant_bounds hw0
  refine ⟨1 / 16, ξ₀, ξ₂, C, fibreWordGateJetConstant Cw, by norm_num,
    hW, by dsimp only [ξ₂]; positivity, by dsimp only [ξ₂]; linarith,
    hC.1, fibreWordGateJetConstant_pos hw0, ?_⟩
  intro η hη0 hη G v g hG hv hm hw _hg0 hgsmall hg
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G v r
  have hGraphC : 0 ≤ fibreCoefficientGraphBound Cw := by
    unfold fibreCoefficientGraphBound
    positivity
  have hgraph := isFibreGraph_radius_restriction
    (fibreCoefficientFamily_isFibreGraph η Cw hη0.le hη hw0 G hG hv hw)
    hW (by linarith) hGraphC hC.2.1
  refine ⟨r, lam, hgraph, ?_⟩
  intro S hS s₀ a b hsa hab hbS
  obtain ⟨V, hb⟩ := hv.2.1
  have hsmall (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < ξ₂) : fibreNorm ξ ≤ fibreWordRadius Cw := by
    dsimp only [ξ₂, ξ₀] at hξ
    linarith
  have hinner (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < ξ₂) :
      fibreNorm ξ < fibreWordRadius Cw / 4 := hξ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ξ hξ
    have hn := fibreNorm_nonneg ξ
    constructor
    · intro D hD
      have hx := fibreCoefficient_homogeneous_raw_xnorm_bound η Cw hη0.le hη hw0 G hG hg hgsmall
        hv hm hw ξ (hsmall ξ hξ) V hb S s₀ a b hS hsa hab hbS D hD
      apply hx.trans
      apply mul_le_mul' _ le_rfl
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right hC.2.2.1 (by positivity)
    · intro F D hF hD hi
      have hx := fibreCoefficient_forced_raw_xnorm_bound η Cw hη0.le hη hw0 G hG hg hgsmall
        hv hm hw ξ (hsmall ξ hξ) V hb S s₀ a b hS hsa hab hbS F hF D hD hi
      apply hx.trans
      apply mul_le_mul' _ le_rfl
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right hC.2.2.2 (sq_nonneg _)
  · intro K h₀ _hm₀ hh₀
    exact fibreWord_homogeneous_jets η Cw hη0.le hη hw0 G hG hg hgsmall hv hm hw
      V hb S s₀ a b hS hsa hab hbS K h₀ hh₀
  · intro K F hFm hFinite
    exact fibreWord_forced_jets η Cw hη0.le hη hw0 G hG hg hgsmall hv hm hw
      V hb S s₀ a b hS hsa hab hbS K F hFm hFinite
  · intro n j ξ hn hξ s t hs hst ht
    have hphaseξ : fibreNorm ξ < fibreCoefficientMajorantRadius Cw / 2 := by
      have hx := hinner ξ hξ
      linarith
    have hx := fibreCoefficientFamily_phase_word_bound η Cw hη0.le hη hw0 G hG hv hw
      S hS s₀ s t hs hst ht n j hn ξ hphaseξ
    apply hx.trans
    have hCj := (fibreWordGateJetConstant_bounds hw0 (n := n) (K := n) le_rfl).2.2
    have hfn := fibreNorm_nonneg ξ
    have hi : 0 ≤ (if n = 1 then Real.sqrt S * fibreNorm ξ else 1) := by split <;> positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCj (by positivity)) hi

end AVRegularity.Providers
end
