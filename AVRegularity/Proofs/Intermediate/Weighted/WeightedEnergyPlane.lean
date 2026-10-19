-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Weighted.WeightedEnergyPlaneExistence
public import AVRegularity.Definitions.CycleWords.CoreScalarPackage
public import AVRegularity.Statements.Intermediate.CycleEvolution.IsMetricNearIdentity

/-! Weighted plane well-posedness and energy. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.Providers

/-- **Weighted plane energy estimate with well-posedness** (used in Step 3 of the proof of
Proposition 11.7 of the paper). -/
theorem weighted_energy_plane (n Kmax : ℕ) (CG Cw : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ x, 0 < π x) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (ta tb : ℝ) (_ht : ta ≤ tb) (rstar δ : ℝ) (_hrstar : 0 < rstar) (_hδ : 0 ≤ δ)
        (_hrδ : rstar * δ ≤ 1)
        (v : ℝ → Vec 2 → Vec 2)
        (_hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ C)
        (_hv_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => v p.1 p.2)
        (_hv_smooth : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
        (_hv_div : ∀ t ∈ Set.Icc ta tb, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
        (a B₀ lam : ℝ) (_ha : 0 ≤ a) (_hB₀ : 1 ≤ B₀) (_hlam : 0 < lam)
        (_hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc ta tb, ∀ x,
          ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
            a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
        (_hB : B₀ * rstar / lam ≤ 1 / 2) (_hab : a * B₀ * rstar ^ 2 ≤ 1 / 8)
        (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
        (_hG_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => G p.1 p.2)
        (_hG_symm : ∀ t ∈ Set.Icc ta tb, ∀ z, (G t z).IsSymm)
        (_hG_near : IsMetricNearIdentity G g)
        (_hG_smooth : ∀ t ∈ Set.Icc ta tb, ∀ a' k : Fin 2,
          ContDiff ℝ (max Kmax 1 : ℕ) (fun z => G t z a' k))
        (_hG_jets : ∀ t ∈ Set.Icc ta tb, ∀ z : Vec 2, ∀ j : ℕ, 1 ≤ j → j ≤ Kmax →
          ∀ a' k : Fin 2, ‖iteratedFDeriv ℝ j (fun z' => G t z' a' k) z‖ ≤ CG j * g * δ ^ j)
        (tw S ϖ : ℝ) (zc : Vec 2) (_htw : tw ≤ ta) (_htb : tb ≤ tw + S)
        (_W : ChartWeights G v tw S ϖ zc n Cw)
        (V₀ : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
        (F : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (PiLp 2 (fun _ : Fin 2 => h x)))
        (_hF : ∀ x, MemLp (F x) 2 (volume.restrict (Set.Icc ta tb))),
        (∃ (V : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
            (Vw : ∀ x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x)),
          IsPlaneChainFrom (geometryScalarData 2 G) (fun _ x => Kslot x) ta tb v
            (fun _ x => V₀ x) (fun _ x => F x) (fun _ x => V x) (fun _ x => Vw x)) ∧
        (∀ (V V' : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
            (Vw Vw' : ∀ x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x)),
          IsPlaneChainFrom (geometryScalarData 2 G) (fun _ x => Kslot x) ta tb v
            (fun _ x => V₀ x) (fun _ x => F x) (fun _ x => V x) (fun _ x => Vw x) →
          IsPlaneChainFrom (geometryScalarData 2 G) (fun _ x => Kslot x) ta tb v
            (fun _ x => V₀ x) (fun _ x => F x) (fun _ x => V' x) (fun _ x => Vw' x) →
          ∀ x, ∀ t ∈ Set.Icc ta tb, V x t = V' x t) ∧
        (∀ (V : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
            (Vw : ∀ x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x)),
          IsPlaneChainFrom (geometryScalarData 2 G) (fun _ x => Kslot x) ta tb v
            (fun _ x => V₀ x) (fun _ x => F x) (fun _ x => V x) (fun _ x => Vw x) →
          geometryEnergyNorm π Kslot n ϖ zc rstar ta tb V Vw ≤
            ENNReal.ofReal C *
              (geometryDataNorm π Kslot n ϖ zc rstar V₀ +
                geometryFluxNorm π Kslot n ϖ zc rstar ta tb F)) := by
  obtain ⟨C, hC, he⟩ := Weighted.weighted_energy_plane_apriori n Kmax CG Cw
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W V₀ F hF
  refine ⟨?_, ?_, ?_⟩
  · exact Weighted.weighted_energy_plane_exists Kmax CG π hπ Kslot hKslot ta tb ht
      rstar δ hrstar hδ hrδ v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam
      hjets hB hab G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets V₀ F hF
  · intro V V' Vw Vw' hs hs' x t ht'
    exact Weighted.scalarChain_energy_solution_unique ta tb ht (fun _ x => Kslot x)
      v (fun t ht' => (hv_smooth t ht').of_le (by norm_num)) hv_meas hv_bdd hv_div G
      (fun t ht' k j => (hG_smooth t ht' k j).continuous) hG_meas g hg4 hG_near hG_symm
      (fun p => V₀ p.2) (fun p => F p.2) (fun p => hF p.2)
      (fun p => V p.2) (fun p => V' p.2) (fun p => Vw p.2) (fun p => Vw' p.2)
      hs hs' (0, x) t ht'
  · exact he π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
      v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
      G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
      tw S ϖ zc htw htb W V₀ F hF

end AVRegularity.Providers
