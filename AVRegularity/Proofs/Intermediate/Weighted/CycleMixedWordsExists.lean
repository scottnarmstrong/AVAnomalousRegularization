-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Weighted.WordNativeSolutionPack
public import AVRegularity.Definitions.CycleWords.ScalarPackage
public import AVRegularity.Statements.Intermediate.CycleEvolution.IsMetricNearIdentity

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.Providers

/-- **Existence of the finite word chain**. -/
theorem cycle_mixed_words_exists (K : ScalarConstants)
    (Nw D H Kf m : ℕ) (hD : 2 ≤ D) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) :
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      (π : ι → ℝ) (_hπ : ∀ x, 0 < π x)
      (letters : Fin Nw → CycleLetter ι h D)
      (_hletters : ∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧
        (letters i).positive = pos i)
      (η S ηg t₀ ϖ : ℝ) (_hη : 0 < η) (_hη1 : η ≤ 1) (_hS : 1 ≤ S) (_hηg : 0 < ηg)
      (_hηg1 : ηg ≤ 1) (_hϖ : ϖ = Real.sqrt (η / S))
      (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
      (_hGm : IsCellMetric (fun t _ => G t)) (_hv : IsCellDrift v)
      (_hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
      (_hv0 : ∀ t (k : Fin 2), cellMean (fun x => (v t x k : ℂ)) = 0)
      (_hvw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
      (_hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj j)
      (_hg0 : 0 ≤ g) (_hgq : g ≤ 1 / 4) (_hg : g ≤ K.g0)
      (_hGn : IsMetricNearIdentity (fun t _ => G t) g)
      (reg : BlockRegions) (_pkg : ScalarPackage K η G v t₀ S ϖ reg)
      (_hlet : ∀ i, IsCycleLetter π (letters i) (Set.Icc t₀ (t₀ + S) ×ˢ Set.univ)
        (wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d) H)
      (_hmeas : ∀ i x y o, ∀ γ ∈ (letters i).edge x y o, ∀ α X z,
        Measurable fun t => γ.coeff α t X z)
      (X₀ : Vec 2) (κ : Fin (Nw + 1) → ι → ℕ) (_hκf : ∀ x, Kf ≤ κ (Fin.last Nw) x)
      (_hκ : ∀ (j : Fin Nw) x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
        κ j.succ x + o.1 ≤ κ j.castSucc y + 2)
      (_hκJ : ∀ (j : Fin Nw) x, κ j.succ x ≤
        wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d)
      (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
      (_hfin : geometryDataNorm π (κ 0) (wordReserveN m Ks) ϖ 0 1 f < ⊤),
      ∃ (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f
          (fun _ _ _ => 0) u w :=
  by
    classical
    intro ι _ h _ _ _ _ _ _ π hπ letters hletters η S ηg t₀ ϖ hη _ hS _ _ hϖ
      G v g hGm hv hvs _ _ hvj hg0 hgq _ hGn reg pkg hlet hmeas X₀ κ _ _ hκJ f hfin
    let Kmax := ∑ p : Fin (Nw + 1) × ι, κ p.1 p.2
    have hK (_j : Fin (Nw + 1)) (_x : ι) : κ _j _x ≤ Kmax :=
      Finset.single_le_sum (f := fun p : Fin (Nw + 1) × ι => κ p.1 p.2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (_j, _x))
    obtain ⟨strain, ha, hjets⟩ := Weighted.finite_drift_jet_envelope Kmax η hη v hvs K.Cvj hvj
    obtain ⟨ρ, hρ, hρh, hsmall⟩ := Weighted.exists_finite_drift_radius strain ha
    have hϖpos : 0 < ϖ := by
      rw [hϖ]
      exact Real.sqrt_pos.mpr (div_pos hη (lt_of_lt_of_le zero_lt_one hS))
    have hfρ : geometryDataNorm π (κ 0) (wordReserveN m Ks) ϖ 0 ρ f ≠ ⊤ :=
      ne_top_of_le_ne_top hfin.ne
        (Weighted.geometryDataNorm_radius_mono π (κ 0) (wordReserveN m Ks) ϖ 0 hρ.le
          (hρh.trans (by norm_num)) f)
    obtain ⟨s, hs, hz, hr⟩ := Weighted.exists_finite_weighted_word_levels π hπ κ Kmax hK
      t₀ S (by linarith) m Ks ϖ ρ strain hϖpos hρ hρh ha hsmall v hv hvs hjets
      G hGm g hg0 hgq hGn K.Cwt pkg.weights letters (fun j => (hletters j).2.1)
      (wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d) H hlet hκJ
      X₀ (ϖ * ηg)
      (fun j x y o k α X z => hmeas j x y o _ (List.get_mem _ k) α X z) f hfρ
    have hflux := Weighted.wordScalarFlux_agreement hD G letters κ X₀ (ϖ * ηg)
      t₀ (t₀ + S) s hz hr
    obtain ⟨w, hw⟩ := Weighted.word_native_solution_pack G letters κ X₀ (ϖ * ηg)
      t₀ (t₀ + S) v f s (fun j => (hs j).1) hflux
    exact ⟨fun j => (s j).u, w, hw⟩

end AVRegularity.Providers
