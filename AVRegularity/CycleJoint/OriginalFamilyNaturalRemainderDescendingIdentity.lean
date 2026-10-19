-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PlaneHomogeneousMaterialWeakCurve
import AVRegularity.CycleJoint.PreparationTransportedWeightedPolynomialAllMomentMap
import AVRegularity.CycleJoint.MetricTaylorFamilyMapMassBudget
public import AVRegularity.CycleJoint.PlaneComponentAllMomentGradientBudget
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs

/-! The source Schur budget is uniform over reference times in the covered preparation window. -/

/-- The same family-independent Schur constant applies at every covered reference time. -/
theorem preparation_window_reference_cell_source_subwindow_schur_budget (D Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν e ρ : ℝ), 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
        ∀ σ ∈ Set.Icc tS tZ,
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
        ∀ (yc : Vec 2) (a b : ℝ),
          Set.Icc a b ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)) → ∀ v u,
          schurMatrix 1 (ρ / e) π K D a b
            (preparationReferenceCellSourceCoefficient F hφ σ
              ν e (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * B v u := by
  obtain ⟨Cprep, hCprep, hglobal⟩ := preparation_window_reference_cell_source_schur_budget
    D Kmax Jchart Jm hchart _hmol Cm Cchart
  obtain ⟨Csamp, _, hsamp⟩ := preparation_window_reference_sampled_envelope_of_pointwise_certificate
    D Kmax Jchart Jm hchart _hmol Cm Cchart
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι _ h _ _ P' Ctx F π hπ K hK actual B hB hc hcover σ hσ henv yc a b hsub v u
  have hs := hsamp α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    F π hπ K hK actual B hB hc hcover σ hσ henv
  have he : 0 < e := hρ.trans_le hρe
  have hfinite v u d := preparationReferenceCellSourceCoefficient_seminorm_ne_top
    F hφ σ ν e (ocEpsilon q Λ (m - 1)) actual K yc
    π hπ tS tZ ρ (ρ / e) Csamp hν hρ he.ne' B hs v u d
  exact (schurMatrix_time_mono 1 (ρ / e) zero_lt_one (div_pos hρ he) π K D a b
    ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)) hsub _ hfinite v u).trans
    (hglobal α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
      F π hπ K hK actual B hB hc hcover σ hσ henv yc v u)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVenhance AVRegularity.ChartTransport AVRegularity.CycleWords AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Inactive-time natural remainders retain the original output-window constituent price. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem familyNaturalRemainder_transported_reserved_jet_budget
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (hw : ∀ p, Measurable (F.weight p)) (hm : F.IsTimeMeasurable)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (W : Set ℝ)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W) ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (hKs : Ks + 1 ≤ J) (p : P) (c : Ctx p)
    (rjet : ℕ) (hrjet : 1 ≤ rjet)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (hsE : ρ / e ≤ ocEpsilon q Λ (m - 1) / e)
    (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hscale : (ρ / e) * ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hδ : e / E = ζ * ϖ) (hn : K v ≤ Jchart + 1)
    (timeScale a b : ℝ) (htime : ∀ t ∈ Set.Icc a b, timeScale * t ∈ W)
    (N : ℕ) (hN : N ≤ Jchart) (hKN : K v + (F.identity v u γ).maxOrder ≤ N)
    (hcellE : 0 < ocEpsilon q Λ (m - 1))
    (yc : Vec 2) (τ : ℝ) (j : ℕ) (hj : j ≤ K v) (Ijet : DerivativeWord2 rjet) (k : Fin 2) (z : Vec 2) :
    let B := fun d I τ z k => naturalSlowRemainderTimeCoefficient Ks
      (fun t X y => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * t) X y k)
      a b hφ r (fun _ => σ) e E yc τ z
    let Num := fun d I => naturalRemainderChartPrice Ks Kmax Jchart Cchart * ζ ^ (Ks + 1) *
      ((Kmax.factorial : ℝ) ^ 2 * E ^ (Ks + 1) * molecularRealPrice ν ρ (K v) (d - 2)
        (pointwiseMolecularJet ρ e (K v) (Ks + 1)
          (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)))
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow N * Cflow
    (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (fun y => transportedCoeff
      (fun x => naturalPreparationJacobian hφ r σ (yc + e • x))
      (F.identity v u γ).maxOrder (fun d I => B d I τ y) rjet Ijet y k) z‖ *
      derivativeReserveFactor (ρ / e) (K v) (rjet - 1) ≤
    transportedPolynomialUniformReservePrice N D (K v) Cpiola *
      (∑ d ∈ Finset.Icc (rjet + 1) (F.identity v u γ).maxOrder,
        ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2, Num d I) *
      polynomialMomentRoot ϖ z ^ (Ks + 1) := by
  let B := fun (d : ℕ) (I : DerivativeWord2 (d - 1)) (τ : ℝ) (z : Vec 2) (k : Fin 2) =>
    naturalSlowRemainderTimeCoefficient Ks
      (fun t X y => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * t) X y k)
      a b hφ r (fun _ => σ) e E yc τ z
  let Num := fun (d : ℕ) (I : DerivativeWord2 (d - 1)) =>
    naturalRemainderChartPrice Ks Kmax Jchart Cchart * ζ ^ (Ks + 1) *
      ((Kmax.factorial : ℝ) ^ 2 * E ^ (Ks + 1) * molecularRealPrice ν ρ (K v) (d - 2)
        (pointwiseMolecularJet ρ e (K v) (Ks + 1)
          (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)))
  have hNum d I : 0 ≤ Num d I := by
    have hnat := naturalRemainderChartPrice_nonneg Ks Kmax Jchart Cchart
    have hM := molecularRealPrice_nonneg ν ρ hν.le hρ.le (K v) (d - 2)
      (pointwiseMolecularJet ρ e (K v) (Ks + 1)
        (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
    dsimp only [Num]
    positivity
  have hRes d : 0 < derivativeReserveFactor (ρ / e) (K v) d := by
    unfold derivativeReserveFactor
    positivity
  have hreg d I i := inactiveTimeZeroFamily_natural_remainder_time_regularity F hw hm W E e
    hE.ne' he.ne' (fun v => K v + J) henv.1 Ks (K v) p c v u γ d I i (by omega)
    timeScale a b htime hφ r σ yc
  have hBj d (hd : d ∈ Finset.Icc (rjet + 1) (F.identity v u γ).maxOrder) I i t l
      (hl : l ≤ K v) y :
      (ρ / e) ^ l * ‖iteratedFDeriv ℝ l (fun x => B d I t x i) y‖ ≤
      (Num d I / derivativeReserveFactor (ρ / e) (K v) (d - 2)) *
        polynomialMomentRoot ϖ y ^ (Ks + 1) := by
    have hd0 : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder := by
      simp only [Finset.mem_Icc] at hd ⊢
      omega
    exact inactiveTimeZeroFamily_natural_time_remainder_reserved_jet_budget Ks F π hπ K Kmax hK
      W ν e E ρ hν he hE hρ C J b₀ henv v u γ hγ d hd0 I hKs p c hc ha r σ hr hσ hage hsE
      ϖ ζ hϖ hscale hζ hδ hn timeScale a b htime t yc y i l hl
  have hb := preparationTransportedPolynomial_coefficient_jet_budget (K v) rjet hc ha hcellE
    r σ hr hσ (by simpa only [abs_sub_comm] using hage) N (F.identity v u γ).maxOrder hN hKN
    e (ρ / e) ϖ he (div_pos hρ he) hsE yc B (fun d I i t => (hreg d I i).2 t)
    (fun d I => Num d I / derivativeReserveFactor (ρ / e) (K v) (d - 2))
    (fun d I => div_nonneg (hNum d I) (hRes _).le) (Ks + 1) hBj τ j hj Ijet k z
  let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
  let Cpiola := compConst Cflow N * Cflow
  have hCf : 1 ≤ Cflow := AVRegularity.ChartTransport.one_le_jetConst _ _
  have hCp : 0 ≤ Cpiola := mul_nonneg
    (AVRegularity.ChartTransport.compConst_nonneg hCf N) (zero_le_one.trans hCf)
  have hprice := transportedPolynomialJetPrice_uniform_reserve_bound N (F.identity v u γ).maxOrder
    D rjet (K v) (F.identity v u γ).le_D hrjet Cpiola (ρ / e)
    (ocEpsilon q Λ (m - 1) / e) hCp (div_pos hρ he) (div_pos hcellE he) hsE Num hNum
  dsimp only at hb ⊢
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (hRes (rjet - 1)).le
    _ = (transportedPolynomialJetPrice N (F.identity v u γ).maxOrder rjet (K v) Cpiola
          (ocEpsilon q Λ (m - 1) / e)
          (fun d I => Num d I / derivativeReserveFactor (ρ / e) (K v) (d - 2)) *
        derivativeReserveFactor (ρ / e) (K v) (rjet - 1)) * polynomialMomentRoot ϖ z ^ (Ks + 1) := by
      dsimp only [Cpiola, Cflow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hprice
      (pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) _)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVenhance AVRegularity.CycleWords AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Inactive-time natural remainders retain the original output-window constituent price. -/

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem exists_familyNaturalRemainder_transported_allMoment_map
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (hw : ∀ p, Measurable (F.weight p)) (hm : F.IsTimeMeasurable)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (W : Set ℝ)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W) ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (hKs : Ks + 1 ≤ J) (p : P) (c : Ctx p)
    {L rjet : ℕ} (hKL : K v + rjet ≤ L + 1) (hrjet : 1 ≤ rjet)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (hsE : ρ / e ≤ ocEpsilon q Λ (m - 1) / e)
    (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hscale : (ρ / e) * ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hδ : e / E = ζ * ϖ) (hn : K v ≤ Jchart + 1)
    (timeScale a b : ℝ) (htime : ∀ t ∈ Set.Icc a b, timeScale * t ∈ W)
    (N : ℕ) (hN : N ≤ Jchart) (hKN : K v + (F.identity v u γ).maxOrder ≤ N)
    (hcellE : 0 < ocEpsilon q Λ (m - 1))
    (yc : Vec 2) (μ : Measure ℝ) (A : U →L[ℝ] V) :
    let B := fun d I τ z k => naturalSlowRemainderTimeCoefficient Ks
      (fun t X y => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * t) X y k)
      a b hφ r (fun _ => σ) e E yc τ z
    ∃ T : PlaneTimeAllMomentCarrier (E := U) (L + 1) ϖ (ρ / e) 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => V)) (K v) ϖ (ρ / e) 0 μ,
    IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 μ
      (fun x τ z => nativeArrayAssembly rjet A
        (fun k I => F.weight p (timeScale * τ) * transportedCoeff
          (fun y => naturalPreparationJacobian hφ r σ (yc + e • y))
          (F.identity v u γ).maxOrder (fun d I => B d I τ z) rjet I z k)
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (L + 1) ϖ (ρ / e) 0 μ x τ) rjet I z))) T := by
  classical
  let B := fun (d : ℕ) (I : DerivativeWord2 (d - 1)) (τ : ℝ) (z : Vec 2) (k : Fin 2) =>
    naturalSlowRemainderTimeCoefficient Ks
      (fun t X y => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * t) X y k)
      a b hφ r (fun _ => σ) e E yc τ z
  have hreg d I k := inactiveTimeZeroFamily_natural_remainder_time_regularity F hw hm W E e
    hE.ne' he.ne' (fun v => K v + J) henv.1 Ks (K v) p c v u γ d I k (by omega)
    timeScale a b htime hφ r σ yc
  have hex (d : ℕ) (I : DerivativeWord2 (d - 1)) : ∃ MB : ℝ, 0 ≤ MB ∧
      (d ∈ Finset.Icc (rjet + 1) (F.identity v u γ).maxOrder → ∀ τ k j, j ≤ K v → ∀ z,
        (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (fun y => B d I τ y k) z‖ ≤
          MB * polynomialMomentRoot ϖ z ^ (Ks + 1)) := by
    by_cases hd : d ∈ Finset.Icc (rjet + 1) (F.identity v u γ).maxOrder
    · have hd0 : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder := by
        simp only [Finset.mem_Icc] at hd ⊢
        omega
      obtain ⟨CR, hCR, hb⟩ := inactiveTimeZeroFamily_natural_time_remainder_uniform_jet_budget
        (α := α) (q := q) (Λ := Λ) (m := m) (φ := φ) (hφ := hφ)
        (tS := tS) (tZ := tZ) (Cpad := Cpad) (Cage := Cage)
        (Jchart := Jchart) (Cchart := Cchart) Ks F π hπ K Kmax hK W ν e E ρ hν he hE hρ
        C J b₀ henv v u γ hγ d hd0 I hKs p c
      let Dchart := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
      let price := (Kmax.factorial : ℝ) ^ 2 * E ^ (Ks + 1) *
        molecularRealPrice ν ρ (K v) (d - 2)
          (pointwiseMolecularJet ρ e (K v) (Ks + 1)
            (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) /
              derivativeReserveFactor (ρ / e) (K v) (d - 2)
      let MB := ((K v).factorial : ℝ) * Dchart ^ K v *
        ((K v + 1 : ℕ) * (CR * price * ζ ^ (Ks + 1))) * (3 + max (Cchart 0) 0) ^ (Ks + 1)
      have hM := molecularRealPrice_nonneg ν ρ hν.le hρ.le (K v) (d - 2)
        (pointwiseMolecularJet ρ e (K v) (Ks + 1)
          (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
      refine ⟨MB, ?_, ?_⟩
      · dsimp only [MB, price, Dchart]
        unfold derivativeReserveFactor
        positivity
      · intro _ τ k j hj z
        exact hb hc ha r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn timeScale a b htime
          τ yc z k j hj
    · exact ⟨0, le_rfl, fun hh => (hd hh).elim⟩
  choose MB hMB hBj using hex
  exact exists_preparationTransportedPolynomial_weighted_allMoment_map hKL hrjet hc ha hcellE
    r σ hr hσ (by simpa only [abs_sub_comm] using hage) N (F.identity v u γ).maxOrder hN hKN
    e (ρ / e) ϖ he (div_pos hρ he) hϖ hsE yc μ B
    (fun d I k z => (hreg d I k).1 z) (fun d I k τ => (hreg d I k).2 τ)
    MB hMB (Ks + 1) (fun d hd I k τ j hj z => hBj d I hd τ k j hj z) A
    (fun τ => F.weight p (timeScale * τ)) ((hw p).comp (measurable_const.mul measurable_id))
    (fun τ => family_weight_abs_le_one F p (timeScale * τ))

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVenhance AVRegularity.ChartTransport AVRegularity.CycleWords AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Inactive-time natural remainders retain the original output-window constituent price. -/

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem familyNaturalRemainder_transported_allMoment_density
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (hw : ∀ p, Measurable (F.weight p)) (hm : F.IsTimeMeasurable)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (W : Set ℝ)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W) ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (hKs : Ks + 1 ≤ J) (p : P) (c : Ctx p)
    {L rjet : ℕ} (hKL : K v + rjet ≤ L + 1) (hrjet : 1 ≤ rjet)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (hsE : ρ / e ≤ ocEpsilon q Λ (m - 1) / e)
    (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hscale : (ρ / e) * ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hδ : e / E = ζ * ϖ) (hn : K v ≤ Jchart + 1)
    (timeScale a b : ℝ) (htime : ∀ t ∈ Set.Icc a b, timeScale * t ∈ W)
    (N : ℕ) (hN : N ≤ Jchart) (hKN : K v + (F.identity v u γ).maxOrder ≤ N)
    (hcellE : 0 < ocEpsilon q Λ (m - 1))
    (yc : Vec 2) (μ : Measure ℝ) (A : U →L[ℝ] V) :
    let B := fun d I τ z k => naturalSlowRemainderTimeCoefficient Ks
      (fun t X y => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * t) X y k)
      a b hφ r (fun _ => σ) e E yc τ z
    ∀ T : PlaneTimeAllMomentCarrier (E := U) (L + 1) ϖ (ρ / e) 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => V)) (K v) ϖ (ρ / e) 0 μ,
    IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 μ
      (fun x τ z => nativeArrayAssembly rjet A
        (fun k I => F.weight p (timeScale * τ) * transportedCoeff
          (fun y => naturalPreparationJacobian hφ r σ (yc + e • y))
          (F.identity v u γ).maxOrder (fun d I => B d I τ z) rjet I z k)
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (L + 1) ϖ (ρ / e) 0 μ x τ) rjet I z))) T → ∀ x : PlaneTimeAllMomentCarrier (E := U) (L + 1) ϖ (ρ / e) 0 μ,
    let Num := fun d I => naturalRemainderChartPrice Ks Kmax Jchart Cchart * ζ ^ (Ks + 1) *
      ((Kmax.factorial : ℝ) ^ 2 * E ^ (Ks + 1) * molecularRealPrice ν ρ (K v) (d - 2)
        (pointwiseMolecularJet ρ e (K v) (Ks + 1)
          (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)))
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow N * Cflow
    let Scale := transportedPolynomialUniformReservePrice N D (K v) Cpiola *
      (∑ d ∈ Finset.Icc (rjet + 1) (F.identity v u γ).maxOrder,
        ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2, Num d I)
    ∀ᵐ τ ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity (ρ / e)
        (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ (T x) τ) z ≤
      F.weight p (timeScale * τ) ^ 2 *
        ((∑ _β : Fin 2 × DerivativeWord2 rjet,
          Real.sqrt (multiplicationDensityBudget (K v)) * (Scale * ‖A‖)) ^ 2 *
          ((polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 *
            planeGradFactorialDensity (ρ / e)
              (planeTimeAllMomentCarrierToLp (L + 1) ϖ (ρ / e) 0 μ x τ) z)) := by
  dsimp only
  intro T hT x
  let B := fun (d : ℕ) (I : DerivativeWord2 (d - 1)) (τ : ℝ) (z : Vec 2) (k : Fin 2) =>
    naturalSlowRemainderTimeCoefficient Ks
      (fun t X y => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * t) X y k)
      a b hφ r (fun _ => σ) e E yc τ z
  let Num := fun (d : ℕ) (I : DerivativeWord2 (d - 1)) =>
    naturalRemainderChartPrice Ks Kmax Jchart Cchart * ζ ^ (Ks + 1) *
      ((Kmax.factorial : ℝ) ^ 2 * E ^ (Ks + 1) * molecularRealPrice ν ρ (K v) (d - 2)
        (pointwiseMolecularJet ρ e (K v) (Ks + 1)
          (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)))
  let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
  let Cpiola := compConst Cflow N * Cflow
  let Scale := transportedPolynomialUniformReservePrice N D (K v) Cpiola *
    (∑ d ∈ Finset.Icc (rjet + 1) (F.identity v u γ).maxOrder,
      ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2, Num d I)
  let Jac := fun y => naturalPreparationJacobian hφ r σ (yc + e • y)
  let coeff := fun k I τ z => transportedCoeff Jac (F.identity v u γ).maxOrder
    (fun d I => B d I τ z) rjet I z k
  have hreg d I i := inactiveTimeZeroFamily_natural_remainder_time_regularity F hw hm W E e
    hE.ne' he.ne' (fun v => K v + J) henv.1 Ks (K v) p c v u γ d I i (by omega)
    timeScale a b htime hφ r σ yc
  have hcm k I z : Measurable (fun τ => coeff k I τ z) := by
    dsimp only [coeff]
    unfold transportedCoeff
    apply Finset.measurable_fun_sum
    intro d _
    apply Finset.measurable_fun_sum
    intro A _
    apply Finset.measurable_fun_sum
    intro i _
    exact (((hreg d A i).1 z).const_mul _).mul_const _
  have hJac i l : ContDiff ℝ (⊤ : ℕ∞) (fun y => Jac y i l) :=
    ((naturalPreparationJacobian_entry_smooth hφ r i l).comp
      (contDiff_const.prodMk contDiff_id)).comp
        (contDiff_const.add (contDiff_id.const_smul e))
  have hcs k I τ : ContDiff ℝ (K v : ℕ) (coeff k I τ) :=
    transportedCoeff_spatial_smooth Jac hJac (F.identity v u γ).maxOrder (K v)
      (fun d I z => B d I τ z) (fun d I i => (hreg d I i).2 τ) rjet I k
  have hCf : 1 ≤ Cflow := one_le_jetConst _ _
  have hCp : 0 ≤ Cpiola := mul_nonneg (compConst_nonneg hCf N) (zero_le_one.trans hCf)
  have hNum d I : 0 ≤ Num d I := by
    have hnat := naturalRemainderChartPrice_nonneg Ks Kmax Jchart Cchart
    have hM := molecularRealPrice_nonneg ν ρ hν.le hρ.le (K v) (d - 2)
      (pointwiseMolecularJet ρ e (K v) (Ks + 1)
        (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
    dsimp only [Num]
    positivity
  have hScale : 0 ≤ Scale := mul_nonneg
    (transportedPolynomialUniformReservePrice_nonneg N D (K v) Cpiola hCp)
    (Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun I _ =>
      Finset.sum_nonneg (fun _ _ => hNum d I))))
  have hRes : 0 < derivativeReserveFactor (ρ / e) (K v) (rjet - 1) := by
    unfold derivativeReserveFactor
    positivity
  have hcb k I : ∀ᵐ τ ∂μ, ∀ j ≤ K v, ∀ z,
      (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (coeff k I τ) z‖ ≤
        (Scale / derivativeReserveFactor (ρ / e) (K v) (rjet - 1)) *
          polynomialMomentRoot ϖ z ^ (Ks + 1) := by
    apply Filter.Eventually.of_forall
    intro τ j hj z
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hRes).mpr
    exact familyNaturalRemainder_transported_reserved_jet_budget Ks F hw hm π hπ K Kmax hK
      W ν e E ρ hν he hE hρ C J b₀ henv v u γ hγ hKs p c rjet hrjet hc ha r σ hr hσ hage
      hsE ϖ ζ hϖ hscale hζ hδ hn timeScale a b htime N hN hKN hcellE yc τ j hj I k z
  have hdens := planeWeightedNativeArrayPolynomial_allMoment_density hKL hrjet (Ks + 1)
    ϖ (ρ / e) hϖ (div_pos hρ he) μ coeff hcm hcs A
    (fun _ _ => Scale / derivativeReserveFactor (ρ / e) (K v) (rjet - 1))
    (fun _ _ => div_nonneg hScale hRes.le) hcb (fun τ => F.weight p (timeScale * τ))
    ((hw p).comp (measurable_const.mul measurable_id))
    (fun τ => family_weight_abs_le_one F p (timeScale * τ)) T hT x
  simpa only [div_mul_cancel₀ Scale hRes.ne'] using hdens

end AVRegularity.CycleJointProofs
end

section
open Set MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleJointProofs

/-! Genuine scalar estimates close finite weighted lift energy by triangular depth induction. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Static polynomial weights give finite geometry energy without an auxiliary chart premise. -/
theorem triangular_static_polynomial_geometry_energy_lt_top
    (a b : ℝ) (hab : a ≤ b) (K : ι → ℕ) (D : ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (ϖ : ℝ) (zc : Vec 2) (m : ℕ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm r (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane 1 a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w)
    (rank : ι → ℕ) (hz : ∀ i i', ¬ rank i' < rank i → ∀ d t x, A i i' d t x = 0)
    (hf : ∀ i, weightedFactorialNormSq m ϖ zc r (K i) (f i) ≠ ⊤) (π : ι → ℝ) :
    geometryEnergyNorm π K m ϖ zc r a b u w < ⊤ := by
  let S := b - a + 1
  have hS : 0 < S := by dsimp [S]; linarith
  let Cw := staticPolynomialChartConstant S ϖ V
  let C := staticPolynomialChartWeights v a S ϖ V zc m hS hV (fun t _ x => hbv t x)
  obtain ⟨L, hL, hreserve⟩ := exists_scalar_square_reserve (Real.exp (18 * Cw m))
    (Real.exp_pos _).le
  exact triangular_weighted_geometry_energy_lt_top a b hab K D Kmax hK
    v hvm hv V strain B lam hV ha hB hlam (fun t _ x => hbv t x) hjets
    a S ϖ zc m m Cw C le_rfl r L hr hL hsmall hstrainSmall hreserve hdiv le_rfl
    (by dsimp [S]; linarith) hr1 A hA hc hAm f u w hs rank hz hf π
end

/-! Genuine scalar estimates close finite weighted lift energy by triangular depth induction. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Finite smooth drift prices and initial moments imply finite geometry energy at any positive radius. -/
theorem triangular_bounded_drift_geometry_energy_lt_top
    (a b : ℝ) (hab : a ≤ b) (K : ι → ℕ) (D : ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V M : ℝ) (hV : 0 ≤ V) (hM : 0 ≤ M)
    (hbv : ∀ t x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        M * (l.factorial : ℝ))
    (ϖ : ℝ) (zc : Vec 2) (m : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane 1 a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w)
    (rank : ι → ℕ) (hz : ∀ i i', ¬ rank i' < rank i → ∀ d t x, A i i' d t x = 0)
    (hf : ∀ i, weightedFactorialNormSq m ϖ zc ρ (K i) (f i) ≠ ⊤) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) :
    geometryEnergyNorm π K m ϖ zc ρ a b u w < ⊤ := by
  obtain ⟨r, hr, hrρ, hrhalf, hrsmall⟩ := exists_auxiliary_absorption_radius ρ 1 M hρ zero_lt_one hM
  have hAr (i i' : ι) (d : admissibleOrders K D i i') :=
    coefficientSeminorm_radius_ne_top r ρ hr.le hrρ (K i) a b (A i i' d) (hA i i' d)
  have hfr (i : ι) : weightedFactorialNormSq m ϖ zc r (K i) (f i) ≠ ⊤ :=
    ne_top_of_le_ne_top (hf i) (weightedFactorialNormSq_radius_mono m ϖ zc hr.le hrρ _ _)
  have he := triangular_static_polynomial_geometry_energy_lt_top a b hab K D Kmax hK
    v hvm hv V M 1 1 hV hM (le_refl 1) zero_lt_one hbv
    (by simpa only [one_pow, one_zpow, mul_one] using hjets)
    ϖ zc m r hr (hrhalf.trans (by norm_num)) (by simpa using hrhalf)
    (by simpa using hrsmall) hdiv A hAr hc hAm f u w hs rank hz hfr π
  exact geometryEnergyNorm_lt_top_of_radius_transfer π hπ K m ϖ zc r ρ a b hr hρ u w he
end

end AVRegularity.CycleJointProofs
end

section
open Set MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Positive metric Taylor insertions followed by the genuine scalar response have a uniform original-mass gradient bound. -/

theorem planeComponentAllMomentResponse_metric_insertion_gradient_budget_uniform
    (Ks Kmax : ℕ) (Cjet : ℕ → ℝ) (hCjet : ∀ r, 0 ≤ Cjet r) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ {ι : Type*} [Fintype ι] {E : ι → Type*}
      [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
      [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
      [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)], ∀
    (a b : ℝ) (_hab : a ≤ b) (K : ι → ℕ) (_hK : ∀ i, K i ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (_hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (_hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (_hV : 0 ≤ V) (_ha : 0 ≤ strain) (_hB : 1 ≤ B) (_hlam : 0 < lam)
    (_hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (_hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (_hMm : Measurable M)
    (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
    (_hnear : IsMetricNearIdentity (fun t _ => M t) g)
    (_hsym : ∀ t ∈ Icc a b, (M t).IsSymm)
    (t₀ S ϖ : ℝ) (N m : ℕ) (Cw : ℕ → ℝ)
    (_C : ChartWeights (fun t _ => M t) v t₀ S ϖ 0 N Cw) (_hm : m ≤ N)
    (ρ L : ℝ) (_hρ : 0 < ρ) (_hL : 1 ≤ L)
    (_hsmall : B * ρ / lam ≤ 1 / 2)
    (_hstrainSmall : strain * B * ρ ^ 2 ≤ 1 / 8)
    (_hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 16)
    (_hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (_hwa : t₀ ≤ a) (_hwb : b ≤ t₀ + S)
    (π : ι → ℝ) (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
      (volume.restrict (Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 (volume.restrict (Icc a b)))
    (_hR : ∀ i, IsPlaneComponentAllMomentResponse (E := E i) M v (K i) a b ϖ ρ (R i))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (δ ζ gm : ℝ)
    (_hGm : ∀ X k l, Measurable (fun t => G t X k l))
    (_hGs : ∀ t ∈ Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l))
    (_hϖ : 0 < ϖ) (_hscale : ρ * ϖ ≤ 1) (_hζ : 0 ≤ ζ) (_hζ1 : ζ ≤ 1)
    (_hgm : 0 ≤ gm) (_hδ : δ = ζ * ϖ)
    (_hGjet : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
      ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ Cjet r * gm * δ ^ r)
    (T : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
      (volume.restrict (Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Icc a b)))
    (_hT : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Icc a b))
      (fun x t => planeMatrixGradientFlux
        (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (E := E i) (K i + 1) ϖ ρ 0
          (volume.restrict (Icc a b)) x t)) (T i))
    (W : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
      (volume.restrict (Icc a b))),
    planeAllMomentFamilyGradientEnergy (E := E) K m ϖ ρ (volume.restrict (Icc a b)) π
      (nativeDiagonalResponseOperator R T W) ≤
      ENNReal.ofReal (L ^ (2 * Kmax)) * 3 *
        (ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
          ENNReal.ofReal (3 * Real.exp (18 * Cw m))) *
        (16 * (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CT * gm * ζ) ^ 2) *
          planeAllMomentFamilyGradientEnergy (E := E) K (m + Ks) ϖ ρ
            (volume.restrict (Icc a b)) π W)) := by
  obtain ⟨CT, hCT, hmetric⟩ := metricTaylor_family_map_mass_moment_budget_uniform Ks Kmax Cjet hCjet
  refine ⟨CT, hCT, ?_⟩
  intro ι _ E _ _ _ _ _ _ a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
    M hMm g hg hg4 hnear hsym t₀ S ϖ N m Cw C hm ρ L hρ hL hsmall hstrainSmall
    hreserve hdiv hwa hwb π R hR G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet T hT W
  have he := planeComponentAllMomentResponse_family_gradient_budget a b hab K Kmax hK
    v hvm hv V strain B lam hV ha hB hlam hbv hjets M hMm g hg hg4 hnear hsym
    t₀ S ϖ N m Cw C hm ρ L hρ hL hsmall hstrainSmall hreserve hdiv hwa hwb π R hR
    (fun i => T i (W i))
  have ht := hmetric K hK G a b ϖ ρ δ ζ gm hGm hGs hϖ hρ hscale hζ hζ1 hgm hδ
    hGjet π T hT W m
  exact he.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht zero_le) zero_le)

end AVRegularity.CycleJointProofs
end

section
open Set MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleJointProofs

/-! Genuine scalar estimates close finite weighted lift energy by triangular depth induction. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Positive-viscosity triangular physical solutions retain finite polynomial geometry energy. -/
theorem physical_triangular_geometry_energy_lt_top
    (a b ν : ℝ) (hab : a ≤ b) (hν : 0 < ν) (K : ι → ℕ) (D : ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V M : ℝ) (hV : 0 ≤ V) (hM : 0 ≤ M)
    (hbv : ∀ t x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        M * (l.factorial : ℝ))
    (ϖ : ℝ) (zc : Vec 2) (m : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w)
    (rank : ι → ℕ) (hz : ∀ i i', ¬ rank i' < rank i → ∀ d t x, A i i' d t x = 0)
    (hf : ∀ i, weightedFactorialNormSq m ϖ zc ρ (K i) (f i) ≠ ⊤) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) :
    geometryEnergyNorm π K m ϖ zc ρ a b u w < ⊤ := by
  let vN := timeNormalizedVelocity ν v
  let AN := fun i i' (d : admissibleOrders K D i i') t x => ν⁻¹ • A i i' d (ν⁻¹ * t) x
  let uN := fun i t => u i (ν⁻¹ * t)
  let wN := fun i t => w i (ν⁻¹ * t)
  have habN : ν * a ≤ ν * b := mul_le_mul_of_nonneg_left hab hν.le
  have htime (t : ℝ) (ht : t ∈ Set.Icc (ν * a) (ν * b)) := inv_mul_mem_Icc_of_scaled hν ht
  let T (p : Set.Icc (ν * a) (ν * b) × Vec 2) : Set.Icc a b × Vec 2 :=
    (⟨ν⁻¹ * p.1, htime _ p.1.property⟩, p.2)
  have hT : Measurable T :=
    (((measurable_const (a := ν⁻¹)).mul
      (measurable_subtype_coe.comp measurable_fst)).subtype_mk).prodMk
      measurable_snd
  have hvmN : Measurable (fun p : Set.Icc (ν * a) (ν * b) × Vec 2 => vN p.1 p.2) :=
    (measurable_const (a := ν⁻¹)).smul (hvm.comp hT)
  have hvN (t : ℝ) (ht : t ∈ Set.Icc (ν * a) (ν * b)) :
      ContDiff ℝ (⊤ : ℕ∞) (vN t) := timeNormalizedVelocity_contDiff ν v t _ (hv _ (htime t ht))
  have hbN (t : ℝ) (x : Vec 2) : ‖vN t x‖ ≤ ν⁻¹ * V :=
    timeNormalizedVelocity_norm_le hν v t (hbv _) x
  have hjN : ∀ t ∈ Set.Icc (ν * a) (ν * b), ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (vN t)) l x‖ ≤
        (ν⁻¹ * M) * (l.factorial : ℝ) := by
    intro t ht l hl hlK x
    have hh := timeNormalizedVelocity_coefficientArray_norm_le hν v t l x
      (hjets _ (htime t ht) l hl hlK x)
    simpa only [mul_assoc] using hh
  have hdN : ∀ t ∈ Icc (ν * a) (ν * b), ∀ x,
      ∑ k : Fin 2, fderiv ℝ (vN t) x (basisVec k) k = 0 := by
    intro t ht x
    exact timeNormalizedVelocity_divergence_zero ν v t
      ((hv _ (htime t ht)).of_le (by simp)) (hdiv _ (htime t ht)) x
  have hAN i i' d := coefficientSeminorm_diffusion_normalized_ne_top ρ hρ (K i) a b ν hν
    (A i i' d) (hA i i' d)
  have hcN : ∀ i i' d t, t ∈ Set.Icc (ν * a) (ν * b) → ContDiff ℝ (K i : ℕ) (AN i i' d t) := by
    intro i i' d t ht
    exact (hc i i' d _ (htime t ht)).const_smul ν⁻¹
  have hAmN i i' d := diffusionNormalizedCoefficient_joint_measurable hν (A i i' d) (hAm i i' d)
  have hzN : ∀ i i', ¬ rank i' < rank i → ∀ d t x, AN i i' d t x = 0 := by
    intro i i' hnot d t x
    dsimp only [AN]
    rw [hz i i' hnot d (ν⁻¹ * t) x]
    apply ContinuousLinearMap.ext
    intro z
    apply PiLp.ext
    intro k
    change ν⁻¹ • (0 : h i) = 0
    exact smul_zero (ν⁻¹ : ℝ)
  have hsN := planeHomogeneous_diffusion_time_solution K D hν v A f u w hs
  have he := triangular_bounded_drift_geometry_energy_lt_top (ν * a) (ν * b) habN K D Kmax hK
    vN hvmN hvN (ν⁻¹ * V) (ν⁻¹ * M)
    (mul_nonneg (inv_nonneg.mpr hν.le) hV) (mul_nonneg (inv_nonneg.mpr hν.le) hM)
    hbN hjN ϖ zc m ρ hρ hdN AN hAN hcN hAmN f uN wN hsN rank hzN hf π hπ
  exact geometryEnergyNorm_lt_top_of_time_dilation π hπ K m ϖ zc ρ a b ν hν u w he

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVenhance AVRegularity.ChartTransport AVRegularity.CycleWords AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Inactive-time natural remainders retain the original output-window constituent price. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem familyNaturalRemainder_identity_allMoment_density
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (hw : ∀ p, Measurable (F.weight p)) (hm : F.IsTimeMeasurable)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (W : Set ℝ)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W) ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (hKs : Ks + 1 ≤ J) (p : P) (c : Ctx p)
    {L rjet : ℕ} (hKL : K v + rjet ≤ L + 1) (hrjet : 1 ≤ rjet) (hrD : rjet ≤ D)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (hsE : ρ / e ≤ ocEpsilon q Λ (m - 1) / e)
    (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hscale : (ρ / e) * ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hδ : e / E = ζ * ϖ) (hn : K v ≤ Jchart + 1)
    (timeScale a b : ℝ) (htime : ∀ t ∈ Set.Icc a b, timeScale * t ∈ W)
    (N : ℕ) (hN : N ≤ Jchart) (hKN : K v + (F.identity v u γ).maxOrder ≤ N)
    (hcellE : 0 < ocEpsilon q Λ (m - 1))
    (yc : Vec 2) (μ : Measure ℝ) :
    let B := fun d I τ z k => naturalSlowRemainderTimeCoefficient Ks
      (fun t X y => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * t) X y k)
      a b hφ r (fun _ => σ) e E yc τ z
    ∀ T : PlaneTimeAllMomentCarrier (E := h u) (L + 1) ϖ (ρ / e) 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 μ,
    IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 μ
      (fun x τ z => nativeArrayAssembly rjet (F.identity v u γ).map
        (fun k I => F.weight p (timeScale * τ) * transportedCoeff
          (fun y => naturalPreparationJacobian hφ r σ (yc + e • y))
          (F.identity v u γ).maxOrder (fun d I => B d I τ z) rjet I z k)
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (L + 1) ϖ (ρ / e) 0 μ x τ) rjet I z))) T → ∀ x : PlaneTimeAllMomentCarrier (E := h u) (L + 1) ϖ (ρ / e) 0 μ,
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow N * Cflow
    let CR := nativeArrayUniformTransportPrice N D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    ∀ᵐ τ ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity (ρ / e)
        (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ (T x) τ) z ≤
      F.weight p (timeScale * τ) ^ 2 *
        (pointwiseOriginalIdentityRemainderPrice F K Ks Kmax
          (ChartedFamily.Domain.onWindow F W) ν e E ρ CR ζ v u γ ^ 2 *
          ((polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 *
            planeGradFactorialDensity (ρ / e)
              (planeTimeAllMomentCarrierToLp (L + 1) ϖ (ρ / e) 0 μ x τ) z)) := by
  dsimp only
  intro T hT x
  have hdens := familyNaturalRemainder_transported_allMoment_density Ks F hw hm π hπ K Kmax hK
    W ν e E ρ hν he hE hρ C J b₀ henv v u γ hγ hKs p c hKL hrjet hc ha r σ hr hσ hage
    hsE ϖ ζ hϖ hscale hζ hδ hn timeScale a b htime N hN hKN hcellE yc μ
    (F.identity v u γ).map T hT x
  let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
  let Cpiola := compConst Cflow N * Cflow
  have hCf : 1 ≤ Cflow := one_le_jetConst _ _
  have hCp : 0 ≤ Cpiola := mul_nonneg (compConst_nonneg hCf N) (zero_le_one.trans hCf)
  have hnat := naturalRemainderChartPrice_nonneg Ks Kmax Jchart Cchart
  have hprice := nativeArray_pointwise_identity_remainder_price_le F K Ks Kmax hK
    (ChartedFamily.Domain.onWindow F W) ν e E ρ
    (naturalRemainderChartPrice Ks Kmax Jchart Cchart) ζ hν.le hE.le hρ.le hnat hζ
    N Cpiola hCp v u γ rjet hrjet hrD
  have hprice0 : 0 ≤ (∑ _β : Fin 2 × DerivativeWord2 rjet,
      Real.sqrt (multiplicationDensityBudget (K v)) *
        (transportedPolynomialUniformReservePrice N D (K v) Cpiola *
          (∑ d ∈ Finset.Icc (rjet + 1) (F.identity v u γ).maxOrder,
            ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
              naturalRemainderChartPrice Ks Kmax Jchart Cchart * ζ ^ (Ks + 1) *
                ((Kmax.factorial : ℝ) ^ 2 * E ^ (Ks + 1) * molecularRealPrice ν ρ (K v) (d - 2)
                  (pointwiseMolecularJet ρ e (K v) (Ks + 1)
                    (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
                    (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)))) * ‖(F.identity v u γ).map‖)) := by
    have hp := transportedPolynomialUniformReservePrice_nonneg N D (K v) Cpiola hCp
    unfold molecularRealPrice
    positivity
  dsimp only at hdens ⊢
  filter_upwards [hdens] with τ hτ
  filter_upwards [hτ] with z hz
  apply hz.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _
    (mul_nonneg (sq_nonneg _) (planeGradFactorialDensity_nonneg _ _ _))
  exact pow_le_pow_left₀ hprice0 hprice 2
end

/-! Inactive-time natural remainders retain the original output-window constituent price. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem exists_originalFamilyNaturalRemainder_identity_density_map
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (hw : ∀ p, Measurable (F.weight p)) (hm : F.IsTimeMeasurable)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (W : Set ℝ)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W) ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (hKs : Ks + 1 ≤ J) (p : P) (c : Ctx p)
    {L rjet : ℕ} (hKL : K v + rjet ≤ L + 1) (hrjet : 1 ≤ rjet) (hrD : rjet ≤ D)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (hsE : ρ / e ≤ ocEpsilon q Λ (m - 1) / e)
    (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hscale : (ρ / e) * ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hδ : e / E = ζ * ϖ) (hn : K v ≤ Jchart + 1)
    (timeScale a b : ℝ) (htime : ∀ t ∈ Set.Icc a b, timeScale * t ∈ W)
    (N : ℕ) (hN : N ≤ Jchart) (hKN : K v + (F.identity v u γ).maxOrder ≤ N)
    (hcellE : 0 < ocEpsilon q Λ (m - 1))
    (yc : Vec 2) (μ : Measure ℝ) :
    let B := fun d I τ z k => naturalSlowRemainderTimeCoefficient Ks
      (fun t X y => F.flux p c v u γ d I (timeScale * t) X y k)
      a b hφ r (fun _ => σ) e E yc τ z
    ∃ T : PlaneTimeAllMomentCarrier (E := h u) (L + 1) ϖ (ρ / e) 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 μ,
    IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 μ
      (fun x τ z => nativeArrayAssembly rjet (F.identity v u γ).map
        (fun k I => F.weight p (timeScale * τ) * transportedCoeff
          (fun y => naturalPreparationJacobian hφ r σ (yc + e • y))
          (F.identity v u γ).maxOrder (fun d I => B d I τ z) rjet I z k)
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (L + 1) ϖ (ρ / e) 0 μ x τ) rjet I z))) T ∧ ∀ x : PlaneTimeAllMomentCarrier (E := h u) (L + 1) ϖ (ρ / e) 0 μ,
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow N * Cflow
    let CR := nativeArrayUniformTransportPrice N D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    ∀ᵐ τ ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity (ρ / e)
        (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ (T x) τ) z ≤
      F.weight p (timeScale * τ) ^ 2 *
        (pointwiseOriginalIdentityRemainderPrice F K Ks Kmax
          (ChartedFamily.Domain.onWindow F W) ν e E ρ CR ζ v u γ ^ 2 *
          ((polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 *
            planeGradFactorialDensity (ρ / e)
              (planeTimeAllMomentCarrierToLp (L + 1) ϖ (ρ / e) 0 μ x τ) z)) := by
  dsimp only
  obtain ⟨T, hT⟩ := exists_familyNaturalRemainder_transported_allMoment_map Ks F hw hm π hπ K
    Kmax hK W ν e E ρ hν he hE hρ C J b₀ henv v u γ hγ hKs p c hKL hrjet hc ha
    r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn timeScale a b htime N hN hKN hcellE yc μ
    (F.identity v u γ).map
  refine ⟨T, ?_, ?_⟩
  · intro x
    filter_upwards [hT x] with τ hτ
    filter_upwards [hτ] with z hz
    rw [hz, familyNaturalRemainder_native_array_weight_eq]
  · exact familyNaturalRemainder_identity_allMoment_density Ks F hw hm π hπ K Kmax hK
      W ν e E ρ hν he hE hρ C J b₀ henv v u γ hγ hKs p c hKL hrjet hrD hc ha
      r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn timeScale a b htime N hN hKN hcellE yc μ
      T hT
end

/-! Inactive-time natural remainders retain the original output-window constituent price. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem exists_originalFamilyNaturalRemainder_identity_density_map_including_zero
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (hw : ∀ p, Measurable (F.weight p)) (hm : F.IsTimeMeasurable)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (W : Set ℝ)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W) ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hKs : Ks + 1 ≤ J) (p : P) (c : Ctx p)
    {L rjet : ℕ} (hKL : K v + rjet ≤ L + 1) (hrjet : 1 ≤ rjet) (hrD : rjet ≤ D)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (hsE : ρ / e ≤ ocEpsilon q Λ (m - 1) / e)
    (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hscale : (ρ / e) * ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hδ : e / E = ζ * ϖ) (hn : K v ≤ Jchart + 1)
    (timeScale a b : ℝ) (htime : ∀ t ∈ Set.Icc a b, timeScale * t ∈ W)
    (N : ℕ) (hN : N ≤ Jchart) (hKN : K v + (F.identity v u γ).maxOrder ≤ N)
    (hcellE : 0 < ocEpsilon q Λ (m - 1))
    (yc : Vec 2) (μ : Measure ℝ) :
    let B := fun d I τ z k => naturalSlowRemainderTimeCoefficient Ks
      (fun t X y => F.flux p c v u γ d I (timeScale * t) X y k)
      a b hφ r (fun _ => σ) e E yc τ z
    ∃ T : PlaneTimeAllMomentCarrier (E := h u) (L + 1) ϖ (ρ / e) 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 μ,
    IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 μ
      (fun x τ z => nativeArrayAssembly rjet (F.identity v u γ).map
        (fun k I => F.weight p (timeScale * τ) * transportedCoeff
          (fun y => naturalPreparationJacobian hφ r σ (yc + e • y))
          (F.identity v u γ).maxOrder (fun d I => B d I τ z) rjet I z k)
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (L + 1) ϖ (ρ / e) 0 μ x τ) rjet I z))) T ∧ ∀ x : PlaneTimeAllMomentCarrier (E := h u) (L + 1) ϖ (ρ / e) 0 μ,
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow N * Cflow
    let CR := nativeArrayUniformTransportPrice N D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    ∀ᵐ τ ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity (ρ / e)
        (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ (T x) τ) z ≤
      F.weight p (timeScale * τ) ^ 2 *
        (pointwiseOriginalIdentityRemainderPrice F K Ks Kmax
          (ChartedFamily.Domain.onWindow F W) ν e E ρ CR ζ v u γ ^ 2 *
          ((polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 *
            planeGradFactorialDensity (ρ / e)
              (planeTimeAllMomentCarrierToLp (L + 1) ϖ (ρ / e) 0 μ x τ) z)) := by
  dsimp only
  classical
  by_cases hγ : (F.identity v u γ).map = 0
  · refine ⟨0, ?_, ?_⟩
    · apply planeRaw_allMoment_zero_map
      intro x τ z
      rw [hγ, nativeArrayAssembly_zero_component_map]
      simp only [zero_apply]
    · intro x
      simp only [LinearMap.zero_apply]
      filter_upwards [planeTimeAllMomentCarrier_zero_representative
        (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 μ 0 rfl] with τ hτ
      rw [hτ]
      filter_upwards [planeFactorialDensity_zero_ae
        (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) (ρ / e)] with z hz
      rw [hz]
      exact mul_nonneg (sq_nonneg _)
        (mul_nonneg (sq_nonneg _)
          (mul_nonneg (sq_nonneg _) (planeGradFactorialDensity_nonneg _ _ _)))
  · exact exists_originalFamilyNaturalRemainder_identity_density_map Ks F hw hm π hπ K Kmax hK
      W ν e E ρ hν he hE hρ C J b₀ henv v u γ hγ hKs p c hKL hrjet hrD hc ha
      r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn timeScale a b htime N hN hKN hcellE yc μ
end

/-! Inactive-time natural remainders retain the original output-window constituent price. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem exists_originalFamilyNaturalRemainder_descending_identity_density_map
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (hw : ∀ p, Measurable (F.weight p)) (hm : F.IsTimeMeasurable)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (W : Set ℝ)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W) ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hKs : Ks + 1 ≤ J) (p : P) (c : Ctx p)
    {rjet : ℕ} (hdesc : F.IsDescending K) (hrjet : 1 ≤ rjet) (hrD : rjet ≤ D)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (hsE : ρ / e ≤ ocEpsilon q Λ (m - 1) / e)
    (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hscale : (ρ / e) * ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hδ : e / E = ζ * ϖ) (hn : K v ≤ Jchart + 1)
    (timeScale a b : ℝ) (htime : ∀ t ∈ Set.Icc a b, timeScale * t ∈ W)
    (N : ℕ) (hN : N ≤ Jchart) (hKN : K v + (F.identity v u γ).maxOrder ≤ N)
    (hcellE : 0 < ocEpsilon q Λ (m - 1))
    (yc : Vec 2) (μ : Measure ℝ) :
    let B := fun d I τ z k => naturalSlowRemainderTimeCoefficient Ks
      (fun t X y => F.flux p c v u γ d I (timeScale * t) X y k)
      a b hφ r (fun _ => σ) e E yc τ z
    ∃ T : PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 μ,
    IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 μ
      (fun x τ z => nativeArrayAssembly rjet (F.identity v u γ).map
        (fun k I => F.weight p (timeScale * τ) * transportedCoeff
          (fun y => naturalPreparationJacobian hφ r σ (yc + e • y))
          (F.identity v u γ).maxOrder (fun d I => B d I τ z) rjet I z k)
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ x τ) rjet I z))) T ∧ ∀ x : PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ,
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow N * Cflow
    let CR := nativeArrayUniformTransportPrice N D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    ∀ᵐ τ ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity (ρ / e)
        (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ (T x) τ) z ≤
      F.weight p (timeScale * τ) ^ 2 *
        (pointwiseOriginalIdentityRemainderPrice F K Ks Kmax
          (ChartedFamily.Domain.onWindow F W) ν e E ρ CR ζ v u γ ^ 2 *
          ((polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 *
            planeGradFactorialDensity (ρ / e)
              (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ x τ) z)) := by
  dsimp only
  classical
  by_cases hord : rjet < (F.identity v u γ).maxOrder
  · have hKL : K v + rjet ≤ K u + 1 := by
      have hh := hdesc v u γ
      omega
    exact exists_originalFamilyNaturalRemainder_identity_density_map_including_zero
      Ks F hw hm π hπ K Kmax hK W ν e E ρ hν he hE hρ C J b₀ henv v u γ hKs p c
      hKL hrjet hrD hc ha r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn
      timeScale a b htime N hN hKN hcellE yc μ
  · have hlarge : (F.identity v u γ).maxOrder ≤ rjet := Nat.le_of_not_gt hord
    refine ⟨0, ?_, ?_⟩
    · apply planeRaw_allMoment_zero_map
      intro x τ z
      have hb : (fun k I => F.weight p (timeScale * τ) * transportedCoeff
          (fun y => naturalPreparationJacobian hφ r σ (yc + e • y))
          (F.identity v u γ).maxOrder
          (fun d I k => naturalSlowRemainderTimeCoefficient Ks
            (fun t X y => F.flux p c v u γ d I (timeScale * t) X y k)
            a b hφ r (fun _ => σ) e E yc τ z) rjet I z k) = 0 := by
        funext k I
        rw [transportedCoeff_zero_at_or_above _ _ _ _ hlarge]
        simp only [Pi.zero_apply, mul_zero]
      rw [hb, map_zero, zero_apply]
    · intro x
      simp only [LinearMap.zero_apply]
      filter_upwards [planeTimeAllMomentCarrier_zero_representative
        (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 μ 0 rfl] with τ hτ
      rw [hτ]
      filter_upwards [planeFactorialDensity_zero_ae
        (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) (ρ / e)] with z hz
      rw [hz]
      exact mul_nonneg (sq_nonneg _)
        (mul_nonneg (sq_nonneg _)
          (mul_nonneg (sq_nonneg _) (planeGradFactorialDensity_nonneg _ _ _)))
end

end AVRegularity.CycleJointProofs
end
