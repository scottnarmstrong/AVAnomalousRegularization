-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PeriodicOperatorLocalization
import AVRegularity.CycleJoint.PlaneCouplingSourceRowGradientTimeSchur
import AVRegularity.CycleJoint.FamilyNaturalTimeRemainderReservedJets
public import AVRegularity.CycleJoint.NativeRawOriginalFamilyTaylorSplitEdges
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Certified preparation charts transfer pointwise native prices to the actual constituent seminorms. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparation_constituent_lowering_budget (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (hchart : Kmax + D + 2 ≤ Jchart)
    (ν e ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hρ : 0 < ρ)
    (hE : 0 < ocEpsilon q Λ (m - 1)) (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (Cm : ℕ → ℝ) (Jm : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K
      (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm b)
    (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u)
    (dout : ℕ) (hdout : dout ∈ Finset.Icc 2 D) :
    coefficientSeminorm ρ (K v) tS tZ
      (constituentPhysical F ν e (ocEpsilon q Λ (m - 1)) actual v u γ dout) ≤
    ENNReal.ofReal (‖(F.identity v u γ).map‖ *
      preparationSamplingSeminormConstant D Kmax Jchart Cchart *
      (∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
        ∑ I : DerivativeWord2 (din - 1), (ocEpsilon q Λ (m - 1))⁻¹ ^ (din - dout) *
          (pointwiseMolecularJet ρ e (K v) 0
            (fun z : F.Index => ChartedFamily.Domain.onWindow F (Set.Icc tS tZ) z.1 z.2)
            (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ din I)).toReal)) := by
  classical
  let E := ocEpsilon q Λ (m - 1)
  let dom := ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)
  let M := fun din (I : DerivativeWord2 (din - 1)) =>
    pointwiseMolecularJet ρ e (K v) 0 (fun z : F.Index => dom z.1 z.2)
      (fun z => F.dimFlux ν e E z.1 z.2 v u γ din I)
  let S := ∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
    ∑ I : DerivativeWord2 (din - 1), E⁻¹ ^ (din - dout) * (M din I).toReal
  by_cases hγ : (F.identity v u γ).map = 0
  · have hz : constituentPhysical F ν e E actual v u γ dout = fun _ _ => 0 := by
      funext t x
      exact constituentPhysical_zero_map F ν e E actual v u γ hγ dout t x
    change coefficientSeminorm ρ (K v) tS tZ
      (constituentPhysical F ν e E actual v u γ dout) ≤ _
    rw [hz, coefficientSeminorm_zero_function]
    exact zero_le
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro din _
    apply Finset.sum_nonneg
    intro I _
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hE.le) _) ENNReal.toReal_nonneg
  let B := ‖(F.identity v u γ).map‖ * preparationSamplingJetConstant D Kmax Jchart Cchart * S
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (norm_nonneg _) (preparationSamplingJetConstant_nonnegative _ _ _ _)) hS
  have hs : ∀ t ∈ Set.Icc tS tZ,
      ContDiff ℝ (K v : ℕ) (constituentPhysical F ν e E actual v u γ dout t) := by
    intro t ht
    exact (constituentPhysical_spatial_smooth F hc ν e E (fun v => K v + Jm)
      henv.1 actual v u γ dout t ht).of_le
        (by exact_mod_cast Nat.le_add_right (K v) Jm)
  have hjets : ∀ t ∈ Set.Icc tS tZ, ∀ j, j ≤ K v → ∀ x,
      ρ ^ j * ‖iteratedFDeriv ℝ j (constituentPhysical F ν e E actual v u γ dout t) x‖ ≤ B := by
    intro t ht j hj x
    let ts : Set.Icc tS tZ := ⟨t, ht⟩
    let g := fun p y => nativeArrayAssembly (dout - 1) (F.identity v u γ).map
      (fun a A => transportedCoeff (naturalPreparationJacobian hφ (F.piece p).anchor t)
        (F.identity v u γ).maxOrder
        (fun din I => F.dimFlux ν e E p (actual p) v u γ din I t
          (streamFlow φ hφ (F.piece p).anchor y t)
          (e⁻¹ • streamFlow φ hφ (F.piece p).anchor y t)) (dout - 1) A y a)
    have hg p (hout : t ∈ (F.piece p).output) : ContDiff ℝ (K v : ℕ) (g p) := by
      exact (natural_constituent_operator_smooth F ν e E hE.ne' (fun v => K v + Jm)
        dom henv.1 p (actual p) v u γ (dout - 1) φ hφ (F.piece p).anchor t
        (fun Y => by
          change (t, Y) ∈ ((F.piece p).output ∩ Set.Icc tS tZ) ×ˢ Set.univ
          exact ⟨⟨hout, ht⟩, Set.mem_univ Y⟩)).of_le (by exact_mod_cast Nat.le_add_right (K v) Jm)
    apply positive_constituentPhysical_jet_assembly F hc ν e E actual v u γ dout j
      ρ B hρ.le hB ts g (fun _ _ => rfl)
      (fun p hout => (hg p hout).of_le (by exact_mod_cast hj)) _ x
    intro p hout y
    have hp : ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty := ⟨t, hout, ht⟩
    obtain ⟨has, hat, hage⟩ := preparation_piece_flow_endpoints hc p hp t
      ((F.piece p).output_subset hout) (preparation_renewal_nonnegative α q Λ m)
    have hnchart : K v ≤ Jchart + 1 := by have hk := hK v; omega
    have hnN : j + (F.identity v u γ).maxOrder ≤ Kmax + D + 2 := by
      have hk := hK v
      have hd := (F.identity v u γ).le_D
      omega
    have hh := pointwise_molecular_native_transport_uniform_budget F π hπ K Kmax hK dom ν e ρ
      hν he hE hρE (preparation_amplitude_nonnegative α q Λ (m - 1) hE.le) hρ
      Cm Jm b henv v u γ hγ p (actual p) hc.flow hnchart (Kmax + D + 2) hchart
      (F.piece p).anchor t has hat (by simpa only [abs_sub_comm] using hage)
      (fun Y => by
        change (t, Y) ∈ ((F.piece p).output ∩ Set.Icc tS tZ) ×ˢ Set.univ
        exact ⟨⟨hout, ht⟩, Set.mem_univ Y⟩) j (dout - 1) hj (by have hh := (Finset.mem_Icc.mp hdout).1; omega)
      hnN (by have hh := Finset.mem_Icc.mp hdout; omega) y
    have hr : dout - 1 + 1 = dout := by have hh := (Finset.mem_Icc.mp hdout).1; omega
    have hediff din : din - 1 - (dout - 1) = din - dout := by
      have hh := (Finset.mem_Icc.mp hdout).1
      omega
    dsimp only at hh
    simp only [hr, hediff] at hh
    change ρ ^ j * ‖iteratedFDeriv ℝ j (g p) y‖ ≤
      ‖(F.identity v u γ).map‖ * preparationSamplingJetConstant D Kmax Jchart Cchart *
        (∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
          ∑ I : DerivativeWord2 (din - 1), (M din I).toReal * E⁻¹ ^ (din - dout)) at hh
    have heq : (∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
        ∑ I : DerivativeWord2 (din - 1), (M din I).toReal * E⁻¹ ^ (din - dout)) = S := by
      dsimp only [S]
      apply Finset.sum_congr rfl
      intro din _
      apply Finset.sum_congr rfl
      intro I _
      exact mul_comm _ _
    rw [heq] at hh
    exact hh
  have hh := uniform_pointwise_coefficient_seminorm ρ hρ (K v) Kmax (hK v) tS tZ
    (constituentPhysical F ν e E actual v u γ dout) hs B hB hjets
  apply hh.trans_eq
  congr 1
  dsimp only [preparationSamplingSeminormConstant, B]
  ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! The full retained coefficient array gives a literal native forcing row with every supplied polynomial moment. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_planeCouplingFluxRow_polynomial_reserve {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i i' d t))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))

    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)))
    (N : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (he : ∀ n ≤ N, ∀ i, (∫⁻ t in Set.Icc a b,
      weightedFactorialNormSq n ϖ zc ρ (K i + 1) (w i t)) ≠ ⊤) :
    ∃ F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)),
      (∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ n ≤ N, ∀ i, (∫⁻ t in Set.Icc a b,
        weightedFactorialNormSq n ϖ zc ρ (K i) (F i t)) ≠ ⊤) ∧
      ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
        planeValue (F i t) =ᵐ[volume] planeRawCouplingFlux K D t A (fun j => w j t) i := by
  let F := planeCouplingFluxRow hab ρ hρ K D A hA hc w
  refine ⟨F, planeCouplingFluxRow_memLp hab ρ hρ K D A hA hc w hAm hw, ?_, ?_⟩
  · intro n hn i
    have hi := planeCouplingFluxRow_weighted_time_energy_ne_top hab ρ hρ K D A hA hc w hAm hw
      (planeMomentSquareRoot n ϖ zc) (planeMomentSquareRoot_continuous n ϖ zc)
      (planeMomentSquareRoot_pos n ϖ zc)
      (fun j => by
        simpa only [planeMomentSquareRoot_sq, ← weightedFactorialNormSq_stored_readout] using he n hn j) i
    simpa only [planeMomentSquareRoot_sq, ← weightedFactorialNormSq_stored_readout] using hi
  · intro i
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [planeValue_eq_rawValue]
    exact (univToPlane_ae ((F i t).val (valueIndex2 (K i)))).symm.trans
      (planeCouplingFluxRow_raw_value_ae hab ρ hρ K D A hA hc w i t ht)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The actual forced metric equation retains both its external flux and source feedback budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeForced_total_flux_weighted_time_budget
    (a b : ℝ) (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (A : ∀ i u, (d : admissibleOrders K D i u) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i u d, coefficientSeminorm ρ (K i) a b (A i u d) ≠ ⊤)
    (hc : ∀ i u d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i u d t))
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (θ : ℝ)
    (hrow : ∀ i, ∑ u, schurMatrix 1 ρ π K D a b A i u ≤ θ)
    (hcol : ∀ u, ∑ i, schurMatrix 1 ρ π K D a b A i u ≤ θ)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (w : ∀ u, ℝ → PlaneHk Set.univ (K u + 1) (h u))
    (hw : ∀ u, MemLp (w u) 2 (volume.restrict (Set.Icc a b)))
    (he : ∀ u, (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ zc ρ (K u) (w u t)) ≠ ⊤)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b))) :
    (∫⁻ t in Set.Icc a b, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq n ϖ zc ρ (K i)
        (F i t + planeCouplingFluxRow hab ρ hρ K D A hA hc w i t)) ≤
      2 * ((∫⁻ t in Set.Icc a b, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n ϖ zc ρ (K i) (F i t)) +
        ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * θ) ^ 2) *
          ∫⁻ t in Set.Icc a b, ∑ u, ENNReal.ofReal ((π u)⁻¹) *
            weightedGradFactorialNormSq n ϖ zc ρ (K u) (w u t)) := by
  have hadd := planeFamily_forcing_energy_add_le K n ϖ ρ zc
    (volume.restrict (Set.Icc a b)) π F
    (planeCouplingFluxRow hab ρ hρ K D A hA hc w) hF
  have hsource := planeCouplingFluxRow_weighted_gradient_time_schur_budget
    a b hab ρ hρ K D A hA hc π hπ θ hrow hcol n ϖ zc w hw he
  apply hadd.trans
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hsource) zero_le

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleReference AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Actual windowed material transport and diffusion operators and their genuine energy dual time class. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

def planeMaterialTransport (a b : ℝ) (hab : a ≤ b)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ t, IsZ2Periodic (v t)) :
    ℝ → PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
  let hb := materialChartDrift_bound hφ s a b v hv hp
  planeIntervalTransport a b hab (chartVector hφ s (fun r x => v r x - streamVel φ r x))
    (fun t _ => materialChartDrift_continuous_slice hφ s v hv t) hb.choose hb.choose_spec.2

def planeMaterialDiffusion (a b : ℝ) (hab : a ≤ b)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s ν : ℝ) :
    ℝ → PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E :=
  let hb := viscousChartMetric_bound hφ s ν a b
  planeWindowScalarDiffusion a b hab (fun t x => ν • chartMetric hφ s t x)
    (fun t _ i j => viscousChartMetric_continuous_entry_slice hφ s ν t i j) hb.choose hb.choose_spec.2

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E]

theorem planeMaterialDual_memLp {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk univ 1 E} (h : PlaneWeakHilbertCurve a b u slice dual)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s ν : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ t, IsZ2Periodic (v t)) (F : ℝ → PlaneFluxL2 E)
    (hF : MemLp F 2 (volume.restrict (Icc a b))) :
    MemLp (fun t => planeWeakDualRepresentative (planeMaterialTransport a b hab hφ s v hv hp t)
      (planeMaterialDiffusion a b hab hφ s ν t)
      (planeH1ChartPull hφ t s (slice t)) (planeFluxChartPull hφ t s (F t)))
      2 (volume.restrict (Icc a b)) := by
  unfold planeMaterialTransport planeMaterialDiffusion
  apply planeWindowDual_memLp
  · exact materialChartDrift_measurable_window hφ s a b v hv
  · exact viscousChartMetric_measurable_window hφ s ν a b
  · exact planeWeakCurve_chart_state_memLp h hφ s
  · exact planeFluxChartPull_time_memLp hφ s F hF

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Weighted AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Native material operator slices are exactly the prescribed coefficients on the preparation window. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem planeMaterialTransport_eq_of_mem (a b : ℝ) (hab : a ≤ b)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ t, IsZ2Periodic (v t)) (t : ℝ) (ht : t ∈ Icc a b)
    (hc : ∀ k, Continuous (fun x => chartVector hφ s (fun r y => v r y - streamVel φ r y) t x k))
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ k x, |chartVector hφ s (fun r y => v r y - streamVel φ r y) t x k| ≤ M) :
    planeMaterialTransport (E := E) a b hab hφ s v hv hp t =
      planeScalarTransport (chartVector hφ s (fun r y => v r y - streamVel φ r y) t) hc hM hb := by
  unfold planeMaterialTransport planeIntervalTransport
  exact planeScalarTransport_congr _ _
    (planeIntervalCoefficient_of_mem a b hab _ t ht) _ hc (le_max_right _ 0) hM _ hb

theorem planeMaterialDiffusion_eq_of_mem (a b : ℝ) (hab : a ≤ b)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s ν t : ℝ) (ht : t ∈ Icc a b)
    (hc : ∀ k j, Continuous (fun x => (ν • chartMetric hφ s t x) k j))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ k j x, |(ν • chartMetric hφ s t x) k j| ≤ M) :
    planeMaterialDiffusion (E := E) a b hab hφ s ν t =
      planeScalarDiffusion (fun x => ν • chartMetric hφ s t x) hc hM hb := by
  unfold planeMaterialDiffusion planeWindowScalarDiffusion
  exact planeScalarDiffusion_congr _ _
    (planeIntervalCoefficient_of_mem a b hab _ t ht) _ hc (le_max_right _ 0) hM _ hb
end

/-! The actual material diffusion deviation has the prescribed viscous chart metric readout on rough L2 gradients. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem planeMaterialDiffusion_deviation_ae (a b : ℝ) (hab : a ≤ b)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s ν t : ℝ) (ht : t ∈ Icc a b)
    (du : PlaneFluxL2 E) (k : Fin 2) :
    ((planeMaterialDiffusion (E := E) a b hab hφ s ν t -
      ContinuousLinearMap.id ℝ (PlaneFluxL2 E)) du k : Vec 2 → E)
      =ᵐ[volume] fun y => ∑ j : Fin 2,
        ((ν • chartMetric hφ s t y) k j - if k = j then 1 else 0) • du j y := by
  let hb := viscousChartMetric_bound hφ s ν a b
  have hc : ∀ k j, Continuous (fun x => (ν • chartMetric hφ s t x) k j) :=
    viscousChartMetric_continuous_entry_slice hφ s ν t
  rw [planeMaterialDiffusion_eq_of_mem a b hab hφ s ν t ht hc hb.choose_spec.1
    (hb.choose_spec.2 t ht)]
  exact planeScalarDiffusion_deviation_ae _ hc hb.choose_spec.1 (hb.choose_spec.2 t ht) du k
end

/-! The actual windowed material diffusion factors its physical viscosity exactly on the solution window. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem planeMaterialDiffusion_viscosity_scaling (a b : ℝ) (hab : a ≤ b)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s ν t : ℝ) (ht : t ∈ Icc a b) :
    planeMaterialDiffusion (E := E) a b hab hφ s ν t =
      ν • planeMaterialDiffusion a b hab hφ s 1 t := by
  let hν := viscousChartMetric_bound hφ s ν a b
  let h1 := viscousChartMetric_bound hφ s 1 a b
  rw [planeMaterialDiffusion_eq_of_mem a b hab hφ s ν t ht
    (viscousChartMetric_continuous_entry_slice hφ s ν t) hν.choose_spec.1 (hν.choose_spec.2 t ht),
    planeMaterialDiffusion_eq_of_mem a b hab hφ s 1 t ht
      (viscousChartMetric_continuous_entry_slice hφ s 1 t) h1.choose_spec.1 (h1.choose_spec.2 t ht)]
  simpa only [one_smul] using planeScalarDiffusion_scaling (E := E)
    (fun x => chartMetric hφ s t x) ν
    (by simpa only [one_smul] using viscousChartMetric_continuous_entry_slice hφ s 1 t)
    (viscousChartMetric_continuous_entry_slice hφ s ν t)
    h1.choose_spec.1 hν.choose_spec.1
    (by simpa only [one_smul] using h1.choose_spec.2 t ht) (hν.choose_spec.2 t ht)
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The homogeneous periodized unit patch starts from the exact original torus datum. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The initial value class identifies the complete periodized Sobolev trace. -/
theorem periodizedUnitPatch_initial_trace {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (K : ι → ℕ) (a b : ℝ) (hab : a ≤ b) (f : ∀ i, TorusHk (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (U : ∀ i, ℝ → TorusHk (K i) (h i))
    (W : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hu0 : ∀ i, u i a = spatialPatchLocalization hζ 1 (by decide) 0 (K i) (f i))
    (hp : IsPeriodizedFamilyPair K a b u w U W) (i : ι) : U i a = f i := by
  apply TorusHk.ext_value
  apply Lp.ext
  have he := hp.2.2.2.1 i a ⟨le_refl a, hab⟩ (valueIndex2 (K i))
  rw [hu0 i] at he
  exact he.trans (unitPatchLocalization_periodized_value_ae hζ (f i))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Compact spacetime tests are admissible in the weak plane time equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakCurve_compact_spacetime_increment {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk univ 1 E}
    (h : PlaneWeakHilbertCurve a b u slice dual)
    (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : HasCompactSupport f) (e : E) :
    let z := compactSpacetimeVectorH1 f hf hs e
    let dz := compactSpacetimeVectorH1 (spacetimeDirectionalField f (1, 0))
      (spacetimeDirectionalField_smooth f hf (1, 0))
      (spacetimeDirectionalField_compact f hs (1, 0)) e
    inner ℝ (u b) (planeHkValueOperator 1 (z b)) -
      inner ℝ (u a) (planeHkValueOperator 1 (z a)) =
      ∫ t in a..b, inner ℝ (dual t) (z t) +
        inner ℝ (planeHkValueOperator 1 (dz t)) (u t) := by
  apply planeWeakCurve_strong_test_increment hab h
  · exact compactSpacetimeVectorH1_strong_time f hf hs e a b
  · exact compactSpacetimeVectorH1_time_memLp hab f hf hs e
  · exact compactSpacetimeVectorH1_time_memLp hab _
      (spacetimeDirectionalField_smooth f hf (1, 0))
      (spacetimeDirectionalField_compact f hs (1, 0)) e

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs

/-! The full preparation sampling bridge from its independent pointwise certificate. -/

/-- **Sampled molecular envelope of the preparation**
    (`l.cycle.joint.preparation-sampled-envelope`). -/
theorem preparation_sampled_envelope_of_pointwise_certificate (D Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν e ρ : ℝ), 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
      ∀ {ι : Type*} {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (b : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ b v u),
        IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm b →
        IsSampledEnvelope F π K actual tS tZ ν e (ocEpsilon q Λ (m - 1)) ρ Cprep b := by
  let C := preparationSamplingSeminormConstant D Kmax Jchart Cchart
  let Cbase := C * D * |Cm 0|
  refine ⟨max 1 Cbase, le_max_left _ _, ?_⟩
  intro α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι h _ _ P' Ctx F π hπ K hK actual b hb hc henv
  have he : 0 < e := hρ.trans_le hρe
  have hρE : ρ ≤ ocEpsilon q Λ (m - 1) := hρe.trans heE
  have hE : 0 < ocEpsilon q Λ (m - 1) := hρ.trans_le hρE
  have hC : 0 ≤ C := preparationSamplingSeminormConstant_nonnegative _ _ _ _
  have hs : ∀ v u (γ : F.Γ v u) d, ∀ t ∈ Set.Icc tS tZ,
      ContDiff ℝ (K v : ℕ)
        (constituentPhysical F ν e (ocEpsilon q Λ (m - 1)) actual v u γ d t) := by
    intro v u γ d t ht
    exact (constituentPhysical_spatial_smooth F hc ν e (ocEpsilon q Λ (m - 1))
      (fun v => K v + Jm) henv.1 actual v u γ d t ht).of_le
        (by exact_mod_cast Nat.le_add_right (K v) Jm)
  have hh := sampled_envelope_of_lowering_budget F π K
    (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) actual tS tZ ν e
    (ocEpsilon q Λ (m - 1)) ρ C hν hρ hE hρE hC Cm Jm b hb henv hs
    (fun v u γ dout hdout => preparation_constituent_lowering_budget F hc π hπ K Kmax hK
      hchart ν e ρ hν he hρ hE hρE Cm Jm b henv actual v u γ dout hdout)
  refine ⟨hh.1, ?_⟩
  intro v u
  exact (hh.2 v u).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_right 1 Cbase) (hb v u)))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Weighted AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The normalized actual material transport is precisely the interval operator of its computed physical velocity. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem planeMaterialTransport_diffusion_time_normalization {a b ν : ℝ}
    (hab : a ≤ b) (hν : 0 < ν)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ t, IsZ2Periodic (v t)) (t : ℝ) (ht : t ∈ Set.Icc (ν * a) (ν * b)) :
    ν⁻¹ • planeMaterialTransport (E := E) a b hab hφ s v hv hp (ν⁻¹ * t) =
      planeIntervalTransport (E := E) (ν * a) (ν * b)
        (mul_le_mul_of_nonneg_left hab hν.le) (normalizedMaterialVelocity hφ s ν v)
        (fun r _ => normalizedMaterialVelocity_continuous hφ s ν v hv r)
        (normalizedMaterialVelocityBudget hφ s ν a b v hv hp)
        (normalizedMaterialVelocity_norm_le hφ s hν a b v hv hp) t := by
  unfold planeMaterialTransport
  exact planeIntervalTransport_time_normalization hab hν _
    (fun r _ => materialChartDrift_continuous_slice hφ s v hv r)
    (materialChartDrift_bound hφ s a b v hv hp).choose
    (materialChartDrift_bound hφ s a b v hv hp).choose_spec.2
    (fun r _ => normalizedMaterialVelocity_continuous hφ s ν v hv r)
    (normalizedMaterialVelocityBudget hφ s ν a b v hv hp)
    (normalizedMaterialVelocity_norm_le hφ s hν a b v hv hp) t ht

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! The moving-test identity with literal value and time-derivative pairings. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakCurve_literal_test_increment {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk univ 1 E}
    (h : PlaneWeakHilbertCurve a b u slice dual)
    (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : HasCompactSupport f) (e : E) :
    (∫ x, f (b, x) * inner ℝ (u b x) e) -
      (∫ x, f (a, x) * inner ℝ (u a x) e) =
      ∫ t in a..b, inner ℝ (dual t) (compactSpacetimeVectorH1 f hf hs e t) +
        ∫ x, deriv (fun r => f (r, x)) t * inner ℝ (u t x) e := by
  have hp := planeWeakCurve_compact_spacetime_increment hab h f hf hs e
  dsimp only at hp
  rw [compactSpacetimeVectorH1_L2_pair, compactSpacetimeVectorH1_L2_pair] at hp
  apply hp.trans
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  congr 1
  rw [real_inner_comm, compactSpacetimeVectorH1_L2_pair]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [spacetime_time_partial_eq f (hf.of_le (by simp))]
    rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Diffusion-time normalization gives the actual material metric, and its computed deviation from identity, in the true weak curve. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable {a b ν : ℝ} (hab : a ≤ b) (hν : 0 < ν)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ)
    (T : ℝ → PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (u : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (state : ℝ → PlaneHk Set.univ 1 E) (Q : ℝ → PlaneFluxL2 E)
    (h : PlaneWeakHilbertCurve a b u state
      (fun t => planeWeakDualRepresentative (T t)
        (planeMaterialDiffusion a b hab hφ s ν t) (state t) (Q t)))
include hν h

theorem planeMaterialWeakCurve_diffusion_time_normalization :
    PlaneWeakHilbertCurve (ν * a) (ν * b) (fun t => u (ν⁻¹ * t))
      (fun t => state (ν⁻¹ * t))
      (fun t => planeWeakDualRepresentative (ν⁻¹ • T (ν⁻¹ * t))
        (planeMaterialDiffusion a b hab hφ s 1 (ν⁻¹ * t))
        (state (ν⁻¹ * t)) (ν⁻¹ • Q (ν⁻¹ * t))) := by
  have hs : PlaneWeakHilbertCurve a b u state
      (fun t => planeWeakDualRepresentative (T t)
        (ν • planeMaterialDiffusion a b hab hφ s 1 t) (state t) (Q t)) := by
    apply planeWeakHilbertCurve_dual_congr_on h
    intro t ht
    rw [planeMaterialDiffusion_viscosity_scaling a b hab hφ s ν t ht]
  exact planeWeakHilbertCurve_diffusion_time_normalization hν T
    (planeMaterialDiffusion a b hab hφ s 1) u state Q hs

theorem planeMaterialWeakCurve_normalized_unit_diffusion :
    PlaneWeakHilbertCurve (ν * a) (ν * b) (fun t => u (ν⁻¹ * t))
      (fun t => state (ν⁻¹ * t))
      (fun t => planeWeakDualRepresentative (ν⁻¹ • T (ν⁻¹ * t))
        (ContinuousLinearMap.id ℝ (PlaneFluxL2 E)) (state (ν⁻¹ * t))
        ((planeMaterialDiffusion (E := E) a b hab hφ s 1 (ν⁻¹ * t) -
          ContinuousLinearMap.id ℝ (PlaneFluxL2 E))
            (planeH1GradientOperator (state (ν⁻¹ * t))) + ν⁻¹ • Q (ν⁻¹ * t))) := by
  exact planeWeakCurve_diffusion_reallocation (fun t => u (ν⁻¹ * t))
    (fun t => state (ν⁻¹ * t)) (fun t => ν⁻¹ • Q (ν⁻¹ * t))
    (fun t => ν⁻¹ • T (ν⁻¹ * t))
    (fun t => planeMaterialDiffusion a b hab hφ s 1 (ν⁻¹ * t))
    (fun _ => ContinuousLinearMap.id ℝ (PlaneFluxL2 E))
    (planeMaterialWeakCurve_diffusion_time_normalization hab hν hφ s T u state Q h)

end AVRegularity.CycleJointProofs
end
end

section
public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Quantitative polynomial energy after a smooth chart pullback, with the
factorial composition price evaluated at the scaled derivative bounds. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHkScaledPullback_factorialNormSq_le {K : ℕ} (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (C : ℕ → ℝ)
    (hscale : ∀ j, 1 ≤ j → j ≤ K → ρ ^ (j - 1) * B j ≤ C j)
    (U : PlaneHk Set.univ K E) :
    factorialNormSq ρ (planeHkSmoothPullback X hX hμ B hB hb U).val ≤
      (compositionFactorialNormBound C K) ^ 2 * factorialNormSq ρ U.val := by
  have hh := planeHkScaledPullback_factorial_norm_le X hX hμ B hB hb hρ C hscale U
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (compositionFactorialNormBound_nonneg C K) (Real.sqrt_nonneg _))).mpr hh
  rw [Real.sq_sqrt (factorialNormSq_nonneg _ _), mul_pow,
    Real.sq_sqrt (factorialNormSq_nonneg _ _)] at hs
  exact hs

theorem planeHkScaledPullback_polynomial_energy_le_of_support {K : ℕ}
    (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (C : ℕ → ℝ)
    (hscale : ∀ j, 1 ≤ j → j ≤ K → ρ ^ (j - 1) * B j ≤ C j)
    (U : PlaneHk Set.univ K E) (S : Set (Vec 2))
    (hs : ∀ a : JetIndex2 K, ∀ᵐ x ∂volume, x ∉ S → U.toFunction.jet a x = 0)
    (n : ℕ) (ϖ : ℝ) (yc : Vec 2) (M : ℝ) (hM : 0 ≤ M)
    (hpoly : ∀ x, X x ∈ S → planeMomentPolynomial n ϖ yc x ≤ M) :
    weightedFactorialNormSq n ϖ yc ρ K (planeHkSmoothPullback X hX hμ B hB hb U) ≤
      ENNReal.ofReal M * ENNReal.ofReal ((compositionFactorialNormBound C K) ^ 2) *
        ENNReal.ofReal (factorialNormSq ρ U.val) := by
  have hp := planeHk_pullback_polynomial_energy_le_of_support U
    (planeHkSmoothPullback X hX hμ B hB hb U) X hX hμ B hb
    (planeHkSmoothPullback_value_ae X hX hμ B hB hb U) S hs n ϖ ρ yc M hM hpoly
  have hf := planeHkScaledPullback_factorialNormSq_le X hX hμ B hB hb hρ C hscale U
  calc
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal
        (factorialNormSq ρ (planeHkSmoothPullback X hX hμ B hB hb U).val) := hp
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal
        ((compositionFactorialNormBound C K) ^ 2 * factorialNormSq ρ U.val) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hf)
    _ = _ := by rw [ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Actual higher material pullbacks commute with every original constituent Hilbert map. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem planeHkSmoothPullback_fiberMap {K : ℕ} (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) ⇑X) (hμ : MeasurePreserving ⇑X volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j ⇑X x‖ ≤ B j)
    (L : E →L[ℝ] F) (U : PlaneHk univ K E) :
    mapPlaneHk L (planeHkSmoothPullback X hX hμ B hB hb U) =
      planeHkSmoothPullback X hX hμ B hB hb (mapPlaneHk L U) := by
  apply planeHk_eq_of_value
  rw [planeHkFiberValue, planeHkSmoothPullback_value_eq,
    planeHkSmoothPullback_value_eq, planeHkFiberValue]
  exact planeLp_compMeasurePreserving_fiberMap ⇑X hμ L (planeHkValueOperator K U)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleReference AVRegularity.CycleWords AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Reserved flow jets give the genuine higher-order material energy state on its prescribed window. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable {K : ℕ} (a b : ℝ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ t ∈ Icc a b, ∀ j, 1 ≤ j → j ≤ K → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => AVRegularity.streamFlow φ hφ t y s) x‖ ≤ B j)

def planeHkWindowChartPull (t : ℝ) (U : PlaneHk univ K E) : PlaneHk univ K E :=
  if ht : t ∈ Icc a b then
    planeHkSmoothPullback (streamFlowHomeomorph hφ t s) (streamFlow_spatial_smooth hφ t s)
      (streamFlow_measurePreserving hφ t s) B hB (hb t ht) U
  else 0

theorem planeHkWindowChartPull_value_eq (t : ℝ) (ht : t ∈ Icc a b) (U : PlaneHk univ K E) :
    planeHkValueOperator K (planeHkWindowChartPull a b hφ s B hB hb t U) =
      planeL2FlowPull hφ t s (planeHkValueOperator K U) := by
  unfold planeHkWindowChartPull
  rw [dite_eq_left ht]
  exact planeHkSmoothPullback_value_eq _ _ _ _ _ _ U

theorem planeHkWindowChartPull_norm_le (t : ℝ) (ht : t ∈ Icc a b) (U : PlaneHk univ K E) :
    ‖planeHkWindowChartPull a b hφ s B hB hb t U‖ ≤ smoothPullbackNormBound B K * ‖U‖ := by
  unfold planeHkWindowChartPull
  rw [dite_eq_left ht]
  exact planeHkSmoothPullback_norm_le _ _ _ _ _ _ U

theorem planeHkWindowChartPull_memLp
    (u : ℝ → Lp E 2 (volume : Measure (Vec 2))) (w : ℝ → PlaneHk univ K E)
    (hu : ContinuousOn u (Icc a b)) (hw : MemLp w 2 (volume.restrict (Icc a b)))
    (hagrees : ∀ᵐ t ∂volume.restrict (Icc a b), u t = planeHkValueOperator K (w t)) :
    MemLp (fun t => planeHkWindowChartPull a b hφ s B hB hb t (w t))
      2 (volume.restrict (Icc a b)) := by
  have he : (fun t => planeHkValueOperator K (planeHkWindowChartPull a b hφ s B hB hb t (w t)))
      =ᵐ[volume.restrict (Icc a b)] (fun t => planeL2FlowPull hφ t s (u t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hagrees] with t ht he
    rw [planeHkWindowChartPull_value_eq a b hφ s B hB hb t ht, he]
  have hv : AEStronglyMeasurable
      (fun t => planeHkValueOperator K (planeHkWindowChartPull a b hφ s B hB hb t (w t)))
      (volume.restrict (Icc a b)) :=
    ((planeL2FlowPull_continuousOn hφ s (Icc a b) u hu).aestronglyMeasurable_of_isCompact
      isCompact_Icc measurableSet_Icc).congr he.symm
  apply hw.of_le_mul (planeHk_time_aestronglyMeasurable_of_value _ _ hv)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact planeHkWindowChartPull_norm_le a b hφ s B hB hb t ht (w t)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Moving compact tests convert their transport time correction into the native H1 gradient pairing. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakCurve_transport_test_increment {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk univ 1 E}
    (h : PlaneWeakHilbertCurve a b u slice dual)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hdiv : ∀ t ∈ Icc a b, ∀ x,
      ∑ i : Fin 2, fderiv ℝ (fun y => v t y i) x (basisVec i) = 0)
    (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : HasCompactSupport f) (e : E)
    (hd : ∀ t ∈ Icc a b, ∀ x, deriv (fun r => f (r, x)) t =
      -vecDot (spaceGrad (fun y => f (t, y)) x) (v t x)) :
    (∫ x, f (b, x) * inner ℝ (u b x) e) -
      (∫ x, f (a, x) * inner ℝ (u a x) e) =
      ∫ t in a..b, inner ℝ (dual t) (compactSpacetimeVectorH1 f hf hs e t) +
        ∫ x, f (t, x) * ∑ i : Fin 2, v t x i *
          inner ℝ (planeH1GradientOperator (slice t) i x) e := by
  apply (planeWeakCurve_literal_test_increment hab h f hf hs e).trans
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hab]
  have ha := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self h.agrees
  filter_upwards [ha, ae_restrict_mem measurableSet_Ioc] with t ht htw
  have hti : t ∈ Icc a b := Ioc_subset_Icc_self htw
  rw [ht]
  congr 1
  exact planeH1_test_transport_correction (slice t) e (v t) (hv t hti)
    (hdiv t hti) f hf hs t (hd t hti)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The reserved native chart operator bound controls differences of arbitrary rough inputs uniformly on the window. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHkWindowChartPull_sub_norm_le {K : ℕ} (a b : ℝ)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ t ∈ Icc a b, ∀ j, 1 ≤ j → j ≤ K → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => AVRegularity.streamFlow φ hφ t y s) x‖ ≤ B j)
    (t : ℝ) (ht : t ∈ Icc a b) (U V : PlaneHk univ K E) :
    ‖planeHkWindowChartPull a b hφ s B hB hb t U -
      planeHkWindowChartPull a b hφ s B hB hb t V‖ ≤ smoothPullbackNormBound B K * ‖U - V‖ := by
  unfold planeHkWindowChartPull
  simp only [dite_eq_left ht]
  let T := planeHkSmoothPullbackLinearMap (E := E) (streamFlowHomeomorph hφ t s)
    (streamFlow_spatial_smooth hφ t s) (streamFlow_measurePreserving hφ t s) B hB (hb t ht)
  change ‖T U - T V‖ ≤ _
  rw [← map_sub]
  exact planeHkSmoothPullback_norm_le (streamFlowHomeomorph hφ t s)
    (streamFlow_spatial_smooth hφ t s) (streamFlow_measurePreserving hφ t s) B hB (hb t ht) (U - V)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleReference AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! The actual native material dual is the physical dual plus the chart-velocity transport correction. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeMaterialDual_pair_eq_physical_plus_stream (a b : ℝ) (hab : a ≤ b)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s ν : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ r, IsZ2Periodic (v r)) (t : ℝ) (ht : t ∈ Icc a b)
    (hvc : ∀ k, Continuous (fun x => v t x k))
    {M : ℝ} (hM : 0 ≤ M) (hvb : ∀ k x, |v t x k| ≤ M)
    (u z : PlaneHk univ 1 E) (F : PlaneFluxL2 E) :
    inner ℝ (planeWeakDualRepresentative (planeMaterialTransport a b hab hφ s v hv hp t)
      (planeMaterialDiffusion a b hab hφ s ν t)
      (planeH1ChartPull hφ t s u) (planeFluxChartPull hφ t s F))
      (planeH1ChartPull hφ t s z) =
    inner ℝ (planeWeakDualRepresentative (planeScalarTransport (v t) hvc hM hvb)
      (ν • ContinuousLinearMap.id ℝ (PlaneFluxL2 E)) u F) z +
      ∫ x, ∑ k : Fin 2, streamVel φ t x k *
        inner ℝ (planeH1GradientOperator u k x) (planeHkValueOperator 1 z x) := by
  obtain ⟨W, hW, hbW⟩ := streamVel_bounded_on_compact_time hφ (Icc a b) isCompact_Icc
  have hstream : Continuous (streamVel φ t) := by
    have hmap : Continuous (fun x : Vec 2 => (t, x)) := continuous_const.prodMk continuous_id
    exact (Infra.Construction.smoothPeriodic_streamVel hφ).smooth.continuous.comp hmap
  have hwc k : Continuous (fun x => streamVel φ t x k) := (continuous_apply k).comp hstream
  have hwb k x : |streamVel φ t x k| ≤ W := by
    have hn : |streamVel φ t x k| ≤ ‖streamVel φ t x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (streamVel φ t x) k
    exact hn.trans (hbW t ht x)
  have hsc k : Continuous (fun x => (v t x - streamVel φ t x) k) := by
    have he : (fun x => (v t x - streamVel φ t x) k) =
        (fun x => v t x k - streamVel φ t x k) := by funext x; rfl
    rw [he]
    exact (hvc k).sub (hwc k)
  have hsb k x : |(v t x - streamVel φ t x) k| ≤ M + W := by
    change |v t x k - streamVel φ t x k| ≤ M + W
    have ha : |v t x k - streamVel φ t x k| ≤ |v t x k| + |streamVel φ t x k| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (v t x k) (streamVel φ t x k)
    exact ha.trans (add_le_add (hvb k x) (hwb k x))
  obtain ⟨C, hC, hbC⟩ := materialChartDrift_bound hφ s a b v hv hp
  have hcc k : Continuous (fun x => chartVector hφ s (fun r y => v r y - streamVel φ r y) t x k) :=
    (continuous_apply k).comp (materialChartDrift_continuous_slice hφ s v hv t)
  have hcb k x : |chartVector hφ s (fun r y => v r y - streamVel φ r y) t x k| ≤ C := by
    have hn : |chartVector hφ s (fun r y => v r y - streamVel φ r y) t x k| ≤
        ‖chartVector hφ s (fun r y => v r y - streamVel φ r y) t x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm
        (chartVector hφ s (fun r y => v r y - streamVel φ r y) t x) k
    exact hn.trans (hbC t ht x)
  obtain ⟨G, hG, hbG⟩ := viscousChartMetric_bound hφ s ν a b
  have hGc k j : Continuous (fun x => (ν • chartMetric hφ s t x) k j) :=
    viscousChartMetric_continuous_entry_slice hφ s ν t k j
  rw [planeMaterialTransport_eq_of_mem a b hab hφ s v hv hp t ht hcc hC hcb,
    planeMaterialDiffusion_eq_of_mem a b hab hφ s ν t ht hGc hG (hbG t ht)]
  have hchart := planeMaterialDual_pairing hφ t s ν
    (fun r x => v r x - streamVel φ r x) hsc (add_nonneg hM hW) hsb
    hcc hC hcb hGc hG (hbG t ht) u z F
  have hsub := planeWeakDual_transport_sub_pair (v t) (streamVel φ t) hvc hwc hsc
    hM hW (add_nonneg hM hW) hvb hwb hsb
    (ν • ContinuousLinearMap.id ℝ (PlaneFluxL2 E)) u z F
  rw [planeScalarTransport_inner_eq_integral] at hsub
  exact hchart.trans hsub

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The pointwise molecular certificate supplies the actual physical coefficient
regularity and measurability needed to transfer its coupled solution. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem preparation_physical_coefficient_pointwise_data
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (hρe : ρ ≤ e)
    (heE : e ≤ ocEpsilon q Λ (m - 1)) (K : ι → ℕ) (Kmax Jm : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (hchart : Kmax + D + 2 ≤ Jchart)
    (hmol : Kmax + D + 2 ≤ Jm) (Cm : ℕ → ℝ)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (actual : ∀ p, Ctx p)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (B : ι → ι → ℝ) (hB : ∀ v u, 0 ≤ B v u)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc a b))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B)
    :
    F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b))
      (ocEpsilon q Λ (m - 1)) K ∧
    (∀ v u d, coefficientSeminorm ρ (K v) a b
      (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K v u d) ≠ ⊤) ∧
    (∀ v u d t, t ∈ Set.Icc a b → ContDiff ℝ (K v : ℕ)
      (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K v u d t)) ∧
    (∀ v u d, Measurable (fun p : Set.Icc a b × Vec 2 =>
      edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K v u d p.1 p.2)) := by
  obtain ⟨Cprep, _, hsamp⟩ := preparation_sampled_envelope_of_pointwise_certificate
    D Kmax Jchart Jm hchart hmol Cm Cchart
  have hsample := hsamp α q Λ m φ hφ a b Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    F π hπ K hK actual B hB hc henv
  have hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b))
      (ocEpsilon q Λ (m - 1)) K := by
    intro p c v u γ d I tY htY z
    exact (henv.1 p c v u γ d I tY htY z).of_le
      (by exact_mod_cast Nat.le_add_right (K v) Jm)
  refine ⟨hs, ?_, ?_, ?_⟩
  · exact sampledEnvelope_edge_seminorm_ne_top F π hπ K actual
      a b ν e (ocEpsilon q Λ (m - 1)) ρ Cprep hν hρ B hsample
  · intro v u d t ht
    exact edgeCoefficient_spatial_smooth F hc ν e (ocEpsilon q Λ (m - 1)) K hs actual K v u d t ht
  · exact edgeCoefficient_joint_measurable F hc ν e (ocEpsilon q Λ (m - 1)) K hs
      hmeas hwmeas actual K

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Actual windowed higher material states and their lower native traces have identical stored truncations. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHkWindowChartPull_truncate {K L : ℕ} (hKL : K ≤ L) (a b : ℝ)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ L → 0 ≤ B j)
    (hb : ∀ t ∈ Icc a b, ∀ j, 1 ≤ j → j ≤ L → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => AVRegularity.streamFlow φ hφ t y s) x‖ ≤ B j)
    (t : ℝ) (ht : t ∈ Icc a b) (U : PlaneHk univ L E) :
    truncatePlaneHk hKL (planeHkWindowChartPull a b hφ s B hB hb t U) =
      planeHkWindowChartPull a b hφ s B (fun j hj hjK => hB j hj (hjK.trans hKL))
        (fun r hr j hj hjK => hb r hr j hj (hjK.trans hKL)) t (truncatePlaneHk hKL U) := by
  unfold planeHkWindowChartPull
  simp only [dite_eq_left ht]
  exact planeHkSmoothPullback_truncate hKL (CycleReference.streamFlowHomeomorph hφ t s)
    (CycleReference.streamFlow_spatial_smooth hφ t s)
    (CycleReference.streamFlow_measurePreserving hφ t s) B hB (hb t ht) U

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Higher native material carriers agree exactly with the H1 chart carriers in the weak equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHkWindowChartPull_h1 {K : ℕ} (hK : 1 ≤ K) (a b : ℝ)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ t ∈ Icc a b, ∀ j, 1 ≤ j → j ≤ K → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => AVRegularity.streamFlow φ hφ t y s) x‖ ≤ B j)
    (t : ℝ) (ht : t ∈ Icc a b) (U : PlaneHk univ K E) :
    truncatePlaneHk hK (planeHkWindowChartPull a b hφ s B hB hb t U) =
      planeH1ChartPull hφ t s (truncatePlaneHk hK U) := by
  apply planeHk_eq_of_value
  rw [planeHkValueOperator_truncate, planeHkWindowChartPull_value_eq a b hφ s B hB hb t ht,
    planeH1ChartPull_value_eq, planeHkValueOperator_truncate]
  rfl

end AVRegularity.CycleJointProofs
end
end
