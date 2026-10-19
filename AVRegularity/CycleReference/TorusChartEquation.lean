-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleReference.TorusStreamFluxEquation
import AVRegularity.CycleReference.ChartCorrectionIntegrability
import AVRegularity.CycleReference.MeanEnhancementScale
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.OcRhoMol
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Velocity.IncrementProvider
import AVenhance.Infra.Classical.Drift
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Reverse transport of the weak equation, with no regularity hypotheses on the forcing. -/

theorem chartWeakEquation_reverse {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s ν a c : ℝ)
    (b q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ)
    (Dθ : ℝ → Vec 2 → Vec 2) (hspace : PlaneEnergySpace a c θ₀ θ Dθ)
    (hweak : PlaneWeakEquation (chartVector hφ s (fun t x => b t x - streamVel φ t x))
      (fun t y => ν • chartMetric hφ s t y) a c (chartVector hφ s q) (chartPull hφ s f)
      (fun y => θ₀ (AVRegularity.streamFlow φ hφ a y s)) (chartPull hφ s θ) (chartGradient hφ s Dθ)) :
    PlaneWeakEquation b (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a c q f θ₀ θ Dθ := by
  intro η hη hcη hzη
  let ζ := chartPull hφ s η
  have hζ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ζ p.1 p.2) :=
    streamFlow_test_smooth hφ s hη
  have hcζ : HasCompactSupport (fun p : ℝ × Vec 2 => ζ p.1 p.2) :=
    streamFlow_test_compact hφ s hcη
  have hzζ : ∀ t, c ≤ t → ∀ x, ζ t x = 0 := fun t ht x => hzη t ht _
  have hI := fun η hη hcη hzη => (hweak η hη hcη hzη).1
  have hi := chart_drift_correction_integrable_from_pulled_tests hφ s a c
    (chartVector hφ s (fun t x => b t x - streamVel φ t x))
    (fun t y => ν • chartMetric hφ s t y) (chartVector hφ s q) (chartPull hφ s f) θ
    (chartGradient hφ s Dθ) hI η hη hcη hzη
  have ht := chart_test_transport_of_drift_correction_integrable hφ s ν a c b q f θ Dθ
    hspace.1 hspace.2.2.2.1 hspace.2.2.2.2 η hη hcη hi
  obtain ⟨him, hem⟩ := hweak ζ hζ hcζ hzζ
  have hip := ht.1.mp him
  refine ⟨hip, (ht.2 hip).symm.trans (hem.trans ?_)⟩
  exact integral_streamFlow hφ a s (fun x => θ₀ x * η a x)

/-! Equivalence of plane energy solutions under a smooth material flow chart. -/

theorem isPlaneEnergySolution_chart_drift_equiv {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s ν a c : ℝ)
    (b q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ) :
    IsPlaneEnergySolution b (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a c q f θ₀ θ ↔
    IsPlaneEnergySolution (chartVector hφ s (fun t x => b t x - streamVel φ t x))
      (fun t y => ν • chartMetric hφ s t y) a c (chartVector hφ s q) (chartPull hφ s f)
      (fun y => θ₀ (AVRegularity.streamFlow φ hφ a y s)) (chartPull hφ s θ) := by
  rw [isPlaneEnergySolution_iff_energySpace_weakEquation,
    isPlaneEnergySolution_iff_energySpace_weakEquation]
  constructor
  · rintro ⟨D, hs, hw⟩
    exact ⟨chartGradient hφ s D, chartPull_energySpace hφ s a c hs,
      chartPull_weakEquation hφ s ν a c b q f θ θ₀ D hs hw⟩
  · rintro ⟨Dm, hs, hw⟩
    let D := chartUnpullGradient hφ s Dm
    have hsp := chartUnpull_energySpace hφ s a c hs
    have hi0 : (fun x => θ₀ (AVRegularity.streamFlow φ hφ a
        (AVRegularity.streamFlow φ hφ s x a) s)) = θ₀ := by
      funext x
      exact congrArg θ₀ ((streamFlowHomeomorph hφ a s).right_inv x)
    rw [chartUnpull_chartPull, hi0] at hsp
    have hD : chartGradient hφ s D = Dm := chartGradient_chartUnpullGradient hφ s Dm
    refine ⟨D, hsp, chartWeakEquation_reverse hφ s ν a c b q f θ θ₀ D hsp ?_⟩
    rw [hD]
    exact hw

end AVRegularity.CycleReference
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Exact transport of the complete periodic tested integrand. -/

 theorem admissible_streamVel_periodic {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t : ℝ) : IsZ2Periodic (streamVel φ t) := by
  intro k x
  simpa using (Infra.Construction.smoothPeriodic_streamVel hφ).periodic 0 k t x

 theorem chartPull_periodic {E : Type*} {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) {u : ℝ → Vec 2 → E}
    (hp : ∀ t, IsZ2Periodic (u t)) (t : ℝ) : IsZ2Periodic (chartPull hφ s u t) := by
  intro k x
  change u t (AVRegularity.streamFlow φ hφ t (x + latticeShift k) s) = _
  rw [streamFlow_lattice_equivariant, hp t k]
  rfl

 theorem chartUnpull_periodic {E : Type*} {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) {u : ℝ → Vec 2 → E}
    (hp : ∀ t, IsZ2Periodic (u t)) (t : ℝ) : IsZ2Periodic (chartUnpull hφ s u t) := by
  intro k x
  change u t (AVRegularity.streamFlow φ hφ s (x + latticeShift k) t) = _
  rw [streamFlow_lattice_equivariant, hp t k]
  rfl

 theorem chartVector_periodic {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) {u : ℝ → Vec 2 → Vec 2}
    (hp : ∀ t, IsZ2Periodic (u t)) (t : ℝ) : IsZ2Periodic (chartVector hφ s u t) := by
  intro k x
  unfold chartVector chartJac chartPull
  rw [streamFlow_jacMatrix_spatial_periodic, streamFlow_lattice_equivariant, hp t k]

 theorem chartPull_windowTest {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s c : ℝ) {η : ℝ → Vec 2 → ℝ}
    (hη : IsWindowTestFunction c η) : IsWindowTestFunction c (chartPull hφ s η) :=
  ⟨streamFlow_test_smooth hφ s hη.1, chartPull_periodic hφ s hη.2.1,
    fun t ht _x => hη.2.2 t ht _⟩

 theorem chartUnpull_windowTest {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s c : ℝ) {η : ℝ → Vec 2 → ℝ}
    (hη : IsWindowTestFunction c η) : IsWindowTestFunction c (chartUnpull hφ s η) :=
  ⟨inverseStreamFlow_test_smooth hφ s hη.1, chartUnpull_periodic hφ s hη.2.1,
    fun t ht _x => hη.2.2 t ht _⟩

 theorem planeWeakIntegrand_periodic
    (b q : ℝ → Vec 2 → Vec 2) (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (f θ η : ℝ → Vec 2 → ℝ) (D : ℝ → Vec 2 → Vec 2)
    (hpb : ∀ t, IsZ2Periodic (b t)) (hpq : ∀ t, IsZ2Periodic (q t))
    (hpA : ∀ t, IsZ2Periodic (A t)) (hpf : ∀ t, IsZ2Periodic (f t))
    (hpη : ∀ t, IsZ2Periodic (η t)) (t : ℝ)
    (hpθ : IsZ2Periodic (θ t)) (hpD : IsZ2Periodic (D t)) :
    IsZ2Periodic (fun x => planeWeakIntegrand b A q f θ D η (t, x)) := by
  intro k x
  dsimp only [planeWeakIntegrand]
  have ht : deriv (fun r => η r (x + latticeShift k)) t = deriv (fun r => η r x) t :=
    timeDeriv_periodic hpη t k x
  rw [hpθ k x, ht, hpb t k x, hpD k x, hpη t k x,
    hpA t k x, spaceGrad_periodic (hpη t) k x, hpq t k x, hpf t k x]

 theorem torus_chart_test_transport {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s ν a c : ℝ)
    (b q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ) (Dθ : ℝ → Vec 2 → Vec 2)
    (hpb : ∀ t, IsZ2Periodic (b t)) (hpq : ∀ t, IsZ2Periodic (q t))
    (hpf : ∀ t, IsZ2Periodic (f t))
    (hDu : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)))
    (hw : ∀ᵐ t ∂(volume.restrict (Set.Ioo a c)), IsPeriodicH1With (θ t) (Dθ t))
    (η : ℝ → Vec 2 → ℝ) (hη : IsWindowTestFunction c η)
    (hi : Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 * Homogenization.vecDot (streamVel φ p.1 p.2)
      (spaceGrad (η p.1) p.2)) (volume.restrict (Set.Ioo a c ×ˢ unitCube))) :
    let Ip := planeWeakIntegrand b (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) q f θ Dθ η
    let Im := planeWeakIntegrand (chartVector hφ s (fun t x => b t x - streamVel φ t x))
      (fun t y => ν • chartMetric hφ s t y) (chartVector hφ s q)
      (chartPull hφ s f) (chartPull hφ s θ) (chartGradient hφ s Dθ) (chartPull hφ s η)
    (Integrable Im (volume.restrict (Set.Ioo a c ×ˢ unitCube)) ↔
      Integrable Ip (volume.restrict (Set.Ioo a c ×ˢ unitCube))) ∧
    (Integrable Ip (volume.restrict (Set.Ioo a c ×ˢ unitCube)) →
      (∫ p in Set.Ioo a c ×ˢ unitCube, Im p) = ∫ p in Set.Ioo a c ×ˢ unitCube, Ip p) := by
  dsimp only
  let μ : Measure (ℝ × Vec 2) := volume.restrict (Set.Ioo a c ×ˢ unitCube)
  let X := streamFlowTimeHomeomorph hφ s
  let Ip := planeWeakIntegrand b (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) q f θ Dθ η
  let Im := planeWeakIntegrand (chartVector hφ s (fun t x => b t x - streamVel φ t x))
    (fun t y => ν • chartMetric hφ s t y) (chartVector hφ s q)
    (chartPull hφ s f) (chartPull hφ s θ) (chartGradient hφ s Dθ) (chartPull hφ s η)
  let K := fun p : ℝ × Vec 2 => θ p.1 p.2 * Homogenization.vecDot (streamVel φ p.1 p.2)
    (spaceGrad (η p.1) p.2) + Homogenization.vecDot (streamVel φ p.1 p.2) (Dθ p.1 p.2) * η p.1 p.2
  obtain ⟨hd, he⟩ := cellSlab_divFree_drift_pairing a c hDu hw
    (Infra.Construction.smoothPeriodic_streamVel hφ).smooth
    (admissible_streamVel_periodic hφ) (Infra.Classical.streamVel_vecDiv_eq_zero φ hφ)
    hη.1 hη.2.1 hi
  have hK : Integrable K μ := hi.add hd
  have hK0 : ∫ p, K p ∂μ = 0 := by
    rw [integral_add hi hd, he]
    ring
  have hpK : ∀ᵐ t ∂(volume.restrict (Set.Ioo a c)), IsZ2Periodic (fun x => K (t, x)) := by
    filter_upwards [hw] with t ht
    intro k x
    dsimp [K]
    rw [ht.1 k x, admissible_streamVel_periodic hφ t k x,
      spaceGrad_periodic (hη.2.1 t) k x, ht.2.1 k x, hη.2.1 t k x]
  have htK := cellSlab_chart_transport_ae hφ s a c K hpK
  have hKX : Integrable (K ∘ X) μ := htK.1.mpr hK
  have hKX0 : ∫ p, K (X p) ∂μ = 0 := htK.2.trans hK0
  have hp : Im = (Ip ∘ X) - (K ∘ X) := by
    funext p
    exact planeWeakIntegrand_chart_pullback hφ s ν b q f θ Dθ η hη.1 p.1 p.2
  have hpIp : ∀ᵐ t ∂(volume.restrict (Set.Ioo a c)), IsZ2Periodic (fun x => Ip (t, x)) :=
    hw.mono (fun t ht => planeWeakIntegrand_periodic b q _ f θ η Dθ hpb hpq
      (fun _ _ _ => rfl) hpf hη.2.1 t ht.1 ht.2.1)
  have htIp := cellSlab_chart_transport_ae hφ s a c Ip hpIp
  have hiff : Integrable (Ip ∘ X) μ ↔ Integrable Ip μ := htIp.1
  change (Integrable Im μ ↔ Integrable Ip μ) ∧ (Integrable Ip μ → _)
  constructor
  · constructor
    · intro him
      apply hiff.mp
      have he : Ip ∘ X = Im + (K ∘ X) := by rw [hp]; abel
      rw [he]
      exact him.add hKX
    · intro hip
      rw [hp]
      exact (hiff.mpr hip).sub hKX
  · intro hip
    change (∫ p, Im p ∂μ) = ∫ p, Ip p ∂μ
    rw [hp]
    simp only [Pi.sub_apply]
    rw [integral_sub (hiff.mpr hip) hKX]
    change (∫ p, Ip (X p) ∂μ) - (∫ p, K (X p) ∂μ) = _
    rw [hKX0, sub_zero]
    exact htIp.2

/-! Forward and reverse transport of the periodic weak equation. -/

 theorem torus_chart_drift_correction_from_pulled_tests
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s a c : ℝ)
    (bm : ℝ → Vec 2 → Vec 2) (Am : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (qm : ℝ → Vec 2 → Vec 2) (fm θ : ℝ → Vec 2 → ℝ) (Dm : ℝ → Vec 2 → Vec 2)
    (hpθ : ∀ᵐ t ∂(volume.restrict (Set.Ioo a c)), IsZ2Periodic (θ t))
    (hI : ∀ ζ : ℝ → Vec 2 → ℝ, IsWindowTestFunction c ζ →
      Integrable (planeWeakIntegrand bm Am qm fm (chartPull hφ s θ) Dm ζ)
        (volume.restrict (Set.Ioo a c ×ˢ unitCube)))
    (η : ℝ → Vec 2 → ℝ) (hη : IsWindowTestFunction c η) :
    Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 * Homogenization.vecDot (streamVel φ p.1 p.2)
      (spaceGrad (η p.1) p.2)) (volume.restrict (Set.Ioo a c ×ˢ unitCube)) := by
  let ζ := chartPull hφ s η
  have hζ := chartPull_windowTest hφ s c hη
  have hi := torus_tested_integrability_implies_drift_correction_integrability bm Am qm fm
    (chartPull hφ s θ) Dm a c hI (chartVector hφ s (streamVel φ))
    (chartVector_joint_smooth hφ s (Infra.Construction.smoothPeriodic_streamVel hφ).smooth)
    (chartVector_periodic hφ s (admissible_streamVel_periodic hφ)) ζ hζ
  let X := streamFlowTimeHomeomorph hφ s
  let g := fun p : ℝ × Vec 2 => θ p.1 p.2 * Homogenization.vecDot (streamVel φ p.1 p.2)
    (spaceGrad (η p.1) p.2)
  have he : g ∘ X = (fun p : ℝ × Vec 2 => chartPull hφ s θ p.1 p.2 *
      Homogenization.vecDot (chartVector hφ s (streamVel φ) p.1 p.2) (spaceGrad (ζ p.1) p.2)) := by
    funext p
    have hs : DifferentiableAt ℝ (η p.1) (AVRegularity.streamFlow φ hφ p.1 p.2 s) :=
      (hη.1.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) _
    have hg := spaceGrad_comp_jacMatrix hs
      ((streamFlow_spatial_smooth hφ p.1 s).differentiable (by simp) p.2)
    change θ p.1 _ * Homogenization.vecDot _ _ = θ p.1 _ * Homogenization.vecDot _ _
    congr 1
    change Homogenization.vecDot _ _ = Homogenization.vecDot
      ((chartJac hφ s p.1 p.2)⁻¹.mulVec _) (spaceGrad
      (fun x => η p.1 (AVRegularity.streamFlow φ hφ p.1 x s)) p.2)
    rw [hg]
    exact (inverse_pullback_pairing _ (by
      rw [chartJac, streamFlow_jacMatrix_det_one hφ]; exact isUnit_one) _ _).symm
  rw [← he] at hi
  have hpg : ∀ᵐ t ∂(volume.restrict (Set.Ioo a c)), IsZ2Periodic (fun x => g (t, x)) := by
    filter_upwards [hpθ] with t ht
    intro k x
    dsimp [g]
    rw [ht k x, admissible_streamVel_periodic hφ t k x,
      spaceGrad_periodic (hη.2.1 t) k x]
  exact (cellSlab_chart_transport_ae hφ s a c g hpg).1.mp hi

 theorem chartPull_torusWeakEquation {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s ν a c : ℝ)
    (b q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ)
    (hpb : ∀ t, IsZ2Periodic (b t)) (hpq : ∀ t, IsZ2Periodic (q t))
    (hpf : ∀ t, IsZ2Periodic (f t)) (hp₀ : IsZ2Periodic θ₀)
    (Dθ : ℝ → Vec 2 → Vec 2) (hspace : TorusEnergySpace a c θ₀ θ Dθ)
    (hweak : TorusWeakEquation b (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a c q f θ₀ θ Dθ) :
    TorusWeakEquation (chartVector hφ s (fun t x => b t x - streamVel φ t x))
      (fun t y => ν • chartMetric hφ s t y) a c (chartVector hφ s q) (chartPull hφ s f)
      (fun y => θ₀ (AVRegularity.streamFlow φ hφ a y s)) (chartPull hφ s θ) (chartGradient hφ s Dθ) := by
  intro ζ hζ
  let η := chartUnpull hφ s ζ
  have hη : IsWindowTestFunction c η := chartUnpull_windowTest hφ s c hζ
  have hi := torus_tested_integrability_implies_drift_correction_integrability b
    (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) q f θ Dθ a c
    (fun η hη => (hweak η hη).1) (streamVel φ)
    (Infra.Construction.smoothPeriodic_streamVel hφ).smooth
    (admissible_streamVel_periodic hφ) η hη
  have ht := torus_chart_test_transport hφ s ν a c b q f θ Dθ hpb hpq hpf
    hspace.2.2.2.1 hspace.2.2.2.2 η hη hi
  obtain ⟨hip, hep⟩ := hweak η hη
  have hm := ht.1.mpr hip
  have he := (ht.2 hip).trans hep
  have hp : chartPull hφ s η = ζ := chartPull_chartUnpull hφ s ζ
  rw [hp] at hm he
  refine ⟨hm, he.trans ?_⟩
  symm
  calc
    (∫ y in unitCube, θ₀ (AVRegularity.streamFlow φ hφ a y s) * ζ a y) =
        ∫ y in unitCube, θ₀ (AVRegularity.streamFlow φ hφ a y s) *
          η a (AVRegularity.streamFlow φ hφ a y s) := by
      rw [← hp]
      rfl
    _ = ∫ x in unitCube, θ₀ x * η a x := streamFlow_cell_integral hφ a s (fun x => θ₀ x * η a x)
      (fun k x => by dsimp only; rw [hp₀ k x, hη.2.1 a k x])

 theorem torus_chartWeakEquation_reverse {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s ν a c : ℝ)
    (b q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ)
    (hpb : ∀ t, IsZ2Periodic (b t)) (hpq : ∀ t, IsZ2Periodic (q t))
    (hpf : ∀ t, IsZ2Periodic (f t)) (hp₀ : IsZ2Periodic θ₀)
    (Dθ : ℝ → Vec 2 → Vec 2) (hspace : TorusEnergySpace a c θ₀ θ Dθ)
    (hweak : TorusWeakEquation (chartVector hφ s (fun t x => b t x - streamVel φ t x))
      (fun t y => ν • chartMetric hφ s t y) a c (chartVector hφ s q) (chartPull hφ s f)
      (fun y => θ₀ (AVRegularity.streamFlow φ hφ a y s)) (chartPull hφ s θ) (chartGradient hφ s Dθ)) :
    TorusWeakEquation b (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a c q f θ₀ θ Dθ := by
  intro η hη
  let ζ := chartPull hφ s η
  have hζ := chartPull_windowTest hφ s c hη
  have hi := torus_chart_drift_correction_from_pulled_tests hφ s a c
    (chartVector hφ s (fun t x => b t x - streamVel φ t x))
    (fun t y => ν • chartMetric hφ s t y) (chartVector hφ s q) (chartPull hφ s f) θ
    (chartGradient hφ s Dθ) (hspace.2.2.2.2.mono (fun _ ht => ht.1))
    (fun η hη => (hweak η hη).1) η hη
  have ht := torus_chart_test_transport hφ s ν a c b q f θ Dθ hpb hpq hpf
    hspace.2.2.2.1 hspace.2.2.2.2 η hη hi
  obtain ⟨him, hem⟩ := hweak ζ hζ
  have hip := ht.1.mp him
  refine ⟨hip, (ht.2 hip).symm.trans (hem.trans ?_)⟩
  exact streamFlow_cell_integral hφ a s (fun x => θ₀ x * η a x)
    (fun k x => by dsimp only; rw [hp₀ k x, hη.2.1 a k x])

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Equivalence of plane energy solutions under a smooth material flow chart. -/

theorem isTorusEnergySolution_chart_drift_equiv {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s ν a c : ℝ)
    (b q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ) (hac : a ≤ c)
    (hpb : ∀ t, IsZ2Periodic (b t)) (hpq : ∀ t, IsZ2Periodic (q t))
    (hpf : ∀ t, IsZ2Periodic (f t)) (hp₀ : IsZ2Periodic θ₀) :
    IsTorusEnergySolution b (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a c q f θ₀ θ ↔
    IsTorusEnergySolution (chartVector hφ s (fun t x => b t x - streamVel φ t x))
      (fun t y => ν • chartMetric hφ s t y) a c (chartVector hφ s q) (chartPull hφ s f)
      (fun y => θ₀ (AVRegularity.streamFlow φ hφ a y s)) (chartPull hφ s θ) := by
  rw [isTorusEnergySolution_iff_energySpace_weakEquation,
    isTorusEnergySolution_iff_energySpace_weakEquation]
  constructor
  · rintro ⟨D, hs, hw⟩
    exact ⟨chartGradient hφ s D, chartPull_torusEnergySpace hφ s a c hac hp₀ hs,
      chartPull_torusWeakEquation hφ s ν a c b q f θ θ₀ hpb hpq hpf hp₀ D hs hw⟩
  · rintro ⟨Dm, hs, hw⟩
    let D := chartUnpullGradient hφ s Dm
    have hpinit : IsZ2Periodic (fun y => θ₀ (AVRegularity.streamFlow φ hφ a y s)) := by
      intro k x
      dsimp only
      rw [streamFlow_lattice_equivariant, hp₀ k]
    have hsp := chartUnpull_torusEnergySpace hφ s a c hac hpinit hs
    have hi0 : (fun x => θ₀ (AVRegularity.streamFlow φ hφ a
        (AVRegularity.streamFlow φ hφ s x a) s)) = θ₀ := by
      funext x
      exact congrArg θ₀ ((streamFlowHomeomorph hφ a s).right_inv x)
    rw [chartUnpull_chartPull, hi0] at hsp
    have hD : chartGradient hφ s D = Dm := chartGradient_chartUnpullGradient hφ s Dm
    refine ⟨D, hsp, torus_chartWeakEquation_reverse hφ s ν a c b q f θ θ₀ hpb hpq hpf hp₀ D hsp ?_⟩
    rw [hD]
    exact hw

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! One common constant and separation threshold for the complete diffusivity and covariance ledger. -/

theorem bandChain_uniform_ledger {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        (∀ m : ℕ, 1 ≤ m → m < M →
          ocAsymp C (κ m) (ocEpsilon q Λ m ^ ((1 + α) + ocGamma α q))) ∧
        (∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
          ν ≤ B ∧
          ocAsymp C B (ocEpsilon q Λ (m - 1) ^ ((1 + α) + ocGamma α q)) ∧
          ocAsymp C B (ocEpsilon q Λ m ^ ((1 + α) - ocGamma α q)) ∧
          ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B ∧
          ocAsymp C (ocRh α q Λ m B) (ocEpsilon q Λ (m - 1) ^ (1 + ocC α q)) ∧
          ocDStar q Λ m ν B / ocEpsilon q Λ (m - 1) ≤ C * ocEpsilon q Λ (m - 1) ^ (ocGamma α q / 2 + 4 * ocDelta α q) ∧
          ocDStar q Λ m ν B / ocRhoPar α q Λ m ≤ C * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) ∧
          ocDStar q Λ m ν B / (ocRh α q Λ m B) ≤ C * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q) ∧
          ocAsymp C (ocEpsilon q Λ m / (ocRh α q Λ m B)) (ocEpsilon q Λ (m - 1) ^ (q * ocGamma α q + 3 * ocDelta α q)) ∧
          ocEll q Λ m ν ^ 2 / ocTau α q Λ m ≤ C * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) ∧
          C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-(6 * ocDelta α q)) ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 ∧
          Real.sqrt (B / ν) ≤ C * ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q)) ∧
          ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤ C * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) ∧
          (m < M →
            ocAsymp C (ocDStar q Λ m ν B / ocEpsilon q Λ (m - 1)) (ocEpsilon q Λ (m - 1) ^ (ocGamma α q / 2 + 4 * ocDelta α q)) ∧
            ocAsymp C (ocDStar q Λ m ν B / ocRhoPar α q Λ m) (ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q)) ∧
            ocAsymp C (ocDStar q Λ m ν B / (ocRh α q Λ m B)) (ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q)) ∧
            ocAsymp C (ocEll q Λ m ν ^ 2 / ocTau α q Λ m) (ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q)) ∧
            ocAsymp C (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) (ocEpsilon q Λ (m - 1) ^ (-(6 * ocDelta α q))) ∧
            ocAsymp C (Real.sqrt (B / ν)) (ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q))) ∧
            ∀ cMol : ℝ, 0 < cMol →
              ocAsymp C (ocRhoMol α q Λ m cMol ν) (cMol * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2)) ∧
              ocRhoMol α q Λ m cMol ν / ocEpsilon q Λ m ^ (1 + ocC α q)
                ≤ C * cMol * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))) ∧
          (m = M → B / ν ≤ C) ∧
          (∀ s t : ℝ, ∀ i j : Fin 2,
            |ocCovariance α q Λ ζ m ν B s t i j| ≤ C * B * ocTauP α q Λ m ∧
            |ocCovariance α q Λ ζ m ν B s t i j| / ocEpsilon q Λ (m - 1) ^ 2 ≤ C * ocEpsilon q Λ (m - 1) ^ (ocGamma α q + 3 * ocDelta α q) ∧
            |ocCovariance α q Λ ζ m ν B s t i j| / ocRhoPar α q Λ m ^ 2 + ocA α q Λ (m - 1) * |ocCovariance α q Λ ζ m ν B s t i j| / B ≤ C * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q) ∧
            |ocCovariance α q Λ ζ m ν B s t i j| / (ocRh α q Λ m B) ^ 2 ≤ C * ocEpsilon q Λ (m - 1) ^ ocDelta α q)) := by
  obtain ⟨Ci, hCi, Li, hLi, hi⟩ := bandChain_interior_diffusivities hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cp, hCp, Lp, hLp, hp⟩ := bandChain_parent_comparisons hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Ce, hCe, Le, hLe, he⟩ := bandChain_enhancement_bound hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cr, hCr, Lr, hLr, hr⟩ := bandChain_renewal_radius hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cd, hCd, Ld, hLd, hd⟩ := bandChain_cell_length hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cf, hCf, Lf, hLf, hf⟩ := bandChain_prepared_cell_length hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Ct, hCt, Lt, hLt, ht⟩ := bandChain_fine_renewal_ratio hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cm, hCm, Lm, hLm, hm⟩ := bandChain_memory_scale hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Ch, hCh, Lh, hLh, hh⟩ := bandChain_renewal_relaxation hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cc, hCc, Lc, hLc, hc⟩ := bandChain_contrast_bounds hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cmol, hCmol, Lmol, hLmol, hmol⟩ := bandChain_molecular_radius hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cv, hCv, Lv, hLv, hv⟩ := bandChain_covariance_estimates hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨C, hC, hCs⟩ := exists_common_constant [Ci, Cp, Ce, Cr, Cd, Cf, Ct, Cm, Ch, Cc, Cmol, Cv]
  have hCpos : 0 < C := by linarith only [hC]
  have hCiC : Ci ≤ C := hCs Ci (by simp)
  have hCpC : Cp ≤ C := hCs Cp (by simp)
  have hCeC : Ce ≤ C := hCs Ce (by simp)
  have hCrC : Cr ≤ C := hCs Cr (by simp)
  have hCdC : Cd ≤ C := hCs Cd (by simp)
  have hCfC : Cf ≤ C := hCs Cf (by simp)
  have hCtC : Ct ≤ C := hCs Ct (by simp)
  have hCmC : Cm ≤ C := hCs Cm (by simp)
  have hChC : Ch ≤ C := hCs Ch (by simp)
  have hCcC : Cc ≤ C := hCs Cc (by simp)
  have hCmolC : Cmol ≤ C := hCs Cmol (by simp)
  have hCvC : Cv ≤ C := hCs Cv (by simp)
  refine ⟨C, hC, max Li (max Lp (max Le (max Lr (max Ld (max Lf (max Lt (max Lm (max Lh (max Lc (max Lmol (Lv))))))))))), hLi.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM κ hκ
  have hΛi : Li ≤ Λ := (le_max_left _ _).trans (hΛ)
  have hΛp : Lp ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans (hΛ))
  have hΛe : Le ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hΛ)))
  have hΛr : Lr ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hΛ))))
  have hΛd : Ld ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hΛ)))))
  have hΛf : Lf ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hΛ))))))
  have hΛt : Lt ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hΛ)))))))
  have hΛm : Lm ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hΛ))))))))
  have hΛh : Lh ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hΛ)))))))))
  have hΛc : Lc ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hΛ))))))))))
  have hΛmol : Lmol ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hΛ)))))))))))
  have hΛv : Lv ≤ Λ := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hΛ)))))))))))
  clear hΛ
  have h128 : 128 ≤ Λ := hLi.trans hΛi
  have hΛ1 : 1 ≤ Λ := by omega
  have up {D x y : ℝ} (hDC : D ≤ C) (hy : 0 ≤ y) (hx : x ≤ D * y) : x ≤ C * y :=
    hx.trans (mul_le_mul_of_nonneg_right hDC hy)
  have ax {D x y : ℝ} (hD : 1 ≤ D) (hDC : D ≤ C) (hy : 0 ≤ y)
      (hx : ocAsymp D x y) : ocAsymp C x y :=
    asymp_mono_constant (by linarith) hDC hy hx
  constructor
  · intro m hm2 hmM
    exact ax hCi hCiC (Real.rpow_pos_of_pos
      (AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128).1 _).le
      (hi Λ hΛi M hM κ hκ m hm2 hmM)
  · intro m hm2 hmM ν B hν hB
    subst ν
    subst B
    have hE := (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1
    have heps := (AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128).1
    have hpow (p : ℝ) : 0 ≤ ocEpsilon q Λ (m - 1) ^ p := (Real.rpow_pos_of_pos hE p).le
    have hBp := bandChain_pos hΛ1 hζ hκ (show m - 1 ≤ M by omega)
    have hpm := hp Λ hΛp M hM κ hκ m hm2 hmM
    have hem := he Λ hΛe M hM κ hκ m hm2 hmM
    have hrm := hr Λ hΛr M hM κ hκ m hm2 hmM
    have hdm := hd Λ hΛd M hM κ hκ m hm2 hmM
    have hfm := hf Λ hΛf M hM κ hκ m hm2 hmM
    have htm := ht Λ hΛt M hM κ hκ m hm2 hmM
    have hmm := hm Λ hΛm M hM κ hκ m hm2 hmM
    have hhm := hh Λ hΛh M hM κ hκ m hm2 hmM
    have hcm := hc Λ hΛc M hM κ hκ m hm2 hmM
    refine ⟨bandChain_step_ge hΛ1 hζ hκ (by omega) hmM,
      ax hCp hCpC (hpow _) hpm.1,
      ax hCp hCpC (Real.rpow_pos_of_pos heps _).le hpm.2,
      up hCeC hBp.le hem,
      ax hCr hCrC (hpow _) hrm,
      up hCdC (hpow _) hdm.1,
      up hCfC (hpow _) hfm.1,
      up hCfC (hpow _) hfm.2.1,
      ax hCt hCtC (hpow _) htm,
      up hCmC (hpow _) hmm.1,
      ?_, up hCcC (hpow _) hcm.1, ?_, ?_, ?_, ?_⟩
    · exact (mul_le_mul_of_nonneg_right
        ((inv_le_inv₀ hCpos (by linarith : 0 < Ch)).2 hChC) (hpow _)).trans hhm.1
    · exact up hC (hpow _) (by simpa only [one_mul] using
        parent_renewal_deformation_bound hα0 hα1 hs0 hs1 hq h128 (by omega : 1 ≤ m))
    · intro hlt
      refine ⟨ax hCd hCdC (hpow _) (hdm.2 hlt),
        ax hCf hCfC (hpow _) (hfm.2.2 hlt).1,
        ax hCf hCfC (hpow _) (hfm.2.2 hlt).2,
        ax hCm hCmC (hpow _) (hmm.2 hlt),
        ax hCh hChC (hpow _) (hhm.2 hlt),
        ax hCc hCcC (hpow _) (hcm.2.1 hlt), ?_⟩
      intro cMol hcMol
      have hmolm := hmol Λ hΛmol M hM κ hκ m hm2 hlt cMol hcMol
      refine ⟨ax hCmol hCmolC (mul_nonneg hcMol.le (Real.rpow_pos_of_pos heps _).le) hmolm.1, ?_⟩
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCmolC hcMol.le) (hpow (-(q * ocDelta α q)))
      exact hmolm.2.trans h
    · intro heq
      exact (hcm.2.2 heq).trans hCcC
    · intro u v i j
      have hvm := hv Λ hΛv M hM κ hκ m hm2 hmM u v i j
      refine ⟨?_, up hCvC (hpow _) hvm.2.1,
        up hCvC (hpow _) hvm.2.2.1, up hCvC (hpow _) hvm.2.2.2⟩
      have hP := (AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ1).trans_le
        (pulse_time_scale_relations hΛ1).1
      exact hvm.1.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCvC hBp.le) hP.le)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
open scoped Matrix
namespace AVRegularity.CycleReference

/-! The exact material energy-solution equation on a renewal block. -/

theorem ocChart_energy_solution_iff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsOCStreamSeq α q Λ ζ Φ) (hm : 1 ≤ m)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (ν : ℝ) (l : ℤ) (a c : ℝ)
    (ha : ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ a)
    (hc : c ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m)
    (q' : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ) :
    IsPlaneEnergySolution (streamVel (Φ m))
      (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a c q' f θ₀ θ ↔
    IsPlaneEnergySolution (fun _ _ => 0)
      (fun t y => ν • ocMaterialMetric α q Λ m (Φ (m - 1)) hφ l t y +
        ocPulseStream α q Λ ζ m t y • sigmaMat) a c
      (fun t y => (jacMatrix (ocChart α q Λ m (Φ (m - 1)) hφ l t) y)⁻¹.mulVec
        (q' t (ocChart α q Λ m (Φ (m - 1)) hφ l t y)))
      (fun t y => f t (ocChart α q Λ m (Φ (m - 1)) hφ l t y))
      (fun y => θ₀ (ocChart α q Λ m (Φ (m - 1)) hφ l a y))
      (fun t y => θ t (ocChart α q Λ m (Φ (m - 1)) hφ l t y)) := by
  let s := (l : ℝ) * ocTauPP α q Λ m
  let ψ := chartStreamIncrement hφ s (Φ m)
  have hΦm := AVRegularity.Velocity.streamSeq_admissible hζ hΛ hseq m
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2) :=
    chartStreamIncrement_smooth hφ hΦm s
  have hb : chartVector hφ s (fun t x => streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x) =
      streamVel ψ := by
    funext t y
    exact (chartStreamIncrement_velocity hφ hΦm s t y).symm
  have ht := isPlaneEnergySolution_chart_drift_equiv hφ s ν a c (streamVel (Φ m)) q' f θ θ₀
  rw [hb] at ht
  have hf := isPlaneEnergySolution_stream_flux_iff a c ψ hψ (fun t y => ν • chartMetric hφ s t y)
    (chartVector hφ s q') (chartPull hφ s f) (chartPull hφ s θ)
    (fun y => θ₀ (AVRegularity.streamFlow (Φ (m - 1)) hφ a y s))
  have hp (t : ℝ) (ht : t ∈ Set.Ioo a c) (y : Vec 2) : ψ t y = ocPulseStream α q Λ ζ m t y :=
    chartStreamIncrement_eq_ocPulseStream (by omega) hseq hm hφ l t
      ⟨ha.trans ht.1.le, ht.2.le.trans hc⟩ y
  have he := isPlaneEnergySolution_coefficients_congr a c (fun _ _ => (0 : Vec 2)) (fun _ _ => 0)
    (fun t y => ν • chartMetric hφ s t y + ψ t y • sigmaMat)
    (fun t y => ν • chartMetric hφ s t y + ocPulseStream α q Λ ζ m t y • sigmaMat)
    (fun _ _ _ => rfl) (fun t ht y => by rw [hp t ht y])
    (chartVector hφ s q') (chartPull hφ s f) (chartPull hφ s θ)
    (fun y => θ₀ (AVRegularity.streamFlow (Φ (m - 1)) hφ a y s))
  exact ht.trans (hf.trans he)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Filter Topology Homogenization
namespace AVRegularity.CycleReference

/-! Every fixed derivative order of an isolated corrector becomes smaller than every fixed power. -/

theorem bandChain_quiet_derivatives {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ a b N : ℕ,
      ∃ mStar : ℕ, ∀ M : ℕ, ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → mStar ≤ m → m ≤ M → ∀ k : ℤ, Odd k →
          ∀ t : ℝ, ((k : ℝ) + 3 / 4) * ocTau α q Λ m ≤ t → ∀ y : Vec 2,
            derivArrayNorm (fun x => iteratedDeriv a
              (fun u => ocPulseCorrector α q Λ ζ m (κ m) k u x) t) b y ≤
              ocEpsilon q Λ (m - 1) ^ (N : ℝ) := by
  obtain ⟨C, hC, Ld, hLd, hd⟩ := bandChain_all_level_bounds hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cm, hCm, Lm, hLm, hm⟩ := bandChain_memory_scale hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Lq, hLq, hqpow⟩ := epsilon_power_asymp_shared_threshold hq.1
  have hCp : 0 < C := by linarith only [hC]
  have hCmp : 0 < Cm := by linarith only [hCm]
  let μC := 4 * Real.pi ^ 2 * C
  have hμC : 0 < μC := by dsimp [μC]; positivity
  let p := (1 + α) + ocGamma α q
  let d := 4 * ocDelta α q
  let b0 := 1 / (12 * Cm)
  have hb0 : 0 < b0 := by dsimp [b0]; positivity
  have hd0 : 0 < d := by
    dsimp [d]
    exact mul_pos (by norm_num) (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  have hsmallExponent : 0 ≤ (1 + α) - ocGamma α q := by
    have h := band_exponent_gt_half hα0 hq
    linarith only [h]
  refine ⟨max Ld (max Lm Lq), by omega, ?_⟩
  intro Λ hΛ a b N
  have hΛd : Ld ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛm : Lm ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans hΛ)
  have hΛq : Lq ≤ Λ := (le_max_right _ _).trans ((le_max_right _ _).trans hΛ)
  have h128 := hLd.trans hΛd
  have hΛ1 : 1 ≤ Λ := by omega
  let A := 2 * (a : ℝ) + p + (b : ℝ)
  let K := (2 : ℝ) ^ (b + 1) * μC ^ a * C * (2 * Real.pi) ^ (b + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨Kq, hKq, hpower⟩ := hqpow (-A)
  have hKqp : 0 < Kq := by linarith only [hKq]
  have hevent := exponential_small_scale_eventually
    (fun m => (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1)
    (epsilon_parent_tendsto_zero hq.1 h128) (q * A) (N : ℝ) (K * Kq) b0 d hb0 hd0
  obtain ⟨mStar, hStar⟩ := eventually_atTop.1 hevent
  refine ⟨mStar, ?_⟩
  intro M κ hκ m h2 hstart hmM k hk t ht y
  have hM : 1 ≤ M := by omega
  have hν := bandChain_pos hΛ1 hζ hκ hmM
  have he := AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128
  have hE := AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128
  have hνbounds := hd Λ hΛd M hM κ hκ m (by omega) hmM
  have hνu : κ m ≤ C := hνbounds.2.trans (by
    have h := mul_le_mul_of_nonneg_left (Real.rpow_le_one he.1.le he.2.1 hsmallExponent) hCp.le
    simpa only [mul_one] using h)
  have hμbounds := memory_rate_polynomial_bounds hΛ1 hν hCp he.2.1 hνu hνbounds.1
  have hμ := ocMu_pos (q := q) (m := m) hΛ1 hν
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ1
  have hpre := quiet_derivative_prefactor_bound he.1 he.2.1 hα0.le hμ hCp hμC
    hμbounds.1 hμbounds.2 a b
  change (2 : ℝ) ^ (b + 1) * (ocMu q Λ m (κ m) ^ a * (ocMu q Λ m (κ m))⁻¹ *
    (2 * Real.pi * ocEpsilon q Λ m ^ α) * (2 * Real.pi * (ocEpsilon q Λ m)⁻¹) ^ b) ≤
      K * ocEpsilon q Λ m ^ (-A) at hpre
  have hscale := (hpower Λ m hΛq h2).2
  have hpre' := hpre.trans (mul_le_mul_of_nonneg_left hscale hK.le)
  have hexp := memory_exponential_bound hμ hτ hE.1 hCmp
    ((inverse_memory_rate_time_le hΛ1 hν hτ).trans (hm Λ hΛm M hM κ hκ m h2 hmM).1)
  have hraw := pulseCorrector_quiet_array_bound hΛ1 hζ hν k hk a b t ht y
  have htotal := mul_le_mul hpre' hexp (Real.exp_pos _).le
    (mul_nonneg hK.le (mul_nonneg hKqp.le (Real.rpow_pos_of_pos hE.1 (q * (-A))).le))
  have hfinal : derivArrayNorm (fun x => iteratedDeriv a
      (fun u => ocPulseCorrector α q Λ ζ m (κ m) k u x) t) b y ≤
      (K * Kq) * ocEpsilon q Λ (m - 1) ^ (-(q * A)) *
        Real.exp (-b0 * ocEpsilon q Λ (m - 1) ^ (-d)) := by
    apply hraw.trans
    rw [show q * (-A) = -(q * A) by ring] at htotal
    simpa only [b0, d, mul_assoc] using htotal
  exact hfinal.trans (hStar m hstart)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
open scoped Matrix
namespace AVRegularity.CycleReference

/-! The exact material energy-solution equation on a renewal block. -/

theorem ocChart_torus_energy_solution_iff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsOCStreamSeq α q Λ ζ Φ) (hm : 1 ≤ m)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (ν : ℝ) (l : ℤ) (a c : ℝ)
    (ha : ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ a)
    (hc : c ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m)
    (q' : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ) (hac : a ≤ c)
    (hpq : ∀ t, IsZ2Periodic (q' t)) (hpf : ∀ t, IsZ2Periodic (f t))
    (hp₀ : IsZ2Periodic θ₀) :
    IsTorusEnergySolution (streamVel (Φ m))
      (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a c q' f θ₀ θ ↔
    IsTorusEnergySolution (fun _ _ => 0)
      (fun t y => ν • ocMaterialMetric α q Λ m (Φ (m - 1)) hφ l t y +
        ocPulseStream α q Λ ζ m t y • sigmaMat) a c
      (fun t y => (jacMatrix (ocChart α q Λ m (Φ (m - 1)) hφ l t) y)⁻¹.mulVec
        (q' t (ocChart α q Λ m (Φ (m - 1)) hφ l t y)))
      (fun t y => f t (ocChart α q Λ m (Φ (m - 1)) hφ l t y))
      (fun y => θ₀ (ocChart α q Λ m (Φ (m - 1)) hφ l a y))
      (fun t y => θ t (ocChart α q Λ m (Φ (m - 1)) hφ l t y)) := by
  let s := (l : ℝ) * ocTauPP α q Λ m
  let ψ := chartStreamIncrement hφ s (Φ m)
  have hΦm := AVRegularity.Velocity.streamSeq_admissible hζ hΛ hseq m
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2) :=
    chartStreamIncrement_smooth hφ hΦm s
  have hb : chartVector hφ s (fun t x => streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x) =
      streamVel ψ := by
    funext t y
    exact (chartStreamIncrement_velocity hφ hΦm s t y).symm
  have ht := isTorusEnergySolution_chart_drift_equiv hφ s ν a c (streamVel (Φ m)) q' f θ θ₀ hac (admissible_streamVel_periodic hΦm) hpq hpf hp₀
  rw [hb] at ht
  have hpψ : ∀ t, IsZ2Periodic (ψ t) := by
    intro t k x
    change Φ m t (AVRegularity.streamFlow _ hφ t (x + latticeShift k) s) -
      Φ (m - 1) t (AVRegularity.streamFlow _ hφ t (x + latticeShift k) s) = _
    have hp1 : IsZ2Periodic (Φ m t) := by
      intro j y
      simpa using hΦm.2 0 j t y
    have hp2 : IsZ2Periodic (Φ (m - 1) t) := by
      intro j y
      simpa using hφ.2 0 j t y
    rw [streamFlow_lattice_equivariant, hp1 k, hp2 k]
    rfl
  have hf := isTorusEnergySolution_stream_flux_iff a c ψ hψ hpψ (fun t y => ν • chartMetric hφ s t y)
    (chartVector hφ s q') (chartPull hφ s f) (chartPull hφ s θ)
    (fun y => θ₀ (AVRegularity.streamFlow (Φ (m - 1)) hφ a y s))
  have hp (t : ℝ) (ht : t ∈ Set.Ioo a c) (y : Vec 2) : ψ t y = ocPulseStream α q Λ ζ m t y :=
    chartStreamIncrement_eq_ocPulseStream (by omega) hseq hm hφ l t
      ⟨ha.trans ht.1.le, ht.2.le.trans hc⟩ y
  have he := isTorusEnergySolution_coefficients_congr a c (fun _ _ => (0 : Vec 2)) (fun _ _ => 0)
    (fun t y => ν • chartMetric hφ s t y + ψ t y • sigmaMat)
    (fun t y => ν • chartMetric hφ s t y + ocPulseStream α q Λ ζ m t y • sigmaMat)
    (fun _ _ _ => rfl) (fun t ht y => by rw [hp t ht y])
    (chartVector hφ s q') (chartPull hφ s f) (chartPull hφ s θ)
    (fun y => θ₀ (AVRegularity.streamFlow (Φ (m - 1)) hφ a y s))
  exact ht.trans (hf.trans he)

end AVRegularity.CycleReference
end
end
