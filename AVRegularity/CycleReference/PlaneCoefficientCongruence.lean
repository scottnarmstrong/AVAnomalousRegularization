-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVenhance.Statements.Construction.StreamVel
public import AVRegularity.Definitions.CycleReference.OcAsymp
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

@[expose] public section

section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleReference

/-! Algebra of the full tested weak equation, retaining arbitrary forcing. -/

noncomputable def planeWeakIntegrand (b : ℝ → Vec 2 → Vec 2)
    (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ)
    (Dθ : ℝ → Vec 2 → Vec 2) (η : ℝ → Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  -θ p.1 p.2 * deriv (fun s => η s p.2) p.1 +
    vecDot (b p.1 p.2) (Dθ p.1 p.2) * η p.1 p.2 +
    vecDot ((A p.1 p.2).mulVec (Dθ p.1 p.2)) (spaceGrad (η p.1) p.2) +
    vecDot (q p.1 p.2) (spaceGrad (η p.1) p.2) - f p.1 p.2 * η p.1 p.2

theorem planeWeakIntegrand_time_mul (b : ℝ → Vec 2 → Vec 2)
    (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ)
    (Dθ : ℝ → Vec 2 → Vec 2) (η : ℝ → Vec 2 → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2)) (p : ℝ × Vec 2) :
    planeWeakIntegrand b A q f θ Dθ (fun t x => t * η t x) p =
      p.1 * planeWeakIntegrand b A q f θ Dθ η p - θ p.1 p.2 * η p.1 p.2 := by
  have ht : DifferentiableAt ℝ (fun r => η r p.2) p.1 :=
    (hη.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) p.1
  have hd := ((hasDerivAt_id p.1).mul ht.hasDerivAt).deriv
  have hg : spaceGrad (fun x => p.1 * η p.1 x) p.2 =
      p.1 • spaceGrad (η p.1) p.2 := by
    ext i
    unfold spaceGrad
    have hs : DifferentiableAt ℝ (η p.1) p.2 :=
      (hη.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) p.2
    rw [fderiv_const_mul hs]
    rfl
  have hd' : deriv (fun r => r * η r p.2) p.1 =
      η p.1 p.2 + p.1 * deriv (fun r => η r p.2) p.1 := by
    simpa only [Pi.mul_def, id_eq, one_mul] using hd
  unfold planeWeakIntegrand
  dsimp only
  rw [hd', hg]
  simp [vecDot, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
  ring

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Algebraic replacement of a stream drift by its antisymmetric flux. -/

theorem planeWeakIntegrand_stream_flux (ψ : ℝ → Vec 2 → ℝ)
    (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ → Vec 2 → Vec 2)
    (f θ : ℝ → Vec 2 → ℝ) (D : ℝ → Vec 2 → Vec 2) (η : ℝ → Vec 2 → ℝ) (p : ℝ × Vec 2) :
    planeWeakIntegrand (fun _ _ => 0) (fun t x => A t x + ψ t x • sigmaMat) q f θ D η p =
      planeWeakIntegrand (streamVel ψ) A q f θ D η p +
        (vecDot ((ψ p.1 p.2 • sigmaMat).mulVec (D p.1 p.2)) (spaceGrad (η p.1) p.2) -
          vecDot (streamVel ψ p.1 p.2) (D p.1 p.2) * η p.1 p.2) := by
  unfold planeWeakIntegrand
  dsimp only
  rw [Matrix.add_mulVec]
  simp [vecDot, Fin.sum_univ_two, Pi.add_apply]
  ring

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleReference

/-! Local integrability is forced by the full weak tested integrand. -/

theorem tested_integrability_implies_mul_test_integrability
    (b : ℝ → Vec 2 → Vec 2) (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ)
    (Dθ : ℝ → Vec 2 → Vec 2) (a c : ℝ)
    (hI : ∀ η : ℝ → Vec 2 → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2) →
      HasCompactSupport (fun p : ℝ × Vec 2 => η p.1 p.2) →
      (∀ t, c ≤ t → ∀ x, η t x = 0) →
      Integrable (planeWeakIntegrand b A q f θ Dθ η)
        (volume.restrict (Set.Ioo a c ×ˢ Set.univ)))
    (η : ℝ → Vec 2 → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2))
    (hc : HasCompactSupport (fun p : ℝ × Vec 2 => η p.1 p.2))
    (hz : ∀ t, c ≤ t → ∀ x, η t x = 0) :
    Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 * η p.1 p.2)
      (volume.restrict (Set.Ioo a c ×ˢ Set.univ)) := by
  have hIη := hI η hη hc hz
  have hItη := hI (fun t x => t * η t x) (contDiff_fst.mul hη) hc.mul_left
    (fun t ht x => by rw [hz t ht x, mul_zero])
  have hbound : ∀ᵐ p : ℝ × Vec 2 ∂(volume.restrict (Set.Ioo a c ×ˢ Set.univ)),
      ‖p.1‖ ≤ |a| + |c| := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with p hp
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have ha := neg_abs_le a
      have hc := abs_nonneg c
      linarith [hp.1.1]
    · have ha := abs_nonneg a
      have hc := le_abs_self c
      linarith [hp.1.2]
  have hweighted := hIη.bdd_mul continuous_fst.aestronglyMeasurable hbound
  convert hweighted.sub hItη using 1
  funext p
  simp only [Pi.sub_apply]
  rw [planeWeakIntegrand_time_mul b A q f θ Dθ η hη p]
  ring

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance MeasureTheory Filter Topology
namespace AVRegularity.CycleReference

/-! Separating the energy-space and tested-equation clauses of the plane solution definition. -/

def PlaneEnergySpace (a c : ℝ) (θ₀ : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (Dθ : ℝ → Vec 2 → Vec 2) : Prop :=
  (∀ t ∈ Set.Icc a c, MemL2On Set.univ (θ t)) ∧
  (∀ t ∈ Set.Icc a c, Tendsto (fun s => eLpNorm (fun x => θ s x - θ t x) 2 volume)
    (𝓝[Set.Icc a c] t) (𝓝 0)) ∧
  θ a =ᵐ[volume] θ₀ ∧
  (∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 i) 2
    (volume.restrict (Set.Ioo a c ×ˢ Set.univ))) ∧
  (∀ᵐ t ∂(volume.restrict (Set.Ioo a c)), HasWeakGradientOn Set.univ (θ t) (Dθ t))

def PlaneWeakEquation (b : ℝ → Vec 2 → Vec 2)
    (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a c : ℝ)
    (q : ℝ → Vec 2 → Vec 2) (f : ℝ → Vec 2 → ℝ)
    (θ₀ : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ) (Dθ : ℝ → Vec 2 → Vec 2) : Prop :=
  ∀ η : ℝ → Vec 2 → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2) →
    HasCompactSupport (fun p : ℝ × Vec 2 => η p.1 p.2) →
    (∀ t, c ≤ t → ∀ x, η t x = 0) →
    Integrable (planeWeakIntegrand b A q f θ Dθ η) (volume.restrict (Set.Ioo a c ×ˢ Set.univ)) ∧
    (∫ p in Set.Ioo a c ×ˢ Set.univ, planeWeakIntegrand b A q f θ Dθ η p) = ∫ x, θ₀ x * η a x

theorem isPlaneEnergySolution_iff_energySpace_weakEquation
    (b : ℝ → Vec 2 → Vec 2) (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a c : ℝ)
    (q : ℝ → Vec 2 → Vec 2) (f : ℝ → Vec 2 → ℝ)
    (θ₀ : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ) :
    IsPlaneEnergySolution b A a c q f θ₀ θ ↔
      ∃ Dθ, PlaneEnergySpace a c θ₀ θ Dθ ∧ PlaneWeakEquation b A a c q f θ₀ θ Dθ := by
  constructor
  · rintro ⟨D, hu, ht, hi, hD, hw, he⟩
    exact ⟨D, ⟨hu, ht, hi, hD, hw⟩, he⟩
  · rintro ⟨D, ⟨hu, ht, hi, hD, hw⟩, he⟩
    exact ⟨D, hu, ht, hi, hD, hw, he⟩

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleReference

/-! Only coefficient values inside the time slab enter its weak equation. -/

theorem planeWeakEquation_coefficients_congr (a c : ℝ)
    (b b' : ℝ → Vec 2 → Vec 2)
    (A A' : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hb : ∀ t ∈ Set.Ioo a c, ∀ x, b t x = b' t x)
    (hA : ∀ t ∈ Set.Ioo a c, ∀ x, A t x = A' t x)
    (q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ)
    (θ₀ : Vec 2 → ℝ) (D : ℝ → Vec 2 → Vec 2) :
    PlaneWeakEquation b A a c q f θ₀ θ D ↔ PlaneWeakEquation b' A' a c q f θ₀ θ D := by
  have he (η : ℝ → Vec 2 → ℝ) : planeWeakIntegrand b A q f θ D η =ᵐ[
      volume.restrict (Set.Ioo a c ×ˢ Set.univ)] planeWeakIntegrand b' A' q f θ D η := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with p hp
    unfold planeWeakIntegrand
    rw [hb p.1 hp.1 p.2, hA p.1 hp.1 p.2]
  constructor
  · intro h η hη hc hz
    obtain ⟨hi, heq⟩ := h η hη hc hz
    exact ⟨hi.congr (he η), (integral_congr_ae (he η)).symm.trans heq⟩
  · intro h η hη hc hz
    obtain ⟨hi, heq⟩ := h η hη hc hz
    exact ⟨hi.congr (he η).symm, (integral_congr_ae (he η)).trans heq⟩

theorem isPlaneEnergySolution_coefficients_congr (a c : ℝ)
    (b b' : ℝ → Vec 2 → Vec 2)
    (A A' : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hb : ∀ t ∈ Set.Ioo a c, ∀ x, b t x = b' t x)
    (hA : ∀ t ∈ Set.Ioo a c, ∀ x, A t x = A' t x)
    (q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ) :
    IsPlaneEnergySolution b A a c q f θ₀ θ ↔ IsPlaneEnergySolution b' A' a c q f θ₀ θ := by
  rw [isPlaneEnergySolution_iff_energySpace_weakEquation,
    isPlaneEnergySolution_iff_energySpace_weakEquation]
  constructor
  · rintro ⟨D, hs, hw⟩
    exact ⟨D, hs, (planeWeakEquation_coefficients_congr a c b b' A A' hb hA q f θ θ₀ D).mp hw⟩
  · rintro ⟨D, hs, hw⟩
    exact ⟨D, hs, (planeWeakEquation_coefficients_congr a c b b' A A' hb hA q f θ θ₀ D).mpr hw⟩

end AVRegularity.CycleReference
end
