-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.KernelEnergyPlane.PlaneKernelDifferentialEnergy
import AVRegularity.CoupledEnergyPlane.PlaneWeakSolutionUniqueness
public import AVRegularity.CoupledEnergyPlane.SourceFixedBandUniformBound
import AVRegularity.CoupledEnergy.CouplingBounds
import AVRegularity.CoupledEnergyPlane.SourceCarrierResidualRhs
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! Differential energy inequality for the perturbed projected kernel solution. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelDriftData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  (Q : PlaneKernelDriftData P)

theorem kernelProjectedEnergy_perturbed_deriv_le
    (N : ℕ) (u : ℝ → ProjectedFamily h) (t : Set.Icc a b)
    (F : ∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, PlaneHk Set.univ k (h i))
    (M ε : ℝ) (hε : 0 < ε)
    (hM : Real.sqrt (massNormSq ρ P.π (fun i => (hilbertBandHk N k (u t i)).val)) ≤ M)
    (hu : HasDerivAt u
      (projectedOperator Q.baseCoefficients N ν t (u t) +
        projectedSource N (fun i _ => F i +
          P.flux t t.property (fun j => hilbertBandHk N (k + 1) (u t j)) i)
          (fun i _ => g i) t) t) :
    deriv (fun s => massNormSq ρ P.π
      (fun i => (hilbertBandHk N k (u s i)).val)) t +
      (5 * ν / 4 - ε) * massGradNormSq ρ P.π (fun i => (hilbertBandHk N (k + 1) (u t i)).val) ≤
    2 * M * Real.sqrt (massNormSq ρ P.π (fun i => (g i).val)) +
      (1 / ε) * massNormSq ρ P.π (fun i => (F i).val) := by
  have he := Q.kernelProjectedRhs_unabsorbed_le N (u t) t F g
  have hd := (hasDerivAt_massBandEnergy N (fun _ => k) ρ P.π P.hπ hu).deriv
  apply kernelEnergy_perturbed_scalar _ _ _ _ _ _ ν ε hε
    (massGradNormSq_nonneg ρ P.π P.hπ _) (massNormSq_nonneg ρ P.π P.hπ _)
    (massNormSq_nonneg ρ P.π P.hπ _) hM
  rw [hd]
  linear_combination 2 * he


end PlaneKernelDriftData
end

/-! Uniform energy bound for the projected kernel solution from time regularity. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelDriftData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  (Q : PlaneKernelDriftData P)

theorem kernelProjectedEnergy_uniform_of_timeRegularity (N : ℕ)
    (u : C(Set.Icc a b, ProjectedFamily h))
    (F : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hac : AbsolutelyContinuousOnInterval (extendCurve P.htime u) a b)
    (hd : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ ht : t ∈ Set.Icc a b,
      HasDerivAt (extendCurve P.htime u)
        (projectedOperator Q.baseCoefficients N ν ⟨t, ht⟩ (extendCurve P.htime u t) +
          projectedSource N (fun i s => F i s + P.flux t ht
            (fun j => hilbertBandHk N (k + 1) (extendCurve P.htime u t j)) i) g t) t) :
    ∃ S : ℝ, 0 ≤ S ∧
      (∀ t : Set.Icc a b, massNormSq ρ P.π
        (fun i => (hilbertBandHk N k (u t i)).val) ≤ S ^ 2) ∧
      S ^ 2 + (ν / 2) * (∫ s in a..b, massGradNormSq ρ P.π
        (fun i => (hilbertBandHk N (k + 1) (extendCurve P.htime u s i)).val)) ≤
      2 * massNormSq ρ P.π (fun i => (hilbertBandHk N k (u ⟨a, le_rfl, P.htime⟩ i)).val) +
        (8 / ν) * (∫ s in a..b, massNormSq ρ P.π (fun i => (F i s).val)) +
          10 * (∫ s in a..b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2 := by
  let E := fun s => massNormSq ρ P.π
    (fun i => (hilbertBandHk N k (extendCurve P.htime u s i)).val)
  let R := fun s => massGradNormSq ρ P.π
    (fun i => (hilbertBandHk N (k + 1) (extendCurve P.htime u s i)).val)
  let G := fun s => Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))
  let Fsq := fun s => massNormSq ρ P.π (fun i => (F i s).val)
  have hE : AbsolutelyContinuousOnInterval E a b :=
    massBandEnergy_absolutelyContinuous N (fun _ => k) ρ P.π P.hπ hac
  have hR : IntervalIntegrable R volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr
      (((continuous_massBandGradient N (fun _ => k) ρ P.π).comp
        (continuous_extendCurve P.htime u)).integrableOn_Icc)
  have hG : IntervalIntegrable G volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr
      (planeMassNorm_integrable ρ P.π P.hπ (fun _ => k) g hg)
  have hFsq : IntervalIntegrable Fsq volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr
      (planeMassNormSq_integrable ρ P.π P.hπ (fun _ => k) F hF)
  have hi : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      deriv E t + ν * R t ≤ 2 * G t * Real.sqrt (E t) + (4 / ν) * Fsq t := by
    filter_upwards [hd, ae_restrict_mem measurableSet_Icc] with t ht htm
    exact Q.kernelProjectedEnergy_deriv_le_of_hasDerivAt N (extendCurve P.htime u)
      ⟨t, htm⟩ (fun i => F i t) (fun i => g i t) (ht htm)
  obtain ⟨S, hS, hbnd, he⟩ := coupledTimeEnergy_uniform_of_deriv_le P.htime P.diffusivity_pos hE
    (fun _ _ => massNormSq_nonneg ρ P.π P.hπ _)
    (fun _ _ => massGradNormSq_nonneg ρ P.π P.hπ _)
    (fun _ _ => Real.sqrt_nonneg _)
    (fun _ _ => massNormSq_nonneg ρ P.π P.hπ _) hR hG hFsq hi
  refine ⟨S, hS, ?_, ?_⟩
  · intro t
    simpa only [E, extendCurve_eq_of_mem P.htime u t.property] using hbnd t t.property
  · simpa only [E, R, G, Fsq, extendCurve_eq_of_mem P.htime u
      (show a ∈ Set.Icc a b from ⟨le_rfl, P.htime⟩)] using he

end PlaneKernelDriftData
end

/-! Row energy bound for the forced projected solution. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelDriftData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  (Q : PlaneKernelDriftData P)

theorem forcedProjected_rowEnergy_le (N : ℕ) (u : ProjectedFamily h) (t : Set.Icc a b) (i : ι)
    (F : ∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, PlaneHk Set.univ k (h i)) :
    factorialPairing ρ (hilbertBandHk N k
      ((projectedOperator Q.baseCoefficients N ν t u +
        projectedSource N (fun i _ => F i) (fun i _ => g i) t) i)).val
      (hilbertBandHk N k (u i)).val ≤
    -(5 * ν / 8) * gradFactorialNormSq ρ (hilbertBandHk N (k + 1) (u i)).val +
      Real.sqrt (factorialNormSq ρ (g i).val) * Real.sqrt (factorialNormSq ρ (hilbertBandHk N k (u i)).val) +
      (2 / ν) * factorialNormSq ρ (F i).val := by
  have hd := Q.diffusionDrift_rowEnergy_le N u t i
  have hf := componentFlux_pairing_young N k ρ ν P.diffusivity_pos (F i) (u i)
  have hg := componentSource_pairing_le N k ρ (g i) (u i)
  simp only [WithLp.ofLp_add, Pi.add_apply, projectedSource, bandPairing_add]
  linarith [le_abs_self (factorialPairing ρ (hilbertBandHk N k
      (bandDivergenceOperator (E := h i) N (planeHkValueOperator k (F i)))).val
      (hilbertBandHk N k (u i)).val),
    le_abs_self (factorialPairing ρ (hilbertBandHk N k
      (hilbertProjection N (planeHkValueOperator k (g i)))).val (hilbertBandHk N k (u i)).val)]

end PlaneKernelDriftData
end

/-! Interval energy bound for the perturbed projected kernel solution. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelDriftData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  (Q : PlaneKernelDriftData P)

theorem kernelProjectedEnergy_perturbed_interval (N : ℕ)
    (u : C(Set.Icc a b, ProjectedFamily h))
    (F : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hac : AbsolutelyContinuousOnInterval (extendCurve P.htime u) a b)
    (hd : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ ht : t ∈ Set.Icc a b,
      HasDerivAt (extendCurve P.htime u)
        (projectedOperator Q.baseCoefficients N ν ⟨t, ht⟩ (extendCurve P.htime u t) +
          projectedSource N (fun i s => F i s + P.flux t ht
            (fun j => hilbertBandHk N (k + 1) (extendCurve P.htime u t j)) i) g t) t) :
    ∀ (M ε : ℝ), 0 < ε →
      (∀ t ∈ Set.Icc a b, Real.sqrt (massNormSq ρ P.π
        (fun i => (hilbertBandHk N k (extendCurve P.htime u t i)).val)) ≤ M) →
      ∀ (s : ℝ) (hs : s ∈ Set.Icc a b) (t : ℝ) (ht : t ∈ Set.Icc a b), s ≤ t →
      massNormSq ρ P.π (fun i => (hilbertBandHk N k (u ⟨t, ht⟩ i)).val) +
        (5 * ν / 4 - ε) * (∫ r in Set.Ioc s t, massGradNormSq ρ P.π
          (fun i => (hilbertBandHk N (k + 1) (extendCurve P.htime u r i)).val)) ≤
      massNormSq ρ P.π (fun i => (hilbertBandHk N k (u ⟨s, hs⟩ i)).val) +
        (2 * M) * (∫ r in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i r).val))) +
        (1 / ε) * (∫ r in Set.Icc a b, massNormSq ρ P.π (fun i => (F i r).val)) := by
  intro M ε hε hM s hs t ht hst
  let E := fun s => massNormSq ρ P.π
    (fun i => (hilbertBandHk N k (extendCurve P.htime u s i)).val)
  let R := fun s => massGradNormSq ρ P.π
    (fun i => (hilbertBandHk N (k + 1) (extendCurve P.htime u s i)).val)
  let G := fun s => Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))
  let Fsq := fun s => massNormSq ρ P.π (fun i => (F i s).val)
  have hE : AbsolutelyContinuousOnInterval E a b :=
    massBandEnergy_absolutelyContinuous N (fun _ => k) ρ P.π P.hπ hac
  have hR : IntervalIntegrable R volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr
      (((continuous_massBandGradient N (fun _ => k) ρ P.π).comp
        (continuous_extendCurve P.htime u)).integrableOn_Icc)
  have hG : IntervalIntegrable G volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr
      (planeMassNorm_integrable ρ P.π P.hπ (fun _ => k) g hg)
  have hFsq : IntervalIntegrable Fsq volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr
      (planeMassNormSq_integrable ρ P.π P.hπ (fun _ => k) F hF)
  let H := fun r => 2 * M * G r + (1 / ε) * Fsq r
  have hH : Integrable H (volume.restrict (Set.Icc a b)) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mp hG).const_mul (2 * M) |>.add
      (((intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mp hFsq).const_mul (1 / ε))
  have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans (hM a ⟨le_rfl, P.htime⟩)
  have hi : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      deriv E t + (5 * ν / 4 - ε) * R t ≤ H t := by
    filter_upwards [hd, ae_restrict_mem measurableSet_Icc] with t ht htm
    exact Q.kernelProjectedEnergy_perturbed_deriv_le N (extendCurve P.htime u)
      ⟨t, htm⟩ (fun i => F i t) (fun i => g i t) M ε hε (hM t htm) (ht htm)
  have he := perturbedTimeEnergyGlobal P.htime hs ht hst hE hR hH
    (fun r => add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0) (Real.sqrt_nonneg _))
      (mul_nonneg (div_nonneg (by norm_num) hε.le) (massNormSq_nonneg ρ P.π P.hπ _))) hi
  simp only [H, integral_add
      (((intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mp hG).const_mul (2 * M))
      (((intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mp hFsq).const_mul (1 / ε)),
    integral_const_mul, E, R, G, Fsq,
    extendCurve_eq_of_mem P.htime u ht, extendCurve_eq_of_mem P.htime u hs] at he
  linarith only [he]

end PlaneKernelDriftData
end

/-! Interval row energy bound for the forced projected solution. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelDriftData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  (Q : PlaneKernelDriftData P)

theorem forcedProjected_row_interval (N : ℕ)
    (u : C(Set.Icc a b, ProjectedFamily h))
    (F : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hac : AbsolutelyContinuousOnInterval (extendCurve P.htime u) a b)
    (hd : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ ht : t ∈ Set.Icc a b,
      HasDerivAt (extendCurve P.htime u)
        (projectedOperator Q.baseCoefficients N ν ⟨t, ht⟩ (extendCurve P.htime u t) +
          projectedSource N F g t) t)
    (i : ι) (M : ℝ)
    (hM : ∀ t ∈ Set.Icc a b, Real.sqrt (factorialNormSq ρ
      (hilbertBandHk N k (extendCurve P.htime u t i)).val) ≤ M)
    (s t : Set.Icc a b) (hst : (s : ℝ) ≤ t) :
    factorialNormSq ρ (hilbertBandHk N k (u t i)).val +
      (5 * ν / 4) * (∫ r in Set.Ioc (s : ℝ) t, gradFactorialNormSq ρ
        (hilbertBandHk N (k + 1) (extendCurve P.htime u r i)).val) ≤
    factorialNormSq ρ (hilbertBandHk N k (u s i)).val +
      (2 * M) * (∫ r in Set.Icc a b, Real.sqrt (factorialNormSq ρ (g i r).val)) +
      (4 / ν) * (∫ r in Set.Icc a b, factorialNormSq ρ (F i r).val) := by
  let E := fun r => factorialNormSq ρ (hilbertBandHk N k (extendCurve P.htime u r i)).val
  let R := fun r => gradFactorialNormSq ρ (hilbertBandHk N (k + 1) (extendCurve P.htime u r i)).val
  let G := fun r => Real.sqrt (factorialNormSq ρ (g i r).val)
  let Fsq := fun r => factorialNormSq ρ (F i r).val
  have hE : AbsolutelyContinuousOnInterval E a b := componentBandEnergy_ac N k ρ i hac
  have hR : IntervalIntegrable R volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr
      (((continuous_componentBandGradient (E := h i) N k ρ).comp
        (((PiLp.proj (𝕜 := ℝ) 2 (fun j => Lp (h j) 2 (volume : Measure (Vec 2))) i).continuous).comp
          (continuous_extendCurve P.htime u))).integrableOn_Icc)
  have hG : Integrable G (volume.restrict (Set.Icc a b)) :=
    planeFactorialRoot_integrable _ k ρ (g i) (hg i)
  have hFsq : Integrable Fsq (volume.restrict (Set.Icc a b)) :=
    planeFactorial_integrable _ k ρ (F i) (hF i)
  let H := fun r => 2 * M * G r + (4 / ν) * Fsq r
  have hH : Integrable H (volume.restrict (Set.Icc a b)) :=
    (hG.const_mul (2 * M)).add (hFsq.const_mul (4 / ν))
  have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans (hM a ⟨le_rfl, P.htime⟩)
  have hi : ∀ᵐ r ∂volume.restrict (Set.Icc a b), deriv E r + (5 * ν / 4) * R r ≤ H r := by
    filter_upwards [hd, ae_restrict_mem measurableSet_Icc] with r hr hmem
    have he := Q.forcedProjected_rowEnergy_le N (extendCurve P.htime u r) ⟨r, hmem⟩ i
      (fun i => F i r) (fun i => g i r)
    have hsource : projectedSource N (fun i _ => F i r) (fun i _ => g i r) r =
        projectedSource N F g r := rfl
    rw [hsource] at he
    have hder := componentBandEnergy_deriv N k ρ i (hr hmem)
    change deriv E r = _ at hder
    rw [hder]
    have hm := mul_le_mul_of_nonneg_left (hM r hmem) (Real.sqrt_nonneg (factorialNormSq ρ (g i r).val))
    dsimp only [R, H, G, Fsq]
    linear_combination 2 * he + 2 * hm
  have he := perturbedTimeEnergyGlobal P.htime s.property t.property hst hE hR hH
    (fun r => add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0) (Real.sqrt_nonneg _))
      (mul_nonneg (div_nonneg (by norm_num) P.diffusivity_pos.le) (factorialNormSq_nonneg ρ _))) hi
  simp only [H, integral_add (hG.const_mul (2 * M)) (hFsq.const_mul (4 / ν)), integral_const_mul,
    E, R, G, Fsq, extendCurve_eq_of_mem P.htime u t.property,
    extendCurve_eq_of_mem P.htime u s.property] at he
  linarith only [he]

end PlaneKernelDriftData
end

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! The energy bound for a forced weak solution on the plane. -/

variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelDriftData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  (Q : PlaneKernelDriftData P)

theorem forcedWeakSolution_energy
    (f : ∀ i, PlaneHk Set.univ k (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ k (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u : ∀ i, ℝ → PlaneHk Set.univ k (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (hsol : IsCoupledWeakSolutionPlane ν a b Q.v 0 (fun _ => k) noLocalCoefficient f F g u w) :
    ∀ t ∈ Set.Icc a b,
      massNormSq ρ P.π (fun i => (u i t).val) +
        (ν / 2) * (∫ s in Set.Icc a b, massGradNormSq ρ P.π (fun i => (w i s).val)) ≤
      2 * massNormSq ρ P.π (fun i => (f i).val) +
        (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
          10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2 :=
  planeWeakSolution_energy (fun _ => k) k (fun _ => le_rfl)
    ρ Q.strain Q.B Q.lam ν P.radius_pos Q.strain_nonneg Q.B_ge_one Q.lam_pos
    P.diffusivity_pos Q.scale_small Q.strain_small P.π P.hπ a b P.htime Q.v Q.smooth
    Q.measurable Q.V Q.V_nonneg Q.bounded Q.divergence_zero Q.jets 0 noLocalCoefficient
    (fun i j d => (noLocalOrders (k := k) i j d).elim)
    (fun i j d _ _ => (noLocalOrders (k := k) i j d).elim)
    (fun i j d => (noLocalOrders (k := k) i j d).elim) (noLocalSchur (P := P))
    F g hF hg f u w hsol

end PlaneKernelDriftData

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! Gradient bound for the difference of forced fluxes. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelDriftData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  (Q : PlaneKernelDriftData P)

theorem forcedFluxDifference_gradient_bound
    (f : ∀ i, PlaneHk Set.univ k (h i))
    (F F' : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hF' : ∀ i, MemLp (F' i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ k (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u u' : ∀ i, ℝ → PlaneHk Set.univ k (h i))
    (w w' : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (hsol : IsCoupledWeakSolutionPlane ν a b Q.v 0 (fun _ => k) noLocalCoefficient f F g u w)
    (hsol' : IsCoupledWeakSolutionPlane ν a b Q.v 0 (fun _ => k) noLocalCoefficient f F' g u' w') :
    (∫ s in Set.Icc a b, massGradNormSq ρ P.π (fun i => (w i s - w' i s).val)) ≤
      (16 / ν ^ 2) * (∫ s in Set.Icc a b,
        massNormSq ρ P.π (fun i => (F i s - F' i s).val)) := by
  let W := planeCarrierHighTime (h := h) (fun _ => k) a b w hsol.2.1
  let W' := planeCarrierHighTime (h := h) (fun _ => k) a b w' hsol'.2.1
  let δu := fun i => extendCurve P.htime
    (planeWeakDifferenceCurve (h := h) (fun _ => k) a b u u' hsol.1 hsol'.1 i)
  let δw := weakHighCarrier (h := h) (fun _ => k) a b (W - W')
  have hd : IsCoupledWeakSolutionPlane ν a b Q.v 0 (fun _ => k) noLocalCoefficient
      (fun _ => 0) (fun i s => F i s - F' i s) (fun _ _ => 0) δu δw :=
    planeWeakSolution_fluxDifference_isWeakSolution P.htime ρ P.radius_pos Q.v Q.smooth
      Q.V Q.V_nonneg Q.bounded (fun _ => k) 0 noLocalCoefficient
      (fun i j d _ _ => (noLocalOrders (k := k) i j d).elim)
      (fun i j d => (noLocalOrders (k := k) i j d).elim) Q.measurable
      (fun i j d => (noLocalOrders (k := k) i j d).elim) k (fun _ => le_rfl)
      Q.strain Q.B Q.lam Q.strain_nonneg (zero_le_one.trans Q.B_ge_one) Q.lam_pos
      Q.jets ν F F' hF hF' g hg f u w hsol u' w' hsol'
  have hE := Q.forcedWeakSolution_energy (fun _ => 0) (fun i s => F i s - F' i s)
    (fun i => (hF i).sub (hF' i)) (fun _ _ => 0) (fun i => integrable_zero ℝ (PlaneHk Set.univ k (h i)) (volume.restrict (Set.Icc a b))) δu δw hd a
      ⟨le_rfl, P.htime⟩
  have h0 := planeMassNormSq_zero (h := h) (fun _ => k) ρ P.π P.hπ
  simp only [h0, Real.sqrt_zero, integral_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_add, add_zero] at hE
  have hI : (∫ s in Set.Icc a b, massGradNormSq ρ P.π (fun i => (δw i s).val)) =
      ∫ s in Set.Icc a b, massGradNormSq ρ P.π (fun i => (w i s - w' i s).val) := by
    have ha (i : ι) : δw i =ᵐ[volume.restrict (Set.Icc a b)] fun s => w i s - w' i s := by
      have hs := weakHighCarrier_sub_ae (h := h) (fun _ => k) a b W W' i
      have hw := planeCarrierHighTime_readout_ae (h := h) (fun _ => k) a b w hsol.2.1 i
      have hw' := planeCarrierHighTime_readout_ae (h := h) (fun _ => k) a b w' hsol'.2.1 i
      filter_upwards [hs, hw, hw'] with s hs hw hw'
      exact hs.trans (congrArg₂ (fun x y => x - y) hw hw')
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr ha] with s hs
    exact congrArg (massGradNormSq ρ P.π) (funext (fun i => congrArg Subtype.val (hs i)))
  rw [hI] at hE
  have hmass := massNormSq_nonneg ρ P.π P.hπ (fun i => (δu i a).val)
  have hb : (ν / 2) * (∫ s in Set.Icc a b,
      massGradNormSq ρ P.π (fun i => (w i s - w' i s).val)) ≤
      (8 / ν) * (∫ s in Set.Icc a b,
        massNormSq ρ P.π (fun i => (F i s - F' i s).val)) := by linarith
  have hν := P.diffusivity_pos
  calc
    _ ≤ ((8 / ν) * (∫ s in Set.Icc a b,
      massNormSq ρ P.π (fun i => (F i s - F' i s).val))) / (ν / 2) :=
      (le_div_iff₀ (by positivity : 0 < ν / 2)).mpr (by simpa only [mul_comm] using hb)
    _ = _ := by field_simp; ring

end PlaneKernelDriftData
end

/-! Mass bound for the difference of forced fluxes. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelDriftData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  (Q : PlaneKernelDriftData P)

theorem forcedFluxDifference_mass_bound
    (f : ∀ i, PlaneHk Set.univ k (h i))
    (F F' : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hF' : ∀ i, MemLp (F' i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ k (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u u' : ∀ i, ℝ → PlaneHk Set.univ k (h i))
    (w w' : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (hsol : IsCoupledWeakSolutionPlane ν a b Q.v 0 (fun _ => k) noLocalCoefficient f F g u w)
    (hsol' : IsCoupledWeakSolutionPlane ν a b Q.v 0 (fun _ => k) noLocalCoefficient f F' g u' w') (t : ℝ) (ht : t ∈ Set.Icc a b) :
    massNormSq ρ P.π (fun i => (u i t - u' i t).val) ≤
      (8 / ν) * (∫ s in Set.Icc a b,
        massNormSq ρ P.π (fun i => (F i s - F' i s).val)) := by
  let W := planeCarrierHighTime (h := h) (fun _ => k) a b w hsol.2.1
  let W' := planeCarrierHighTime (h := h) (fun _ => k) a b w' hsol'.2.1
  let δu := fun i => extendCurve P.htime
    (planeWeakDifferenceCurve (h := h) (fun _ => k) a b u u' hsol.1 hsol'.1 i)
  let δw := weakHighCarrier (h := h) (fun _ => k) a b (W - W')
  have hd : IsCoupledWeakSolutionPlane ν a b Q.v 0 (fun _ => k) noLocalCoefficient
      (fun _ => 0) (fun i s => F i s - F' i s) (fun _ _ => 0) δu δw :=
    planeWeakSolution_fluxDifference_isWeakSolution P.htime ρ P.radius_pos Q.v Q.smooth
      Q.V Q.V_nonneg Q.bounded (fun _ => k) 0 noLocalCoefficient
      (fun i j d _ _ => (noLocalOrders (k := k) i j d).elim)
      (fun i j d => (noLocalOrders (k := k) i j d).elim) Q.measurable
      (fun i j d => (noLocalOrders (k := k) i j d).elim) k (fun _ => le_rfl)
      Q.strain Q.B Q.lam Q.strain_nonneg (zero_le_one.trans Q.B_ge_one) Q.lam_pos
      Q.jets ν F F' hF hF' g hg f u w hsol u' w' hsol'
  have hE := Q.forcedWeakSolution_energy (fun _ => 0) (fun i s => F i s - F' i s)
    (fun i => (hF i).sub (hF' i)) (fun _ _ => 0) (fun i => integrable_zero ℝ (PlaneHk Set.univ k (h i)) (volume.restrict (Set.Icc a b))) δu δw hd t ht
  have h0 := planeMassNormSq_zero (h := h) (fun _ => k) ρ P.π P.hπ
  simp only [h0, Real.sqrt_zero, integral_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_add, add_zero] at hE
  have hdiss : 0 ≤ (ν / 2) * (∫ s in Set.Icc a b,
      massGradNormSq ρ P.π (fun i => (δw i s).val)) :=
    mul_nonneg (div_nonneg P.diffusivity_pos.le (by norm_num))
      (integral_nonneg (fun s => massGradNormSq_nonneg ρ P.π P.hπ _))
  have hb : massNormSq ρ P.π (fun i => (δu i t).val) ≤
      (8 / ν) * (∫ s in Set.Icc a b,
        massNormSq ρ P.π (fun i => (F i s - F' i s).val)) := by linarith
  simpa only [δu, extendCurve_eq_of_mem P.htime _ ht, planeWeakDifferenceCurve_apply] using hb

end PlaneKernelDriftData
end

/-! Data of a forced cutoff solution: its high-time carrier, components and fluxes. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

structure PlaneForcedCutoffData
    {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
    (Q : PlaneKernelDriftData P) where
  f : ∀ i, PlaneHk Set.univ k (h i)
  F : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))
  hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b))
  g : ∀ i, ℝ → PlaneHk Set.univ k (h i)
  hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))
  u : ∀ i, ℝ → PlaneHk Set.univ k (h i)
  w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i)
  solution : IsCoupledWeakSolutionPlane ν a b Q.v 0 (fun _ => k) noLocalCoefficient f F g u w

namespace PlaneForcedCutoffData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneForcedCutoffData Q)

def highTime := planeCarrierHighTime (h := h) (fun _ => k) a b T.w T.solution.2.1

def highComponent (i : ι) := weakHighCarrierTimeCLM (h := h) (fun _ => k) a b i T.highTime

def fluxComponent (i : ι) := (T.hF i).toLp (T.F i)

def residualFlux (N : ℕ) (i : ι) :=
  planeResidualFluxTime (h := h) P.htime ρ P.radius_pos (fun _ => k) 0 noLocalCoefficient
    (fun i j d _ _ => (noLocalOrders (k := k) i j d).elim)
    (fun i j d => (noLocalOrders (k := k) i j d).elim)
    (fun i j d => (noLocalOrders (k := k) i j d).elim)
    T.highComponent T.fluxComponent N i

def residualValue (N : ℕ) (i : ι) :=
  planeResidualValueSource P.htime (show k ≤ k from le_rfl) Q.v Q.measurable Q.smooth
    Q.V Q.strain Q.B Q.lam Q.V_nonneg Q.strain_nonneg
    (le_trans zero_le_one Q.B_ge_one) Q.lam_pos Q.bounded Q.jets (T.highComponent i) (T.g i) N

def curve (N : ℕ) :=
  sourceNativeFamilyPrimitive (h := h) P.htime ρ P.radius_pos Q.v Q.smooth Q.V Q.V_nonneg Q.bounded
    (fun _ => k) 0 noLocalCoefficient
    (fun i j d _ _ => (noLocalOrders (k := k) i j d).elim)
    (fun i j d => (noLocalOrders (k := k) i j d).elim)
    Q.measurable (fun i j d => (noLocalOrders (k := k) i j d).elim)
    ν T.f T.F T.hF T.g T.hg T.highTime N

theorem timeRegularity (N : ℕ) :
    AbsolutelyContinuousOnInterval (extendCurve P.htime (T.curve N)) a b ∧
      (∀ᵐ t ∂volume, t ∈ Set.Icc a b → HasDerivAt (extendCurve P.htime (T.curve N))
        (projectedOperator (Q.baseCoefficients.reindex (clampPoint a b P.htime)) N ν t
          (extendCurve P.htime (T.curve N) t) +
          projectedSource N (fun i => T.residualFlux N i) (T.residualValue N) t) t) :=
  planeWeakSolution_nativeFamily_timeRegularity (h := h) P.htime ρ P.radius_pos Q.v Q.smooth
    Q.V Q.V_nonneg Q.bounded (fun _ => k) 0 noLocalCoefficient
    (fun i j d _ _ => (noLocalOrders (k := k) i j d).elim)
    (fun i j d => (noLocalOrders (k := k) i j d).elim)
    Q.measurable (fun i j d => (noLocalOrders (k := k) i j d).elim)
    k (fun _ => le_rfl) Q.strain Q.B Q.lam Q.strain_nonneg
    (le_trans zero_le_one Q.B_ge_one) Q.lam_pos Q.jets ν T.F T.hF T.g T.hg T.f T.u T.w T.solution N

end PlaneForcedCutoffData
end

/-! Forced carriers and the data of the kernel feedback map. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

structure PlaneForcedCarrier
    {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
    (Q : PlaneKernelDriftData P)
    (f : ∀ i, PlaneHk Set.univ k (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ k (h i)) where
  u : ∀ i, ℝ → PlaneHk Set.univ k (h i)
  w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i)
  solution : IsCoupledWeakSolutionPlane ν a b Q.v 0 (fun _ => k) noLocalCoefficient f F g u w

namespace PlaneKernelDriftData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  (Q : PlaneKernelDriftData P)

theorem forcedCarrier_nonempty
    (f : ∀ i, PlaneHk Set.univ k (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ k (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) :
    Nonempty (PlaneForcedCarrier Q f F g) := by
  obtain ⟨u, w, hs⟩ := Q.exists_forcedWeakSolution f F hF g hg
  exact ⟨⟨u, w, hs⟩⟩

def chooseForcedCarrier
    (f : ∀ i, PlaneHk Set.univ k (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ k (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) : PlaneForcedCarrier Q f F g :=
  Classical.choice (Q.forcedCarrier_nonempty f F hF g hg)

end PlaneKernelDriftData

structure PlaneKernelFeedbackData
    {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
    (Q : PlaneKernelDriftData P) where
  f : ∀ i, PlaneHk Set.univ k (h i)
  F : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))
  hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b))
  g : ∀ i, ℝ → PlaneHk Set.univ k (h i)
  hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))

namespace PlaneKernelFeedbackData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneKernelFeedbackData Q)


def inputFlux (Z : Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2 (volume.restrict (Set.Icc a b)))
    (i : ι) (t : ℝ) : PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)) := T.F i t + Z t i

abbrev inputFlux_memLp (Z : Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2 (volume.restrict (Set.Icc a b))) (i : ι) :=
  timeFamily_input_memLp (E := fun i => PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (volume.restrict (Set.Icc a b)) T.F T.hF Z i

def forcedCarrier (Z : Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2 (volume.restrict (Set.Icc a b))) :
    PlaneForcedCarrier Q T.f (T.inputFlux Z) T.g :=
  Q.chooseForcedCarrier T.f (T.inputFlux Z) (T.inputFlux_memLp Z) T.g T.hg

def feedback (Z : Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2 (volume.restrict (Set.Icc a b))) :
    Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2 (volume.restrict (Set.Icc a b)) :=
  (memLp_pi_iff.mpr (fun i => P.carrierFlux_memLp (T.forcedCarrier Z).w
    (T.forcedCarrier Z).solution.2.1 i)).toLp
      (fun t i => P.carrierFlux (T.forcedCarrier Z).w i t)

theorem feedback_ae (Z : Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2 (volume.restrict (Set.Icc a b))) :
    T.feedback Z =ᵐ[volume.restrict (Set.Icc a b)]
      fun t i => P.carrierFlux (T.forcedCarrier Z).w i t :=
  (memLp_pi_iff.mpr (fun i => P.carrierFlux_memLp (T.forcedCarrier Z).w
    (T.forcedCarrier Z).solution.2.1 i)).coeFn_toLp

end PlaneKernelFeedbackData
end

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! Almost everywhere alignment of the residual flux with the flux component of a forced cutoff solution. -/

variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneForcedCutoffData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneForcedCutoffData Q)

theorem residualFlux_eq (N : ℕ) (i : ι) : T.residualFlux N i = T.fluxComponent i := by
  classical
  let inst (j : ι) : IsEmpty (admissibleOrders (fun _ : ι => k) 0 i j) :=
    ⟨noLocalOrders i j⟩
  unfold AVRegularity.KernelEnergyPlane.PlaneForcedCutoffData.residualFlux planeResidualFluxTime assemblePlaneResidualFlux
  exact assembleTimeFlux_zero_empty
    (J := PlaneHk Set.univ ((fun _ : ι => k) i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (I := ι) (D := fun j => admissibleOrders (fun _ => k) 0 i j) _ _ _ _

theorem residualFlux_ae (N : ℕ) (i : ι) :
    T.residualFlux N i =ᵐ[volume.restrict (Set.Icc a b)] T.F i := by
  rw [T.residualFlux_eq]
  exact (T.hF i).coeFn_toLp

theorem curve_component (N : ℕ) (t : Set.Icc a b) (i : ι) :
    T.curve N t i = hilbertProjection N (planeHkValueOperator (E := h i) k (T.u i t)) :=
  planeWeakSolution_nativeFamily_component (h := h) P.htime ρ P.radius_pos Q.v Q.smooth
    Q.V Q.V_nonneg Q.bounded (fun _ => k) 0 noLocalCoefficient
    (fun i j d _ _ => (noLocalOrders (k := k) i j d).elim)
    (fun i j d => (noLocalOrders (k := k) i j d).elim)
    Q.measurable (fun i j d => (noLocalOrders (k := k) i j d).elim)
    k (fun _ => le_rfl) Q.strain Q.B Q.lam Q.strain_nonneg
    (le_trans zero_le_one Q.B_ge_one) Q.lam_pos Q.jets ν T.F T.hF T.g T.hg T.f T.u T.w T.solution N t i

theorem curve_alignment_ae (N : ℕ) (i : ι) :
    (fun t => extendCurve P.htime (T.curve N) t i) =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => hilbertProjection N (planeHkValueOperator (E := h i) (k + 1) (T.w i t)) := by
  have ha := planeWeakSolution_nativeFamily_alignment_ae (h := h) P.htime ρ P.radius_pos Q.v Q.smooth
    Q.V Q.V_nonneg Q.bounded (fun _ => k) 0 noLocalCoefficient
    (fun i j d _ _ => (noLocalOrders (k := k) i j d).elim)
    (fun i j d => (noLocalOrders (k := k) i j d).elim)
    Q.measurable (fun i j d => (noLocalOrders (k := k) i j d).elim)
    k (fun _ => le_rfl) Q.strain Q.B Q.lam Q.strain_nonneg
    (le_trans zero_le_one Q.B_ge_one) Q.lam_pos Q.jets ν T.F T.hF T.g T.hg T.f T.u T.w T.solution N i
  have hw := planeCarrierHighTime_readout_ae (h := h) (fun _ => k) a b T.w T.solution.2.1 i
  filter_upwards [ha, hw] with t ht hw
  exact ht.trans (congrArg (fun p : PlaneHk Set.univ (k + 1) (h i) =>
    hilbertProjection N (planeHkValueOperator (k + 1) p)) hw)

end PlaneForcedCutoffData

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! The carrier-valued time curve of a forced cutoff solution and its band truncations. -/

variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneForcedCutoffData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneForcedCutoffData Q)

def carrierTime : Lp (∀ i, PlaneHk Set.univ (k + 1) (h i)) 2 (volume.restrict (Set.Icc a b)) :=
  (memLp_pi_iff.mpr T.solution.2.1).toLp (fun t i => T.w i t)

theorem carrierTime_ae : T.carrierTime =ᵐ[volume.restrict (Set.Icc a b)] fun t i => T.w i t :=
  (memLp_pi_iff.mpr T.solution.2.1).coeFn_toLp

def bandCarrierTime (N : ℕ) :=
  (planeFamilyCutoff (E := h) N (fun _ => k + 1)).compLpL 2
    (volume.restrict (Set.Icc a b)) T.carrierTime

theorem bandCarrierTime_ae (N : ℕ) :
    T.bandCarrierTime N =ᵐ[volume.restrict (Set.Icc a b)]
      fun t i => hilbertBandHk N (k + 1) (extendCurve P.htime (T.curve N) t i) := by
  have hp := ContinuousLinearMap.coeFn_compLpL (planeFamilyCutoff (E := h) N (fun _ => k + 1))
    T.carrierTime
  filter_upwards [hp, T.carrierTime_ae, ae_all_iff.mpr (T.curve_alignment_ae N)]
    with t hp hw hq
  unfold bandCarrierTime
  rw [hp, hw]
  funext i
  change planeHkCutoff N (k + 1) (T.w i t) = _
  rw [hq i]
  change hilbertBandHk N (k + 1) (planeHkValueOperator (k + 1) (T.w i t)) =
    hilbertBandHk N (k + 1) (hilbertProjection N (planeHkValueOperator (k + 1) (T.w i t)))
  rw [hilbertBandHk_projection]

theorem bandCarrierTime_tendsto :
    Filter.Tendsto (fun N => T.bandCarrierTime N) Filter.atTop (𝓝 T.carrierTime) :=
  tendsto_planeFamilyCutoff_time (E := h) (volume.restrict (Set.Icc a b))
    (fun _ => k + 1) T.carrierTime

end PlaneForcedCutoffData

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! Bundled data of a kernel solution, and the forced cutoff data it determines. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

structure PlaneKernelSolutionData
    {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
    (Q : PlaneKernelDriftData P) where
  f : ∀ i, PlaneHk Set.univ k (h i)
  F : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))
  hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b))
  g : ∀ i, ℝ → PlaneHk Set.univ k (h i)
  hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))
  u : ∀ i, ℝ → PlaneHk Set.univ k (h i)
  w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i)
  y : ∀ i j (α : Γ i j), ℝ → PlaneHk Set.univ (k + D - 1) (G i j α)
  solution : IsKernelWeakSolutionPlane ν a b Q.v k D P.B P.C P.S f F g u w y

namespace PlaneKernelSolutionData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneKernelSolutionData Q)

abbrev totalFlux_memLp (i : ι) :=
  timeMemLp_pointwise_add (volume.restrict (Set.Icc a b)) 2 (T.F i)
    (P.carrierFlux T.w i) (T.hF i) (P.carrierFlux_memLp T.w T.solution.2.1 i)

def forced : PlaneForcedCutoffData Q where
  f := T.f
  F := fun i t => T.F i t + P.carrierFlux T.w i t
  hF := T.totalFlux_memLp
  g := T.g
  hg := T.hg
  u := T.u
  w := T.w
  solution := P.kernelWeakSolution_forcedWeakSolution Q.v Q.smooth Q.V Q.bounded
    T.f T.F T.g T.u T.w T.y T.solution

end PlaneKernelSolutionData
end

/-! The carrier difference and the mass equation for the feedback readout. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelFeedbackData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneKernelFeedbackData Q)

def carrierDifference
    (Z Z' : Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2 (volume.restrict (Set.Icc a b)))
    (i : ι) (s : ℝ) : PlaneHk Set.univ (k + 1) (h i) :=
  (T.forcedCarrier Z).w i s - (T.forcedCarrier Z').w i s

theorem carrierDifference_memLp
    (Z Z' : Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    MemLp (T.carrierDifference Z Z' i) 2 (volume.restrict (Set.Icc a b)) :=
  timeMemLp_pointwise_sub (volume.restrict (Set.Icc a b)) 2
    ((T.forcedCarrier Z).w i) ((T.forcedCarrier Z').w i)
    ((T.forcedCarrier Z).solution.2.1 i) ((T.forcedCarrier Z').solution.2.1 i)

abbrev feedbackDifference_rawMassEq
    (Z Z' : Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2 (volume.restrict (Set.Icc a b))) :=
  timeSubReadout_integral (volume.restrict (Set.Icc a b)) (T.feedback Z) (T.feedback Z')
    (fun q => massNormSq ρ P.π (fun i => (q i).val))
    (fun t i => P.carrierFlux (T.forcedCarrier Z).w i t)
    (fun t i => P.carrierFlux (T.forcedCarrier Z').w i t) (T.feedback_ae Z) (T.feedback_ae Z')

theorem feedbackDifference_massEq
    (Z Z' : Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2 (volume.restrict (Set.Icc a b))) :
    (∫ s in Set.Icc a b,
      massNormSq ρ P.π (fun i => ((T.feedback Z - T.feedback Z') s i).val)) =
      ∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (P.carrierFlux (T.carrierDifference Z Z') i s).val) := by
  have hs := T.feedbackDifference_rawMassEq Z Z'
  apply hs.trans
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => congrArg (massNormSq ρ P.π)
    (funext (fun i => congrArg Subtype.val
      (P.carrierFlux_sub (T.forcedCarrier Z).w (T.forcedCarrier Z').w i s))))

theorem inputDifference_massEq
    (Z Z' : Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b))) :
    (∫ s in Set.Icc a b,
      massNormSq ρ P.π (fun i => (T.inputFlux Z i s - T.inputFlux Z' i s).val)) =
      ∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => ((Z - Z') s i).val) := by
  apply integral_congr_ae
  filter_upwards [timeSub_ae (volume.restrict (Set.Icc a b)) Z Z'] with s hs
  rw [hs]
  apply congrArg (massNormSq ρ P.π)
  funext i
  exact congrArg Subtype.val (by simp only [inputFlux, add_sub_add_left_eq_sub, Pi.sub_apply])

abbrev inputGradient_bound
    (Z Z' : Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2 (volume.restrict (Set.Icc a b))) :=
  Q.forcedFluxDifference_gradient_bound T.f (T.inputFlux Z) (T.inputFlux Z')
    (T.inputFlux_memLp Z) (T.inputFlux_memLp Z') T.g T.hg
    (T.forcedCarrier Z).u (T.forcedCarrier Z').u
    (T.forcedCarrier Z).w (T.forcedCarrier Z').w
    (T.forcedCarrier Z).solution (T.forcedCarrier Z').solution

end PlaneKernelFeedbackData
end

/-! Contraction estimates for the kernel feedback map. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelFeedbackData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneKernelFeedbackData Q)

def weightedTimeReadout :=
  (planeMassWeightedCarrierCLM (E := fun i => PiLp 2 (fun _ : Fin 2 => h i))
    (fun _ => k) ρ P.π).compLpL 2 (volume.restrict (Set.Icc a b))

theorem feedback_mass_integral_contraction [Nonempty ι]
    (Z Z' : Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2 (volume.restrict (Set.Icc a b))) :
    (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => ((T.feedback Z - T.feedback Z') s i).val)) ≤
      (1 / 4) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => ((Z - Z') s i).val)) := by
  classical
  have hf := P.carrierFlux_mass_integral_le (T.carrierDifference Z Z')
    (T.carrierDifference_memLp Z Z')
  have hg := T.inputGradient_bound Z Z'
  rw [T.inputDifference_massEq Z Z'] at hg
  rw [T.feedbackDifference_massEq Z Z']
  exact kernelFeedback_quarter_bound ν P.θ _ _ _ P.diffusivity_pos
    (P.theta_nonneg_of_component (Classical.arbitrary ι)) P.hθ
    (integral_nonneg (fun s => massNormSq_nonneg ρ P.π P.hπ _)) hf hg

set_option backward.isDefEq.respectTransparency false in
theorem feedback_weighted_contraction [Nonempty ι]
    (Z Z' : Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2 (volume.restrict (Set.Icc a b))) :
    ‖(weightedTimeReadout (P := P)) (T.feedback Z - T.feedback Z')‖ ≤
      (1 / 2 : ℝ) * ‖(weightedTimeReadout (P := P)) (Z - Z')‖ := by
  let U : Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b)) := T.feedback Z - T.feedback Z'
  let V : Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b)) := Z - Z'
  exact (planeFluxTime_half_bound (h := h) (volume.restrict (Set.Icc a b)) k ρ P.π P.hπ
    U V (T.feedback_mass_integral_contraction Z Z') : _)

end PlaneKernelFeedbackData
end

end AVRegularity.KernelEnergyPlane
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! The residual flux of the kernel solution and its convergence. -/

variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelSolutionData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneKernelSolutionData Q)

def residualFlux (N : ℕ) (i : ι) :=
  T.forced.residualFlux N i - P.fluxTimeComponent i (T.forced.bandCarrierTime N)

abbrev carrierTimeFlux_ae (i : ι) :=
  timeOperatorComponent_readout_ae (volume.restrict (Set.Icc a b)) P.clampedFluxCLM
    P.clampedFlux_stronglyMeasurable P.fluxBudget P.fluxBudget_nonneg P.clampedFlux_norm_le i
    T.forced.carrierTime (fun t j => T.w j t) T.forced.carrierTime_ae

abbrev totalFluxClass_sub_kernelFlux (i : ι) :=
  timeClass_sub_eq_of_ae_add
    (volume.restrict (Set.Icc a b)) (T.forced.fluxComponent i)
    (P.fluxTimeComponent i T.forced.carrierTime) ((T.hF i).toLp (T.F i))
    (T.F i) (P.carrierFlux T.w i) (T.totalFlux_memLp i).coeFn_toLp
    (T.carrierTimeFlux_ae i) (T.hF i).coeFn_toLp

abbrev residualFlux_tendsto (i : ι) :=
  timeResidualMinusCLM_tendsto (T.forced.fluxComponent i) ((T.hF i).toLp (T.F i))
    (P.fluxTimeComponent i) (fun N => T.forced.bandCarrierTime N) T.forced.carrierTime
    T.forced.bandCarrierTime_tendsto (fun N => T.forced.residualFlux N i)
    (fun N => T.forced.residualFlux_eq N i) (T.totalFluxClass_sub_kernelFlux i)

end PlaneKernelSolutionData

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! Decomposition of the residual flux into band kernel flux and source. -/

variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelSolutionData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneKernelSolutionData Q)

abbrev bandKernelFlux_ae (N : ℕ) (i : ι) :=
  timeOperatorComponent_readout_ae (volume.restrict (Set.Icc a b)) P.clampedFluxCLM
    P.clampedFlux_stronglyMeasurable P.fluxBudget P.fluxBudget_nonneg P.clampedFlux_norm_le i
    (T.forced.bandCarrierTime N)
    (fun s j => hilbertBandHk N (k + 1) (extendCurve P.htime (T.forced.curve N) s j))
    (T.forced.bandCarrierTime_ae N)

theorem residualFlux_source_decomposition_ae (N : ℕ) (i : ι) :
    ∀ᵐ s ∂volume.restrict (Set.Icc a b),
      T.forced.residualFlux N i s = T.residualFlux N i s +
        P.carrierFlux (fun j r => hilbertBandHk N (k + 1)
          (extendCurve P.htime (T.forced.curve N) r j)) i s := by
  have hs := timeSub_ae (volume.restrict (Set.Icc a b)) (T.forced.residualFlux N i)
    (P.fluxTimeComponent i (T.forced.bandCarrierTime N))
  filter_upwards [hs, T.bandKernelFlux_ae N i] with s hs hf
  change T.forced.residualFlux N i s =
    (T.forced.residualFlux N i - P.fluxTimeComponent i (T.forced.bandCarrierTime N)) s + _
  rw [hs, hf]
  simp only [PlaneKernelOperator.carrierFlux, sub_add_cancel]

end PlaneKernelSolutionData

end AVRegularity.KernelEnergyPlane
end
end
end
