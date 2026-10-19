-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleReference.SingleModeFlux
import AVenhance.Infra.Classical.GalerkinModeCalculus
public import AVRegularity.CycleReference.ChartDerivativeBounded
public import AVenhance.Statements.Section3.SpaceAvg
import AVRegularity.CycleReference.CoreFlux
import AVenhance.Infra.Section3.FluxMatrix
import AVenhance.Infra.Torus.FrozenBridge

/-! Smooth periodic structure and zero-mean derivatives of the glued corrector. -/

@[expose] public section

open MeasureTheory Homogenization AVenhance
open scoped ContDiff

namespace AVRegularity.CycleReference

theorem odd_int_mod_four {k : ℤ} (hk : Odd k) : k % 4 = 1 ∨ k % 4 = 3 := by
  rcases hk with ⟨a, ha⟩
  have hrem := Int.emod_lt k (b := 4) (by norm_num)
  have hnon := Int.emod_nonneg k (b := 4) (by norm_num)
  omega

theorem pulseCorrector_horizontal_components {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {k : ℤ} (h1 : k % 4 = 1) (ν t : ℝ) :
    ((fun y : Vec 2 => ocPulseCorrector α q Λ ζ m ν k t y 0) = (fun _ => 0)) ∧
    ((fun y : Vec 2 => ocPulseCorrector α q Λ ζ m ν k t y 1) = (fun y =>
      -(ocPulseMemory α q Λ ζ m ν k t *
        (2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹)) *
        Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 0))) := by
  constructor <;> funext y
  · simp [ocPulseCorrector, ocShearVel_horizontal h1]
  · simp [ocPulseCorrector, ocShearVel_horizontal h1]
    ring

theorem pulseCorrector_vertical_components {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {k : ℤ} (h3 : k % 4 = 3) (ν t : ℝ) :
    ((fun y : Vec 2 => ocPulseCorrector α q Λ ζ m ν k t y 0) = (fun y =>
      ocPulseMemory α q Λ ζ m ν k t *
        (2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹) *
        Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1))) ∧
    ((fun y : Vec 2 => ocPulseCorrector α q Λ ζ m ν k t y 1) = (fun _ => 0)) := by
  constructor <;> funext y
  · simp [ocPulseCorrector, ocShearVel_vertical h3]
    ring
  · simp [ocPulseCorrector, ocShearVel_vertical h3]

theorem pulseCorrector_component_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {k : ℤ} (hk : Odd k) (ν t : ℝ) (i : Fin 2) :
    ContDiff ℝ ⊤ (fun y : Vec 2 => ocPulseCorrector α q Λ ζ m ν k t y i) := by
  rcases odd_int_mod_four hk with h1 | h3
  · rcases pulseCorrector_horizontal_components (α := α) (q := q) (Λ := Λ)
      (m := m) (ζ := ζ) h1 ν t with ⟨h0, h1f⟩
    fin_cases i
    · change ContDiff ℝ ⊤ (fun y => ocPulseCorrector α q Λ ζ m ν k t y (0 : Fin 2))
      rw [h0]
      fun_prop
    · change ContDiff ℝ ⊤ (fun y => ocPulseCorrector α q Λ ζ m ν k t y (1 : Fin 2))
      rw [h1f]
      fun_prop
  · rcases pulseCorrector_vertical_components (α := α) (q := q) (Λ := Λ)
      (m := m) (ζ := ζ) h3 ν t with ⟨h0, h1f⟩
    fin_cases i
    · change ContDiff ℝ ⊤ (fun y => ocPulseCorrector α q Λ ζ m ν k t y (0 : Fin 2))
      rw [h0]
      fun_prop
    · change ContDiff ℝ ⊤ (fun y => ocPulseCorrector α q Λ ζ m ν k t y (1 : Fin 2))
      rw [h1f]
      fun_prop

theorem cos_ocFrequency_lattice_periodic {q : ℝ} {Λ m : ℕ}
    (hΛ : 1 ≤ Λ) (hm : 1 ≤ m) (i : Fin 2) (n : Fin 2 → ℤ) (y : Vec 2) :
    Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ *
      ((y + latticeShift n) i)) =
    Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y i) := by
  obtain ⟨N, hN, _⟩ := ocFrequencyNat (q := q) (Λ := Λ) (m := m) hΛ hm
  have harg : 2 * Real.pi * (ocEpsilon q Λ m)⁻¹ *
      ((y + latticeShift n) i) =
      2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y i +
        (((n i * N : ℤ) : ℝ) * (2 * Real.pi)) := by
    rw [show (y + latticeShift n) i = y i + (n i : ℝ) by simp [latticeShift], hN]
    push_cast
    ring
  rw [harg]
  exact Real.cos_add_int_mul_two_pi _ _

theorem pulseCorrector_component_isZ2Periodic {α q : ℝ} {Λ m : ℕ}
    {ζ : ℝ → ℝ} {k : ℤ} (hΛ : 1 ≤ Λ) (hm : 1 ≤ m) (hk : Odd k)
    (ν t : ℝ) (i : Fin 2) :
    IsZ2Periodic (fun y : Vec 2 => ocPulseCorrector α q Λ ζ m ν k t y i) := by
  intro n y
  rcases odd_int_mod_four hk with h1 | h3
  · rcases pulseCorrector_horizontal_components (α := α) (q := q) (Λ := Λ)
      (m := m) (ζ := ζ) h1 ν t with ⟨h0, h1f⟩
    fin_cases i
    · change ocPulseCorrector α q Λ ζ m ν k t (y + latticeShift n) (0 : Fin 2) =
        ocPulseCorrector α q Λ ζ m ν k t y 0
      rw [congrFun h0 (y + latticeShift n), congrFun h0 y]
    · change ocPulseCorrector α q Λ ζ m ν k t (y + latticeShift n) (1 : Fin 2) =
        ocPulseCorrector α q Λ ζ m ν k t y 1
      rw [congrFun h1f (y + latticeShift n), congrFun h1f y]
      exact congrArg (fun z : ℝ =>
        -(ocPulseMemory α q Λ ζ m ν k t *
          (2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) *
            (ocEpsilon q Λ m)⁻¹)) * z)
          (cos_ocFrequency_lattice_periodic hΛ hm 0 n y)
  · rcases pulseCorrector_vertical_components (α := α) (q := q) (Λ := Λ)
      (m := m) (ζ := ζ) h3 ν t with ⟨h0, h1f⟩
    fin_cases i
    · change ocPulseCorrector α q Λ ζ m ν k t (y + latticeShift n) (0 : Fin 2) =
        ocPulseCorrector α q Λ ζ m ν k t y 0
      rw [congrFun h0 (y + latticeShift n), congrFun h0 y]
      exact congrArg (fun z : ℝ =>
        ocPulseMemory α q Λ ζ m ν k t *
          (2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) *
            (ocEpsilon q Λ m)⁻¹) * z)
          (cos_ocFrequency_lattice_periodic hΛ hm 1 n y)
    · change ocPulseCorrector α q Λ ζ m ν k t (y + latticeShift n) (1 : Fin 2) =
        ocPulseCorrector α q Λ ζ m ν k t y 1
      rw [congrFun h1f (y + latticeShift n), congrFun h1f y]

theorem ocRefCorrector_component_sum {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν t : ℝ) (i : Fin 2) :
    (fun y : Vec 2 => ocRefCorrector α q Λ ζ m ν t y i) = fun y =>
      ∑ k ∈ (ocCutoff_support_finite (α := α) (q := q) (Λ := Λ) (m := m)
        hΛ (t := t)).toFinset,
        ocCutoff α q Λ m k.1 t * ocPulseCorrector α q Λ ζ m ν k.1 t y i := by
  funext y
  rw [ocRefCorrector_eq_finset_cutoff hΛ ν t]
  simp [Pi.smul_apply, smul_eq_mul]

theorem ocRefCorrector_component_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν t : ℝ) (i : Fin 2) :
    ContDiff ℝ ⊤ (fun y : Vec 2 => ocRefCorrector α q Λ ζ m ν t y i) := by
  classical
  rw [ocRefCorrector_component_sum hΛ ν t i]
  apply AVenhance.Infra.Classical.GalerkinModeCalculus.contDiff_finset_sum
  intro k hk
  exact contDiff_const.mul
    (pulseCorrector_component_contDiff k.2 ν t i)

theorem ocRefCorrector_component_isZ2Periodic {α q : ℝ} {Λ m : ℕ}
    {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hm : 1 ≤ m) (ν t : ℝ) (i : Fin 2) :
    IsZ2Periodic (fun y : Vec 2 => ocRefCorrector α q Λ ζ m ν t y i) := by
  classical
  intro n y
  rw [ocRefCorrector_component_sum hΛ ν t i]
  apply Finset.sum_congr rfl
  intro k hk
  have hper := pulseCorrector_component_isZ2Periodic
    (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ) hΛ hm k.2 ν t i
  exact congrArg (fun x : ℝ => ocCutoff α q Λ m k.1 t * x) (hper n y)

theorem spaceAvg_spaceGrad_zero_of_periodic {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hper : IsZ2Periodic f) (j : Fin 2) :
    spaceAvg (fun x => spaceGrad f x j) = 0 := by
  have hperC : AVenhance.Infra.Torus.IsZdPeriodic
      (AVenhance.Infra.Torus.realToComplex f) := by
    intro n x
    have h := (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen f).2 hper n x
    exact congrArg (fun y : ℝ => (y : ℂ)) h
  have hcomplex := AVenhance.Infra.Torus.integral_unitCell_coord_deriv_eq_zero
    (n := 1) j (Complex.ofRealCLM.contDiff.comp hf) hperC
  change (∫ x in AVenhance.Infra.Torus.unitCell 2,
      AVenhance.Infra.Torus.coordDeriv j
        (AVenhance.Infra.Torus.realToComplex f) x) = 0 at hcomplex
  have hderiv : AVenhance.Infra.Torus.coordDeriv j
      (AVenhance.Infra.Torus.realToComplex f) =
      fun x => (spaceGrad f x j : ℂ) := by
    funext x
    exact AVenhance.Infra.Torus.coordDeriv_realToComplex hf j x
  rw [hderiv] at hcomplex
  have hcont : Continuous (fun x => spaceGrad f x j) := by
    unfold spaceGrad
    exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hmap : (∫ x in AVenhance.Infra.Torus.unitCell 2,
      (spaceGrad f x j : ℂ)) =
      ((∫ x in AVenhance.Infra.Torus.unitCell 2, spaceGrad f x j : ℝ) : ℂ) := by
    simpa using (Complex.ofRealCLM.integral_comp_comm
      (μ := (volume : Measure (Vec 2)).restrict
        (AVenhance.Infra.Torus.unitCell 2))
      (AVenhance.Infra.Section3.FluxMatrix.continuous_integrableOn_unitCell hcont))
  have hcell : ∫ x in AVenhance.Infra.Torus.unitCell 2,
      spaceGrad f x j = 0 := by
    apply Complex.ofReal_injective
    calc
      ((∫ x in AVenhance.Infra.Torus.unitCell 2, spaceGrad f x j : ℝ) : ℂ) =
          ∫ x in AVenhance.Infra.Torus.unitCell 2, (spaceGrad f x j : ℂ) := hmap.symm
      _ = 0 := hcomplex
  unfold spaceAvg
  rw [← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
  exact hcell

end AVRegularity.CycleReference
