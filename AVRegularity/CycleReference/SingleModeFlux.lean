-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleReference.JacMatrix
public import AVRegularity.Definitions.CycleReference.OcRefCorrector
import AVRegularity.Construction.Stream.NextAdmissible
import AVenhance.Infra.Section3.FluxMatrix
public import AVenhance.Statements.Section3.SpaceAvgMat
import AVenhance.Infra.Section3.CorrectorGradient
import AVenhance.Infra.Section3.ShearFormula
import AVenhance.Infra.Section3.SpaceAverages

/-! Spatial average identities for one active shear and its pulse corrector. -/

@[expose] public section

open MeasureTheory Homogenization AVenhance
open scoped Matrix

namespace AVRegularity.CycleReference

theorem ocFrequencyNat {q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) (hm : 1 ≤ m) :
    ∃ n : ℕ, (ocEpsilon q Λ m)⁻¹ = (n : ℝ) ∧ 0 < n := by
  let n : ℕ := ⌈(Λ : ℝ) ^ (q ^ m / (q - 1))⌉₊
  have he : (ocEpsilon q Λ m)⁻¹ = (n : ℝ) := by
    simpa [n] using AVRegularity.Construction.Stream.ocEpsilon_inv_eq_nat
      (q := q) (Λ := Λ) (m := m) hm
  have hEpos := AVRegularity.Construction.Stream.ocEpsilon_pos
    (q := q) (Λ := Λ) (n := m) hΛ
  have hnR : (0 : ℝ) < (n : ℝ) := by rw [← he]; positivity
  exact ⟨n, he, by exact_mod_cast hnR⟩

theorem spaceAvg_ocSin_zero {q : ℝ} {Λ m : ℕ} {i : Fin 2}
    (hΛ : 1 ≤ Λ) (hm : 1 ≤ m) :
    AVenhance.spaceAvg (fun y : Vec 2 => Real.sin
      (2 * Real.pi * ((ocEpsilon q Λ m)⁻¹ * y i))) = 0 := by
  obtain ⟨n, he, _⟩ := ocFrequencyNat (q := q) (Λ := Λ) (m := m) hΛ hm
  have hfreq : ∀ x : ℝ,
      2 * Real.pi * ((ocEpsilon q Λ m)⁻¹ * x) = 2 * Real.pi * (n : ℝ) * x := by
    intro x
    rw [he]
    ring
  rw [show (fun y : Vec 2 => Real.sin
      (2 * Real.pi * ((ocEpsilon q Λ m)⁻¹ * y i))) =
      fun y => Real.sin (2 * Real.pi * (n : ℝ) * y i) by
        funext y
        rw [hfreq]]
  rw [AVenhance.Infra.Section3.spaceAvg_coordIntegral
    (F := fun x : ℝ => Real.sin (2 * Real.pi * (n : ℝ) * x))
    (by fun_prop) i]
  exact AVenhance.Infra.Section3.intervalAverage_sin_nat n

theorem spaceAvg_ocSin_sq_half {q : ℝ} {Λ m : ℕ} {i : Fin 2}
    (hΛ : 1 ≤ Λ) (hm : 1 ≤ m) :
    AVenhance.spaceAvg (fun y : Vec 2 => Real.sin
      (2 * Real.pi * ((ocEpsilon q Λ m)⁻¹ * y i)) ^ 2) = 1 / 2 := by
  obtain ⟨n, he, hn⟩ := ocFrequencyNat (q := q) (Λ := Λ) (m := m) hΛ hm
  have hfreq : ∀ x : ℝ,
      2 * Real.pi * ((ocEpsilon q Λ m)⁻¹ * x) = 2 * Real.pi * (n : ℝ) * x := by
    intro x
    rw [he]
    ring
  rw [show (fun y : Vec 2 => Real.sin
      (2 * Real.pi * ((ocEpsilon q Λ m)⁻¹ * y i)) ^ 2) =
      fun y => Real.sin (2 * Real.pi * (n : ℝ) * y i) ^ 2 by
        funext y
        rw [hfreq]]
  rw [AVenhance.Infra.Section3.spaceAvg_coordIntegral
    (F := fun x : ℝ => Real.sin (2 * Real.pi * (n : ℝ) * x) ^ 2)
    (by fun_prop) i]
  exact AVenhance.Infra.Section3.intervalAverage_sin_square_nat n hn

theorem ocShear_sine_formula {α q : ℝ} {Λ m : ℕ} (k : ℤ) (y : Vec 2) :
    ocShear α q Λ m k y =
      if k % 4 = 1 then
        ocEpsilon q Λ m ^ (1 + α) *
          Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 0)
      else if k % 4 = 3 then
        ocEpsilon q Λ m ^ (1 + α) *
          Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1)
      else 0 := by
  change ocEpsilon q Λ m ^ (1 + α) *
      AVenhance.psi0 k ((ocEpsilon q Λ m)⁻¹ • y) = _
  have harg (i : Fin 2) :
      2 * Real.pi * ((ocEpsilon q Λ m)⁻¹ * y i) =
        2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y i := by ring
  by_cases h1 : k % 4 = 1
  · have hR : (if k % 4 = 1 then
        ocEpsilon q Λ m ^ (1 + α) *
          Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 0)
      else if k % 4 = 3 then
        ocEpsilon q Λ m ^ (1 + α) *
          Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1)
      else 0) = ocEpsilon q Λ m ^ (1 + α) *
          Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 0) := ite_eq_left h1
    have hψ : AVenhance.psi0 k ((ocEpsilon q Λ m)⁻¹ • y) =
        Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 0) := by
      unfold AVenhance.psi0
      rw [ite_eq_left h1]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [harg 0]
    rw [hR, hψ]
  · by_cases h3 : k % 4 = 3
    · have hR1 : (if k % 4 = 1 then
          ocEpsilon q Λ m ^ (1 + α) *
            Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 0)
        else if k % 4 = 3 then
          ocEpsilon q Λ m ^ (1 + α) *
            Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1)
        else 0) = if k % 4 = 3 then
          ocEpsilon q Λ m ^ (1 + α) *
            Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1)
        else 0 := ite_eq_right h1
      have hR2 : (if k % 4 = 3 then
          ocEpsilon q Λ m ^ (1 + α) *
            Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1)
        else 0) = ocEpsilon q Λ m ^ (1 + α) *
            Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1) := ite_eq_left h3
      have hψ : AVenhance.psi0 k ((ocEpsilon q Λ m)⁻¹ • y) =
          Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1) := by
        unfold AVenhance.psi0
        rw [ite_eq_right h1, ite_eq_left h3]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [harg 1]
      rw [hR1, hR2, hψ]
    · have hR1 : (if k % 4 = 1 then
          ocEpsilon q Λ m ^ (1 + α) *
            Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 0)
        else if k % 4 = 3 then
          ocEpsilon q Λ m ^ (1 + α) *
            Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1)
        else 0) = if k % 4 = 3 then
          ocEpsilon q Λ m ^ (1 + α) *
            Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1)
        else 0 := ite_eq_right h1
      have hR2 : (if k % 4 = 3 then
          ocEpsilon q Λ m ^ (1 + α) *
            Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1)
        else 0) = 0 := ite_eq_right h3
      have hψ : AVenhance.psi0 k ((ocEpsilon q Λ m)⁻¹ • y) = 0 := by
        unfold AVenhance.psi0
        rw [ite_eq_right h1, ite_eq_right h3]
      rw [hR1, hR2, hψ]
      simp only [mul_zero]

theorem ocShearVel_horizontal {α q : ℝ} {Λ m : ℕ} {k : ℤ}
    (h1 : k % 4 = 1) (y : Vec 2) :
    ocShearVel α q Λ m k y =
      ![0, (2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) *
        (ocEpsilon q Λ m)⁻¹) *
        Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 0)] := by
  have hψ : ocShear α q Λ m k = fun z : Vec 2 =>
      ocEpsilon q Λ m ^ (1 + α) *
        Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * z 0) := by
    funext z
    rw [ocShear_sine_formula]
    simp only [h1, ite_true]
  change AVenhance.sigmaMat.mulVec
      (AVenhance.spaceGrad (ocShear α q Λ m k) y) = _
  rw [hψ, AVenhance.Infra.Section3.ShearFormula.sigmaMat_mulVec_formula]
  ext i
  fin_cases i
  · simp only [Matrix.cons_val_zero']
    rw [AVenhance.Infra.Section3.spaceGrad_sineCoordinate
      (A := ocEpsilon q Λ m ^ (1 + α))
      (ω := 2 * Real.pi * (ocEpsilon q Λ m)⁻¹) (i := 0) (j := 1) y]
    rw [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
    simp
  · simp only [Matrix.cons_val_succ']
    rw [AVenhance.Infra.Section3.spaceGrad_sineCoordinate
      (A := ocEpsilon q Λ m ^ (1 + α))
      (ω := 2 * Real.pi * (ocEpsilon q Λ m)⁻¹) (i := 0) (j := 0) y]
    rw [ite_eq_left (by decide : (0 : Fin 2) = 0)]
    ring_nf

theorem ocShearVel_vertical {α q : ℝ} {Λ m : ℕ} {k : ℤ}
    (h3 : k % 4 = 3) (y : Vec 2) :
    ocShearVel α q Λ m k y =
      ![-(2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) *
        (ocEpsilon q Λ m)⁻¹) *
        Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1), 0] := by
  have hψ : ocShear α q Λ m k = fun z : Vec 2 =>
      ocEpsilon q Λ m ^ (1 + α) *
        Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * z 1) := by
    funext z
    rw [ocShear_sine_formula]
    have h1 : k % 4 ≠ 1 := by omega
    rw [ite_eq_right h1, ite_eq_left h3]
  change AVenhance.sigmaMat.mulVec
      (AVenhance.spaceGrad (ocShear α q Λ m k) y) = _
  rw [hψ, AVenhance.Infra.Section3.ShearFormula.sigmaMat_mulVec_formula]
  ext i
  fin_cases i
  · simp only [Matrix.cons_val_zero']
    rw [AVenhance.Infra.Section3.spaceGrad_sineCoordinate
      (A := ocEpsilon q Λ m ^ (1 + α))
      (ω := 2 * Real.pi * (ocEpsilon q Λ m)⁻¹) (i := 1) (j := 1) y]
    rw [ite_eq_left (by decide : (1 : Fin 2) = 1)]
    ring_nf
  · simp only [Matrix.cons_val_succ']
    rw [AVenhance.Infra.Section3.spaceGrad_sineCoordinate
      (A := ocEpsilon q Λ m ^ (1 + α))
      (ω := 2 * Real.pi * (ocEpsilon q Λ m)⁻¹) (i := 1) (j := 0) y]
    rw [ite_eq_right (by decide : (0 : Fin 2) ≠ 1)]

theorem jacMatrix_entry_eq_spaceGrad (f : Vec 2 → Vec 2) (x : Vec 2)
    (hf : DifferentiableAt ℝ f x) (i j : Fin 2) :
    jacMatrix f x i j = AVenhance.spaceGrad (fun y => f y i) x j := by
  simp only [jacMatrix, AVenhance.spaceGrad]
  rw [fderiv_apply hf i]
  simp [Homogenization.basisVec]

theorem ocPulseCorrectorJacT_horizontal {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {k : ℤ} (h1 : k % 4 = 1) (ν t : ℝ) (y : Vec 2) :
    (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 0 1 =
      4 * Real.pi ^ 2 * (ocEpsilon q Λ m) ^ (1 + α) *
        (ocEpsilon q Λ m)⁻¹ ^ 2 *
        ocPulseMemory α q Λ ζ m ν k t *
        Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 0) := by
  have hfun : (fun z : Vec 2 =>
      ocPulseCorrector α q Λ ζ m ν k t z 1) = fun z =>
      -(ocPulseMemory α q Λ ζ m ν k t *
        (2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) *
          (ocEpsilon q Λ m)⁻¹)) *
        Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * z 0) := by
    funext z
    rw [ocPulseCorrector]
    change -ocPulseMemory α q Λ ζ m ν k t *
      ocShearVel α q Λ m k z 1 = _
    rw [ocShearVel_horizontal (k := k) h1 z]
    change -ocPulseMemory α q Λ ζ m ν k t *
      ((2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) *
        (ocEpsilon q Λ m)⁻¹) *
        Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * z 0)) = _
    ring_nf
  have hzero : (fun z : Vec 2 => ocPulseCorrector α q Λ ζ m ν k t z 0) =
      fun _ => 0 := by
    funext z
    rw [ocPulseCorrector, ocShearVel_horizontal (k := k) h1 z]
    change -ocPulseMemory α q Λ ζ m ν k t * 0 = 0
    ring
  have hdf : DifferentiableAt ℝ (ocPulseCorrector α q Λ ζ m ν k t) y := by
    apply differentiableAt_pi.2
    intro i
    fin_cases i
    · change DifferentiableAt ℝ
        (fun x => ocPulseCorrector α q Λ ζ m ν k t x (0 : Fin 2)) y
      rw [hzero]
      exact differentiableAt_const 0
    · change DifferentiableAt ℝ
        (fun x => ocPulseCorrector α q Λ ζ m ν k t x (1 : Fin 2)) y
      rw [hfun]
      fun_prop
  rw [show (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 0 1 =
      jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y 1 0 by rfl]
  rw [jacMatrix_entry_eq_spaceGrad _ _ hdf, hfun,
    AVenhance.Infra.Section3.CorrectorGradient.spaceGrad_cosCoordinate]
  simp only [↓reduceIte]
  ring

theorem ocPulseCorrectorJacT_vertical {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {k : ℤ} (h3 : k % 4 = 3) (ν t : ℝ) (y : Vec 2) :
    (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 1 0 =
      -(4 * Real.pi ^ 2 * (ocEpsilon q Λ m) ^ (1 + α) *
        (ocEpsilon q Λ m)⁻¹ ^ 2 *
        ocPulseMemory α q Λ ζ m ν k t *
        Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1)) := by
  have hfun : (fun z : Vec 2 =>
      ocPulseCorrector α q Λ ζ m ν k t z 0) = fun z =>
      ocPulseMemory α q Λ ζ m ν k t *
        (2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) *
          (ocEpsilon q Λ m)⁻¹) *
        Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * z 1) := by
    funext z
    rw [ocPulseCorrector]
    change -ocPulseMemory α q Λ ζ m ν k t *
      ocShearVel α q Λ m k z 0 = _
    rw [ocShearVel_vertical (k := k) h3 z]
    change -ocPulseMemory α q Λ ζ m ν k t *
      (-(2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) *
        (ocEpsilon q Λ m)⁻¹) *
        Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * z 1)) = _
    ring_nf
  have hzero : (fun z : Vec 2 => ocPulseCorrector α q Λ ζ m ν k t z 1) =
      fun _ => 0 := by
    funext z
    rw [ocPulseCorrector, ocShearVel_vertical (k := k) h3 z]
    change -ocPulseMemory α q Λ ζ m ν k t * 0 = 0
    ring
  have hdf : DifferentiableAt ℝ (ocPulseCorrector α q Λ ζ m ν k t) y := by
    apply differentiableAt_pi.2
    intro i
    fin_cases i
    · change DifferentiableAt ℝ
        (fun x => ocPulseCorrector α q Λ ζ m ν k t x (0 : Fin 2)) y
      rw [hfun]
      fun_prop
    · change DifferentiableAt ℝ
        (fun x => ocPulseCorrector α q Λ ζ m ν k t x (1 : Fin 2)) y
      rw [hzero]
      exact differentiableAt_const 0
  rw [show (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 1 0 =
      jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y 0 1 by rfl]
  rw [jacMatrix_entry_eq_spaceGrad _ _ hdf, hfun,
    AVenhance.Infra.Section3.CorrectorGradient.spaceGrad_cosCoordinate]
  simp only [↓reduceIte]
  ring

theorem ocPulseCorrectorJacT_horizontal_matrix {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {k : ℤ} (h1 : k % 4 = 1) (ν t : ℝ) (y : Vec 2) :
    (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ =
      Matrix.single 0 1
        (4 * Real.pi ^ 2 * (ocEpsilon q Λ m) ^ (1 + α) *
          (ocEpsilon q Λ m)⁻¹ ^ 2 * ocPulseMemory α q Λ ζ m ν k t *
          Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 0)) := by
  have hfun : (fun z : Vec 2 => ocPulseCorrector α q Λ ζ m ν k t z 1) = fun z =>
      -(ocPulseMemory α q Λ ζ m ν k t *
        (2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) *
          (ocEpsilon q Λ m)⁻¹)) *
        Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * z 0) := by
    funext z
    rw [ocPulseCorrector]
    change -ocPulseMemory α q Λ ζ m ν k t * ocShearVel α q Λ m k z 1 = _
    rw [ocShearVel_horizontal (k := k) h1 z]
    change -ocPulseMemory α q Λ ζ m ν k t *
      ((2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) *
        (ocEpsilon q Λ m)⁻¹) *
        Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * z 0)) = _
    ring_nf
  have hzero : (fun z : Vec 2 => ocPulseCorrector α q Λ ζ m ν k t z 0) = fun _ => 0 := by
    funext z
    rw [ocPulseCorrector, ocShearVel_horizontal (k := k) h1 z]
    change -ocPulseMemory α q Λ ζ m ν k t * 0 = 0
    ring
  have hdf : DifferentiableAt ℝ (ocPulseCorrector α q Λ ζ m ν k t) y := by
    apply differentiableAt_pi.2
    intro i
    fin_cases i
    · change DifferentiableAt ℝ (fun x => ocPulseCorrector α q Λ ζ m ν k t x (0 : Fin 2)) y
      rw [hzero]
      exact differentiableAt_const 0
    · change DifferentiableAt ℝ (fun x => ocPulseCorrector α q Λ ζ m ν k t x (1 : Fin 2)) y
      rw [hfun]
      fun_prop
  ext i j
  fin_cases i <;> fin_cases j
  · rw [Matrix.single_apply]
    change (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 0 0 = 0
    rw [show (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 0 0 =
      jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y 0 0 by rfl]
    rw [jacMatrix_entry_eq_spaceGrad _ _ hdf]
    change AVenhance.spaceGrad (fun z => ocPulseCorrector α q Λ ζ m ν k t z 0) y 0 = 0
    rw [hzero]
    simp [AVenhance.spaceGrad]
  · change (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 0 1 =
      4 * Real.pi ^ 2 * (ocEpsilon q Λ m) ^ (1 + α) *
        (ocEpsilon q Λ m)⁻¹ ^ 2 * ocPulseMemory α q Λ ζ m ν k t *
        Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 0)
    exact ocPulseCorrectorJacT_horizontal h1 ν t y
  · rw [Matrix.single_apply]
    change (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 1 0 = 0
    rw [show (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 1 0 =
      jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y 0 1 by rfl]
    rw [jacMatrix_entry_eq_spaceGrad _ _ hdf]
    change AVenhance.spaceGrad (fun z => ocPulseCorrector α q Λ ζ m ν k t z 0) y 1 = 0
    rw [hzero]
    simp [AVenhance.spaceGrad]
  · rw [Matrix.single_apply]
    change (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 1 1 = 0
    rw [show (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 1 1 =
      jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y 1 1 by rfl]
    rw [jacMatrix_entry_eq_spaceGrad _ _ hdf, hfun,
      AVenhance.Infra.Section3.CorrectorGradient.spaceGrad_cosCoordinate]
    simp

theorem ocPulseCorrectorJacT_vertical_matrix {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {k : ℤ} (h3 : k % 4 = 3) (ν t : ℝ) (y : Vec 2) :
    (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ =
      Matrix.single 1 0
        (-(4 * Real.pi ^ 2 * (ocEpsilon q Λ m) ^ (1 + α) *
          (ocEpsilon q Λ m)⁻¹ ^ 2 * ocPulseMemory α q Λ ζ m ν k t *
          Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1))) := by
  have hfun : (fun z : Vec 2 => ocPulseCorrector α q Λ ζ m ν k t z 0) = fun z =>
      ocPulseMemory α q Λ ζ m ν k t *
        (2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) *
          (ocEpsilon q Λ m)⁻¹) *
        Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * z 1) := by
    funext z
    rw [ocPulseCorrector]
    change -ocPulseMemory α q Λ ζ m ν k t * ocShearVel α q Λ m k z 0 = _
    rw [ocShearVel_vertical (k := k) h3 z]
    change -ocPulseMemory α q Λ ζ m ν k t *
      (-(2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) *
        (ocEpsilon q Λ m)⁻¹) *
        Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * z 1)) = _
    ring_nf
  have hzero : (fun z : Vec 2 => ocPulseCorrector α q Λ ζ m ν k t z 1) = fun _ => 0 := by
    funext z
    rw [ocPulseCorrector, ocShearVel_vertical (k := k) h3 z]
    change -ocPulseMemory α q Λ ζ m ν k t * 0 = 0
    ring
  have hdf : DifferentiableAt ℝ (ocPulseCorrector α q Λ ζ m ν k t) y := by
    apply differentiableAt_pi.2
    intro i
    fin_cases i
    · change DifferentiableAt ℝ (fun x => ocPulseCorrector α q Λ ζ m ν k t x (0 : Fin 2)) y
      rw [hfun]
      fun_prop
    · change DifferentiableAt ℝ (fun x => ocPulseCorrector α q Λ ζ m ν k t x (1 : Fin 2)) y
      rw [hzero]
      exact differentiableAt_const 0
  ext i j
  fin_cases i <;> fin_cases j
  · rw [Matrix.single_apply]
    change (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 0 0 = 0
    rw [show (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 0 0 =
      jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y 0 0 by rfl]
    rw [jacMatrix_entry_eq_spaceGrad _ _ hdf, hfun,
      AVenhance.Infra.Section3.CorrectorGradient.spaceGrad_cosCoordinate]
    simp
  · rw [Matrix.single_apply]
    change (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 0 1 = 0
    rw [show (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 0 1 =
      jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y 1 0 by rfl]
    rw [jacMatrix_entry_eq_spaceGrad _ _ hdf]
    change AVenhance.spaceGrad (fun z => ocPulseCorrector α q Λ ζ m ν k t z 1) y 0 = 0
    rw [hzero]
    simp [AVenhance.spaceGrad]
  · change (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 1 0 =
      -(4 * Real.pi ^ 2 * (ocEpsilon q Λ m) ^ (1 + α) *
        (ocEpsilon q Λ m)⁻¹ ^ 2 * ocPulseMemory α q Λ ζ m ν k t *
        Real.sin (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1))
    exact ocPulseCorrectorJacT_vertical h3 ν t y
  · rw [Matrix.single_apply]
    change (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 1 1 = 0
    rw [show (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ 1 1 =
      jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y 1 1 by rfl]
    rw [jacMatrix_entry_eq_spaceGrad _ _ hdf]
    change AVenhance.spaceGrad (fun z => ocPulseCorrector α q Λ ζ m ν k t z 1) y 1 = 0
    rw [hzero]
    simp [AVenhance.spaceGrad]

theorem pulseCellFlux_horizontal {α q ν p M : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {k : ℤ} (hΛ : 1 ≤ Λ) (hm : 1 ≤ m) (hν : 0 < ν)
    (hk : Odd k) (h1 : k % 4 = 1)
    (t : ℝ) (hM : M = ocPulseMemory α q Λ ζ m ν k t) :
    AVenhance.spaceAvgMat (fun y : Vec 2 =>
      ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (p * ocShear α q Λ m k y) • AVenhance.sigmaMat) *
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ))) =
      ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (ocMu q Λ m ν * ocHStar α q Λ m ν * p * M) • ocPi ⟨k, hk⟩ := by
  let e := ocEpsilon q Λ m
  let ψ : Vec 2 → ℝ := fun y => p * e ^ (1 + α) *
    Real.sin (2 * Real.pi * (e⁻¹ * y 0))
  let g : Vec 2 → ℝ := fun y => 4 * Real.pi ^ 2 * e ^ (1 + α) * (e ^ 2)⁻¹ *
    M * Real.sin (2 * Real.pi * (e⁻¹ * y 0))
  have he : 0 < e := AVRegularity.Construction.Stream.ocEpsilon_pos
    (q := q) (Λ := Λ) (n := m) hΛ
  have hψ (y : Vec 2) : p * ocShear α q Λ m k y = ψ y := by
    dsimp [ψ, e]
    rw [ocShear_sine_formula]
    simp [h1]
    ring_nf
  have hg (y : Vec 2) :
      (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ = Matrix.single 0 1 (g y) := by
    have hsin : Real.sin (2 * Real.pi * e⁻¹ * y 0) =
        Real.sin (2 * Real.pi * (e⁻¹ * y 0)) := by
      congr 1
      ring
    rw [ocPulseCorrectorJacT_horizontal_matrix
      (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ) h1 ν t y]
    congr 1
    dsimp [g, e]
    rw [inv_pow, hM]
    rw [← hsin]
  have hpoint (y : Vec 2) :
      ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (p * ocShear α q Λ m k y) • AVenhance.sigmaMat) *
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ)) =
      !![ν, ν * g y - ψ y; ψ y, ν + ψ y * g y] := by
    rw [hψ y, hg y]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply,
        Matrix.one_apply, Matrix.smul_apply, Matrix.add_apply,
        AVenhance.sigmaMat, ψ, g]
    all_goals ring
  have hψcont : Continuous ψ := by dsimp [ψ]; fun_prop
  have hgcont : Continuous g := by dsimp [g]; fun_prop
  have hψavg : AVenhance.spaceAvg ψ = 0 := by
    dsimp [ψ, e]
    rw [AVenhance.Infra.Section3.FluxMatrix.spaceAvg_const_mul,
      spaceAvg_ocSin_zero hΛ hm]
    ring
  have hgavg : AVenhance.spaceAvg g = 0 := by
    dsimp [g, e]
    rw [AVenhance.Infra.Section3.FluxMatrix.spaceAvg_const_mul,
      spaceAvg_ocSin_zero hΛ hm]
    ring
  let C : ℝ := p * e ^ (1 + α) *
    (4 * Real.pi ^ 2 * e ^ (1 + α) * (e ^ 2)⁻¹ * M)
  have hcross : AVenhance.spaceAvg (fun y => ψ y * g y) = C / 2 := by
    calc
      AVenhance.spaceAvg (fun y => ψ y * g y) =
          AVenhance.spaceAvg (fun y => C *
            Real.sin (2 * Real.pi * (e⁻¹ * y 0)) ^ 2) := by
        congr 1
        funext y
        dsimp [ψ, g, C]
        ring
      _ = C / 2 := by
        rw [AVenhance.Infra.Section3.FluxMatrix.spaceAvg_const_mul,
          spaceAvg_ocSin_sq_half hΛ hm]
        ring
  have hlin : AVenhance.spaceAvg (fun y => ν * g y - ψ y) = 0 := by
    calc
      AVenhance.spaceAvg (fun y => ν * g y - ψ y) =
          AVenhance.spaceAvg (fun y => (ν * g y) - ψ y) := rfl
      _ = AVenhance.spaceAvg (fun y => ν * g y) - AVenhance.spaceAvg ψ :=
        AVenhance.Infra.Section3.FluxMatrix.spaceAvg_sub_of_continuous
          (continuous_const.mul hgcont) hψcont
      _ = ν * AVenhance.spaceAvg g - 0 := by
        rw [AVenhance.Infra.Section3.FluxMatrix.spaceAvg_const_mul, hψavg]
      _ = 0 := by rw [hgavg]; ring
  have hdiag : AVenhance.spaceAvg (fun y => ν + ψ y * g y) = ν + C / 2 := by
    calc
      AVenhance.spaceAvg (fun y => ν + ψ y * g y) =
          AVenhance.spaceAvg (fun y => (fun _ : Vec 2 => ν) y + ψ y * g y) := rfl
      _ = AVenhance.spaceAvg (fun _ : Vec 2 => ν) +
          AVenhance.spaceAvg (fun y => ψ y * g y) :=
        AVenhance.Infra.Section3.FluxMatrix.spaceAvg_add_of_continuous
          continuous_const (hψcont.mul hgcont)
      _ = ν + C / 2 := by rw [AVenhance.Infra.Section3.FluxMatrix.spaceAvg_const_eq, hcross]
  have hC : C / 2 = ocMu q Λ m ν * ocHStar α q Λ m ν * p * M := by
    dsimp [C]
    have hpow : ocEpsilon q Λ m ^ (1 + α) * ocEpsilon q Λ m ^ (1 + α) =
        ocEpsilon q Λ m ^ (2 * (1 + α)) := by
      rw [← Real.rpow_add he]
      congr 1
      ring
    calc
      C / 2 = p * (4 * Real.pi ^ 2 *
          (ocEpsilon q Λ m ^ (1 + α) * ocEpsilon q Λ m ^ (1 + α)) *
          (ocEpsilon q Λ m ^ 2)⁻¹ * M) / 2 := by ring
      _ = p * (4 * Real.pi ^ 2 * ocEpsilon q Λ m ^ (2 * (1 + α)) *
          (ocEpsilon q Λ m ^ 2)⁻¹ * M) / 2 := by rw [hpow]
      _ = ocMu q Λ m ν * ocHStar α q Λ m ν * p * M := by
        dsimp [ocMu, ocHStar]
        field_simp [ne_of_gt he, ne_of_gt hν]
        
  calc
    _ = AVenhance.spaceAvgMat (fun y : Vec 2 =>
        !![ν, ν * g y - ψ y; ψ y, ν + ψ y * g y]) := by
      congr 1
      funext y
      exact hpoint y
    _ = ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (ocMu q Λ m ν * ocHStar α q Λ m ν * p * M) • ocPi ⟨k, hk⟩ := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [AVenhance.spaceAvgMat, Matrix.of_apply, Matrix.smul_apply,
          Matrix.add_apply, ocPi, h1,
          AVenhance.Infra.Section3.FluxMatrix.spaceAvg_const_eq]
      · simp [AVenhance.spaceAvgMat, Matrix.of_apply, Matrix.smul_apply,
          Matrix.add_apply, ocPi, h1, hlin]
      · simp [AVenhance.spaceAvgMat, Matrix.of_apply, Matrix.smul_apply,
          Matrix.add_apply, ocPi, h1, hψavg]
      · simp [AVenhance.spaceAvgMat, Matrix.of_apply, Matrix.smul_apply,
          Matrix.add_apply, ocPi, h1,
          hdiag, hC]

theorem pulseCellFlux_vertical {α q ν p M : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {k : ℤ} (hΛ : 1 ≤ Λ) (hm : 1 ≤ m) (hν : 0 < ν)
    (hk : Odd k) (h3 : k % 4 = 3)
    (t : ℝ) (hM : M = ocPulseMemory α q Λ ζ m ν k t) :
    AVenhance.spaceAvgMat (fun y : Vec 2 =>
      ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (p * ocShear α q Λ m k y) • AVenhance.sigmaMat) *
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ))) =
      ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (ocMu q Λ m ν * ocHStar α q Λ m ν * p * M) • ocPi ⟨k, hk⟩ := by
  let e := ocEpsilon q Λ m
  let ψ : Vec 2 → ℝ := fun y => p * e ^ (1 + α) *
    Real.sin (2 * Real.pi * (e⁻¹ * y 1))
  let g : Vec 2 → ℝ := fun y => -4 * Real.pi ^ 2 * e ^ (1 + α) * (e ^ 2)⁻¹ *
    M * Real.sin (2 * Real.pi * (e⁻¹ * y 1))
  have he : 0 < e := AVRegularity.Construction.Stream.ocEpsilon_pos
    (q := q) (Λ := Λ) (n := m) hΛ
  have hψ (y : Vec 2) : p * ocShear α q Λ m k y = ψ y := by
    dsimp [ψ, e]
    rw [ocShear_sine_formula]
    have hk1 : k % 4 ≠ 1 := by omega
    rw [ite_eq_right hk1, ite_eq_left h3]
    ring_nf
  have hg (y : Vec 2) :
      (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ = Matrix.single 1 0 (g y) := by
    have hsin : Real.sin (2 * Real.pi * e⁻¹ * y 1) =
        Real.sin (2 * Real.pi * (e⁻¹ * y 1)) := by
      congr 1
      ring
    have hsin' : Real.sin (2 * Real.pi * (e⁻¹ * y 1)) =
        Real.sin (2 * Real.pi * ((ocEpsilon q Λ m)⁻¹ * y 1)) := by
      congr 1
    rw [ocPulseCorrectorJacT_vertical_matrix
      (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ) h3 ν t y]
    congr 1
    dsimp [g, e]
    rw [inv_pow, hM, hsin']
    rw [hsin, hsin']
    ring
  have hpoint (y : Vec 2) :
      ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (p * ocShear α q Λ m k y) • AVenhance.sigmaMat) *
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ)) =
      !![ν - ψ y * g y, -ψ y; ψ y + ν * g y, ν] := by
    rw [hψ y, hg y]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply,
        Matrix.one_apply, Matrix.smul_apply, Matrix.add_apply,
        AVenhance.sigmaMat, ψ, g]
  have hψcont : Continuous ψ := by dsimp [ψ]; fun_prop
  have hgcont : Continuous g := by dsimp [g]; fun_prop
  have hψavg : AVenhance.spaceAvg ψ = 0 := by
    dsimp [ψ, e]
    rw [AVenhance.Infra.Section3.FluxMatrix.spaceAvg_const_mul,
      spaceAvg_ocSin_zero hΛ hm]
    ring
  have hgavg : AVenhance.spaceAvg g = 0 := by
    dsimp [g, e]
    rw [AVenhance.Infra.Section3.FluxMatrix.spaceAvg_const_mul,
      spaceAvg_ocSin_zero hΛ hm]
    ring
  let C : ℝ := -p * e ^ (1 + α) *
    (4 * Real.pi ^ 2 * e ^ (1 + α) * (e ^ 2)⁻¹ * M)
  have hcross : AVenhance.spaceAvg (fun y => ψ y * g y) = C / 2 := by
    calc
      AVenhance.spaceAvg (fun y => ψ y * g y) =
          AVenhance.spaceAvg (fun y => C *
            Real.sin (2 * Real.pi * (e⁻¹ * y 1)) ^ 2) := by
        congr 1
        funext y
        dsimp [ψ, g, C]
        ring
      _ = C / 2 := by
        rw [AVenhance.Infra.Section3.FluxMatrix.spaceAvg_const_mul,
          spaceAvg_ocSin_sq_half hΛ hm]
        ring
  have hdiag : AVenhance.spaceAvg (fun y => ν - ψ y * g y) = ν - C / 2 := by
    calc
      AVenhance.spaceAvg (fun y => ν - ψ y * g y) =
          AVenhance.spaceAvg (fun y => (fun _ : Vec 2 => ν) y - ψ y * g y) := rfl
      _ = AVenhance.spaceAvg (fun _ : Vec 2 => ν) -
          AVenhance.spaceAvg (fun y => ψ y * g y) :=
        AVenhance.Infra.Section3.FluxMatrix.spaceAvg_sub_of_continuous
          continuous_const (hψcont.mul hgcont)
      _ = ν - C / 2 := by
        rw [AVenhance.Infra.Section3.FluxMatrix.spaceAvg_const_eq, hcross]
  have hlin : AVenhance.spaceAvg (fun y => ψ y + ν * g y) = 0 := by
    calc
      AVenhance.spaceAvg (fun y => ψ y + ν * g y) =
          AVenhance.spaceAvg (fun y => ψ y + (fun _ : Vec 2 => ν) y * g y) := rfl
      _ = AVenhance.spaceAvg ψ + AVenhance.spaceAvg (fun y => ν * g y) :=
        AVenhance.Infra.Section3.FluxMatrix.spaceAvg_add_of_continuous
          hψcont (continuous_const.mul hgcont)
      _ = 0 + ν * AVenhance.spaceAvg g := by
        rw [hψavg, AVenhance.Infra.Section3.FluxMatrix.spaceAvg_const_mul]
      _ = 0 := by rw [hgavg]; ring
  have hnegψ : AVenhance.spaceAvg (fun y => -ψ y) = 0 := by
    calc
      AVenhance.spaceAvg (fun y => -ψ y) = -AVenhance.spaceAvg ψ := by
        unfold AVenhance.spaceAvg
        rw [integral_neg]
      _ = 0 := by rw [hψavg]; ring
  have hC : -C / 2 = ocMu q Λ m ν * ocHStar α q Λ m ν * p * M := by
    dsimp [C]
    have hpow : ocEpsilon q Λ m ^ (1 + α) * ocEpsilon q Λ m ^ (1 + α) =
        ocEpsilon q Λ m ^ (2 * (1 + α)) := by
      rw [← Real.rpow_add he]
      congr 1
      ring
    calc
      -C / 2 = p * (4 * Real.pi ^ 2 *
          (ocEpsilon q Λ m ^ (1 + α) * ocEpsilon q Λ m ^ (1 + α)) *
          (ocEpsilon q Λ m ^ 2)⁻¹ * M) / 2 := by ring
      _ = p * (4 * Real.pi ^ 2 * ocEpsilon q Λ m ^ (2 * (1 + α)) *
          (ocEpsilon q Λ m ^ 2)⁻¹ * M) / 2 := by rw [hpow]
      _ = ocMu q Λ m ν * ocHStar α q Λ m ν * p * M := by
        dsimp [ocMu, ocHStar]
        field_simp [ne_of_gt he, ne_of_gt hν]
  calc
    _ = AVenhance.spaceAvgMat (fun y : Vec 2 =>
        !![ν - ψ y * g y, -ψ y; ψ y + ν * g y, ν]) := by
      congr 1
      funext y
      exact hpoint y
    _ = ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (ocMu q Λ m ν * ocHStar α q Λ m ν * p * M) • ocPi ⟨k, hk⟩ := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [AVenhance.spaceAvgMat, Matrix.of_apply, Matrix.smul_apply,
          Matrix.add_apply, ocPi, h3, hdiag]
        rw [← hC]
        ring
      · simp [AVenhance.spaceAvgMat, Matrix.of_apply, Matrix.smul_apply,
          Matrix.add_apply, ocPi, h3, hnegψ]
      · simp [AVenhance.spaceAvgMat, Matrix.of_apply, Matrix.smul_apply,
          Matrix.add_apply, ocPi, h3, hlin]
      · simp [AVenhance.spaceAvgMat, Matrix.of_apply, Matrix.smul_apply,
          Matrix.add_apply, ocPi, h3,
          AVenhance.Infra.Section3.FluxMatrix.spaceAvg_const_eq]

end AVRegularity.CycleReference
