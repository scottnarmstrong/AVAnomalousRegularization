-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.KernelEnergyPlane.PlaneFluxTermFamily
public import AVRegularity.Statements.Intermediate.KernelEnergy.KernelWeakSolutionPlane
public import AVRegularity.CoupledEnergyPlane.SourceSobolevFlux
import AVRegularity.KernelEnergy.TorusTimeFlux
import AVRegularity.CoupledEnergy.CouplingBounds
import AVRegularity.CoupledEnergyPlane.Fourier.LaplacianProjection
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.KernelEnergyPlane

/-! Continuous closed-time primitives of the actual limit kernel flux. -/

variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)



def inputRawFlux (y : ∀ i j (α : Γ i j), ℝ → PlaneHk Set.univ (k + D - 1) (G i j α))
    (i : ι) (t : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => h i) :=
  ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
    P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      (y i j α t).toFunction.jet
        ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x)

omit [DecidableEq ι] in
theorem kernelWeakSolution_restart
    (v : ℝ → Vec 2 → Vec 2) (f : ∀ i, PlaneHk Set.univ k (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ k (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ k (h i)) (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (y : ∀ i j (α : Γ i j), ℝ → PlaneHk Set.univ (k + D - 1) (G i j α))
    (hsol : IsKernelWeakSolutionPlane ν a b v k D P.B P.C P.S f F g u w y)
    (s : ℝ) (hs : s ∈ Set.Icc a b) :
    IsKernelWeakSolutionPlane ν s b v k D P.B P.C P.S (fun i => u i s) F g u w y := by
  have hsub : Set.Icc s b ⊆ Set.Icc a b := Set.Icc_subset_Icc hs.1 le_rfl
  have hμ : volume.restrict (Set.Icc s b) ≤ volume.restrict (Set.Icc a b) :=
    Measure.restrict_mono hsub le_rfl
  refine ⟨(fun i => (hsol.1 i).mono hsub), (fun i => (hsol.2.1 i).mono_measure hμ),
    (fun i => ae_restrict_of_ae_restrict_of_subset hsub (hsol.2.2.1 i)),
    (fun _ => rfl), (fun i j α => (hsol.2.2.2.2.1 i j α).mono_measure hμ),
    (fun i j α => ae_restrict_of_ae_restrict_of_subset hsub (hsol.2.2.2.2.2.1 i j α)), ?_⟩
  intro i t ht φ
  exact weakIdentity_restart (volume.restrict (Set.univ : Set (Vec 2))) ν a s t hs.1 ht.1 v
    ((u i t).toFunction.jet (valueIndex2 k)) ((u i s).toFunction.jet (valueIndex2 k))
    ((f i).toFunction.jet (valueIndex2 k)) (φ.toFunction.jet (valueIndex2 1))
    (fun q => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
    (fun r q => (w i r).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q⟩)
    (P.inputRawFlux y i) (fun r => (F i r).toFunction.jet (valueIndex2 k))
    (fun r => (g i r).toFunction.jet (valueIndex2 k))
    (hsol.2.2.2.2.2.2 i t (hsub ht) φ) (hsol.2.2.2.2.2.2 i s hs φ)

end PlaneKernelOperator

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
namespace AVRegularity.KernelEnergyPlane

/-! Retain every regularizer gain to control the complete higher lifted carrier. -/

section
variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]

omit [FiniteDimensional ℝ G] in
theorem castPlaneHk_norm {K L : ℕ} (he : K = L) (Y : PlaneHk Set.univ K G) :
    ‖castPlaneHk he Y‖ = ‖Y‖ := by
  cases he
  rfl

theorem planeRegularizedInput_normSq_bound (ρ : ℝ) (hρ : 0 < ρ) (k D : ℕ) (hD : 2 ≤ D)
    (a b t : ℝ) (ht : t ∈ Set.Icc a b) (c : ℕ → ℝ) (r : ℝ)
    (C : H →L[ℝ] G)
    (S : ℝ → Lp G 2 (volume.restrict (Set.univ : Set (Vec 2))) →L[ℝ]
      Lp G 2 (volume.restrict (Set.univ : Set (Vec 2))))
    (hS : IsSpatialRegularizer ρ k D a b c r S) (V : PlaneHk Set.univ (k + 1) H) :
    ‖planeRegularizedInput ρ k D hD a b c r C S hS t ht V‖ ^ 2 ≤
      ((k + (D - 2) + 2 : ℕ) : ℝ) * regularizerGainBudget c r D *
        (‖C‖ ^ 2 * factorialWeightMax ρ k) / factorialWeightMin ρ k * ‖V‖ ^ 2 := by
  obtain ⟨Y, hY, hb⟩ := planeRegularizer_exists_shifted_bounds ρ k D hD a b t ht c r C S hS V
  have hm : 0 ≤ factorialWeightMax ρ k :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (k + 1)))
  have hbase : 0 ≤ ‖C‖ ^ 2 * factorialWeightMax ρ k * ‖V‖ ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg ‖C‖) hm) (sq_nonneg ‖V‖)
  have hB (m : ℕ) (hm : m ≤ D - 2 + 1) :
      derivFactorialNormSq m ρ (truncateJet (by omega : k + m ≤ k + (D - 2) + 1) Y.val) ≤
        regularizerGainBudget c r D * (‖C‖ ^ 2 * factorialWeightMax ρ k * ‖V‖ ^ 2) :=
    (hb m hm).trans (mul_le_mul_of_nonneg_right (regularizer_gain_le_budget c r D m hD hm) hbase)
  have hnorm := shiftedJet_full_norm_bound ρ hρ (D - 2 + 1) Y.val
    (regularizerGainBudget c r D * (‖C‖ ^ 2 * factorialWeightMax ρ k * ‖V‖ ^ 2)) hB
  have he : k + (D - 2) + 1 = k + D - 1 := by omega
  have hcanon : castPlaneHk he Y = planeRegularizedInput ρ k D hD a b c r C S hS t ht V := by
    apply PlaneHk.ext_value isOpen_univ
    rw [castPlaneHk_valueIndex, planeRegularizedInput_value]
    exact hY
  rw [← hcanon, castPlaneHk_norm]
  change ‖Y.val‖ ^ 2 ≤ _
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hnorm ⊢
  convert hnorm using 1
  ring
end

/-! Canonical higher kernel inputs, their linearity, and measurable switching.
The lift supplies regularity; Fourier reconstruction supplies
measurability from the value class. -/

section
variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
variable (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D) (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
  (C : H →L[ℝ] G)
  (S : ℝ → (Lp G 2 (volume.restrict (Set.univ : Set (Vec 2)))) →L[ℝ]
    Lp G 2 (volume.restrict (Set.univ : Set (Vec 2))))
  (hS : IsSpatialRegularizer ρ k D a b c r S)

def planeRegularizedInputNormBudget : ℝ :=
  Real.sqrt (((k + (D - 2) + 2 : ℕ) : ℝ) * regularizerGainBudget c r D *
    (‖C‖ ^ 2 * factorialWeightMax ρ k) / factorialWeightMin ρ k)

theorem planeRegularizedInput_norm_bound (hρ : 0 < ρ)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (V : PlaneHk Set.univ (k + 1) H) :
    ‖planeRegularizedInput ρ k D hD a b c r C S hS t ht V‖ ≤
      planeRegularizedInputNormBudget ρ k D c r C * ‖V‖ := by
  have hm : 0 ≤ factorialWeightMax ρ k :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (k + 1)))
  have hgain := regularizerGainBudget_nonneg c r D
  have hmin := (factorialWeightMin_pos ρ hρ (K := k)).le
  have hB : 0 ≤ ((k + (D - 2) + 2 : ℕ) : ℝ) * regularizerGainBudget c r D *
      (‖C‖ ^ 2 * factorialWeightMax ρ k) / factorialWeightMin ρ k := by positivity
  have hs := Real.abs_le_sqrt (planeRegularizedInput_normSq_bound ρ hρ k D hD a b t ht c r C S hS V)
  simpa only [abs_of_nonneg (norm_nonneg _), Real.sqrt_mul hB, Real.sqrt_sq_eq_abs,
    planeRegularizedInputNormBudget] using hs

def planeRegularizedInputCLM (hρ : 0 < ρ) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    PlaneHk Set.univ (k + 1) H →L[ℝ] PlaneHk Set.univ (k + D - 1) G :=
  (planeRegularizedInputLinearMap ρ k D hD a b c r C S hS t ht).mkContinuous
    (planeRegularizedInputNormBudget ρ k D c r C)
    (planeRegularizedInput_norm_bound ρ k D hD a b c r C S hS hρ t ht)
end

/-! Canonical higher kernel inputs, their linearity, and measurable switching.
The lift supplies regularity; Fourier reconstruction supplies
measurability from the value class. -/

section
variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
variable (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D) (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
  (C : H →L[ℝ] G)
  (S : ℝ → (Lp G 2 (volume.restrict (Set.univ : Set (Vec 2)))) →L[ℝ]
    Lp G 2 (volume.restrict (Set.univ : Set (Vec 2))))
  (hS : IsSpatialRegularizer ρ k D a b c r S)

variable (hρ : 0 < ρ) (hab : a ≤ b)

def clampedRegularizedInputCLM (t : ℝ) : PlaneHk Set.univ (k + 1) H →L[ℝ] PlaneHk Set.univ (k + D - 1) G :=
  planeRegularizedInputCLM ρ k D hD a b c r C S hS hρ (Set.projIcc a b hab t)
    (Set.projIcc a b hab t).property

theorem clampedRegularizedInput_stronglyMeasurable (V : PlaneHk Set.univ (k + 1) H) :
    StronglyMeasurable (fun t => clampedRegularizedInputCLM ρ k D hD a b c r C S hS hρ hab t V) := by
  apply planeCarrier_stronglyMeasurable_of_value (k + D - 1)
  have hs := (hS.1 (C.compLp (V.val (valueIndex2 (k + 1))))).comp_measurable
    (continuous_projIcc (a := a) (b := b) (h := hab)).measurable
  convert hs using 1
  funext t
  exact planeRegularizedInput_value ρ k D hD a b c r C S hS
    (Set.projIcc a b hab t) (Set.projIcc a b hab t).property V

theorem clampedRegularizedInput_norm_le (t : ℝ) :
    ‖clampedRegularizedInputCLM ρ k D hD a b c r C S hS hρ hab t‖ ≤
      planeRegularizedInputNormBudget ρ k D c r C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro V
  exact planeRegularizedInput_norm_bound ρ k D hD a b c r C S hS hρ
    (Set.projIcc a b hab t) (Set.projIcc a b hab t).property V

theorem clampedRegularizedInput_memLp (V : ℝ → PlaneHk Set.univ (k + 1) H)
    (hV : MemLp V 2 (volume.restrict (Set.Icc a b))) :
    MemLp (fun t => clampedRegularizedInputCLM ρ k D hD a b c r C S hS hρ hab t (V t)) 2
      (volume.restrict (Set.Icc a b)) :=
  AVRegularity.KernelEnergy.memLp_operator_action (volume.restrict (Set.Icc a b))
    (clampedRegularizedInputCLM ρ k D hD a b c r C S hS hρ hab)
    (clampedRegularizedInput_stronglyMeasurable ρ k D hD a b c r C S hS hρ hab)
    (planeRegularizedInputNormBudget ρ k D c r C) (Real.sqrt_nonneg _)
    (clampedRegularizedInput_norm_le ρ k D hD a b c r C S hS hρ hab) hV
end

/-! The mass pairing of the canonical kernel flux is bounded. -/

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

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

open AVRegularity.CoupledEnergy.Variational

theorem matrix_nonneg (i j : ι) :
    0 ≤ kernelSchurMatrix ν ρ P.π k D a b P.c P.r P.C P.B i j := by
  unfold kernelSchurMatrix
  apply mul_nonneg (Real.sqrt_nonneg _)
  apply Finset.sum_nonneg
  intro α _
  apply mul_nonneg (norm_nonneg _)
  apply Finset.sum_nonneg
  intro d _
  apply div_nonneg
  · exact mul_nonneg ENNReal.toReal_nonneg
      ((P.hS i j α).2.2.1 (d.1 - 2) (by have := Finset.mem_Icc.1 d.2; omega))
  · exact mul_nonneg P.diffusivity_pos.le (pow_nonneg (P.hr i j α).le _)

theorem theta_nonneg_of_component (i : ι) : 0 ≤ P.θ :=
  (Finset.sum_nonneg (fun j _ => P.matrix_nonneg i j)).trans (P.hschur.1 i)

theorem flux_massPairing_abs_le (t : ℝ) (ht : t ∈ Set.Icc a b)
    (V : ∀ i, PlaneHk Set.univ (k + 1) (h i)) :
    |∑ i, (P.π i)⁻¹ * inner ℝ
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (P.flux t ht V i).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (AVRegularity.CoupledEnergyPlane.Variational.planeGradientTensor (V i)).val)| ≤
      (ν / 8) * massGradNormSq ρ P.π (fun i => (V i).val) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl he =>
    let _ := he
    simp only [Finset.univ_eq_empty, Finset.sum_empty, abs_zero, massGradNormSq, mul_zero, le_refl]
  | inr he =>
    let _ := he
    have hθ0 := P.theta_nonneg_of_component (Classical.choice he)
    have hνθ : 0 ≤ ν * P.θ := mul_nonneg P.diffusivity_pos.le hθ0
    let R := massGradNormSq ρ P.π (fun i => (V i).val)
    have hR : 0 ≤ R := massGradNormSq_nonneg ρ P.π P.hπ _
    have hg : massNormSq ρ P.π (fun i =>
        (AVRegularity.CoupledEnergyPlane.Variational.planeGradientTensor (V i)).val) = R := by
      unfold massNormSq R massGradNormSq
      apply Finset.sum_congr rfl
      intro i _
      rw [AVRegularity.CoupledEnergyPlane.Variational.planeGradientTensor_factorialNormSq]
    have hq := Real.sqrt_le_sqrt (P.flux_mass_bound t ht V)
    rw [Real.sqrt_mul (sq_nonneg (ν * P.θ)), Real.sqrt_sq_eq_abs, abs_of_nonneg hνθ] at hq
    have hp := massFactorialPairing_abs_le ρ P.π P.hπ
      (fun i => (P.flux t ht V i).val)
      (fun i => (AVRegularity.CoupledEnergyPlane.Variational.planeGradientTensor (V i)).val)
    rw [hg] at hp
    have hh := hp.trans (mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg R))
    have hs : (ν * P.θ * Real.sqrt R) * Real.sqrt R = (ν * P.θ) * R := by
      rw [mul_assoc, ← pow_two, Real.sq_sqrt hR]
    rw [hs] at hh
    apply hh.trans
    have hb := mul_le_mul_of_nonneg_left P.hθ P.diffusivity_pos.le
    exact mul_le_mul_of_nonneg_right (hb.trans_eq (by ring)) hR

end PlaneKernelOperator
end

/-! The canonical flux as a continuous linear map, with its gradient budget. -/

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

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

open AVRegularity.CoupledEnergy.Variational
open AVRegularity.KernelEnergyPlane

def gradientBudget : ℝ := ∑ i, (P.π i)⁻¹ * factorialWeightMax ρ k

theorem gradientBudget_nonneg : 0 ≤ P.gradientBudget := by
  have hm : 0 ≤ factorialWeightMax ρ k :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (k + 1)))
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (inv_nonneg.mpr (P.hπ i).le) hm)

theorem gradient_mass_le_normSq (V : ∀ i, PlaneHk Set.univ (k + 1) (h i)) :
    massGradNormSq ρ P.π (fun i => (V i).val) ≤ P.gradientBudget * ‖V‖ ^ 2 := by
  have hm : 0 ≤ factorialWeightMax ρ k :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (k + 1)))
  unfold massGradNormSq gradientBudget
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hi := gradFactorialNormSq_le_jetNormSq ρ (V i).val
  have hn : ‖(V i).val‖ ≤ ‖V‖ := (show ‖(V i).val‖ = ‖V i‖ from rfl).trans_le (norm_le_pi_norm V i)
  have hs := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hn
  exact (mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_left hs hm))
    (inv_nonneg.mpr (P.hπ i).le)).trans_eq (by ring)

theorem flux_component_norm_bound (t : ℝ) (ht : t ∈ Set.Icc a b)
    (V : ∀ i, PlaneHk Set.univ (k + 1) (h i)) (i : ι) :
    ‖P.flux t ht V i‖ ≤
      (Real.sqrt (P.π i * (ν * P.θ) ^ 2 * P.gradientBudget) /
        Real.sqrt (factorialWeightMin ρ k)) * ‖V‖ := by
  have hf := (componentFactorial_le_mass ρ P.π P.hπ
    (fun i => (P.flux t ht V i).val) i).trans
      (mul_le_mul_of_nonneg_left (P.flux_mass_bound t ht V) (P.hπ i).le)
  have hb := hf.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (P.gradient_mass_le_normSq V) (sq_nonneg (ν * P.θ))) (P.hπ i).le)
  have hn := jetNorm_le_factorialRoot ρ P.radius_pos (P.flux t ht V i).val
  have hs := Real.sqrt_le_sqrt hb
  have hc : 0 ≤ P.π i * (ν * P.θ) ^ 2 * P.gradientBudget :=
    mul_nonneg (mul_nonneg (P.hπ i).le (sq_nonneg _)) P.gradientBudget_nonneg
  rw [← mul_assoc, ← mul_assoc, Real.sqrt_mul hc,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hs
  have hh := hn.trans (div_le_div_of_nonneg_right hs (Real.sqrt_nonneg _))
  change ‖P.flux t ht V i‖ ≤ _ at hh
  convert hh using 1; ring

def fluxBudget : ℝ := ∑ i,
  Real.sqrt (P.π i * (ν * P.θ) ^ 2 * P.gradientBudget) / Real.sqrt (factorialWeightMin ρ k)

theorem fluxBudget_nonneg : 0 ≤ P.fluxBudget :=
  Finset.sum_nonneg (fun _ _ => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem flux_norm_bound (t : ℝ) (ht : t ∈ Set.Icc a b)
    (V : ∀ i, PlaneHk Set.univ (k + 1) (h i)) : ‖P.flux t ht V‖ ≤ P.fluxBudget * ‖V‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg P.fluxBudget_nonneg (norm_nonneg _))).mpr
  intro i
  apply (P.flux_component_norm_bound t ht V i).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  unfold fluxBudget
  simpa only using! (Finset.single_le_sum
    (f := fun j : ι => Real.sqrt (P.π j * (ν * P.θ) ^ 2 * P.gradientBudget) /
      Real.sqrt (factorialWeightMin ρ k))
    (fun _ _ => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Finset.mem_univ i))

def fluxCLM (t : ℝ) (ht : t ∈ Set.Icc a b) :
    (∀ i, PlaneHk Set.univ (k + 1) (h i)) →L[ℝ] (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  (P.fluxLinearMap t ht).mkContinuous P.fluxBudget (P.flux_norm_bound t ht)

end PlaneKernelOperator
end

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.Analysis.Convolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.KernelEnergy
namespace AVRegularity.KernelEnergyPlane

/-! Joint coefficient measurability suffices for the actual plane Sobolev product. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem planeMultiplyIntervalCoefficient_time_stronglyMeasurable
    (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) (a b : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (hm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A t))
    (u : Set.Icc a b → PlaneHk Set.univ K E) (hu : StronglyMeasurable u) :
    StronglyMeasurable (fun t : Set.Icc a b =>
      planeMultiplyIntervalCoefficient ρ hρ K a b A hA t t.property (hc t t.property) (u t)) := by
  let M := (coefficientSeminorm ρ K a b A).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hb (t : Set.Icc a b) (x : Vec 2) : ‖A t x‖ ≤ M :=
    sourceCoefficient_norm_le ρ hρ K a b A hA t t.property x
  let L := fun t : Set.Icc a b => planeCoefficientOperator (A t) (hc t t.property).continuous hM (hb t)
  have hL (z : Lp E 2 (volume : Measure (Vec 2))) : StronglyMeasurable (fun t => L t z) :=
    planeCoefficientOperator_stronglyMeasurable (fun t : Set.Icc a b => A t)
      (fun t => (hc t t.property).continuous) hm hM hb z
  have hv := (planeHkValueOperator (E := E) K).continuous.comp_stronglyMeasurable hu
  have hs := timeOperator_stronglyMeasurable L hL _ hv
  apply planeCarrier_stronglyMeasurable_of_value K
  have he (t : Set.Icc a b) :
      planeToUniv (L t (planeHkValueOperator K (u t))) =
      (planeMultiplyIntervalCoefficient ρ hρ K a b A hA t t.property (hc t t.property) (u t)).val
        (valueIndex2 K) := by
    have hx := planeCoefficientOperator_eq_productValue (u t) (A t) (hc t t.property)
      (fun l x => coefficientOrderSup_derivative_bound ρ hρ K a b A hA l.val
        (Nat.le_of_lt_succ l.isLt) t t.property x) hM (hb t)
    simpa only [planeHkValueOperator_apply, planeToUniv_univToPlane, planeMultiplyIntervalCoefficient, L]
      using congrArg (planeToUniv (E := F)) hx
  have ht := (planeToUniv (E := F)).continuous.comp_stronglyMeasurable hs
  have hef := funext he
  rwa [hef] at ht

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.KernelEnergyPlane

/-! Exact gradient-energy convergence for band curves aligned with genuine time Sobolev carriers. -/

open AVRegularity.CoupledEnergyPlane.Variational
variable {ι T : Type*} [Fintype ι] [MeasurableSpace T] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

theorem bandCurve_gradient_tendsto_of_fields (μ : Measure T) (K : ι → ℕ)
    (ρ : ℝ) (π : ι → ℝ) (w : ∀ i, T → PlaneHk Set.univ (K i + 1) (E i))
    (hw : ∀ i, MemLp (w i) 2 μ) (q : ℕ → T → ProjectedFamily E)
    (hq : ∀ N i, (fun t => q N t i) =ᵐ[μ] fun t =>
      hilbertProjection N (planeHkValueOperator (K i + 1) (w i t))) :
    Tendsto (fun N => ∫ t, massGradNormSq ρ π
      (fun i => (hilbertBandHk N (K i + 1) (q N t i)).val) ∂μ)
      atTop (𝓝 (∫ t, massGradNormSq ρ π (fun i => (w i t).val) ∂μ)) := by
  let U := fun i => (hw i).toLp (w i)
  have ha (N : ℕ) (i : ι) : (fun t => q N t i) =ᵐ[μ] fun t =>
      hilbertProjection N (planeHkValueOperator (K i + 1) (U i t)) := by
    filter_upwards [hq N i, (hw i).coeFn_toLp] with t ht hw
    rw [ht, hw]
  have ht := bandCurve_gradient_integral_tendsto_of_alignment μ K ρ π U q ha
  have he : (∫ t, massGradNormSq ρ π (fun i => (U i t).val) ∂μ) =
      ∫ t, massGradNormSq ρ π (fun i => (w i t).val) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun i => (hw i).coeFn_toLp)] with t ht
    simp only [U, ht]
  rw [he] at ht
  exact ht

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! The exact mass norm `massNormSq` is a fixed continuous linear readout of the
finite family of genuine Sobolev carriers. -/

section
variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

def planeMassCoercivityBudget (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) : ℝ :=
  ∑ i, Real.sqrt (π i) / Real.sqrt (factorialWeightMin ρ (K i))

theorem planeMassCoercivityBudget_nonneg (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) :
    0 ≤ planeMassCoercivityBudget K ρ π :=
  Finset.sum_nonneg (fun _ _ => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem planeMassWeightedCarrier_lower_bound (K : ι → ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (w : ∀ i, PlaneHk Set.univ (K i) (E i)) :
    ‖w‖ ≤ planeMassCoercivityBudget K ρ π * ‖planeMassWeightedCarrierCLM (E := E) K ρ π w‖ := by
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (planeMassCoercivityBudget_nonneg K ρ π) (norm_nonneg _))).mpr
  intro i
  have hc := componentFactorial_le_mass ρ π hπ
    (fun i => (w i).val) i
  have hs := Real.sqrt_le_sqrt hc
  rw [Real.sqrt_mul (hπ i).le, ← planeMassWeightedCarrierCLM_norm (E := E) K ρ π hπ w] at hs
  have hn := jetNorm_le_factorialRoot ρ hρ (w i).val
  have hb := hn.trans (div_le_div_of_nonneg_right hs (Real.sqrt_nonneg _))
  change ‖w i‖ ≤ _ at hb
  have he : (Real.sqrt (π i) * ‖planeMassWeightedCarrierCLM (E := E) K ρ π w‖) /
      Real.sqrt (factorialWeightMin ρ (K i)) =
      (Real.sqrt (π i) / Real.sqrt (factorialWeightMin ρ (K i))) *
        ‖planeMassWeightedCarrierCLM (E := E) K ρ π w‖ := by ring
  rw [he] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  unfold planeMassCoercivityBudget
  exact Finset.single_le_sum
    (fun j _ => div_nonneg (Real.sqrt_nonneg (π j))
      (Real.sqrt_nonneg (factorialWeightMin ρ (K j)))) (Finset.mem_univ i)

local instance massTimeCarrierAdd (K : ι → ℕ) (i : ι) :
    AddCommGroup (PlaneHk Set.univ (K i) (E i)) := inferInstance
local instance massTimeCarrierTopAdd (K : ι → ℕ) (i : ι) :
    IsTopologicalAddGroup (PlaneHk Set.univ (K i) (E i)) := inferInstance

theorem planeMassWeightedTime_lower_bound {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : ι → ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (U : Lp (∀ i, PlaneHk Set.univ (K i) (E i)) 2 μ) :
    ‖U‖ ≤ planeMassCoercivityBudget K ρ π *
      ‖(planeMassWeightedCarrierCLM (E := E) K ρ π).compLpL 2 μ U‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (planeMassWeightedCarrierCLM (E := E) K ρ π) U]
    with t ht
  rw [ht]
  exact planeMassWeightedCarrier_lower_bound (E := E) K ρ hρ π hπ (U t)

theorem planeMassWeightedTime_normSq {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : ι → ℕ) (ρ : ℝ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (U : Lp (∀ i, PlaneHk Set.univ (K i) (E i)) 2 μ) :
    ‖(planeMassWeightedCarrierCLM (E := E) K ρ π).compLpL 2 μ U‖ ^ 2 =
      ∫ t, massNormSq ρ π (fun i => (U t i).val) ∂μ := by
  rw [← AVRegularity.CoupledEnergyPlane.Variational.timeLp_readout_integral_norm_square]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => planeMassWeightedCarrierCLM_normSq (E := E) K ρ π hπ (U t))

/-- Square roots of a quarter bound, over abstract reals. -/
private theorem half_le_of_sq_le_quarter {x y : ℝ} (hy : 0 ≤ y)
    (h : x ^ 2 ≤ 1 / 4 * y ^ 2) : x ≤ 1 / 2 * y := by
  nlinarith

theorem planeMassWeightedTime_half_norm_le_of_integral {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : ι → ℕ) (ρ : ℝ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (U V : Lp (∀ i, PlaneHk Set.univ (K i) (E i)) 2 μ)
    (hi : (∫ t, massNormSq ρ π (fun i => (U t i).val) ∂μ) ≤
      (1 / 4) * (∫ t, massNormSq ρ π (fun i => (V t i).val) ∂μ)) :
    ‖(planeMassWeightedCarrierCLM (E := E) K ρ π).compLpL 2 μ U‖ ≤
      (1 / 2 : ℝ) * ‖(planeMassWeightedCarrierCLM (E := E) K ρ π).compLpL 2 μ V‖ := by
  rw [← planeMassWeightedTime_normSq (E := E) μ K ρ π hπ U,
    ← planeMassWeightedTime_normSq (E := E) μ K ρ π hπ V] at hi
  exact half_le_of_sq_le_quarter (norm_nonneg _) hi
end

/-! The exact mass norm `massNormSq` is a fixed continuous linear readout of the
finite family of genuine Sobolev carriers. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

abbrev planeFluxTime_half_bound (μ : Measure ℝ) (k : ℕ) (ρ : ℝ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) :=
  planeMassWeightedTime_half_norm_le_of_integral
    (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) μ (fun _ => k) ρ π hπ

abbrev planeFluxTime_lower_bound (μ : Measure ℝ) (k : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) :=
  planeMassWeightedTime_lower_bound
    (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) μ (fun _ => k) ρ hρ π hπ
end

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.KernelEnergyPlane

/-! Measurable switching of the kernel flux terms. -/

theorem planeKernelFluxTerm_time_stronglyMeasurable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
    {K m r : ℕ} (hr : r = m + 1) (ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ)
    (A : ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 r => G)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => H)))
    (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (hm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (hC : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A t))
    (Y : Set.Icc a b → PlaneHk Set.univ (K + (m + 1)) G) (hY : StronglyMeasurable Y) :
    StronglyMeasurable (fun t : Set.Icc a b =>
      planeKernelFluxTerm hr ρ hρ a b A hA t t.property (hC t t.property) (Y t)) := by
  let e : DerivativeWord2 (m + 1) ≃ DerivativeWord2 r :=
    Equiv.cast (congrArg DerivativeWord2 hr.symm)
  let L := derivativeWordArrayIsometry (E := G) e
  have htensor := (planeKernelDerivativeTensorCLM (E := G) K (m + 1)).continuous.comp_stronglyMeasurable hY
  have hmap := (AVRegularity.CoupledEnergyPlane.mapPlaneHkOperator K
    L.toContinuousLinearMap).continuous.comp_stronglyMeasurable htensor
  have hout := planeMultiplyIntervalCoefficient_time_stronglyMeasurable ρ hρ K a b A hA hm hC _ hmap
  simpa only [planeKernelDerivativeTensorCLM_apply, kernelMapPlaneHkOperator_apply,
    AVRegularity.CoupledEnergyPlane.Variational.planeMultiplyIntervalCoefficient,
    planeKernelFluxTerm, e, L] using! hout

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergyPlane

/-! The exact mass norm `massNormSq` is a fixed continuous linear readout of the
finite family of genuine Sobolev carriers. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def componentBandJet (N k : ℕ) (i : ι) : ProjectedFamily h →L[ℝ]
    JetL2 (volume.restrict Set.univ) k (h i) :=
  (bandJetOperator N k).comp (PiLp.proj (𝕜 := ℝ) 2
    (fun j => Lp (h j) 2 (volume : Measure (Vec 2))) i)

theorem componentBandEnergy_ac (N k : ℕ) (ρ : ℝ) (i : ι)
    {a b : ℝ} {u : ℝ → ProjectedFamily h}
    (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun t => factorialNormSq ρ (hilbertBandHk N k (u t i)).val) a b :=
  factorialNormSq_absolutelyContinuous (E := h i) (μ := volume.restrict Set.univ) (K := k) ρ
    ((componentBandJet (h := h) N k i).lipschitzWith.comp_absolutelyContinuousOnInterval hu)

theorem componentBandEnergy_deriv (N k : ℕ) (ρ : ℝ) (i : ι)
    {u : ℝ → ProjectedFamily h} {q : ProjectedFamily h} {t : ℝ}
    (hu : HasDerivAt u q t) :
    deriv (fun s => factorialNormSq ρ (hilbertBandHk N k (u s i)).val) t =
      2 * factorialPairing ρ (hilbertBandHk N k (q i)).val
        (hilbertBandHk N k (u t i)).val := by
  have ht := (hasDerivAt_factorialNormSq (E := h i) (μ := volume.restrict Set.univ) (K := k) ρ
    ((componentBandJet (h := h) N k i).hasFDerivAt.comp_hasDerivAt t hu)).deriv
  simpa only [Function.comp_def, componentBandJet, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    bandJetOperator_apply, factorialPairing_comm] using ht

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeGradient_factorial_nonneg (k : ℕ) (ρ : ℝ) (u : PlaneHk Set.univ (k + 1) E) :
    0 ≤ gradFactorialNormSq ρ u.val := by
  rw [← planeGradientTensor_factorialNormSq ρ u]
  exact factorialNormSq_nonneg ρ _

theorem componentSource_pairing_le (N k : ℕ) (ρ : ℝ)
    (g : PlaneHk Set.univ k E) (u : Lp E 2 (volume : Measure (Vec 2))) :
    |factorialPairing ρ (hilbertBandHk N k (hilbertProjection N (planeHkValueOperator k g))).val
      (hilbertBandHk N k u).val| ≤
      Real.sqrt (factorialNormSq ρ g.val) * Real.sqrt (factorialNormSq ρ (hilbertBandHk N k u).val) := by
  rw [hilbertBandHk_projection, hilbertBandHk_carrier_factorialPairing]
  exact factorialPairing_abs_le ρ _ _

theorem componentFlux_pairing_young (N k : ℕ) (ρ ν : ℝ) (hν : 0 < ν)
    (F : PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E)))
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    |factorialPairing ρ (hilbertBandHk N k
      (bandDivergenceOperator (E := E) N (planeHkValueOperator k F))).val (hilbertBandHk N k u).val| ≤
      (ν / 8) * gradFactorialNormSq ρ (hilbertBandHk N (k + 1) u).val +
        (2 / ν) * factorialNormSq ρ F.val := by
  rw [bandDivergence_factorialPairing, abs_neg]
  have ht := factorialPairing_abs_le ρ F.val (planeGradientTensor (hilbertBandHk N (k + 1) u)).val
  rw [planeGradientTensor_factorialNormSq] at ht
  have hy := AVRegularity.coupledFluxYoung hν (Real.sqrt (factorialNormSq ρ F.val))
    (Real.sqrt (gradFactorialNormSq ρ (hilbertBandHk N (k + 1) u).val))
  rw [Real.sq_sqrt (factorialNormSq_nonneg ρ _),
    Real.sq_sqrt (planeGradient_factorial_nonneg k ρ _)] at hy
  exact ht.trans hy
end

/-! The exact mass norm `massNormSq` is a fixed continuous linear readout of the
finite family of genuine Sobolev carriers. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeFactorialReadout (k : ℕ) (ρ : ℝ) : PlaneHk Set.univ k E →L[ℝ]
    JetL2 (volume.restrict Set.univ) k E :=
  (factorialWeightedJetCLM ρ k).comp (planeHkGraph Set.univ k).toSubmodule.subtypeL

omit [FiniteDimensional ℝ E] in
theorem planeFactorialReadout_normSq (k : ℕ) (ρ : ℝ) (u : PlaneHk Set.univ k E) :
    ‖planeFactorialReadout (E := E) k ρ u‖ ^ 2 = factorialNormSq ρ u.val :=
  factorialWeightedJet_normSq ρ u.val

omit [FiniteDimensional ℝ E] in
theorem planeFactorialReadout_norm (k : ℕ) (ρ : ℝ) (u : PlaneHk Set.univ k E) :
    ‖planeFactorialReadout (E := E) k ρ u‖ = Real.sqrt (factorialNormSq ρ u.val) :=
  factorialWeightedJet_norm ρ u.val

omit [FiniteDimensional ℝ E] in
theorem planeFactorial_integrable (μ : Measure ℝ) (k : ℕ) (ρ : ℝ)
    (F : ℝ → PlaneHk Set.univ k E) (hF : MemLp F 2 μ) :
    Integrable (fun t => factorialNormSq ρ (F t).val) μ := by
  have ht := ((planeFactorialReadout (E := E) k ρ).comp_memLp' hF).norm.integrable_sq
  simpa only [Function.comp_def, planeFactorialReadout_normSq] using ht

omit [FiniteDimensional ℝ E] in
theorem planeFactorialRoot_integrable (μ : Measure ℝ) (k : ℕ) (ρ : ℝ)
    (g : ℝ → PlaneHk Set.univ k E) (hg : Integrable g μ) :
    Integrable (fun t => Real.sqrt (factorialNormSq ρ (g t).val)) μ := by
  have ht := ((planeFactorialReadout (E := E) k ρ).integrable_comp hg).norm
  simpa only [Function.comp_def, planeFactorialReadout_norm] using ht

theorem continuous_componentBandGradient (N k : ℕ) (ρ : ℝ) :
    Continuous (fun u : Lp E 2 (volume : Measure (Vec 2)) =>
      gradFactorialNormSq ρ (hilbertBandHk N (k + 1) u).val) := by
  let L := (planeFactorialReadout (E := PiLp 2 (fun _ : Fin 2 => E)) k ρ).comp
    ((AVRegularity.CoupledEnergyPlane.Variational.planeGradientTensorOperator (E := E) k).comp
      (hilbertBandHkOperator (E := E) N (k + 1)))
  have ht : Continuous (fun u => ‖L u‖ ^ 2) := L.continuous.norm.pow 2
  simpa only [L, ContinuousLinearMap.comp_apply, hilbertBandHkOperator_apply,
    planeFactorialReadout_normSq, AVRegularity.CoupledEnergyPlane.Variational.planeGradientTensorOperator_apply,
    AVRegularity.CoupledEnergyPlane.Variational.planeGradientTensor_factorialNormSq] using ht
end

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! The mass pairing of the projected flux is bounded. -/

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

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

open AVRegularity.CoupledEnergy.Variational

theorem projectedFlux_massPairing_abs_le (N : ℕ) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (u : ProjectedFamily h) :
    |∑ i, (P.π i)⁻¹ * factorialPairing ρ
      (hilbertBandHk N k (bandDivergenceOperator (E := h i) N
        (planeHkValueOperator k (P.flux t ht (fun j => hilbertBandHk N (k + 1) (u j)) i)))).val
      (hilbertBandHk N k (u i)).val| ≤
      (ν / 8) * massGradNormSq ρ P.π
        (fun i => (hilbertBandHk N (k + 1) (u i)).val) := by
  simp_rw [bandDivergence_factorialPairing, mul_neg, Finset.sum_neg_distrib, abs_neg,
    factorialPairing_eq_weighted_inner]
  exact P.flux_massPairing_abs_le t ht (fun i => hilbertBandHk N (k + 1) (u i))

end PlaneKernelOperator

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! The native plane fields subtract with independently prescribed flux sources. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem planeFluxDifferenceFields {K : ι → ℕ} {D : ℕ} {a b : ℝ} (hab : a ≤ b)
    (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D) (hc : C.IsMeasurable)
    (W W' : PlaneHighTime (h := h) K a b) (i : ι)
    (F F' : Lp (Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b))) :
    limitFluxField hab C hc (W - W') i (F - F') =
      limitFluxField hab C hc W i F - limitFluxField hab C hc W' i F' := by
  have hs (j : ι) (d : admissibleOrders K D i j) :
      limitEdgeField hab C hc i j d (W - W') =
        limitEdgeField hab C hc i j d W - limitEdgeField hab C hc i j d W' :=
    (limitEdgeField hab C hc i j d).toLinearMap.map_sub W W'
  simp only [limitFluxField, hs, Finset.sum_sub_distrib]
  abel

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.KernelEnergy
namespace AVRegularity.KernelEnergyPlane

/-! Sum of component absolute kernel pairings on the plane. -/

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

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
theorem flux_massPairing_sumAbs_le (t : ℝ) (ht : t ∈ Set.Icc a b)
    (V : ∀ i, PlaneHk Set.univ (k + 1) (h i)) :
    (∑ i, (P.π i)⁻¹ * |inner ℝ
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (P.flux t ht V i).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (AVRegularity.CoupledEnergyPlane.Variational.planeGradientTensor (V i)).val)|) ≤
      (ν * P.θ) * massGradNormSq ρ P.π (fun i => (V i).val) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl he =>
    let _ := he
    simp only [Finset.univ_eq_empty, Finset.sum_empty, massGradNormSq, mul_zero, le_refl]
  | inr he =>
    let _ := he
    have hθ0 := P.theta_nonneg_of_component (Classical.choice he)
    have hνθ : 0 ≤ ν * P.θ := mul_nonneg P.diffusivity_pos.le hθ0
    let R := massGradNormSq ρ P.π (fun i => (V i).val)
    have hR : 0 ≤ R := massGradNormSq_nonneg ρ P.π P.hπ _
    have hg : massNormSq ρ P.π (fun i =>
        (AVRegularity.CoupledEnergyPlane.Variational.planeGradientTensor (V i)).val) = R := by
      unfold massNormSq R massGradNormSq
      apply Finset.sum_congr rfl
      intro i _
      rw [AVRegularity.CoupledEnergyPlane.Variational.planeGradientTensor_factorialNormSq]
    have hq := Real.sqrt_le_sqrt (P.flux_mass_bound t ht V)
    rw [Real.sqrt_mul (sq_nonneg (ν * P.θ)), Real.sqrt_sq_eq_abs, abs_of_nonneg hνθ] at hq
    have hp := massFactorialPairing_sumAbs_le ρ P.π P.hπ
      (fun i => (P.flux t ht V i).val)
      (fun i => (AVRegularity.CoupledEnergyPlane.Variational.planeGradientTensor (V i)).val)
    rw [hg] at hp
    have hh := hp.trans (mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg R))
    have hs : (ν * P.θ * Real.sqrt R) * Real.sqrt R = (ν * P.θ) * R := by
      rw [mul_assoc, ← pow_two, Real.sq_sqrt hR]
    rw [hs] at hh
    exact hh

end PlaneKernelOperator

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
namespace AVRegularity.KernelEnergyPlane

/-! Time measurability of the canonical kernel flux under the premises of `kernel_energy_plane`. -/

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

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem lift_time_stronglyMeasurable
    (V : Set.Icc a b → ∀ i, PlaneHk Set.univ (k + 1) (h i)) (hV : StronglyMeasurable V)
    (i j : ι) (α : Γ i j) :
    StronglyMeasurable (fun t : Set.Icc a b => P.lift t t.property (V t) i j α) := by
  exact planeRegularizedInput_time_stronglyMeasurable ρ k D P.order_ge_two a b P.c
    (P.r i j α) (P.C i j α) (P.S i j α) (P.hS i j α) _
    ((continuous_apply j).comp_stronglyMeasurable hV)

theorem fluxTerm_time_stronglyMeasurable
    (V : Set.Icc a b → ∀ i, PlaneHk Set.univ (k + 1) (h i)) (hV : StronglyMeasurable V)
    (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :
    StronglyMeasurable (fun t : Set.Icc a b => P.fluxTerm t t.property (V t) i j α d) := by
  have hlow : k + ((d.1 - 2) + 1) ≤ k + D - 1 := by
    have := Finset.mem_Icc.1 d.2
    omega
  have hY := (AVRegularity.Sobolev.truncatePlaneHk (E := G i j α) hlow).continuous.comp_stronglyMeasurable
    (P.lift_time_stronglyMeasurable V hV i j α)
  exact planeKernelFluxTerm_time_stronglyMeasurable
    (by have := Finset.mem_Icc.1 d.2; omega) ρ P.radius_pos a b
    (P.B i j α d) (P.hB_fin i j α d) (P.hB_meas i j α d)
    (P.hB_smooth i j α d) _ hY

theorem flux_time_stronglyMeasurable
    (V : Set.Icc a b → ∀ i, PlaneHk Set.univ (k + 1) (h i)) (hV : StronglyMeasurable V)
    (i : ι) : StronglyMeasurable (fun t : Set.Icc a b => P.flux t t.property (V t) i) := by
  classical
  have hs : StronglyMeasurable (fun t : Set.Icc a b => P.assembledFlux t t.property (V t) i) :=
    (Finset.stronglyMeasurable_fun_sum _ (fun j _ =>
      (Finset.stronglyMeasurable_fun_sum _ (fun α _ =>
        (Finset.stronglyMeasurable_fun_sum _
          (fun d _ => P.fluxTerm_time_stronglyMeasurable V hV i j α d) : _)) : _)) : _)
  have he : (fun t : Set.Icc a b => P.assembledFlux t t.property (V t) i) =
      (fun t : Set.Icc a b => P.flux t t.property (V t) i) :=
    funext (fun t => P.assembledFlux_eq_flux t t.property (V t) i)
  rwa [he] at hs

end PlaneKernelOperator
end

/-! Time measurability of the canonical kernel flux under the premises of `kernel_energy_plane`. -/

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

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

local instance planeCarrierFluxNormed {U : Set (Vec 2)} {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (PlaneHk U K E) := inferInstance
local instance planeCarrierFluxInner {U : Set (Vec 2)} {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (PlaneHk U K E) := inferInstance
local instance planeCarrierFluxSpace {U : Set (Vec 2)} {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (PlaneHk U K E) := inferInstance

local instance highCarrierAdd (i : ι) : AddCommGroup (PlaneHk Set.univ (k + 1) (h i)) := inferInstance
local instance highCarrierTopAdd (i : ι) : IsTopologicalAddGroup (PlaneHk Set.univ (k + 1) (h i)) := inferInstance
local instance fluxCarrierAdd (i : ι) : AddCommGroup
    (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance fluxCarrierTopAdd (i : ι) : IsTopologicalAddGroup
    (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance

def clampedFluxCLM (t : ℝ) :
    (∀ i, PlaneHk Set.univ (k + 1) (h i)) →L[ℝ]
      (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  P.fluxCLM (Set.projIcc a b P.htime t) (Set.projIcc a b P.htime t).property

theorem clampedFlux_stronglyMeasurable (V : ∀ i, PlaneHk Set.univ (k + 1) (h i)) :
    StronglyMeasurable (fun t => P.clampedFluxCLM t V) := by
  classical
  have hs : StronglyMeasurable (fun t : Set.Icc a b =>
      ∑ i : ι, (ContinuousLinearMap.single ℝ _ i) (P.flux t t.property V i)) :=
    (Finset.stronglyMeasurable_fun_sum _ (fun i _ =>
      ((ContinuousLinearMap.single ℝ _ i).continuous.comp_stronglyMeasurable
        (P.flux_time_stronglyMeasurable _ stronglyMeasurable_const i) : _)) : _)
  have he : (fun t : Set.Icc a b => ∑ i : ι,
      (ContinuousLinearMap.single ℝ _ i) (P.flux t t.property V i)) =
      (fun t : Set.Icc a b => P.flux t t.property V) := by
    funext t
    simp only [ContinuousLinearMap.single_apply, Finset.univ_sum_single]
  rw [he] at hs
  exact hs.comp_measurable (continuous_projIcc (a := a) (b := b) (h := P.htime)).measurable

theorem clampedFlux_norm_le (t : ℝ) : ‖P.clampedFluxCLM t‖ ≤ P.fluxBudget := by
  apply ContinuousLinearMap.opNorm_le_bound _ P.fluxBudget_nonneg
  intro V
  exact P.flux_norm_bound _ _ V

def carrierFlux (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i)) (i : ι) (t : ℝ) :
    PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  P.clampedFluxCLM t (fun j => w j t) i

theorem carrierFlux_of_mem (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    P.carrierFlux w i t = P.flux t ht (fun j => w j t) i := by
  change P.flux (Set.projIcc a b P.htime t) _ (fun j => w j t) i = _
  simp only [Set.projIcc_of_mem P.htime ht]

theorem carrierFlux_memLp (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    MemLp (P.carrierFlux w i) 2 (volume.restrict (Set.Icc a b)) := by
  have hp : MemLp (fun t => fun j => w j t) 2 (volume.restrict (Set.Icc a b)) :=
    memLp_pi_iff.mpr hw
  have hs := memLp_operator_action (volume.restrict (Set.Icc a b)) P.clampedFluxCLM
    P.clampedFlux_stronglyMeasurable P.fluxBudget P.fluxBudget_nonneg P.clampedFlux_norm_le hp
  exact (memLp_pi_iff.mp hs) i

end PlaneKernelOperator
end

/-! Time measurability of the canonical kernel flux under the premises of `kernel_energy_plane`. -/

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

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

abbrev fluxTimeComponent (i : ι) :=
  timeOperatorComponent (H := ∀ j, PlaneHk Set.univ (k + 1) (h j))
    (G := fun i => PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (volume.restrict (Set.Icc a b)) P.clampedFluxCLM P.clampedFlux_stronglyMeasurable
    P.fluxBudget P.fluxBudget_nonneg P.clampedFlux_norm_le i

end PlaneKernelOperator
end

end AVRegularity.KernelEnergyPlane
end
