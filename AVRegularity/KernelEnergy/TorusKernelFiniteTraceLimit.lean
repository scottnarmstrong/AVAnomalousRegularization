-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.KernelEnergy.TorusKernelDifferentialEnergy
import AVRegularity.CoupledEnergy.CouplingBounds
import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
import AVRegularity.CoupledEnergy.Galerkin.PlainClosedTraceIdentity
import AVRegularity.CoupledEnergy.Variational.PullbackForm
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! The solved kernel coefficient ODE has the native differential mass estimate. -/

section
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

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk k (h i))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelODE_mass_deriv_perturbed_le
    (y : ℝ → CoupledPlainCoefficients (h := h) N) (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) initial a b y)
    (M ε : ℝ) (hε : 0 < ε)
    (hM : ∀ t ∈ Set.Icc a b,
      Real.sqrt (massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (y t)).val)) ≤ M)
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) y) volume a b) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      deriv (fun s => massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (y s)).val)) t +
        (5 * ν / 4 - ε) * massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) (y t)).val) ≤
      2 * M * Real.sqrt (massNormSq ρ P.π (fun i => (g i t).val)) +
        (1 / ε) * massNormSq ρ P.π (fun i => (F i t).val) := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [plainODE_mass_ae_deriv N (fun _ => k) ρ P.π P.htime
    (P.projectedMatrix N v)
    (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t))
    y initial hy hint] with t ht
  intro hmem
  rw [(ht hmem).deriv]
  have hpoint := P.kernelRhs_mass_unabsorbed_le N v t hmem (hv t hmem) (hvp t hmem)
    (y t) (fun i => F i t) (fun i => g i t) αv B lam hα hB hlam
    hsmall hstrain (hd t hmem) (hjets t hmem)
  have hyoung := coupledFluxYoung (show 0 < 4 * ε by positivity)
    (Real.sqrt (massNormSq ρ P.π (fun i => (F i t).val)))
    (Real.sqrt (massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) (y t)).val)))
  rw [Real.sq_sqrt (massNormSq_nonneg ρ P.π P.hπ _),
    Real.sq_sqrt (massGradNormSq_nonneg ρ P.π P.hπ _)] at hyoung
  have hdiv : 2 / (4 * ε) = 1 / (2 * ε) := by field_simp; ring
  rw [hdiv] at hyoung
  have hy2 :
      2 * Real.sqrt (massNormSq ρ P.π (fun i => (F i t).val)) *
        Real.sqrt (massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) (y t)).val)) ≤
      ε * massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) (y t)).val) +
        (1 / ε) * massNormSq ρ P.π (fun i => (F i t).val) := by
    calc
      _ ≤ 2 * ((4 * ε / 8) * massGradNormSq ρ P.π
          (fun i => (coupledPlainSynthesis N i (k + 1) (y t)).val) +
          (1 / (2 * ε)) * massNormSq ρ P.π (fun i => (F i t).val)) := by linarith only [hyoung]
      _ = _ := by field_simp; ring
  have hg := mul_le_mul_of_nonneg_left (hM t hmem)
    (Real.sqrt_nonneg (massNormSq ρ P.π (fun i => (g i t).val)))
  linarith only [hpoint, hy2, hg]

end TorusKernelOperator
end

/-! The solved kernel coefficient ODE has the native differential mass estimate. -/

section
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

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelODE_mass_homogeneous_deriv_le
    (y : ℝ → CoupledPlainCoefficients (h := h) N) (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun _t => plainSourceCoefficients N (fun _ => k) (fun _ => 0) (fun _ => 0)) initial a b y)
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun _t => plainSourceCoefficients N (fun _ => k) (fun _ => 0) (fun _ => 0)) y) volume a b) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      deriv (fun s => massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (y s)).val)) t +
        (5 * ν / 4) * massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) (y t)).val) ≤ 0 := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [plainODE_mass_ae_deriv N (fun _ => k) ρ P.π P.htime
    (P.projectedMatrix N v)
    (fun _t => plainSourceCoefficients N (fun _ => k) (fun _ => 0) (fun _ => 0))
    y initial hy hint] with t ht
  intro hmem
  rw [(ht hmem).deriv]
  have hpoint := P.kernelRhs_mass_homogeneous_le N v t hmem (hv t hmem) (hvp t hmem)
    (y t) αv B lam hα hB hlam
    hsmall hstrain (hd t hmem) (hjets t hmem)
  convert mul_le_mul_of_nonneg_left hpoint (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring

end TorusKernelOperator
end

/-! Time closure with the exact parenthesized forcing constants. -/

section
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

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk k (h i))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelODE_uniform_mass_energy
    (y : ℝ → CoupledPlainCoefficients (h := h) N) (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) initial a b y)
    (hycont : Continuous y)
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) y) volume a b) :
    ∀ t ∈ Set.Icc a b,
      massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (y t)).val) +
        (ν / 2) * (∫ s in Set.Icc a b,
          massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) (y s)).val)) ≤
      2 * massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (y a)).val) +
        (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
        10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2 := by
  have hac := plainSynthesis_mass_absolutelyContinuous N (fun _ => k) ρ P.π
    (hy.absolutelyContinuousOnInterval P.htime hint)
  have hr := (plainSynthesis_massGrad_continuous N (fun _ => k) ρ P.π hycont).intervalIntegrable (μ := volume) a b
  have hf := (intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr
    (massNormSq_integrable ρ P.π P.hπ (fun i => torusJet_memLp (k) (hF i)))
  have hg' := (intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr
    (massNorm_integrable ρ P.π P.hπ (fun i => torusJet_memLp (k) (memLp_one_iff_integrable.mpr (hg i))))
  have hd := P.kernelODE_mass_deriv_energy_le N v hv hvp F g αv B lam hα hB hlam
    hsmall hstrain hd hjets y initial hy hint
  obtain ⟨S, _, hbound, hclose⟩ := coupledTimeEnergy_uniform_of_deriv_le P.htime P.diffusivity_pos hac
    (fun t _ => massNormSq_nonneg ρ P.π P.hπ _)
    (fun t _ => massGradNormSq_nonneg ρ P.π P.hπ _)
    (fun t _ => Real.sqrt_nonneg _)
    (fun t _ => massNormSq_nonneg ρ P.π P.hπ _) hr hg' hf hd
  simp only [intervalIntegral.integral_of_le P.htime, ← integral_Icc_eq_integral_Ioc] at hclose
  intro t ht
  linarith [hbound t ht]

end TorusKernelOperator
end

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! Actual finite kernel solutions with an energy budget independent of truncation. -/

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

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk k (h i))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelFourierODE_exists_energy
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) :
    ∃ y : C(Set.Icc a b, CoupledPlainCoefficients (h := h) N),
      AVenhance.Infra.ODE.IsLinearIntegralSolution
        (fun t => plainMatrixCLM (P.projectedMatrix N v t))
        (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t))
        (plainInitialCoefficients N (fun _ => k) f) a b (AVenhance.Infra.ODE.extendCurve P.htime y) ∧
      AbsolutelyContinuousOnInterval (AVenhance.Infra.ODE.extendCurve P.htime y) a b ∧
    ∀ t ∈ Set.Icc a b,
      massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (AVenhance.Infra.ODE.extendCurve P.htime y t)).val) +
        (ν / 2) * (∫ s in Set.Icc a b,
          massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) (AVenhance.Infra.ODE.extendCurve P.htime y s)).val)) ≤
      2 * massNormSq ρ P.π (fun i => (f i).val) +
        (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
        10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2 := by
  obtain ⟨y, ⟨hy, hyac⟩, _⟩ := P.kernelFourierODE_existsUnique N v hv_bdd hv_meas f F g hF hg
  obtain ⟨C, hC, hb⟩ := P.projectedMatrix_bounded N v hv_bdd
  have hm : ∀ r c, AEStronglyMeasurable (fun t => P.projectedMatrix N v t r c) volume :=
    fun r c => (P.projectedMatrix_stronglyMeasurable N v hv_meas r c).aestronglyMeasurable
  have hf : IntervalIntegrable
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr
      (plainSourceCoefficients_integrable N (fun _ => k) a b F g hF hg)
  have hint := plainMatrixODE_rhs_intervalIntegrable P.htime (P.projectedMatrix N v)
    _ (plainInitialCoefficients N (fun _ => k) f) C hC hm hb hf y
  have henergy := P.kernelODE_uniform_mass_energy N v hv hvp F g αv B lam hα hB hlam
    hsmall hstrain hd hjets (AVenhance.Infra.ODE.extendCurve P.htime y)
    (plainInitialCoefficients N (fun _ => k) f) hy
    (AVenhance.Infra.ODE.continuous_extendCurve P.htime y) hF hg hint
  have hinit : AVenhance.Infra.ODE.extendCurve P.htime y a =
      plainInitialCoefficients N (fun _ => k) f := by
    simpa only [intervalIntegral.integral_same, add_zero] using hy a ⟨le_rfl, P.htime⟩
  rw [hinit] at henergy
  refine ⟨y, hy, hyac, ?_⟩
  intro t ht
  have hproj := plainInitialCoefficients_mass_le N (fun _ => k) ρ P.π P.hπ f
  linarith [henergy t ht]

end TorusKernelOperator

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! Time closure with the exact parenthesized forcing constants. -/

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

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk k (h i))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))


include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelODE_mass_perturbed_interval_le
    (y : ℝ → CoupledPlainCoefficients (h := h) N) (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) initial a b y)
    (hycont : Continuous y) (M ε : ℝ) (hM0 : 0 ≤ M) (hε : 0 < ε)
    (hM : ∀ t ∈ Set.Icc a b,
      Real.sqrt (massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (y t)).val)) ≤ M)
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) y) volume a b) :
    ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s ≤ t →
      massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (y t)).val) +
        (5 * ν / 4 - ε) * (∫ r in Set.Ioc s t,
          massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) (y r)).val)) ≤
      massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (y s)).val) +
        2 * M * (∫ r in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i r).val))) +
        (1 / ε) * (∫ r in Set.Icc a b, massNormSq ρ P.π (fun i => (F i r).val)) := by
  have hac := plainSynthesis_mass_absolutelyContinuous N (fun _ => k) ρ P.π
    (hy.absolutelyContinuousOnInterval P.htime hint)
  have hr := (plainSynthesis_massGrad_continuous N (fun _ => k) ρ P.π hycont).intervalIntegrable (μ := volume) a b
  have hf := massNormSq_integrable ρ P.π P.hπ (fun i => torusJet_memLp k (hF i))
  have hg' := massNorm_integrable ρ P.π P.hπ
    (fun i => torusJet_memLp k (memLp_one_iff_integrable.mpr (hg i)))
  let H := fun r => 2 * M * Real.sqrt (massNormSq ρ P.π (fun i => (g i r).val)) +
    (1 / ε) * massNormSq ρ P.π (fun i => (F i r).val)
  have hH : Integrable H (volume.restrict (Set.Icc a b)) :=
    (hg'.const_mul (2 * M)).add (hf.const_mul (1 / ε))
  have hd := P.kernelODE_mass_deriv_perturbed_le N v hv hvp F g αv B lam hα hB hlam
    hsmall hstrain hd hjets y initial hy M ε hε hM hint
  intro s hs t ht hst
  have he := perturbedTimeEnergy P.htime hs ht hst hac hr
    ((intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr hH) hd
  have hsub : Set.Ioc s t ⊆ Set.Icc a b := fun r hr => ⟨hs.1.trans hr.1.le, hr.2.trans ht.2⟩
  have hhi : (∫ r in Set.Ioc s t, H r) ≤ ∫ r in Set.Icc a b, H r :=
    setIntegral_mono_set hH (Filter.Eventually.of_forall (fun r =>
      add_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        (mul_nonneg (by positivity) (massNormSq_nonneg ρ P.π P.hπ _))))
      (Filter.Eventually.of_forall hsub)
  have heq : (∫ r in Set.Icc a b, H r) =
      2 * M * (∫ r in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i r).val))) +
      (1 / ε) * (∫ r in Set.Icc a b, massNormSq ρ P.π (fun i => (F i r).val)) := by
    rw [integral_add (hg'.const_mul (2 * M)) (hf.const_mul (1 / ε)), integral_const_mul, integral_const_mul]
  rw [heq] at hhi
  linarith

end TorusKernelOperator

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! The projected integrated equation for each kernel trajectory. -/

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

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem kernelFourier_projected_integrated_equation (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ V : ℝ, ∀ s ∈ Set.Icc a b, ∀ x, ‖v s x‖ ≤ V)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ s ∈ Set.Icc a b, Continuous (v s))
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (y : C(Set.Icc a b, CoupledPlainCoefficients (h := h) N))
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun s => plainMatrixCLM (P.projectedMatrix N v s))
      (fun s => plainSourceCoefficients N (fun _ => k) (fun i => F i s) (fun i => g i s))
      (plainInitialCoefficients N (fun _ => k) f) a b (AVenhance.Infra.ODE.extendCurve P.htime y))
    (φ : ∀ i, TorusHk 1 (h i)) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    (∑ i, inner ℝ (torusHkValueCLM (coupledPlainSynthesis N i k
      (AVenhance.Infra.ODE.extendCurve P.htime y t))) (torusHkValueCLM (galerkinProj N (φ i)))) -
    (∑ i, inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM (galerkinProj N (φ i)))) =
    ∑ i, coupledIntegratedRhs (fun _ => k) 0 ν a t v noLocalCoefficient
      (fun i s => F i s + P.finiteFlux N (AVenhance.Infra.ODE.extendCurve P.htime y) i s)
      g (plainHigherBochner N (fun _ => k) a b P.htime y) i (galerkinProj N (φ i)) := by
  have hforce (i : ι) : MemLp
      (fun s => F i s + P.finiteFlux N (AVenhance.Infra.ODE.extendCurve P.htime y) i s) 2
      (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_add (volume.restrict (Set.Icc a b)) 2 (F i)
      (P.finiteFlux N (AVenhance.Infra.ODE.extendCurve P.htime y) i) (hF i)
      (P.finiteFlux_memLp N _ (AVenhance.Infra.ODE.continuous_extendCurve P.htime y) i)
  have hsol := P.kernelODE_as_forced_diffusionDrift N v F g _ _ hy
  apply plainFourier_projected_integrated_equation N 0 ν ρ P.radius_pos (fun _ => k)
    P.htime v noLocalCoefficient hv_bdd hv_meas
  · intro i j d
    exact (noLocalOrders (k := k) i j d).elim
  · intro i j d
    exact (noLocalOrders (k := k) i j d).elim
  · exact hv
  · intro s hs i j d
    exact (noLocalOrders (k := k) i j d).elim
  · exact hforce
  · exact hg
  · exact hsol
  · exact ht

end TorusKernelOperator

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! Separate the actual kernel flux from prescribed flux in the integrated RHS. -/

section
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

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

omit [DecidableEq ι] in
include P in
theorem integratedRhs_add_flux (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ℝ → Vec 2 → Vec 2)
    (F Q : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (U : ℝ → CoupledHighHilbert (h := h) (fun _ => k)) (i : ι) (φ : TorusHk 1 (h i))
    (hF : MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hQ : MemLp (Q i) 2 (volume.restrict (Set.Icc a b))) :
    coupledIntegratedRhs (fun _ => k) 0 ν a t v noLocalCoefficient
      (fun i r => F i r + Q i r) g U i φ =
    coupledIntegratedRhs (fun _ => k) 0 ν a t v noLocalCoefficient F g U i φ -
      (∫ r in a..t, ∫ x in AVenhance.unitCube,
        inner ℝ (torusHkValueCLM (Q i r) x) (torusH1GradientL2CLM (E := h i) φ x)) := by
  have hsub : Set.uIcc a t ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le P.htime]
    exact Set.Icc_subset_Icc le_rfl ht.2
  have hFi0 : IntervalIntegrable (fun r => ∫ x in AVenhance.unitCube,
      inner ℝ (torusHkValueCLM (F i r) x) (torusH1GradientL2CLM (E := h i) φ x)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr
      (torusFluxSource_test_integrable k a b (F i) hF φ)
  have hQi0 : IntervalIntegrable (fun r => ∫ x in AVenhance.unitCube,
      inner ℝ (torusHkValueCLM (Q i r) x) (torusH1GradientL2CLM (E := h i) φ x)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr
      (torusFluxSource_test_integrable k a b (Q i) hQ φ)
  have hFi := hFi0.mono_set hsub
  have hQi := hQi0.mono_set hsub
  have hpoint (r : ℝ) :
      (∫ x in AVenhance.unitCube, inner ℝ (torusHkValueCLM (F i r + Q i r) x)
        (torusH1GradientL2CLM (E := h i) φ x)) =
      (∫ x in AVenhance.unitCube, inner ℝ (torusHkValueCLM (F i r) x)
        (torusH1GradientL2CLM (E := h i) φ x)) +
      (∫ x in AVenhance.unitCube, inner ℝ (torusHkValueCLM (Q i r) x)
        (torusH1GradientL2CLM (E := h i) φ x)) := by
    exact torusValuePairing_add (F i r) (Q i r) (torusH1GradientL2CLM (E := h i) φ)
  unfold coupledIntegratedRhs
  simp_rw [hpoint]
  rw [intervalIntegral.integral_add hFi hQi]
  ring

theorem finiteIntegratedRhs_eq_kernelIntegratedRhs (N : ℕ)
    (y : C(Set.Icc a b, CoupledPlainCoefficients (h := h) N))
    (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ℝ → Vec 2 → Vec 2)
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i)) (i : ι) (φ : TorusHk 1 (h i))
    (hF : MemLp (F i) 2 (volume.restrict (Set.Icc a b))) :
    coupledIntegratedRhs (fun _ => k) 0 ν a t v noLocalCoefficient
      (fun i r => F i r + P.finiteFlux N (AVenhance.Infra.ODE.extendCurve P.htime y) i r)
      g (plainHigherBochner N (fun _ => k) a b P.htime y) i φ =
    P.kernelIntegratedRhs t v F g (plainHigherBochner N (fun _ => k) a b P.htime y) i φ := by
  rw [P.integratedRhs_add_flux t ht v F
    (P.finiteFlux N (AVenhance.Infra.ODE.extendCurve P.htime y)) g _ i φ hF
    (P.finiteFlux_memLp N _ (AVenhance.Infra.ODE.continuous_extendCurve P.htime y) i)]
  have hflux :
      (∫ r in a..t, ∫ x in AVenhance.unitCube,
        inner ℝ (torusHkValueCLM (P.finiteFlux N (AVenhance.Infra.ODE.extendCurve P.htime y) i r) x)
          (torusH1GradientL2CLM (E := h i) φ x)) =
      (∫ r in a..t, ∫ x in AVenhance.unitCube,
        inner ℝ (torusHkValueCLM (P.clampedAmbientFluxCLM i r
          (plainHigherBochner N (fun _ => k) a b P.htime y r)) x)
          (torusH1GradientL2CLM (E := h i) φ x)) := by
    apply intervalIntegral.integral_congr_ae_restrict
    have hsub : Set.uIoc a t ⊆ Set.Icc a b := by
      rw [Set.uIoc_of_le ht.1]
      exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
      (P.kernelTimeFluxCLM_finite_ae N y i), ae_restrict_of_ae_restrict_of_subset hsub
      (P.kernelTimeFluxCLM_ae i (plainHigherBochner N (fun _ => k) a b P.htime y))] with r hf ha
    rw [← hf, ha]
  exact congrArg (fun z : ℝ => coupledIntegratedRhs (fun _ => k) 0 ν a t v noLocalCoefficient
    F g (plainHigherBochner N (fun _ => k) a b P.htime y) i φ - z) hflux

end TorusKernelOperator
end

/-! Coercivity bound for the higher Sobolev Bochner norm. -/

section
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

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk k (h i))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelODE_uniform_highTime_integral
    (y : ℝ → CoupledPlainCoefficients (h := h) N) (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) initial a b y)
    (hycont : Continuous y)
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) y) volume a b) :
    (∫ t in Set.Icc a b, ‖plainHigherSynthesisCLM N (fun _ => k) (y t)‖ ^ 2) ≤
      ((∑ i, P.π i) * (b - a) + (∑ i, P.π i / factorialWeightMin ρ k) * (2 / ν)) *
        (2 * massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (y a)).val) +
          (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
          10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2) := by
  have hν := P.diffusivity_pos
  let massP := ∑ i, P.π i
  let Q := ∑ i, P.π i / factorialWeightMin ρ (k)
  let C := 2 * massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k) (y a)).val) +
    (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
    10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2
  have hP : 0 ≤ massP := Finset.sum_nonneg (fun i _ => (P.hπ i).le)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => div_nonneg (P.hπ i).le (factorialWeightMin_pos ρ P.radius_pos).le)
  have henergy := P.kernelODE_uniform_mass_energy N v hv hvp F g αv B lam hα hB hlam
    hsmall hstrain hd hjets y initial hy hycont hF hg hint
  have hn : 0 ≤ ∫ s in Set.Icc a b,
      massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) (y s)).val) :=
    MeasureTheory.integral_nonneg (fun s => massGradNormSq_nonneg ρ P.π P.hπ _)
  have hEbound (t : ℝ) (ht : t ∈ Set.Icc a b) :
      massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k) (y t)).val) ≤ C := by
    have hc := henergy t ht
    change _ ≤ C at hc
    nlinarith
  have hRbound : (ν / 2) * (∫ s in Set.Icc a b,
      massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) (y s)).val)) ≤ C := by
    have hc := henergy a ⟨le_rfl, P.htime⟩
    change _ ≤ C at hc
    linarith [massNormSq_nonneg ρ P.π P.hπ (fun i => (coupledPlainSynthesis N i (k) (y a)).val)]
  have hr := (plainSynthesis_massGrad_continuous N (fun _ => k) ρ P.π hycont).intervalIntegrable (μ := volume) a b
  have hh := (intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr
    (plainHigherSynthesis_memLp N (fun _ => k) a b hycont).norm.integrable_sq
  have hconst : IntervalIntegrable (fun _ : ℝ => massP * C) volume a b := intervalIntegrable_const
  have hm := intervalIntegral.integral_mono_on P.htime hh (hconst.add (hr.const_mul Q)) (fun t ht => by
    have hc := plainHigherSynthesis_normSq_le N (fun _ => k) ρ P.radius_pos P.π P.hπ (y t)
    change _ ≤ massP * massNormSq ρ P.π (fun j => (coupledPlainSynthesis N j (k) (y t)).val) +
      Q * massGradNormSq ρ P.π (fun j => (coupledPlainSynthesis N j (k + 1) (y t)).val) at hc
    exact hc.trans (add_le_add (mul_le_mul_of_nonneg_left (hEbound t ht) hP) le_rfl))
  rw [intervalIntegral.integral_add hconst (hr.const_mul Q), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul] at hm
  simp only [smul_eq_mul] at hm
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le P.htime] at hRbound
  have hrle : (∫ s in a..b, massGradNormSq ρ P.π
      (fun i => (coupledPlainSynthesis N i (k + 1) (y s)).val)) ≤ 2 * C / ν := by
    apply (le_div_iff₀ P.diffusivity_pos).mpr
    linarith
  have hqle := mul_le_mul_of_nonneg_left hrle hQ
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le P.htime]
  change _ ≤ (massP * (b - a) + Q * (2 / ν)) * C
  have halg : (massP * (b - a) + Q * (2 / ν)) * C = (b - a) * (massP * C) + Q * (2 * C / ν) := by ring
  rw [halg]
  linarith

end TorusKernelOperator
end

/-! Continuous closed-time primitives of the actual limit kernel flux. -/

section
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

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

def carrierFlux (w : ∀ i, ℝ → TorusHk (k + 1) (h i)) (i : ι) (t : ℝ) :
    TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  P.flux (Set.projIcc a b P.htime t) (Set.projIcc a b P.htime t).property (fun j => w j t) i

omit [DecidableEq ι] in
theorem carrierFlux_eq_ambient_ae (U : CoupledHighTime (h := h) (fun _ => k) a b)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j, (w j t).val = U t j) (i : ι) :
    (fun t => P.clampedAmbientFluxCLM i t (U t)) =ᵐ[volume.restrict (Set.Icc a b)] P.carrierFlux w i := by
  filter_upwards [hW] with t ht
  have he : U t = WithLp.toLp 2 (fun j => (w j t).val) := by
    apply WithLp.ofLp_injective 2
    funext j
    exact (ht j).symm
  change P.flux (Set.projIcc a b P.htime t) _
    (ambientCarrierCLM (h := h) (k := k) (U t)) i = _
  rw [he, ambientCarrierCLM_graph]
  rfl

omit [DecidableEq ι] in
theorem carrierFlux_memLp (U : CoupledHighTime (h := h) (fun _ => k) a b)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j, (w j t).val = U t j) (i : ι) :
    MemLp (P.carrierFlux w i) 2 (volume.restrict (Set.Icc a b)) :=
  (memLp_congr_ae (P.carrierFlux_eq_ambient_ae U w hW i)).mp (P.limitFlux_memLp U i)

omit [DecidableEq ι] in
theorem kernelIntegratedRhs_eq_forcedRhs (t : ℝ) (ht : t ∈ Set.Icc a b)
    (v : ℝ → Vec 2 → Vec 2)
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (U : CoupledHighTime (h := h) (fun _ => k) a b)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hW : ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ j, (w j r).val = U r j)
    (i : ι) (φ : TorusHk 1 (h i)) :
    coupledIntegratedRhs (fun _ => k) 0 ν a t v noLocalCoefficient
      (fun i r => F i r + P.carrierFlux w i r) g U i φ = P.kernelIntegratedRhs t v F g U i φ := by
  rw [P.integratedRhs_add_flux t ht v F (P.carrierFlux w) g U i φ (hF i)
    (P.carrierFlux_memLp U w hW i)]
  have he :
      (∫ r in a..t, ∫ x in AVenhance.unitCube,
        inner ℝ (torusHkValueCLM (P.carrierFlux w i r) x) (torusH1GradientL2CLM (E := h i) φ x)) =
      (∫ r in a..t, ∫ x in AVenhance.unitCube,
        inner ℝ (torusHkValueCLM (P.clampedAmbientFluxCLM i r (U r)) x)
          (torusH1GradientL2CLM (E := h i) φ x)) := by
    apply intervalIntegral.integral_congr_ae_restrict
    have hsub : Set.uIoc a t ⊆ Set.Icc a b := by
      rw [Set.uIoc_of_le ht.1]
      exact fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
      (P.carrierFlux_eq_ambient_ae U w hW i)] with r hr
    rw [hr]
  exact congrArg (fun z : ℝ => coupledIntegratedRhs (fun _ => k) 0 ν a t v noLocalCoefficient
    F g U i φ - z) he

end TorusKernelOperator
end

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! Actual finite kernel solutions with an energy budget independent of truncation. -/

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

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk k (h i))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelFourierODE_exists_bochner_bound
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) :
    ∃ y : C(Set.Icc a b, CoupledPlainCoefficients (h := h) N),
      AVenhance.Infra.ODE.IsLinearIntegralSolution
        (fun t => plainMatrixCLM (P.projectedMatrix N v t))
        (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t))
        (plainInitialCoefficients N (fun _ => k) f) a b (AVenhance.Infra.ODE.extendCurve P.htime y) ∧
      AbsolutelyContinuousOnInterval (AVenhance.Infra.ODE.extendCurve P.htime y) a b ∧
    (∀ t ∈ Set.Icc a b,
      massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (AVenhance.Infra.ODE.extendCurve P.htime y t)).val) +
        (ν / 2) * (∫ s in Set.Icc a b,
          massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) (AVenhance.Infra.ODE.extendCurve P.htime y s)).val)) ≤
      2 * massNormSq ρ P.π (fun i => (f i).val) +
        (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
        10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2) ∧
      ‖plainHigherBochner N (fun _ => k) a b P.htime y‖ ^ 2 ≤
        ((∑ i, P.π i) * (b - a) + (∑ i, P.π i / factorialWeightMin ρ k) * (2 / ν)) *
          (2 * massNormSq ρ P.π (fun i => (f i).val) +
            (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
            10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2) := by
  obtain ⟨y, hy, hyac, henergy⟩ := P.kernelFourierODE_exists_energy N v hv hvp F g αv B lam
    hα hB hlam hsmall hstrain hd hjets hv_bdd hv_meas f hF hg
  obtain ⟨C, hC, hb⟩ := P.projectedMatrix_bounded N v hv_bdd
  have hm : ∀ r c, AEStronglyMeasurable (fun t => P.projectedMatrix N v t r c) volume :=
    fun r c => (P.projectedMatrix_stronglyMeasurable N v hv_meas r c).aestronglyMeasurable
  have hf : IntervalIntegrable
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr
      (plainSourceCoefficients_integrable N (fun _ => k) a b F g hF hg)
  have hint := plainMatrixODE_rhs_intervalIntegrable P.htime (P.projectedMatrix N v)
    _ (plainInitialCoefficients N (fun _ => k) f) C hC hm hb hf y
  have hh := P.kernelODE_uniform_highTime_integral N v hv hvp F g αv B lam hα hB hlam
    hsmall hstrain hd hjets (AVenhance.Infra.ODE.extendCurve P.htime y)
    (plainInitialCoefficients N (fun _ => k) f) hy
    (AVenhance.Infra.ODE.continuous_extendCurve P.htime y) hF hg hint
  have hinit : AVenhance.Infra.ODE.extendCurve P.htime y a =
      plainInitialCoefficients N (fun _ => k) f := by
    simpa only [intervalIntegral.integral_same, add_zero] using hy a ⟨le_rfl, P.htime⟩
  rw [hinit] at hh
  refine ⟨y, hy, hyac, henergy, ?_⟩
  rw [plainHigherBochner_normSq]
  have hproj := plainInitialCoefficients_mass_le N (fun _ => k) ρ P.π P.hπ f
  have hfactor : 0 ≤ (∑ i, P.π i) * (b - a) +
      (∑ i, P.π i / factorialWeightMin ρ k) * (2 / ν) :=
    add_nonneg (mul_nonneg (Finset.sum_nonneg (fun i _ => (P.hπ i).le)) (sub_nonneg.mpr P.htime))
      (mul_nonneg (Finset.sum_nonneg (fun i _ => div_nonneg (P.hπ i).le
        (factorialWeightMin_pos ρ P.radius_pos).le))
        (div_nonneg (by norm_num) P.diffusivity_pos.le))
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hfactor
  linarith

end TorusKernelOperator

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! Closed-time trace identification using the actual kernel weak limit. -/

section
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

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
theorem kernelClosedTrace_integrated_identity (t : ℝ) (ht : t ∈ Set.Icc a b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ B : ℝ, ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (F : ∀ i, ℝ → TorusHk (k) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (k) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, TorusHk (k) (h i))
    (N : ℕ → ℕ) (hN : StrictMono N)
    (y : (n : ℕ) → C(Set.Icc a b, CoupledPlainCoefficients (h := h) (N n)))
    (hy : ∀ n, AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun r => plainMatrixCLM (P.projectedMatrix (N n) v r))
      (fun r => plainSourceCoefficients (N n) (fun _ => k) (fun i => F i r) (fun i => g i r))
      (plainInitialCoefficients (N n) (fun _ => k) f) a b (AVenhance.Infra.ODE.extendCurve P.htime (y n)))
    (U : CoupledHighTime (h := h) (fun _ => k) a b) (Q : ℝ)
    (hu : ∀ n, ‖plainHigherBochner (N n) (fun _ => k) a b P.htime (y n)‖ ≤ Q)
    (hw : ∀ ell : CoupledHighTime (h := h) (fun _ => k) a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (plainHigherBochner (N n) (fun _ => k) a b P.htime (y n))) atTop (𝓝 (ell U)))
    (V : CoupledLowHilbert (h := h) (fun _ => k)) (R : ℝ)
    (hlow : ∀ n, ‖plainLowerSynthesisCLM (N n) (fun _ => k) (AVenhance.Infra.ODE.extendCurve P.htime (y n) t)‖ ≤ R)
    (htrace : ∀ ell : CoupledLowHilbert (h := h) (fun _ => k) →L[ℝ] ℝ,
      Tendsto (fun n => ell (plainLowerSynthesisCLM (N n) (fun _ => k) (AVenhance.Infra.ODE.extendCurve P.htime (y n) t)))
        atTop (𝓝 (ell V))) (φ : ∀ i, TorusHk 1 (h i)) :
    (∑ i, inner ℝ (coupledLowValueCLM (h := h) (fun _ => k) i V) (torusHkValueCLM (φ i))) -
      (∑ i, inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM (φ i))) =
      ∑ i, P.kernelIntegratedRhs t v F g U i (φ i) := by
  let L := fun n => plainLowerSynthesisCLM (N n) (fun _ => k) (AVenhance.Infra.ODE.extendCurve P.htime (y n) t)
  have hleft (i : ι) : Tendsto (fun n => inner ℝ (coupledLowValueCLM (h := h) (fun _ => k) i (L n))
      (torusHkValueCLM (galerkinProj (N n) (φ i)))) atTop
      (𝓝 (inner ℝ (coupledLowValueCLM (h := h) (fun _ => k) i V) (torusHkValueCLM (φ i)))) := by
    simpa only [L2.inner_def, coupledLowValueCLM_apply] using
      coupledLow_projected_test_weak_limit (fun _ => k) i L V R hlow htrace N hN (φ i)
  have hinitial (i : ι) : Tendsto (fun n => inner ℝ (torusHkValueCLM (f i))
      (torusHkValueCLM (galerkinProj (N n) (φ i)))) atTop
      (𝓝 (inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM (φ i)))) := by
    exact ((innerSL ℝ (torusHkValueCLM (f i))).continuous.continuousAt.tendsto).comp
      ((torusHkValueCLM (E := h i) (K := 1)).continuous.continuousAt.tendsto.comp
        ((galerkinProj_tendsto (φ i)).comp hN.tendsto_atTop))
  have hlhs := (tendsto_finsetSum Finset.univ (fun i _ => hleft i)).sub
    (tendsto_finsetSum Finset.univ (fun i _ => hinitial i))
  have hrhs := tendsto_finsetSum Finset.univ (fun i _ =>
    P.kernelIntegratedRhs_projected_weak_limit t ht v hv_bdd hv_meas hv F g hF hg
      (fun n => plainHigherBochner (N n) (fun _ => k) a b P.htime (y n)) U Q hu hw N hN i (φ i))
  apply tendsto_nhds_unique hlhs
  apply hrhs.congr'
  filter_upwards [] with n
  have he := P.kernelFourier_projected_integrated_equation (N n) v hv_bdd hv_meas hv
    F g f hF hg (y n) (hy n) φ t ht
  have hR (i : ι) := P.finiteIntegratedRhs_eq_kernelIntegratedRhs (N n) (y n) t ht v F g i
    (galerkinProj (N n) (φ i)) (hF i)
  simp_rw [hR] at he
  exact he.symm

end TorusKernelOperator
end

/-! Extract each component of the actual closed-time kernel identity. -/

section
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

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
omit [DecidableEq ι] in
theorem kernelIntegratedRhs_zero (t : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (U : ℝ → CoupledHighHilbert (h := h) (fun _ => k)) (i : ι) :
    P.kernelIntegratedRhs t v F g U i 0 = 0 := by
  rw [kernelIntegratedRhs, coupledIntegratedRhs_zero]
  simp only [map_zero, integral_inner_zeroLp, intervalIntegral.integral_zero, sub_zero]
theorem kernelClosedTrace_component_identity (t : ℝ) (ht : t ∈ Set.Icc a b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ B : ℝ, ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (F : ∀ i, ℝ → TorusHk (k) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (k) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, TorusHk (k) (h i))
    (N : ℕ → ℕ) (hN : StrictMono N)
    (y : (n : ℕ) → C(Set.Icc a b, CoupledPlainCoefficients (h := h) (N n)))
    (hy : ∀ n, AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun r => plainMatrixCLM (P.projectedMatrix (N n) v r))
      (fun r => plainSourceCoefficients (N n) (fun _ => k) (fun i => F i r) (fun i => g i r))
      (plainInitialCoefficients (N n) (fun _ => k) f) a b (AVenhance.Infra.ODE.extendCurve P.htime (y n)))
    (U : CoupledHighTime (h := h) (fun _ => k) a b) (Q : ℝ)
    (hu : ∀ n, ‖plainHigherBochner (N n) (fun _ => k) a b P.htime (y n)‖ ≤ Q)
    (hw : ∀ ell : CoupledHighTime (h := h) (fun _ => k) a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (plainHigherBochner (N n) (fun _ => k) a b P.htime (y n))) atTop (𝓝 (ell U)))
    (V : CoupledLowHilbert (h := h) (fun _ => k)) (R : ℝ)
    (hlow : ∀ n, ‖plainLowerSynthesisCLM (N n) (fun _ => k) (AVenhance.Infra.ODE.extendCurve P.htime (y n) t)‖ ≤ R)
    (htrace : ∀ ell : CoupledLowHilbert (h := h) (fun _ => k) →L[ℝ] ℝ,
      Tendsto (fun n => ell (plainLowerSynthesisCLM (N n) (fun _ => k) (AVenhance.Infra.ODE.extendCurve P.htime (y n) t)))
        atTop (𝓝 (ell V))) (i : ι) (φ : TorusHk 1 (h i)) :
    inner ℝ (coupledLowValueCLM (h := h) (fun _ => k) i V) (torusHkValueCLM φ) -
      inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
      P.kernelIntegratedRhs t v F g U i φ := by
  refine finiteComponent_identity
    (fun j ψ => inner ℝ (coupledLowValueCLM (h := h) (fun _ => k) j V) (torusHkValueCLM ψ) -
      inner ℝ (torusHkValueCLM (f j)) (torusHkValueCLM ψ))
    (fun j ψ => P.kernelIntegratedRhs t v F g U j ψ) ?_ ?_ ?_ i φ
  · intro j
    simp only [map_zero, inner_zero_right, sub_self]
  · intro j
    exact P.kernelIntegratedRhs_zero t v F g U j
  · intro ψ
    simpa only [Finset.sum_sub_distrib] using
      P.kernelClosedTrace_integrated_identity t ht v hv_bdd hv_meas hv F g hF hg f N hN y hy
        U Q hu hw V R hlow htrace ψ

end TorusKernelOperator
end

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! The projected integrated equation for each kernel trajectory. -/

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

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem kernelFourier_projected_component_equation (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ V : ℝ, ∀ s ∈ Set.Icc a b, ∀ x, ‖v s x‖ ≤ V)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ s ∈ Set.Icc a b, Continuous (v s))
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (y : C(Set.Icc a b, CoupledPlainCoefficients (h := h) N))
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun s => plainMatrixCLM (P.projectedMatrix N v s))
      (fun s => plainSourceCoefficients N (fun _ => k) (fun i => F i s) (fun i => g i s))
      (plainInitialCoefficients N (fun _ => k) f) a b (AVenhance.Infra.ODE.extendCurve P.htime y))
    (i : ι) (φ : TorusHk 1 (h i)) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    inner ℝ (torusHkValueCLM (coupledPlainSynthesis N i k
      (AVenhance.Infra.ODE.extendCurve P.htime y t))) (torusHkValueCLM (galerkinProj N φ)) -
    inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM (galerkinProj N φ)) =
    P.kernelIntegratedRhs t v F g (plainHigherBochner N (fun _ => k) a b P.htime y) i
      (galerkinProj N φ) := by
  refine finiteComponent_identity
    (fun j ψ => inner ℝ (torusHkValueCLM (coupledPlainSynthesis N j k
      (AVenhance.Infra.ODE.extendCurve P.htime y t))) (torusHkValueCLM (galerkinProj N ψ)) -
      inner ℝ (torusHkValueCLM (f j)) (torusHkValueCLM (galerkinProj N ψ)))
    (fun j ψ => P.kernelIntegratedRhs t v F g
      (plainHigherBochner N (fun _ => k) a b P.htime y) j (galerkinProj N ψ)) ?_ ?_ ?_ i φ
  · intro j
    simp only [map_zero, inner_zero_right, sub_self]
  · intro j
    rw [map_zero]
    exact P.kernelIntegratedRhs_zero t v F g _ j
  · intro ψ
    have he := P.kernelFourier_projected_integrated_equation N v hv_bdd hv_meas hv F g f hF hg y hy ψ t ht
    have hr (j : ι) := P.finiteIntegratedRhs_eq_kernelIntegratedRhs N y t ht v F g j
      (galerkinProj N (ψ j)) (hF j)
    simp_rw [hr] at he
    simpa only [Finset.sum_sub_distrib] using he

end TorusKernelOperator

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! Extract each component of the actual closed-time kernel identity. -/

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

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
theorem kernelFiniteTrace_value_pairing_tendsto (t : ℝ) (ht : t ∈ Set.Icc a b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ B : ℝ, ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (F : ∀ i, ℝ → TorusHk (k) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (k) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, TorusHk (k) (h i))
    (N : ℕ → ℕ) (hN : StrictMono N)
    (y : (n : ℕ) → C(Set.Icc a b, CoupledPlainCoefficients (h := h) (N n)))
    (hy : ∀ n, AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun r => plainMatrixCLM (P.projectedMatrix (N n) v r))
      (fun r => plainSourceCoefficients (N n) (fun _ => k) (fun i => F i r) (fun i => g i r))
      (plainInitialCoefficients (N n) (fun _ => k) f) a b (AVenhance.Infra.ODE.extendCurve P.htime (y n)))
    (U : CoupledHighTime (h := h) (fun _ => k) a b) (Q : ℝ)
    (hu : ∀ n, ‖plainHigherBochner (N n) (fun _ => k) a b P.htime (y n)‖ ≤ Q)
    (hw : ∀ ell : CoupledHighTime (h := h) (fun _ => k) a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (plainHigherBochner (N n) (fun _ => k) a b P.htime (y n))) atTop (𝓝 (ell U)))
    (i : ι) (φ : TorusHk 1 (h i)) :
    Tendsto (fun n => inner ℝ (torusHkValueCLM (coupledPlainSynthesis (N n) i k
      (AVenhance.Infra.ODE.extendCurve P.htime (y n) t))) (torusHkValueCLM φ)) atTop
      (𝓝 (inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) +
        P.kernelIntegratedRhs t v F g U i φ)) := by
  have hinitial : Tendsto (fun n => inner ℝ (torusHkValueCLM (f i))
      (torusHkValueCLM (galerkinProj (N n) φ))) atTop
      (𝓝 (inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ))) :=
    ((innerSL ℝ (torusHkValueCLM (f i))).continuous.continuousAt.tendsto).comp
      ((torusHkValueCLM (E := h i) (K := 1)).continuous.continuousAt.tendsto.comp
        ((galerkinProj_tendsto φ).comp hN.tendsto_atTop))
  have hrhs := P.kernelIntegratedRhs_projected_weak_limit t ht v hv_bdd hv_meas hv F g hF hg
    (fun n => plainHigherBochner (N n) (fun _ => k) a b P.htime (y n)) U Q hu hw N hN i φ
  apply (hinitial.add hrhs).congr'
  filter_upwards [] with n
  have heq := P.kernelFourier_projected_component_equation (N n) v hv_bdd hv_meas hv
    F g f hF hg (y n) (hy n) i φ t ht
  rw [galerkinProj_fixed_value_pairing k 1 (N n) _ φ
    (plainSynthesis_galerkin_fixed (N n) (fun _ => k) _ i)] at heq
  exact (add_comm _ _).trans (eq_add_of_sub_eq heq).symm

end TorusKernelOperator

end AVRegularity.KernelEnergy
end
