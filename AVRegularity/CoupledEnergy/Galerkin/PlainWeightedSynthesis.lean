-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Galerkin.PlainVariationalEnergy
import AVRegularity.CoupledEnergy.Galerkin.PlainLowerSynthesis
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassGradNormSq
public import AVRegularity.CoupledEnergy.Variational.FactorialPairing
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassNormSq
import AVenhance.Infra.ODE.Linear.Energy

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Extending the actual interval Fourier matrix without any Sobolev state instances. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Clamp only the coefficient time argument, keeping the ODE state a plain scalar vector. -/
def plainIntervalMatrix (N D : ℕ) (ν : ℝ) (K : ι → ℕ)
    (a b : ℝ) (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (t : ℝ) (r c : CoupledFourierModeIndex (h := h) N) : ℝ :=
  plainFourierMatrix N D ν K v A (Set.projIcc a b hab t) r c

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Time clamping changes no Fourier entry on the original closed interval. -/
theorem plainIntervalMatrix_of_mem (N D : ℕ) (ν : ℝ) (K : ι → ℕ)
    (a b : ℝ) (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (t : ℝ) (ht : t ∈ Set.Icc a b) (r c : CoupledFourierModeIndex (h := h) N) :
    plainIntervalMatrix N D ν K a b hab v A t r c = plainFourierMatrix N D ν K v A t r c := by
  simp only [plainIntervalMatrix, Set.projIcc_of_mem hab ht]

omit [∀ i, CompleteSpace (h i)] in
theorem plainIntervalMatrix_stronglyMeasurable (N D : ℕ) (ν : ℝ) (K : ι → ℕ)
    (a b : ℝ) (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (r c : CoupledFourierModeIndex (h := h) N) :
    StronglyMeasurable (fun t => plainIntervalMatrix N D ν K a b hab v A t r c) := by
  exact (plainFourierMatrix_stronglyMeasurable N D ν K
    (fun t : Set.Icc a b => v t) hv (fun i i' d t => A i i' d t) hA r c).comp_measurable
      (continuous_projIcc (a := a) (b := b) (h := hab)).measurable

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The zeroth summand of the seminorm bounds the coefficient itself. -/
theorem plainCoefficient_norm_le_seminorm (ρ : ℝ) (hρ : 0 < ρ) (K₀ : ℕ)
    (a b : ℝ) {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hA : coefficientSeminorm ρ K₀ a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (x : Vec 2) :
    ‖A t x‖ ≤ (coefficientSeminorm ρ K₀ a b A).toReal := by
  have hz : ‖A t x‖ ≤ ‖coefficientDerivativeArray (A t) 0 x‖ := by
    simpa only [orderedCoefficientDerivative_zero] using
      orderedCoefficientDerivative_norm_le_array (A t) 0 (fun j => Fin.elim0 j) x
  have hb := coefficientSeminorm_derivative_bound ρ hρ K₀ a b A hA
    ⟨0, Nat.succ_pos K₀⟩ t ht x
  exact hz.trans (by simpa using hb)

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The actual clamped Fourier entries have a common finite bound from the data. -/
theorem plainIntervalMatrix_bounded (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ)
    (a b : ℝ) (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hv : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t r c, |plainIntervalMatrix N D ν K a b hab v A t r c| ≤ C := by
  obtain ⟨V, hv⟩ := hv
  let B : ∀ i i', admissibleOrders K D i i' → ℝ := fun i i' d => (coefficientSeminorm ρ (K i) a b (A i i' d)).toReal
  have hB : ∀ i i' d, 0 ≤ B i i' d := fun _ _ _ => ENNReal.toReal_nonneg
  let C₀ := plainFourierEntryBound (h := h) N D ν (max V 0) K B
  have hC₀ : ∀ r c, 0 ≤ C₀ r c :=
    plainFourierEntryBound_nonneg (h := h) N D ν (max V 0) (le_max_right _ _) K B hB
  refine ⟨∑ r, ∑ c, C₀ r c,
    Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun c _ => hC₀ r c)), ?_⟩
  intro t r c
  have hentry : |plainIntervalMatrix N D ν K a b hab v A t r c| ≤ C₀ r c := by
    exact plainFourierMatrix_entry_bound N D ν (max V 0) (le_max_right _ _) K
      (fun s => v (Set.projIcc a b hab s))
      (fun s x => (hv _ (Set.projIcc a b hab s).property x).trans (le_max_left _ _))
      (fun i i' d s => A i i' d (Set.projIcc a b hab s)) B hB
      (fun i i' d s x => plainCoefficient_norm_le_seminorm ρ hρ (K i) a b (A i i' d)
        (hA i i' d) _ (Set.projIcc a b hab s).property x) t r c
  exact hentry.trans ((Finset.single_le_sum (fun c _ => hC₀ r c) (Finset.mem_univ c)).trans
    (Finset.single_le_sum (fun r _ => Finset.sum_nonneg (fun c _ => hC₀ r c))
      (Finset.mem_univ r)))
end

/-! Remove time clamping from the solved Fourier ODE on its original interval. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (N D : ℕ) (ν : ℝ) (K : ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (f y : ℝ → CoupledPlainCoefficients (h := h) N)

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The clamped and original scalar matrix actions agree on the full interval. -/
theorem plainIntervalMatrixCLM_of_mem (t : ℝ) (ht : t ∈ Set.Icc a b) :
    plainMatrixCLM (plainIntervalMatrix N D ν K a b hab v A t) =
      plainMatrixCLM (plainFourierMatrix N D ν K v A t) := by
  congr 1
  funext r c
  exact plainIntervalMatrix_of_mem N D ν K a b hab v A t ht r c

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The actual unclamped RHS inherits the integrability already proved for the finite ODE. -/
theorem plainIntervalRhs_intervalIntegrable
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (plainIntervalMatrix N D ν K a b hab v A t)) f y) volume a b) :
    IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (plainFourierMatrix N D ν K v A t)) f y) volume a b := by
  apply hint.congr_ae
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  filter_upwards with t
  intro ht
  have ht' : t ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc ht
  simp only [AVenhance.Infra.ODE.linearRhs, plainIntervalMatrixCLM_of_mem N D ν K a b hab v A t ht']

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The solved clamped system is the literal Fourier integral system on the original interval. -/
theorem plainIntervalSolution_unclamp (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (plainIntervalMatrix N D ν K a b hab v A t)) f initial a b y) :
    AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (plainFourierMatrix N D ν K v A t)) f initial a b y := by
  intro t ht
  rw [hy t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Set.Icc a b := by
    rw [Set.uIcc_of_le ht.1] at hs
    exact Set.Icc_subset_Icc le_rfl ht.2 hs
  simp only [AVenhance.Infra.ODE.linearRhs, plainIntervalMatrixCLM_of_mem N D ν K a b hab v A s hs']
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Time differentiation of the exact factorial mass energy after finite synthesis. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- A single fixed linear observable realizes the entire weighted component jet. -/
def plainWeightedSynthesisCLM (N : ℕ) (i : ι) (K : ℕ) (ρ : ℝ) :
    CoupledPlainCoefficients (h := h) N →L[ℝ] JetL2 (volume.restrict AVenhance.unitCube) K (h i) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : JetIndex2 K =>
    ComponentL2 (volume.restrict AVenhance.unitCube) (h i))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun j => factorialRootWeight ρ j.1.val • plainJetSynthesisCLM N i K j))

@[simp] theorem plainWeightedSynthesisCLM_apply (N : ℕ) (i : ι) (K : ℕ) (ρ : ℝ)
    (c : CoupledPlainCoefficients (h := h) N) :
    plainWeightedSynthesisCLM N i K ρ c = factorialWeightedJet ρ (coupledPlainSynthesis N i K c).val := rfl

/-- The factorial component energy is absolutely continuous whenever the finite curve is. -/
theorem plainSynthesis_factorial_absolutelyContinuous (N : ℕ) (i : ι) (K : ℕ) (ρ : ℝ)
    {a b : ℝ} {y : ℝ → CoupledPlainCoefficients (h := h) N}
    (hy : AbsolutelyContinuousOnInterval y a b) :
    AbsolutelyContinuousOnInterval
      (fun s => factorialNormSq ρ (coupledPlainSynthesis N i K (y s)).val) a b := by
  have hc := ((plainWeightedSynthesisCLM N i K ρ).lipschitzWith.comp_absolutelyContinuousOnInterval hy).norm_sq
  simpa only [Function.comp_apply, plainWeightedSynthesisCLM_apply, factorialWeightedJet_normSq] using hc

/-- The mass energy uses only a finite scalar sum of absolutely continuous component energies. -/
theorem plainSynthesis_mass_absolutelyContinuous (N : ℕ) (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    {a b : ℝ} {y : ℝ → CoupledPlainCoefficients (h := h) N}
    (hy : AbsolutelyContinuousOnInterval y a b) :
    AbsolutelyContinuousOnInterval
      (fun s => massNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i) (y s)).val)) a b := by
  exact plainFiniteSum_absolutelyContinuous Finset.univ _
    (fun i _ => (plainSynthesis_factorial_absolutelyContinuous N i (K i) ρ hy).const_mul ((π i)⁻¹))

/-- The mass energy satisfies the native pairing chain rule almost everywhere for the finite ODE. -/
theorem plainODE_mass_ae_deriv (N : ℕ) (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → CoupledFourierModeIndex (h := h) N → CoupledFourierModeIndex (h := h) N → ℝ)
    (f y : ℝ → CoupledPlainCoefficients (h := h) N) (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution (fun s => plainMatrixCLM (A s)) f initial a b y)
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs (fun s => plainMatrixCLM (A s)) f y) volume a b) :
    ∀ᵐ t ∂volume, t ∈ Set.Icc a b → HasDerivAt
      (fun s => massNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i) (y s)).val))
      (2 * ∑ i, (π i)⁻¹ * inner ℝ
        (factorialWeightedJet ρ (coupledPlainSynthesis N i (K i)
          (plainMatrixCLM (A t) (y t) + f t)).val)
        (factorialWeightedJet ρ (coupledPlainSynthesis N i (K i) (y t)).val)) t := by
  filter_upwards [hy.ae_hasDerivAt hab hint] with t ht
  intro hmem
  exact plainSynthesis_mass_hasDerivAt N K ρ π (ht hmem)

/-- Finite paths have a continuous exact mass gradient square, at every truncation. -/
theorem plainSynthesis_massGrad_continuous (N : ℕ) (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    {y : ℝ → CoupledPlainCoefficients (h := h) N} (hy : Continuous y) :
    Continuous (fun s => massGradNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i + 1) (y s)).val)) := by
  have hjet (i : ι) (j : Fin (K i + 1)) (w : DerivativeWord2 (j.val + 1)) :
      Continuous (fun s => ‖plainJetSynthesisCLM N i (K i + 1)
        ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, w⟩ (y s)‖ ^ 2) :=
    ((plainJetSynthesisCLM N i (K i + 1) ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, w⟩).continuous.comp hy).norm.pow 2
  have hord (i : ι) (j : Fin (K i + 1)) : Continuous (fun s =>
      ∑ w : DerivativeWord2 (j.val + 1), ‖plainJetSynthesisCLM N i (K i + 1)
        ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, w⟩ (y s)‖ ^ 2) :=
    continuous_finsetSum _ (fun w _ => hjet i j w)
  have hcomp (i : ι) : Continuous (fun s => gradFactorialNormSq ρ
      (coupledPlainSynthesis N i (K i + 1) (y s)).val) :=
    continuous_finsetSum _ (fun j _ => (hord i j).const_mul (factorialWeight ρ j.val))
  exact continuous_finsetSum _ (fun i _ => (hcomp i).const_mul ((π i)⁻¹))

end AVRegularity.CoupledEnergy.Galerkin
end
