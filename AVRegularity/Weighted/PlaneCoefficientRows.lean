-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.PlaneJetFluxOperator
public import AVRegularity.CoupledEnergyPlane.LowerReadout

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! Split a genuine stored source into its principal scalar equation and residual sources. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeSourceDual_scalar_residual
    (T : PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (D : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (u : PlaneHk Set.univ 1 E)
    (H : Lp E 2 (volume : Measure (Vec 2))) (S : PlaneFluxL2 E) :
    planeSourceDual H S =
      planeValueForcedDual T D u (S - D (planeH1GradientOperator u))
        (H + T (planeH1GradientOperator u)) := by
  apply ext_inner_right ℝ
  intro z
  rw [planeSourceDual_pair, planeValueForcedDual_pair, planeWeakDualRepresentative_pair]
  simp only [inner_add_left, inner_sub_left]
  ring

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! Each word in the lower trace equals the value of its actual H1 slice. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWord_truncate_value {K : ℕ} (α : JetIndex2 K)
    (W : PlaneHk Set.univ (K + 1) E) :
    planeJetReadoutOperator K α (truncatePlaneHk (Nat.le_succ K) W) =
      planeHkValueOperator 1 (planeWordH1SliceOperator K α W) := by
  rw [planeWordH1Slice_value, planeJetReadoutOperator_apply]
  simp only [truncatePlaneHk_apply]
  rfl

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! Each stored flux readout has the exact original pointwise component. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeJetFluxOperator_ae {K : ℕ} (α : JetIndex2 K)
    (S : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) (k : Fin 2) :
    planeJetFluxOperator K α S k =ᵐ[volume] fun x => S.val α x k := by
  rw [planeJetFluxOperator_apply]
  have hm := ContinuousLinearMap.coeFn_compLpL
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (S.val α)
  rw [← mapPlaneHk_component] at hm
  simp only [Measure.restrict_univ] at hm
  exact (univToPlane_ae _).trans hm

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Time square integrability for the actual stored value and flux dual. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeJetSourceDual_memLp {K : ℕ} {μ : Measure ℝ}
    (H : ℝ → PlaneHk Set.univ K E)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hH : MemLp H 2 μ) (hS : MemLp S 2 μ) (α : JetIndex2 K) :
    MemLp (fun t => planeSourceDual (planeJetReadoutOperator K α (H t))
      (planeJetFluxOperator K α (S t))) 2 μ := by
  have hvalue := (planeJetReadoutOperator (E := E) K α).comp_memLp' hH
  have hflux := (planeJetFluxOperator (E := E) K α).comp_memLp' hS
  exact planeSourceDual_memLp _ hvalue _ hflux
end

/-! True stored sources and integrable principal actions give integrable word residuals. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem orderedSourceResidual_memLp {K : ℕ} {μ : Measure ℝ}
    (H : ℝ → PlaneHk Set.univ K E)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hH : MemLp H 2 μ) (hS : MemLp S 2 μ) (α : JetIndex2 K)
    (T : ℝ → Lp E 2 (volume : Measure (Vec 2))) (D : ℝ → PlaneFluxL2 E)
    (hT : MemLp T 2 μ) (hD : MemLp D 2 μ) :
    MemLp (fun t => planeJetReadoutOperator K α (H t) + T t) 2 μ ∧
    MemLp (fun t => planeJetFluxOperator K α (S t) - D t) 2 μ := by
  have hh := (planeJetReadoutOperator (E := E) K α).comp_memLp' hH
  have hs := (planeJetFluxOperator (E := E) K α).comp_memLp' hS
  exact ⟨bochnerSource_memLp_add hh hT, bochnerSource_memLp_sub hs hD⟩
end

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane
namespace AVRegularity.Weighted

/-! Finite component rows of bounded plane coefficient multiplication. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- A scalar coefficient acts on the Hilbert fiber by scalar multiplication. -/
def scalarFiberCoefficient (c : ℝ) : E →L[ℝ] E :=
  c • ContinuousLinearMap.id ℝ E

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
@[simp] theorem scalarFiberCoefficient_apply (c : ℝ) (e : E) :
    scalarFiberCoefficient c e = c • e := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem scalarFiberCoefficient_norm_le (c : ℝ) :
    ‖scalarFiberCoefficient (E := E) c‖ ≤ |c| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg c)
  intro e
  simp only [scalarFiberCoefficient_apply, norm_smul, Real.norm_eq_abs]
  exact le_rfl

/-- A bounded continuous scalar field gives the literal plane `L²` multiplier. -/
def planeScalarMultiplier (c : Vec 2 → ℝ) (hc : Continuous c)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z, |c z| ≤ M) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
  planeCoefficientOperator (fun z => scalarFiberCoefficient (E := E) (c z))
    (hc.smul continuous_const) hM
    (fun z => (scalarFiberCoefficient_norm_le (c z)).trans (hb z))

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem planeScalarMultiplier_ae (c : Vec 2 → ℝ) (hc : Continuous c)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z, |c z| ≤ M)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    planeScalarMultiplier c hc hM hb u =ᵐ[volume] fun z => c z • u z :=
  planeCoefficientOperator_ae _ _ _ _ _

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem planeScalarMultiplier_norm_le (c : Vec 2 → ℝ) (hc : Continuous c)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z, |c z| ≤ M) :
    ‖planeScalarMultiplier (E := E) c hc hM hb‖ ≤ M :=
  planeCoefficientOperator_norm_le _ _ _ _

omit [BorelSpace E] [CompleteSpace E] in
/-- Each fixed input has a strongly measurable multiplier output. -/
theorem planeScalarMultiplier_stronglyMeasurable {T : Type*} [MeasurableSpace T]
    (c : T → Vec 2 → ℝ) (hc : ∀ t, Continuous (c t))
    (hj : Measurable (Function.uncurry c)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t z, |c t z| ≤ M) (u : Lp E 2 (volume : Measure (Vec 2))) :
    StronglyMeasurable (fun t => planeScalarMultiplier (c t) (hc t) hM (hb t) u) := by
  apply planeCoefficientOperator_stronglyMeasurable
  exact hj.smul measurable_const

/-- A transport row applies a scalar multiplier to each weak gradient component. -/
def planeTransportRow (L : Fin 2 → Lp E 2 (volume : Measure (Vec 2)) →L[ℝ]
    Lp E 2 (volume : Measure (Vec 2))) :
    PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
  ∑ k : Fin 2, (L k).comp (PiLp.proj (𝕜 := ℝ) 2 _ k)

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
@[simp] theorem planeTransportRow_apply
    (L : Fin 2 → Lp E 2 (volume : Measure (Vec 2)) →L[ℝ]
      Lp E 2 (volume : Measure (Vec 2))) (u : PlaneFluxL2 E) :
    planeTransportRow L u = ∑ k : Fin 2, L k (u k) := by
  simp [planeTransportRow]

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- A two-component transport row has a bound independent of the fiber dimension. -/
theorem planeTransportRow_norm_le
    (L : Fin 2 → Lp E 2 (volume : Measure (Vec 2)) →L[ℝ]
      Lp E 2 (volume : Measure (Vec 2)))
    {M : ℝ} (hM : 0 ≤ M) (hL : ∀ k, ‖L k‖ ≤ M) :
    ‖planeTransportRow L‖ ≤ 2 * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [planeTransportRow_apply]
  calc
    ‖∑ k : Fin 2, L k (u k)‖ ≤ ∑ k : Fin 2, ‖L k (u k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin 2, M * ‖u‖ := by
      apply Finset.sum_le_sum
      intro k _
      exact ((L k).le_opNorm _).trans
        (mul_le_mul (hL k) (PiLp.norm_apply_le u k) (norm_nonneg _) hM)
    _ = 2 * M * ‖u‖ := by simp; ring

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- Finite row assembly preserves inputwise strong time measurability. -/
theorem planeTransportRow_stronglyMeasurable {T : Type*} [MeasurableSpace T]
    (L : T → Fin 2 → Lp E 2 (volume : Measure (Vec 2)) →L[ℝ]
      Lp E 2 (volume : Measure (Vec 2)))
    (hL : ∀ k u, StronglyMeasurable (fun t => L t k u)) (u : PlaneFluxL2 E) :
    StronglyMeasurable (fun t => planeTransportRow (L t) u) := by
  simp_rw [planeTransportRow_apply]
  exact Finset.stronglyMeasurable_fun_sum _ (fun k _ => hL k (u k))

/-- Embed one spatial `L²` component in the two-component flux carrier. -/
def planeFluxInjection (k : Fin 2) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] PlaneFluxL2 E :=
  (((WithLp.linearEquiv 2 ℝ
      (Fin 2 → Lp E 2 (volume : Measure (Vec 2)))).symm.toLinearMap).comp
    (LinearMap.single ℝ (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2))) k)).mkContinuous 1
      (fun u => by
        change ‖(PiLp.single 2 k u : PlaneFluxL2 E)‖ ≤ 1 * ‖u‖
        simp)

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
@[simp] theorem planeFluxInjection_norm (k : Fin 2)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    ‖planeFluxInjection k u‖ = ‖u‖ := by
  change ‖(PiLp.single 2 k u : PlaneFluxL2 E)‖ = ‖u‖
  exact PiLp.norm_single 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2))) k u

/-- Assemble a diffusion matrix out of its bounded spatial coefficient multipliers. -/
def planeDiffusionRows
    (L : Fin 2 → Fin 2 → Lp E 2 (volume : Measure (Vec 2)) →L[ℝ]
      Lp E 2 (volume : Measure (Vec 2))) : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E :=
  ∑ k : Fin 2, (planeFluxInjection k).comp (planeTransportRow (L k))

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
@[simp] theorem planeDiffusionRows_apply
    (L : Fin 2 → Fin 2 → Lp E 2 (volume : Measure (Vec 2)) →L[ℝ]
      Lp E 2 (volume : Measure (Vec 2))) (u : PlaneFluxL2 E) (k : Fin 2) :
    planeDiffusionRows L u k = ∑ j : Fin 2, L k j (u j) := by
  change (∑ a : Fin 2, (PiLp.single 2 a (planeTransportRow (L a) u) : PlaneFluxL2 E)) k = _
  simp [Fin.sum_univ_two, PiLp.single_apply, planeTransportRow_apply]
  fin_cases k <;> simp

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- Diffusion assembly has a uniform dimension-free operator bound. -/
theorem planeDiffusionRows_norm_le
    (L : Fin 2 → Fin 2 → Lp E 2 (volume : Measure (Vec 2)) →L[ℝ]
      Lp E 2 (volume : Measure (Vec 2)))
    {M : ℝ} (hM : 0 ≤ M) (hL : ∀ k j, ‖L k j‖ ≤ M) :
    ‖planeDiffusionRows L‖ ≤ 4 * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change ‖∑ k : Fin 2, planeFluxInjection k (planeTransportRow (L k) u)‖ ≤ _
  calc
    _ ≤ ∑ k : Fin 2, ‖planeFluxInjection k (planeTransportRow (L k) u)‖ := norm_sum_le _ _
    _ = ∑ k : Fin 2, ‖planeTransportRow (L k) u‖ := by simp only [planeFluxInjection_norm]
    _ ≤ ∑ _k : Fin 2, (2 * M) * ‖u‖ := by
      apply Finset.sum_le_sum
      intro k _
      exact (planeTransportRow (L k)).le_of_opNorm_le
        (planeTransportRow_norm_le (L k) hM (hL k)) u
    _ = 4 * M * ‖u‖ := by simp; ring

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- Matrix assembly preserves inputwise strong time measurability. -/
theorem planeDiffusionRows_stronglyMeasurable {T : Type*} [MeasurableSpace T]
    (L : T → Fin 2 → Fin 2 → Lp E 2 (volume : Measure (Vec 2)) →L[ℝ]
      Lp E 2 (volume : Measure (Vec 2)))
    (hL : ∀ k j u, StronglyMeasurable (fun t => L t k j u)) (u : PlaneFluxL2 E) :
    StronglyMeasurable (fun t => planeDiffusionRows (L t) u) := by
  change StronglyMeasurable (fun t =>
    ∑ k : Fin 2, planeFluxInjection k (planeTransportRow (L t k) u))
  apply Finset.stronglyMeasurable_fun_sum
  intro k _
  exact (planeFluxInjection k).continuous.comp_stronglyMeasurable
    (planeTransportRow_stronglyMeasurable (fun t => L t k) (hL k) u)

end AVRegularity.Weighted
end
