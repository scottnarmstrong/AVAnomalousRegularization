-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlaneHomogeneousImageAtomEquation
import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
public import AVRegularity.CycleJoint.UnitPatchValuePeriodization
import AVRegularity.CoupledEnergyPlane.Variational.ProductPlaneHkOperator
import AVRegularity.CycleReference.TransitionTaylorBounds
import AVRegularity.CycleJoint.PeriodicOperatorImageBudget
import AVRegularity.Construction.Scales.Times
import AVRegularity.CycleReference.MeanEnhancementScale
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Actual plane weak solutions superpose, including their time traces and Sobolev lifts. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeWeakSolution_add_ae_linear_data (K : ι → ℕ) (D : ℕ) (ν a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (lf : E →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (lF : E → ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (lg : E →ₗ[ℝ] (∀ i, ℝ → PlaneHk Set.univ (K i) (h i)))
    (x y : E)
    (hread : ∀ i, lF (x + y) i =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => lF x i t + lF y i t)
    (u u' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w w' : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A (lf x) (lF x) (lg x) u w)
    (hs' : IsCoupledWeakSolutionPlane ν a b v D K A (lf y) (lF y) (lg y) u' w') :
    IsCoupledWeakSolutionPlane ν a b v D K A (lf (x + y)) (lF (x + y)) (lg (x + y))
      (fun i t => u i t + u' i t) (fun i t => w i t + w' i t) := by
  have hh := planeWeakSolution_add K D ν a b v A (lf x) (lf y)
    (lF x) (lF y) (lg x) (lg y) u u' w w' hs hs'
  have hsum : IsCoupledWeakSolutionPlane ν a b v D K A (lf (x + y))
      (fun i t => lF x i t + lF y i t) (lg (x + y))
      (fun i t => u i t + u' i t) (fun i t => w i t + w' i t) := by
    simpa only [map_add, Pi.add_def] using hh
  apply planeWeakSolution_forcing_time_ae_congr _ hsum
  intro i
  filter_upwards [hread i] with t ht
  rw [ht]

end AVRegularity.CycleJointProofs
end
end

section
section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The literal metric-source equation and its raw flux depend only on the metric
on the solution time window. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {K : ι → ℕ} {D : ℕ}
  {G G' : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
  {A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i)}

theorem planeMetricSourceCoefficient_congr_time {t : ℝ} (heq : G' t = G t)
    (i j : ι) (d : admissibleOrders K D i j) :
    planeMetricSourceCoefficient K D G' A i j d t =
      planeMetricSourceCoefficient K D G A i j d t := by
  funext z
  simp only [planeMetricSourceCoefficient, planeDiagonalGradientCoefficient, heq]

theorem planeMetricSource_raw_flux_congr_time {t : ℝ} (heq : G' t = G t)
    (w : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) :
    planeRawCouplingFlux K D t (planeMetricSourceCoefficient K D G' A) w i =
      planeRawCouplingFlux K D t (planeMetricSourceCoefficient K D G A) w i := by
  funext z
  simp only [planeRawCouplingFlux, planeMetricSourceCoefficient_congr_time heq]

theorem planeMetricSource_coupled_solution_window_congr
    {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {f : ∀ i, PlaneHk Set.univ (K i) (h i)}
    {F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)}
    {w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)}
    (heq : ∀ t ∈ Set.Icc a b, G' t = G t)
    (hs : IsCoupledWeakSolutionPlane ν a b v D K
      (planeMetricSourceCoefficient K D G A) f F g u w) :
    IsCoupledWeakSolutionPlane ν a b v D K
      (planeMetricSourceCoefficient K D G' A) f F g u w := by
  exact CycleWords.isCoupledWeakSolutionPlane_congr_coeff
    (fun i j d t ht => planeMetricSourceCoefficient_congr_time (heq t ht) i j d) hs

theorem planeMetricSource_coupled_solution_metricClamp
    {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {f : ∀ i, PlaneHk Set.univ (K i) (h i)}
    {F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)}
    {w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)}
    (hs : IsCoupledWeakSolutionPlane ν a b v D K
      (planeMetricSourceCoefficient K D G A) f F g u w) :
    IsCoupledWeakSolutionPlane ν a b v D K
      (planeMetricSourceCoefficient K D (CycleWords.metricClamp a b G) A) f F g u w := by
  exact planeMetricSource_coupled_solution_window_congr
    (fun _ ht => CycleWords.metricClamp_of_mem G ht) hs

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Actual plane weak solutions scale linearly, with the same physical coefficients. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeWeakSolution_smul (K : ι → ℕ) (D : ℕ) (c ν a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) :
    IsCoupledWeakSolutionPlane ν a b v D K A (fun i => c • f i)
      (fun i t => c • F i t) (fun i t => c • g i t)
      (fun i t => c • u i t) (fun i t => c • w i t) := by
  refine ⟨fun i => normedCurve_continuousOn_smul c (u i) _ (hs.1 i),
    fun i => normedCurve_memLp_smul c (w i) _ (hs.2.1 i), ?_, ?_, ?_⟩
  · intro i
    filter_upwards [hs.2.2.1 i] with s hsu
    change truncatePlaneHk (Nat.le_succ (K i)) (c • w i s) = c • u i s
    rw [map_smul, hsu]
  · intro i
    change c • u i a = c • f i
    rw [hs.2.2.2.1 i]
  · intro i t ht φ
    simp only [Measure.restrict_univ]
    exact planeWeakSolution_smul_identities K D c ν a b v A f F g u w hs i t ht φ

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Recover the diagonal coupled weak solution from the actual scalar geometry chain. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarPlaneChain_diagonalMetric_solution (K : ι → ℕ) (a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsPlaneChainFrom (geometryScalarData 2 G) (fun _ i => K i) a b v
      (fun _ i => f i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i)) :
    IsCoupledWeakSolutionPlane 1 a b v 2 K
      (planeDiagonalGradientCoefficient K 2 (fun _ t z => G t z - 1))
      f F (fun _ _ => 0) u w := by
  have heq : planeOneLevelCoefficient K 2
      (planeDiagonalGradientCoefficient (h := h) K 2 (fun _ t z => G t z - 1)) =
      planeChainCoefficient (geometryScalarData 2 G) (fun _ => K) := by
    funext p p' d t z
    exact planeDiagonalGradientCoefficient_eq_scalar_chain K 2 G p p' d t z
  apply planeWeakSolution_of_oneLevel K 2 1 a b v
    (planeDiagonalGradientCoefficient K 2 (fun _ t z => G t z - 1))
    f F (fun _ _ => 0) u w
  rw [heq]
  exact hs

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Positive source blocks and a diagonal L2 bound control the joint operator's exact mass norm. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusJointOperator_mass_bound (K : ι → ℕ) (Mout H : ℕ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u)
    (δ C θ ρ : ℝ) (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hrow : ∀ v, ∑ u, massConjugatedMatrix π A v u ≤ θ)
    (hcol : ∀ u, ∑ v, massConjugatedMatrix π A v u ≤ θ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (hPd : ∀ v f, torusHkNorm 1 (Nat.zero_le _) (Pd v f) ≤ δ * ‖f‖)
    (hPg : ∀ n, 1 ≤ n → n ≤ H → ∀ v u f,
      torusHkNorm ρ (le_max_left Mout (K v)) (Pg n v u f) ≤ C * (A ^ n) v u * ‖f‖)
    (f : ∀ i, TorusHk 0 (h i)) :
    Real.sqrt (massNormSq 1 π (fun v =>
      (truncateTorusHk (Nat.zero_le _) (jointOperator K Mout H Pd Pg f v)).val)) ≤
      (δ + C * ∑ n ∈ Finset.Icc 1 H, θ ^ n) *
        Real.sqrt (massNormSq 1 π (fun v => (f v).val)) := by
  let d : ∀ v, TorusHk 0 (h v) := fun v => truncateTorusHk (Nat.zero_le _) (Pd v (f v))
  let s : ∀ v, TorusHk 0 (h v) := fun v =>
    ∑ u, ∑ n ∈ Finset.Icc 1 H, truncateTorusHk (Nat.zero_le _) (Pg n v u (f u))
  have hd v : ‖d v‖ ≤ δ * ‖f v‖ := by
    simpa only [d, torusHkNorm_order_zero] using hPd v (f v)
  have hdSq : massNormSq 1 π (fun v => (d v).val) ≤
      δ ^ 2 * massNormSq 1 π (fun v => (f v).val) := by
    rw [massNormSq_order_zero, massNormSq_order_zero, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    have hb := pow_le_pow_left₀ (norm_nonneg _) (hd v) 2
    calc
      (π v)⁻¹ * ‖d v‖ ^ 2 ≤ (π v)⁻¹ * (δ * ‖f v‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (hπ v).le)
      _ = δ ^ 2 * ((π v)⁻¹ * ‖f v‖ ^ 2) := by ring
  have hsSq : massNormSq 1 π (fun v => (s v).val) ≤
      (C * ∑ n ∈ Finset.Icc 1 H, θ ^ n) ^ 2 *
        massNormSq 1 π (fun v => (f v).val) := by
    rw [massNormSq_order_zero, massNormSq_order_zero]
    apply massSourcePolynomial_operator_bound π hπ A hA C θ hC hθ hrow hcol
      (Finset.Icc 1 H)
      (fun n v u z => truncateTorusHk (Nat.zero_le _) (Pg n v u z))
    intro n hn v u z
    exact (torusHk_value_le_modelNorm ρ (le_max_left Mout (K v)) _).trans
      (hPg n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2 v u z)
  have hdRoot := Real.sqrt_le_sqrt hdSq
  rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq_eq_abs, abs_of_nonneg hδ] at hdRoot
  have hcSum : 0 ≤ C * ∑ n ∈ Finset.Icc 1 H, θ ^ n :=
    mul_nonneg hC (Finset.sum_nonneg (fun n _ => pow_nonneg hθ n))
  have hsRoot := Real.sqrt_le_sqrt hsSq
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hcSum] at hsRoot
  have he : (fun v => truncateTorusHk (Nat.zero_le _) (jointOperator K Mout H Pd Pg f v)) =
      fun v => d v + s v := by
    funext v
    simp only [jointOperator, map_add, map_sum, d, s]
    rw [Finset.sum_comm]
  have he' : (fun v => (truncateTorusHk (Nat.zero_le _)
      (jointOperator K Mout H Pd Pg f v)).val) = fun v => (d v + s v).val :=
    funext (fun v => congrArg Subtype.val (congrFun he v))
  rw [he']
  exact (torusMassNorm_triangle (fun _ => 0) 1 π hπ d s).trans
    (by simpa only [add_mul] using add_le_add hdRoot hsRoot)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Every actual translated jet coefficient pairing has a genuine spatial integral. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K L : ℕ}

theorem translated_coefficient_pairing_space_integrable (z : Vec 2)
    (C : Vec 2 → E →L[ℝ] F) (hc : Continuous C) (MC : ℝ) (hMC : 0 ≤ MC)
    (hC : ∀ x, ‖C x‖ ≤ MC) (f : PlaneHk Set.univ K E) (α : JetIndex2 K)
    (φ : PlaneHk Set.univ L F) (β : JetIndex2 L) :
    Integrable (fun x => inner ℝ (C x ((planeCarrierTranslation K z f).toFunction.jet α x))
      (φ.toFunction.jet β x)) volume := by
  apply (planeStaticCoefficient_pairing_integrable C hc MC hMC hC
    (planeJetReadoutOperator K α (planeCarrierTranslation K z f))
    (planeJetReadoutOperator L β φ)).congr
  filter_upwards [univToPlane_ae ((planeCarrierTranslation K z f).val α),
    univToPlane_ae (φ.val β)] with x hx hy
  exact congrArg₂ (inner ℝ) (congrArg (C x) hx) hy

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.CycleReference
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Joint Hilbert gradients remain product L2 in a material chart on the stated closed window. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hilbertChartGradient_joint_memLp {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a b : ℝ) (G : Fin 2 → ℝ × Vec 2 → E)
    (hG : ∀ i, MemLp (G i) 2 (volume.restrict (Icc a b ×ˢ univ))) (j : Fin 2) :
    MemLp (fun p : ℝ × Vec 2 =>
      hilbertChartGradient hφ p.1 s (fun i x => G i (p.1, x)) j p.2)
      2 (volume.restrict (Icc a b ×ˢ univ)) := by
  let μ := volume.restrict (Icc a b ×ˢ (univ : Set (Vec 2)))
  let J := fun p : ℝ × Vec 2 => jacMatrix (fun x => AVRegularity.streamFlow φ hφ p.1 x s) p.2
  obtain ⟨C, _, hb⟩ := streamFlow_jacMatrix_bounded_on_compact_time hφ s (Icc a b) isCompact_Icc
  have htop (i : Fin 2) : MemLp (fun p => J p i j) ⊤ μ := by
    have hc := (continuous_apply j).comp ((continuous_apply i).comp
      (streamFlow_jacMatrix_joint_continuous hφ s))
    apply memLp_top_of_bound hc.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with p hp
    rw [Real.norm_eq_abs]
    exact hb p.1 hp.1 p.2 i j
  have hcomp (i : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => G i (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)) 2 μ :=
    (hG i).comp_measurePreserving (streamFlowTime_window_measurePreserving hφ s measurableSet_Icc)
  change MemLp (fun p => ∑ i : Fin 2,
    J p i j • G i (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)) 2 μ
  exact memLp_finsetSum _ (fun i _ => (htop i).smul (hcomp i))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Zero-extended physical natural-flow Taylor remainders are measurable in time. -/

attribute [local instance] Classical.propDecidable

def naturalSlowRemainderTimeCoefficient (K : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → ℝ) (a b : ℝ)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (r : ℝ) (τ : ℝ → ℝ) (e E : ℝ) (yc : Vec 2) (t : ℝ) (z : Vec 2) : ℝ :=
  if t ∈ Set.Icc a b then
    let Y := streamFlow φ hφ r (yc + e • z) (τ t)
    let Yc := streamFlow φ hφ r yc (τ t)
    f t (E⁻¹ • Y) (e⁻¹ • Y) -
      taylorSlow 0 K (fun X => f t X (e⁻¹ • Y)) (E⁻¹ • Yc) (E⁻¹ • (Y - Yc))
  else 0

theorem naturalSlowRemainderTimeCoefficient_measurable (K : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → ℝ) (a b : ℝ)
    (hm : ∀ X z, Measurable (fun t => f t X z))
    (hf : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (Function.uncurry (f t)))
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (r : ℝ) (τ : ℝ → ℝ) (hτ : Measurable τ) (e E : ℝ) (yc z : Vec 2) :
    Measurable (fun t => naturalSlowRemainderTimeCoefficient K f a b hφ r τ e E yc t z) := by
  let Y := fun t : Set.Icc a b => streamFlow φ hφ r (yc + e • z) (τ t)
  let Yc := fun t : Set.Icc a b => streamFlow φ hφ r yc (τ t)
  have htime : Measurable (fun t : Set.Icc a b => τ t) := hτ.comp measurable_subtype_coe
  have hY : Measurable Y := (streamFlow_joint_smooth hφ).continuous.measurable.comp
    (measurable_const.prodMk (measurable_const.prodMk htime))
  have hYc : Measurable Yc := (streamFlow_joint_smooth hφ).continuous.measurable.comp
    (measurable_const.prodMk (measurable_const.prodMk htime))
  have hfm (X z : Vec 2) : Measurable (fun t : Set.Icc a b => f t X z) :=
    (hm X z).comp measurable_subtype_coe
  have hfs (t : Set.Icc a b) : ContDiff ℝ (K : ℕ) (Function.uncurry (f t)) := hf t t.property
  have hfj : Measurable (fun p : Set.Icc a b × (Vec 2 × Vec 2) => f p.1 p.2.1 p.2.2) :=
    (measurable_uncurry_of_continuous_of_measurable (fun t => (hfs t).continuous)
      (fun w => hfm w.1 w.2)).comp measurable_swap
  have hraw : Measurable (fun t : Set.Icc a b => f t (E⁻¹ • Y t) (e⁻¹ • Y t)) :=
    hfj.comp (measurable_id.prodMk
      ((hY.const_smul (E⁻¹)).prodMk (hY.const_smul (e⁻¹))))
  have htaylor := moving_slow_taylor_measurable 0 K (fun t : Set.Icc a b => f t)
    hfm hfs (fun t => E⁻¹ • Yc t) (fun t => e⁻¹ • Y t) (fun t => E⁻¹ • (Y t - Yc t))
    (hYc.const_smul (E⁻¹)) (hY.const_smul (e⁻¹))
    ((hY.sub hYc).const_smul (E⁻¹))
  exact (hraw.sub htaylor).dite measurable_const measurableSet_Icc

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! Smooth native H1 representatives are strongly approximated by compact smooth spatial truncations. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1_compact_truncation_tendsto (u : PlaneHk univ 1 E)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hu : (planeHkValueOperator 1 u : Vec 2 → E) =ᵐ[volume] f) :
    Tendsto (fun n => compactSmoothHilbertH1Product (spatialApproximationCutoff n)
      (spatialApproximationCutoff_smooth n) (spatialApproximationCutoff_compact n) f hf)
      atTop (𝓝 u) := by
  let χ := spatialApproximationCutoff
  let hχ := spatialApproximationCutoff_smooth
  let hsχ := spatialApproximationCutoff_compact
  have hb (n : ℕ) (x : Vec 2) : |χ n x| ≤ 1 := by
    rw [abs_of_nonneg (spatialApproximationCutoff_bounds n x).1]
    exact (spatialApproximationCutoff_bounds n x).2
  let Z := fun n => compactSmoothHilbertH1Product (χ n) (hχ n) (hsχ n) f hf
  apply planeH1_tendsto_of_readouts (u := Z)
  · have he n : planeHkValueOperator 1 (Z n) =
        planeScalarMultiplier (χ n) (hχ n).continuous (by norm_num : (0 : ℝ) ≤ 1)
          (hb n) (planeHkValueOperator 1 u) :=
      compactSmoothHilbertH1Product_value (χ n) (hχ n) (hsχ n)
        (by norm_num : (0 : ℝ) ≤ 1) (hb n) u f hf hu
    have ht := planeScalarMultiplier_tendsto_one χ (fun n => (hχ n).continuous)
      spatialApproximationCutoff_bounds spatialApproximationCutoff_tendsto (planeHkValueOperator 1 u)
    simpa only [he] using ht
  · obtain ⟨C, hC, hbound⟩ := spatialApproximationCutoff_derivative_bound
    have hc : Tendsto (fun n => fun i : Fin 2 => planeH1GradientOperator (Z n) i)
        atTop (𝓝 (fun i : Fin 2 => planeH1GradientOperator u i)) := by
      apply tendsto_pi_nhds.mpr
      intro i
      let D := fun n => C * spatialApproximationScale n * ‖(basisVec i : Vec 2)‖
      have hD n : 0 ≤ D n :=
        mul_nonneg (mul_nonneg hC (spatialApproximationScale_pos n).le) (norm_nonneg _)
      have hd n x : |fderiv ℝ (χ n) x (basisVec i)| ≤ D n := hbound n x (basisVec i)
      have hdc n : Continuous (fun x => fderiv ℝ (χ n) x (basisVec i)) :=
        ((hχ n).continuous_fderiv (by simp)).clm_apply continuous_const
      have hDlim : Tendsto D atTop (𝓝 0) := by
        simpa only [mul_zero, zero_mul] using
          (spatialApproximationScale_tendsto.const_mul C).mul_const ‖(basisVec i : Vec 2)‖
      have ht0 := planeScalarMultiplier_tendsto_zero
        (fun n x => fderiv ℝ (χ n) x (basisVec i)) hdc D hD hd hDlim (planeHkValueOperator 1 u)
      have ht1 := planeScalarMultiplier_tendsto_one χ (fun n => (hχ n).continuous)
        spatialApproximationCutoff_bounds spatialApproximationCutoff_tendsto (planeH1GradientOperator u i)
      have he n : planeH1GradientOperator (Z n) i =
          planeScalarMultiplier (fun x => fderiv ℝ (χ n) x (basisVec i)) (hdc n)
            (hD n) (hd n) (planeHkValueOperator 1 u) +
          planeScalarMultiplier (χ n) (hχ n).continuous (by norm_num : (0 : ℝ) ≤ 1)
            (hb n) (planeH1GradientOperator u i) :=
        compactSmoothHilbertH1Product_gradient (χ n) (hχ n) (hsχ n)
          (by norm_num : (0 : ℝ) ≤ 1) (hb n) i (hD n) (hd n) u f hf hu
      simpa only [he, zero_add] using ht0.add ht1
    have hp := (PiLp.continuous_toLp 2
      (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2)))).tendsto
        (fun i : Fin 2 => planeH1GradientOperator u i) |>.comp hc
    simpa only [Function.comp_def, WithLp.toLp_ofLp] using hp

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The raw coupled flux of the actual physical family retains each original identity exactly once. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem planeRawCouplingFlux_family_constituents
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (ν e E : ℝ) (actual : ∀ p, Ctx p)
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (v : ι) (t : ℝ) (x : Vec 2) :
    planeRawCouplingFlux K D t (edgeCoefficient F ν e E actual K) U v x =
      ∑ u, ∑ γ : F.Γ v u, ∑ d : admissibleOrders K D v u,
        constituentPhysical F ν e E actual v u γ d t x
          (WithLp.toLp 2 (planeNativeJetExtension (U u) x (d.1 - 1))) := by
  classical
  unfold planeRawCouplingFlux edgeCoefficient physicalCoefficient
  apply Finset.sum_congr rfl
  intro u hu
  simp only [sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro γ hγ
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  congr 1
  funext I
  have hr : d.1 - 1 ≤ K u + 1 := by
    have hh := admissibleOrders_reserve K D v u d
    omega
  simp only [planeNativeJetExtension, dite_eq_left hr]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVenhance.Infra.Section5
namespace AVRegularity.CycleJointProofs

/-! The inverse Jacobian in the literal physical coefficient is the derivative of the
certified material map evaluated at its inverse coordinate. -/

theorem chartInvJacobian_homeomorph_symm (X : Vec 2 ≃ₜ Vec 2)
    (hX : Differentiable ℝ ⇑X) (hY : Differentiable ℝ ⇑X.symm) (x : Vec 2) :
    chartInvJacobian ⇑X.symm x = chartJacobian ⇑X (X.symm x) := by
  have he := CycleReference.homeomorph_inverse_jacMatrix X hX hY (X.symm x)
  simpa only [Homeomorph.apply_symm_apply, chartInvJacobian, chartJacobian, jacMatrix] using he

end AVRegularity.CycleJointProofs
end
end

section
public section
open AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! One separation threshold makes every preparation mixing length small,
including after multiplication by any fixed response constant. -/

theorem exists_uniform_preparation_mixing_scale_small {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧
      ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ M : ℕ, 1 ≤ M →
      ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
        C * (Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) ≤ η := by
  obtain ⟨Cm, hCm, Lm, hLm, hm⟩ :=
    bandChain_preparation_mixing_scale hα0 hα1 hs0 hs1 hq hζ
  have hp : 0 < ocGamma α q / 2 + ocDelta α q :=
    add_pos (div_pos (preparation_gamma_pos hα0 hq) (by norm_num))
      (preparation_delta_pos hα0 hq)
  have hden : 0 < C * Cm + 1 :=
    add_pos_of_nonneg_of_pos (mul_nonneg hC (zero_le_one.trans hCm)) zero_lt_one
  obtain ⟨Ls, hLs, hs⟩ := exists_small_scale_error_budget hq.1 hp (div_pos hη hden)
  refine ⟨max Lm Ls, hLm.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM κ hκ m hm2 hmM
  have hΛm := (le_max_left _ _).trans hΛ
  have hΛs := (le_max_right _ _).trans hΛ
  have hbound := hm Λ hΛm M hM κ hκ m hm2 hmM
  have hpow := (epsilon_power_le_tail hq.1 hp (hLs.trans hΛs)
    (show 1 ≤ m - 1 by omega)).trans (hs Λ hΛs).2
  have hprice : (C * Cm + 1) *
      ocEpsilon q Λ (m - 1) ^ (ocGamma α q / 2 + ocDelta α q) ≤ η := by
    simpa only [mul_comm] using (le_div_iff₀ hden).mp hpow
  calc
    C * (Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) ≤
        (C * Cm) * ocEpsilon q Λ (m - 1) ^ (ocGamma α q / 2 + ocDelta α q) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound hC
    _ ≤ (C * Cm + 1) * ocEpsilon q Λ (m - 1) ^ (ocGamma α q / 2 + ocDelta α q) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (Real.rpow_nonneg (AVRegularity.Scales.epsilon_basic hq.1 (hLs.trans hΛs)).1.le _)
    _ ≤ η := hprice

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Scalar geometry solutions retain their full weak class when the diagonal metric array is read at any order bound at least two. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (K : ι → ℕ) (D : ℕ) (hD : 2 ≤ D) (a b : ℝ)
  (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
  (f : ∀ i, PlaneHk Set.univ (K i) (h i))
  (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
  (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
  (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))

include hD in
theorem scalarPlaneChain_diagonalMetric_order_solution
    (hs : IsPlaneChainFrom (geometryScalarData 2 G) (fun _ i => K i) a b v
      (fun _ i => f i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i)) :
    IsCoupledWeakSolutionPlane 1 a b v D K
      (planeDiagonalGradientCoefficient K D (fun _ t z => G t z - 1))
      f F (fun _ _ => 0) u w := by
  have hold := scalarPlaneChain_diagonalMetric_solution K a b v G f F u w hs
  refine ⟨hold.1, hold.2.1, hold.2.2.1, hold.2.2.2.1, ?_⟩
  intro i t ht φ
  have hi := hold.2.2.2.2 i t ht φ
  have hflux : (fun s => planeRawCouplingFlux K 2 s
      (planeDiagonalGradientCoefficient (h := h) K 2 (fun _ t z => G t z - 1))
      (fun j => w j s) i) =
      (fun s => planeRawCouplingFlux K D s
        (planeDiagonalGradientCoefficient (h := h) K D (fun _ t z => G t z - 1))
        (fun j => w j s) i) := by
    funext s z
    apply PiLp.ext
    intro k
    rw [planeRawCouplingFlux_diagonal_gradient _ _ (le_refl 2),
      planeRawCouplingFlux_diagonal_gradient _ _ hD]
  change CoupledWeakIdentity _ _ _ _ _ _ _ _ _ _
    (fun s => planeRawCouplingFlux K 2 s
      (planeDiagonalGradientCoefficient (h := h) K 2 (fun _ t z => G t z - 1))
      (fun j => w j s) i) _ _ at hi
  rw [hflux] at hi
  exact hi

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Summed cutoff coefficient squares have a uniform nine-patch overlap budget. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem spatialPatchCoefficient_zero_off_overlap {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N j : ℕ) (x : Vec 2) (k : Fin 2 → ℤ)
    (hk : k ∉ spatialPatchOverlapIndices ((N : ℝ) • x)) :
    coefficientDerivativeArray (spatialPatchCoefficient (E := E) ζ N k) j x = 0 := by
  by_contra hn
  apply hk
  apply mem_spatialPatchOverlapIndices
  intro i
  exact spatialPatchCoefficient_array_support hζ N j k x hn i

theorem spatialPatchCoefficient_square_sum_le {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N j : ℕ) (x : Vec 2) (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ k, ‖coefficientDerivativeArray (spatialPatchCoefficient (E := E) ζ N k) j x‖ ≤ D) :
    (∑' k : Fin 2 → ℤ,
      ENNReal.ofReal (‖coefficientDerivativeArray (spatialPatchCoefficient (E := E) ζ N k) j x‖ ^ 2)) ≤
      9 * ENNReal.ofReal (D ^ 2) := by
  let s := spatialPatchOverlapIndices ((N : ℝ) • x)
  have hz (k : Fin 2 → ℤ) (hk : k ∉ s) :
      ENNReal.ofReal (‖coefficientDerivativeArray (spatialPatchCoefficient (E := E) ζ N k) j x‖ ^ 2) = 0 := by
    rw [spatialPatchCoefficient_zero_off_overlap hζ N j x k hk]
    simp only [ContinuousLinearMap.opNorm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero]
  rw [tsum_eq_sum hz]
  have he : (∑ k ∈ s, ENNReal.ofReal (‖coefficientDerivativeArray
      (spatialPatchCoefficient (E := E) ζ N k) j x‖ ^ 2)) ≤
      ∑ _k ∈ s, ENNReal.ofReal (D ^ 2) :=
    Finset.sum_le_sum (fun k _ => ENNReal.ofReal_le_ofReal
      ((sq_le_sq₀ (ContinuousLinearMap.opNorm_nonneg _) hD).mpr (hb k)))
  exact he.trans_eq (by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [show s.card = 9 from spatialPatchOverlapIndices_card _]
    norm_num)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The literal native Piola Jacobian composes exactly when a physical piece is read in a second material chart. -/

theorem chartInvJacobian_reference_transition
    (P X : Vec 2 ≃ₜ Vec 2)
    (hP : Differentiable ℝ ⇑P) (hYP : Differentiable ℝ ⇑P.symm)
    (hX : Differentiable ℝ ⇑X) (hYX : Differentiable ℝ ⇑X.symm) (y : Vec 2) :
    chartInvJacobian ⇑(P.trans X.symm).symm y =
      (chartJacobian ⇑X y)⁻¹ * chartInvJacobian ⇑P.symm (X y) := by
  rw [chartInvJacobian_homeomorph_symm (P.trans X.symm) (hYX.comp hP) (hYP.comp hX),
    chartInvJacobian_homeomorph_symm P hP hYP]
  change jacMatrix (⇑X.symm ∘ ⇑P) (P.symm (X y)) =
    (jacMatrix ⇑X y)⁻¹ * jacMatrix ⇑P (P.symm (X y))
  rw [jacMatrix_comp _ (hYX _) (hP _), P.apply_symm_apply]
  have hi := homeomorph_inverse_jacMatrix X.symm hYX hX (X y)
  simpa only [Homeomorph.symm_symm, Homeomorph.symm_apply_apply] using
    congrArg (fun M => M * jacMatrix ⇑P (P.symm (X y))) hi.symm

end AVRegularity.CycleJointProofs
end
end

section
public section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Any finite family of fixed response constants has simultaneous uniform
small gains on every permitted preparation block. -/

theorem response_coefficient_gain_le {c C g z : ℝ}
    (hc : c ≤ C) (hC : 0 ≤ C) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hz : 0 ≤ z)
    (hcap : C * z ≤ 1) : c * g * z ≤ 1 := by
  calc
    c * g * z ≤ C * g * z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hg0) hz
    _ ≤ C * z := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg1 hC) hz
    _ ≤ 1 := hcap

theorem exists_uniform_preparation_response_gains {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {ι : Type*} [Fintype ι] (C : ι → ℝ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧
      ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ M : ℕ, 1 ≤ M →
      ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
      let z := Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)
      z ≤ 1 ∧ ∀ (g : ℝ), 0 ≤ g → g ≤ 1 →
        ∀ i, ENNReal.ofReal (C i * g * z) ≤ 1 := by
  let Ccap := 1 + ∑ i, |C i|
  have hsum : 0 ≤ ∑ i, |C i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hcap1 : 1 ≤ Ccap := le_add_of_nonneg_right hsum
  have hcap0 : 0 ≤ Ccap := zero_le_one.trans hcap1
  obtain ⟨Λ₀, hΛ₀, hs⟩ := exists_uniform_preparation_mixing_scale_small
    hα0 hα1 hs0 hs1 hq hζ Ccap 1 hcap0 zero_lt_one
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM z
  have hz : 0 ≤ z := div_nonneg (Real.sqrt_nonneg _)
    (AVRegularity.Scales.epsilon_basic hq.1 (hΛ₀.trans hΛ)).1.le
  have hb : Ccap * z ≤ 1 := hs Λ hΛ M hM κ hκ m hm hmM
  refine ⟨(by simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right hcap1 hz).trans hb), ?_⟩
  intro g hg0 hg1 i
  have hi : C i ≤ Ccap := (le_abs_self _).trans
    ((Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one))
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
    (response_coefficient_gain_le hi hcap0 hg0 hg1 hz hb)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Actual singleton component scalar solutions assemble into the scalar equation on the original family. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (K : ι → ℕ) (a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))

theorem scalarPlaneChain_of_components
    (hs : ∀ i, IsPlaneChainFrom (h := fun _ : Unit => h i)
      (geometryScalarData (h := fun _ : Unit => h i) 2 G)
      (fun _ _ => K i) a b v (fun _ _ => f i) (fun _ _ => F i)
      (fun _ _ => u i) (fun _ _ => w i)) :
    IsPlaneChainFrom (geometryScalarData 2 G) (fun _ i => K i) a b v
      (fun _ i => f i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i) := by
  have hc (i : ι) := scalarPlaneChain_diagonalMetric_solution
    (h := fun _ : Unit => h i) (fun _ => K i) a b v G
    (fun _ => f i) (fun _ => F i) (fun _ => u i) (fun _ => w i) (hs i)
  apply planeDiagonalMetric_scalar_solution K a b v G f F u w
  refine ⟨fun i => (hc i).1 (), fun i => (hc i).2.1 (),
    fun i => (hc i).2.2.1 (), fun i => (hc i).2.2.2.1 (), ?_⟩
  intro i t ht φ
  have hold := (hc i).2.2.2.2 () t ht φ
  have hflux : (fun s => planeRawCouplingFlux (fun _ : Unit => K i) 2 s
      (planeDiagonalGradientCoefficient (h := fun _ : Unit => h i)
        (fun _ => K i) 2 (fun _ t z => G t z - 1)) (fun _ => w i s) ()) =
      (fun s => planeRawCouplingFlux K 2 s
        (planeDiagonalGradientCoefficient (h := h) K 2 (fun _ t z => G t z - 1))
        (fun j => w j s) i) := by
    funext s z
    apply PiLp.ext
    intro k
    rw [planeRawCouplingFlux_diagonal_gradient _ _ (le_refl 2),
      planeRawCouplingFlux_diagonal_gradient _ _ (le_refl 2)]
  change CoupledWeakIdentity _ _ _ _ _ _ _ _ _ _
    (fun s => planeRawCouplingFlux (fun _ : Unit => K i) 2 s
      (planeDiagonalGradientCoefficient (h := fun _ : Unit => h i)
        (fun _ => K i) 2 (fun _ t z => G t z - 1)) (fun _ => w i s) ()) _ _ at hold
  rw [hflux] at hold
  exact hold

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Positive source blocks and a diagonal L2 bound control the joint operator's exact mass norm. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusJointOperator_analytic_mass_bound (K : ι → ℕ) (Mout H : ℕ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u)
    (δ C Cth Θ ρ : ℝ) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hCth : 0 ≤ Cth) (hΘ₀ : 0 ≤ Θ) (hΘ₁ : Θ ≤ 1)
    (hrow : ∀ v, ∑ u, massConjugatedMatrix π A v u ≤ Cth * Θ)
    (hcol : ∀ u, ∑ v, massConjugatedMatrix π A v u ≤ Cth * Θ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (hPd : ∀ v f, torusHkNorm 1 (Nat.zero_le _) (Pd v f) ≤ δ * ‖f‖)
    (hPg : ∀ n, 1 ≤ n → n ≤ H → ∀ v u f,
      torusHkNorm ρ (le_max_left Mout (K v)) (Pg n v u f) ≤ C * (A ^ n) v u * ‖f‖)
    (f : ∀ i, TorusHk 0 (h i)) :
    Real.sqrt (massNormSq 1 π (fun v =>
      (truncateTorusHk (Nat.zero_le _) (jointOperator K Mout H Pd Pg f v)).val)) ≤
      (δ + (C * ∑ n ∈ Finset.Icc 1 H, Cth ^ n) * Θ) *
        Real.sqrt (massNormSq 1 π (fun v => (f v).val)) := by
  have hs := torusJointOperator_mass_bound K Mout H π hπ A hA
    δ C (Cth * Θ) ρ hδ hC (mul_nonneg hCth hΘ₀) hrow hcol Pd Pg hPd hPg f
  have hb : (∑ n ∈ Finset.Icc 1 H, (Cth * Θ) ^ n) ≤
      Θ * ∑ n ∈ Finset.Icc 1 H, Cth ^ n := by
    simpa only [one_mul] using positive_source_powers_linear_theta Cth Θ hΘ₀ hΘ₁
      (Finset.Icc 1 H) (fun n hn => (Finset.mem_Icc.mp hn).1)
      (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) hCth
  apply hs.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply add_le_add le_rfl
  simpa only [mul_left_comm, mul_assoc, mul_comm] using mul_le_mul_of_nonneg_left hb hC

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergy.Variational
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! Joint measurability supplies genuine time integrals of translated weak flux tests. -/

variable {E F X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [MeasurableSpace X] {K L : ℕ}

theorem translated_coefficient_pairing_time_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (C : X → Vec 2 → E →L[ℝ] F) (hc : ∀ t, Continuous (C t))
    (hj : Measurable (Function.uncurry C)) (MC : ℝ) (hMC : 0 ≤ MC)
    (hC : ∀ t x, ‖C t x‖ ≤ MC)
    (f : X → PlaneHk Set.univ K E) (hf : MemLp f 2 μ) (z : Vec 2) (α : JetIndex2 K)
    (φ : PlaneHk Set.univ L F) (β : JetIndex2 L) :
    Integrable (fun t => ∫ x, inner ℝ
      (C t x ((planeCarrierTranslation K z (f t)).toFunction.jet α x))
      (φ.toFunction.jet β x)) μ := by
  let u : X → Lp E 2 (volume : Measure (Vec 2)) := fun t =>
    planeJetReadoutOperator K α (planeCarrierTranslation K z (f t))
  have hft : MemLp (fun t => planeCarrierTranslation (E := E) K z (f t)) 2 μ :=
    (planeCarrierTranslation (E := E) K z).comp_memLp' hf
  have hu : MemLp u 2 μ :=
    (planeJetReadoutOperator (E := E) K α).comp_memLp' hft
  have hp := plane_coefficient_pairing_time_integrable μ C hc hj MC hMC hC u hu
    (planeJetReadoutOperator L β φ)
  have he (t : X) : inner ℝ (planeJetReadoutOperator L β φ)
      (planeCoefficientOperator (C t) (hc t) hMC (hC t) (u t)) =
      ∫ x, inner ℝ (C t x ((planeCarrierTranslation K z (f t)).toFunction.jet α x))
        (φ.toFunction.jet β x) := by
    rw [real_inner_comm, planeCoefficientOperator_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [univToPlane_ae ((planeCarrierTranslation K z (f t)).val α),
      univToPlane_ae (φ.val β)] with x hx hy
    exact congrArg₂ (inner ℝ) (congrArg (C t x) hx) hy
  exact hp.congr (Filter.Eventually.of_forall he)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Positive native-order majorants for the literal transported coefficient array. -/

theorem transportedCoeff_polynomial_jet_bound
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (N Dγ n r : ℕ) (C E ρ : ℝ) (hC : 0 ≤ C) (hE : 0 < E)
    (hρ : 0 ≤ ρ) (hρE : ρ ≤ E) (hn : n + Dγ ≤ N)
    (hKC : ∀ a b j, j ≤ N → ∀ x,
      E ^ j * ‖iteratedFDeriv ℝ j (fun y => K y a b) x‖ ≤ C)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 → Vec 2)
    (hB : ∀ d I i, ContDiff ℝ (n : ℕ) (fun x => B d I x i))
    (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ)
    (ϖ : ℝ) (p : ℕ)
    (hBj : ∀ d ∈ Finset.Icc (r + 1) Dγ, ∀ I i j, j ≤ n → ∀ y,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => B d I x i) y‖ ≤ MB d I * polynomialMomentRoot ϖ y ^ p)
    (A : DerivativeWord2 r) (a : Fin 2) (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y =>
      transportedCoeff K Dγ (fun d I => B d I y) r A y a) x‖ ≤
      (∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
        ((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C * MB d I *
          ((3 * (N + 1 : ℕ) * 2 ^ N * C) ^ (d - 1) * E⁻¹ ^ (d - 1 - r))) *
          polynomialMomentRoot ϖ x ^ p := by
  let f := fun d (I : DerivativeWord2 (d - 1)) (i : Fin 2) (y : Vec 2) =>
    K y a i * B d I y i * transitionT K (List.ofFn I) (List.ofFn A) y
  have hf d I i : ContDiff ℝ (n : ℕ) (f d I i) :=
    (((hK a i).of_le (by simp)).mul (hB d I i)).mul
      ((transitionT_spatial_smooth K hK _ _).of_le (by simp))
  have hfi d I : ContDiff ℝ (n : ℕ) (fun y => ∑ i, f d I i y) :=
    ContDiff.sum (fun i _ => hf d I i)
  have hfd d : ContDiff ℝ (n : ℕ) (fun y => ∑ I, ∑ i, f d I i y) :=
    ContDiff.sum (fun I _ => hfi d I)
  simp_rw [Finset.sum_mul]
  change ρ ^ n * ‖iteratedFDeriv ℝ n
    (fun y => ∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I, ∑ i, f d I i y) x‖ ≤ _
  apply (mul_le_mul_of_nonneg_left
    (finite_jet_finset_sum_norm_le _ _ n (fun d _ => hfd d) x) (pow_nonneg hρ n)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  apply (mul_le_mul_of_nonneg_left
    (finite_jet_sum_norm_le _ n (hfi d) x) (pow_nonneg hρ n)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I _
  apply (mul_le_mul_of_nonneg_left
    (finite_jet_sum_norm_le _ n (hf d I) x) (pow_nonneg hρ n)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hd' := Finset.mem_Icc.mp hd
  have hh := native_piola_summand_polynomial_jet_bound K hK N C E ρ hC hE hρ hρE hKC
    (List.ofFn I) (List.ofFn A) (by simp; omega) n (by simp; omega)
    (fun y => B d I y i) (hB d I i) (MB d I) ϖ p (hBj d hd I i) a i x
  simpa only [List.length_ofFn] using hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The full coupled coefficient reserve and spatial regularity survive the
metric clamp on their native time window. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {K : ι → ℕ} {D : ℕ}
  {G G' : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
  {A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i)}

theorem planeMetricSource_coefficient_data_window_congr
    (ρ a b : ℝ) (heq : ∀ t ∈ Set.Icc a b, G' t = G t)
    (hfinite : ∀ i j d, coefficientSeminorm ρ (K i) a b
      (planeMetricSourceCoefficient K D G A i j d) ≠ ⊤)
    (hsmooth : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ)
      (planeMetricSourceCoefficient K D G A i j d t)) :
    (∀ i j d, coefficientSeminorm ρ (K i) a b
      (planeMetricSourceCoefficient K D G' A i j d) ≠ ⊤) ∧
    (∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ)
      (planeMetricSourceCoefficient K D G' A i j d t)) := by
  constructor
  · intro i j d
    rw [coefficientSeminorm_window_congr ρ (K i) a b _ _
      (fun t ht => planeMetricSourceCoefficient_congr_time (heq t ht) i j d)]
    exact hfinite i j d
  · intro i j d t ht
    rw [planeMetricSourceCoefficient_congr_time (heq t ht)]
    exact hsmooth i j d t ht

theorem planeMetricSource_coefficient_data_metricClamp
    (ρ a b : ℝ)
    (hfinite : ∀ i j d, coefficientSeminorm ρ (K i) a b
      (planeMetricSourceCoefficient K D G A i j d) ≠ ⊤)
    (hsmooth : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ)
      (planeMetricSourceCoefficient K D G A i j d t)) :
    (∀ i j d, coefficientSeminorm ρ (K i) a b
      (planeMetricSourceCoefficient K D (CycleWords.metricClamp a b G) A i j d) ≠ ⊤) ∧
    (∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ)
      (planeMetricSourceCoefficient K D (CycleWords.metricClamp a b G) A i j d t)) := by
  exact planeMetricSource_coefficient_data_window_congr ρ a b
    (fun _ ht => CycleWords.metricClamp_of_mem G ht) hfinite hsmooth
end

/-! A uniform positive price for every lower jet of a native transported polynomial array. -/

def transportedPolynomialJetPrice (N D r n : ℕ) (C R : ℝ)
    (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc (r + 1) D, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
    ((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C * MB d I *
      ((3 * (N + 1 : ℕ) * 2 ^ N * C) ^ (d - 1) * R⁻¹ ^ (d - 1 - r))

theorem transportedPolynomialJetPrice_nonneg (N D r n : ℕ) (C R : ℝ)
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) (hMB : ∀ d I, 0 ≤ MB d I) :
    0 ≤ transportedPolynomialJetPrice N D r n C R MB := by
  unfold transportedPolynomialJetPrice
  apply Finset.sum_nonneg
  intro d _
  apply Finset.sum_nonneg
  intro I _
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hC) (hMB d I)) (by positivity)

theorem leibnizJetPrice_mono {j n : ℕ} (hjn : j ≤ n) :
    (((j + 1 : ℕ) : ℝ) * (2 : ℝ) ^ j) ^ 2 ≤
      (((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ n) ^ 2 := by
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul (by exact_mod_cast Nat.add_le_add_right hjn 1)
    (pow_le_pow_right₀ (by norm_num) hjn) (by positivity) (by positivity)

theorem transportedPolynomialJetPrice_mono (N D r : ℕ) {j n : ℕ} (hjn : j ≤ n)
    (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) (hMB : ∀ d I, 0 ≤ MB d I) :
    transportedPolynomialJetPrice N D r j C R MB ≤ transportedPolynomialJetPrice N D r n C R MB := by
  unfold transportedPolynomialJetPrice
  apply Finset.sum_le_sum
  intro d _
  apply Finset.sum_le_sum
  intro I _
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (hMB d I)
  exact mul_le_mul_of_nonneg_right (leibnizJetPrice_mono hjn) hC

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The actual image L2 series reads the literal periodized weak jet. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem periodized_image_jet_series_ae (U : Set (Vec 2)) (a : JetIndex2 K)
    (f : PlaneHk Set.univ K E)
    (hs : (∑' n : Fin 2 → ℤ,
      ‖planeImageJetCLM U (AVenhance.latticeShift n) a f‖ₑ) < ⊤) :
    (∑' n : Fin 2 → ℤ, planeImageJetCLM U (AVenhance.latticeShift n) a f) =ᵐ[volume.restrict U]
      periodizeRawJet f.toFunction.jet a := by
  have ha : ∀ᵐ x ∂volume.restrict U, ∀ n : Fin 2 → ℤ,
      planeImageJetCLM U (AVenhance.latticeShift n) a f x =
        f.toFunction.jet a (x + AVenhance.latticeShift n) :=
    ae_all_iff.mpr (fun n => planeImageJetCLM_ae U (AVenhance.latticeShift n) a f)
  filter_upwards [Lp.coeFn_tsum hs.ne, ha] with x hx hn
  exact hx.trans (tsum_congr hn)

end AVRegularity.CycleJointProofs
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Inactive-time extension preserves the literal weighted natural remainder,
including its Taylor term, at each physical sample time. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem inactiveTimeZeroFamily_weighted_natural_remainder_eq
    (F : ChartedFamily ι h D P Ctx) (p : P) (c : Ctx p) (v u : ι)
    (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (k : Fin 2)
    (Ks : ℕ) (timeScale a b : ℝ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (r σ e E : ℝ) (yc : Vec 2) (t : ℝ) (z : Vec 2) :
    F.weight p (timeScale * t) * naturalSlowRemainderTimeCoefficient Ks
      (fun τ X y => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * τ) X y k)
      a b hφ r (fun _ => σ) e E yc t z =
    F.weight p (timeScale * t) * naturalSlowRemainderTimeCoefficient Ks
      (fun τ X y => F.flux p c v u γ d I (timeScale * τ) X y k)
      a b hφ r (fun _ => σ) e E yc t z := by
  by_cases hw : F.weight p (timeScale * t) = 0
  · rw [hw, zero_mul, zero_mul]
  · by_cases ht : t ∈ Set.Icc a b
    · simp only [naturalSlowRemainderTimeCoefficient, ite_eq_left ht,
        inactiveTimeZeroFamily_flux_of_weight_ne_zero F p c v u γ d I (timeScale * t) hw]
    · simp only [naturalSlowRemainderTimeCoefficient, ite_eq_right ht]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! The inverse Jacobian `chartInvJacobian` differentiates the chart coordinate. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem chartInvJacobian_column_inverse (X : Vec 2 ≃ₜ Vec 2)
    (hX : Differentiable ℝ ⇑X) (hY : Differentiable ℝ ⇑X.symm)
    (y : Vec 2) (i : Fin 2) :
    fderiv ℝ ⇑X.symm y (fun b => chartInvJacobian ⇑X.symm y b i) = basisVec i := by
  have he : (X.symm : Vec 2 → Vec 2) ∘ (X : Vec 2 → Vec 2) = id := by
    funext z
    exact X.symm_apply_apply z
  have hc := fderiv_comp (X.symm y) (hY (X (X.symm y))) (hX (X.symm y))
  rw [he, fderiv_id, X.apply_symm_apply] at hc
  have hh := congrArg (fun L : Vec 2 →L[ℝ] Vec 2 => L (basisVec i)) hc
  rw [chartInvJacobian_homeomorph_symm X hX hY]
  change fderiv ℝ ⇑X.symm y (fderiv ℝ ⇑X (X.symm y) (basisVec i)) = basisVec i
  exact hh.symm

theorem inverseChart_coordinate_derivative (X : Vec 2 ≃ₜ Vec 2)
    (hX : Differentiable ℝ ⇑X) (hY : Differentiable ℝ ⇑X.symm)
    (g : Vec 2 → E) (hg : Differentiable ℝ g) (y : Vec 2) (i : Fin 2) :
    weightedCoordinateDerivative (chartInvJacobian ⇑X.symm) i (g ∘ X.symm) y =
      fderiv ℝ g (X.symm y) (basisVec i) :=
  weightedCoordinateDerivative_comp _ i _ g y (hY y) (hg (X.symm y))
    (chartInvJacobian_column_inverse X hX hY y i)

end AVRegularity.CycleJointProofs
end
end
