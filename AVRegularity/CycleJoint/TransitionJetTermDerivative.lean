-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.InverseChartCoordinateDerivative
import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
import AVRegularity.Weighted.MetricWordCoefficientArrayBound
import AVRegularity.CycleReference.TransitionTaylorBounds
import AVRegularity.CycleJoint.PeriodicOperatorLocalization
import AVRegularity.CycleJoint.PeriodicOperatorImageBudget
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs

/-! Spatial regularity of the literal zero-extended natural-flow remainder coefficient. -/

theorem naturalSlowRemainderTimeCoefficient_spatial_contDiff (K N : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → ℝ) (a b : ℝ)
    (hf : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K + N : ℕ) (Function.uncurry (f t)))
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (r : ℝ) (τ : ℝ → ℝ) (e E : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ) :
    ContDiff ℝ (N : ℕ) (naturalSlowRemainderTimeCoefficient K f a b hφ r τ e E yc t) := by
  by_cases ht : t ∈ Set.Icc a b
  · let Yc := streamFlow φ hφ r yc (τ t)
    let X0 := E⁻¹ • Yc
    let phase := e⁻¹ • Yc
    let g := fun X z => f t X (z + phase)
    have hg : ContDiff ℝ (K + N : ℕ) (Function.uncurry g) :=
      (hf t ht).comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))
    have hgN : ContDiff ℝ (N : ℕ) (Function.uncurry g) :=
      hg.of_le (by exact_mod_cast Nat.le_add_left N K)
    let R := fun z => g (X0 + (e / E) • z) z -
      taylorSlow 0 K (fun X => g X z) X0 ((e / E) • z)
    have hR : ContDiff ℝ (N : ℕ) R :=
      (hgN.comp ((contDiff_const.add (contDiff_id.const_smul (e / E))).prodMk contDiff_id)).sub
        (Weighted.taylorSlow_spatial_contDiff 0 K N g hg X0 (e / E))
    have heq : naturalSlowRemainderTimeCoefficient K f a b hφ r τ e E yc t =
        R ∘ naturalPreparationCellFlow hφ r (τ t) e yc := by
      funext z
      simp only [naturalSlowRemainderTimeCoefficient, ite_eq_left ht]
      exact naturalPreparation_slow_remainder_coordinates hφ r (τ t) e E he yc z K (f t)
    rw [heq]
    exact hR.comp ((naturalPreparationCellFlow_smooth hφ r (τ t) e yc).of_le (by simp))
  · have heq : naturalSlowRemainderTimeCoefficient K f a b hφ r τ e E yc t = fun _ => 0 := by
      funext z
      simp only [naturalSlowRemainderTimeCoefficient, ite_eq_right ht]
    rw [heq]
    exact contDiff_const

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Actual plane weak solutions superpose, including their time traces and Sobolev lifts. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance aeLinearDataScalingNativeAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance aeLinearDataScalingNativeModule (i : ι) (k : ℕ) : Module ℝ (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance linearDataScalingFluxAdd (i : ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance linearDataScalingFluxModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance

theorem planeWeakSolution_smul_ae_linear_data (K : ι → ℕ) (D : ℕ) (ν a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (lf : E →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (lF : E → ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (lg : E →ₗ[ℝ] (∀ i, ℝ → PlaneHk Set.univ (K i) (h i)))
    (c : ℝ) (x : E)
    (hread : ∀ i, lF (c • x) i =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => c • lF x i t)
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A (lf x) (lF x) (lg x) u w)
    : IsCoupledWeakSolutionPlane ν a b v D K A (lf (c • x)) (lF (c • x)) (lg (c • x))
      (fun i t => c • u i t) (fun i t => c • w i t) := by
  have hh := planeWeakSolution_smul K D c ν a b v A (lf x) (lF x) (lg x) u w hs
  have hscale : IsCoupledWeakSolutionPlane ν a b v D K A (lf (c • x))
      (fun i t => c • lF x i t) (lg (c • x))
      (fun i t => c • u i t) (fun i t => c • w i t) := by
    simpa only [map_smul, Pi.smul_def] using hh
  apply planeWeakSolution_forcing_time_ae_congr _ hscale
  intro i
  filter_upwards [hread i] with t ht
  rw [ht]
end

/-! Subtracting the retained approximation gives the actual native residual error equation with its time traces and lifts. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeWeakSolution_sub (K : ι → ℕ) (D : ℕ) (ν a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (f f' : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F F' : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g g' u u' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w w' : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w)
    (hs' : IsCoupledWeakSolutionPlane ν a b v D K A f' F' g' u' w') :
    IsCoupledWeakSolutionPlane ν a b v D K A (fun i => f i - f' i)
      (fun i t => F i t - F' i t) (fun i t => g i t - g' i t)
      (fun i t => u i t - u' i t) (fun i t => w i t - w' i t) := by
  have hn := planeWeakSolution_smul K D (-1) ν a b v A f' F' g' u' w' hs'
  have he := planeWeakSolution_add K D ν a b v A f (fun i => (-1 : ℝ) • f' i)
    F (fun i t => (-1 : ℝ) • F' i t) g (fun i t => (-1 : ℝ) • g' i t)
    u (fun i t => (-1 : ℝ) • u' i t) w (fun i t => (-1 : ℝ) • w' i t) hs hn
  simpa only [neg_one_smul, sub_eq_add_neg] using he

theorem planeHomogeneousSolution_residual_error_equation
    (K : ι → ℕ) (D : ℕ) (ν a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (Ferr : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (u uP : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w wP : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w)
    (hP : IsCoupledWeakSolutionPlane ν a b v D K A f Ferr (fun _ _ => 0) uP wP) :
    IsCoupledWeakSolutionPlane ν a b v D K A (fun _ => 0)
      (fun i t => -Ferr i t) (fun _ _ => 0)
      (fun i t => u i t - uP i t) (fun i t => w i t - wP i t) := by
  simpa only [sub_self, zero_sub] using
    planeWeakSolution_sub K D ν a b v A f f (fun _ _ => 0) Ferr
      (fun _ _ => 0) (fun _ _ => 0) u uP w wP hs hP
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! All periodic images of the derivative arrays have the full-lattice overlap budget. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem spatialPatchCoefficient_array_translate (ζ : ℝ → ℝ) (N j : ℕ)
    (k n : Fin 2 → ℤ) (x : Vec 2) :
    coefficientDerivativeArray (spatialPatchCoefficient (E := E) ζ N k) j
        (x + AVenhance.latticeShift n) =
      coefficientDerivativeArray (spatialPatchCoefficient (E := E) ζ N
        (fun i => k i - (N : ℤ) * n i)) j x := by
  have he : (fun y => spatialPatchCoefficient (E := E) ζ N k (y + AVenhance.latticeShift n)) =
      spatialPatchCoefficient (E := E) ζ N (fun i => k i - (N : ℤ) * n i) := by
    funext y
    change spatialPatchCutoff ζ N k (y + AVenhance.latticeShift n) • ContinuousLinearMap.id ℝ E = _
    rw [spatialPatchCutoff_translate]
    rfl
  rw [← coefficientDerivativeArray_translate, he]

theorem spatialPatch_array_image_square_budget {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (j : ℕ) (x : Vec 2) (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ k, ‖coefficientDerivativeArray (spatialPatchCoefficient (E := E) ζ N k) j x‖ ≤ D) :
    (∑ p : Fin 2 → Fin N, ∑' n : Fin 2 → ℤ,
      ENNReal.ofReal (‖coefficientDerivativeArray
        (spatialPatchCoefficient (E := E) ζ N (fun i => (p i : ℤ))) j
          (x + AVenhance.latticeShift n)‖ ^ 2)) ≤ 9 * ENNReal.ofReal (D ^ 2) := by
  have he := ((negatePeriodImages N).trans (periodImageLatticeEquiv N hN)).tsum_eq
    (fun k => ENNReal.ofReal (‖coefficientDerivativeArray (spatialPatchCoefficient (E := E) ζ N k) j x‖ ^ 2))
  change (∑' p : (Fin 2 → Fin N) × (Fin 2 → ℤ),
    ENNReal.ofReal (‖coefficientDerivativeArray (spatialPatchCoefficient (E := E) ζ N
      (fun i => (p.1 i : ℤ) + (N : ℤ) * (-p.2 i))) j x‖ ^ 2)) = _ at he
  have ht := he.trans_le (spatialPatchCoefficient_square_sum_le hζ N j x D hD hb)
  simpa only [ENNReal.tsum_prod', tsum_fintype, mul_neg, ← sub_eq_add_neg,
    spatialPatchCoefficient_array_translate] using ht

end AVRegularity.CycleJointProofs
end

section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Ordered native coordinate derivatives are reproduced exactly by inverse-chart differential words. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def listCoordinateDerivative : List (Fin 2) → (Vec 2 → E) → Vec 2 → E
  | [], g => g
  | i :: I, g => fun y => fderiv ℝ (listCoordinateDerivative I g) y (basisVec i)

def weightedListCoordinateDerivative (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) :
    List (Fin 2) → (Vec 2 → E) → Vec 2 → E
  | [], g => g
  | i :: I, g => weightedCoordinateDerivative K i (weightedListCoordinateDerivative K I g)

theorem listCoordinateDerivative_smooth (I : List (Fin 2)) (g : Vec 2 → E)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (listCoordinateDerivative I g) := by
  induction I with
  | nil => exact hg
  | cons i I ih =>
    exact (ContinuousLinearMap.apply ℝ E (basisVec i)).contDiff.comp
      (ih.fderiv_right (by simp))

theorem inverseChart_list_coordinate_derivative (X : Vec 2 ≃ₜ Vec 2)
    (hX : Differentiable ℝ ⇑X) (hY : Differentiable ℝ ⇑X.symm)
    (I : List (Fin 2)) (g : Vec 2 → E) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    weightedListCoordinateDerivative (chartInvJacobian ⇑X.symm) I (g ∘ X.symm) =
      (listCoordinateDerivative I g) ∘ X.symm := by
  induction I with
  | nil => rfl
  | cons i I ih =>
    change weightedCoordinateDerivative (chartInvJacobian ⇑X.symm) i
      (weightedListCoordinateDerivative (chartInvJacobian ⇑X.symm) I (g ∘ X.symm)) = _
    rw [ih]
    funext y
    exact inverseChart_coordinate_derivative X hX hY (listCoordinateDerivative I g)
      ((listCoordinateDerivative_smooth I g hg).differentiable (by simp)) y i

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVenhance.Infra.Section5
open AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! A globally smooth natural formula for the family's certified inverse-Piola Jacobian.
It agrees with the actual chart wherever that piece is available. -/

def naturalPreparationJacobian {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s t : ℝ) (x : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  chartJacobian (fun y => streamFlow φ hφ t y s) (streamFlow φ hφ s x t)

theorem naturalPreparationJacobian_entry_smooth {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ℝ × Vec 2 => naturalPreparationJacobian hφ s z.1 z.2 i j) := by
  have hy : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ℝ × Vec 2 => streamFlow φ hφ s z.2 z.1) :=
    (streamFlow_joint_smooth hφ).comp
      (contDiff_const.prodMk (contDiff_snd.prodMk contDiff_fst))
  simpa only [naturalPreparationJacobian, chartJacobian, chartJac, jacMatrix, Function.comp_def] using
    (chartJac_entry_smooth hφ s i j).comp (contDiff_fst.prodMk hy)

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

theorem preparation_inverse_material_eq_streamFlow
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (p : P') (hp : ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty)
    (r : ℝ) (hr : r ∈ (F.piece p).geometry) :
    ⇑((F.piece p).material r).symm = fun x => streamFlow φ hφ (F.piece p).anchor x r := by
  have he : (F.piece p).material r = streamFlowHomeomorph hφ r (F.piece p).anchor := by
    apply Homeomorph.ext
    intro y
    exact congrFun (preparation_material_eq_streamFlow hc p hp r hr) y
  rw [he]
  rfl

theorem preparation_inverseJacobian_eq_natural
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (p : P') (hp : ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty)
    (r : ℝ) (hr : r ∈ (F.piece p).geometry) :
    chartInvJacobian ⇑((F.piece p).material r).symm =
      naturalPreparationJacobian hφ (F.piece p).anchor r := by
  funext x
  rw [chartInvJacobian_homeomorph_symm ((F.piece p).material r)
    (((F.piece p).material_smooth r).differentiable (by simp))
    (((F.piece p).material_symm_smooth r).differentiable (by simp)),
    preparation_inverse_material_eq_streamFlow hc p hp r hr,
    preparation_material_eq_streamFlow hc p hp r hr]
  rfl

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! Compact smooth Hilbert-valued fields approximate every genuine native plane H1 carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1_exists_compact_smooth_approximation (u : PlaneHk univ 1 E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f),
      dist (compactSmoothHilbertH1 f hf hs) u < ε := by
  obtain ⟨κ, hcκ, hdκ, hκ, hmass⟩ := exists_normalized_smooth_kernel
  obtain ⟨R, hR⟩ := exists_shrinking_linearEquiv
  have havg := planeH1Average_tendsto (fun n => (R n).toLinearEquiv.toAddHom)
    (fun n => (R n).continuous) hR κ hκ hmass u
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp havg (ε / 2) (half_pos hε)
  let z := planeH1Average (R N).toLinearEquiv.toAddHom (R N).continuous κ hκ u
  let g := planeH1AverageLiteral (R N) κ u
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := planeH1AverageLiteral_smooth (R N) κ hcκ hdκ u
  have hz : (planeHkValueOperator 1 z : Vec 2 → E) =ᵐ[volume] g :=
    planeH1AverageLiteral_value_ae (R N) κ hκ u
  have htr := planeH1_compact_truncation_tendsto z g hg hz
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp htr (ε / 2) (half_pos hε)
  let f := fun x => spatialApproximationCutoff K x • g x
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (spatialApproximationCutoff_smooth K).smul hg
  have hs : HasCompactSupport f := (spatialApproximationCutoff_compact K).smul_right
  refine ⟨f, hf, hs, ?_⟩
  have hk : dist (compactSmoothHilbertH1 f hf hs) z < ε / 2 := hK K le_rfl
  have hn : dist z u < ε / 2 := hN N le_rfl
  calc
    _ ≤ dist (compactSmoothHilbertH1 f hf hs) z + dist z u := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hk hn
    _ = ε := add_halves ε

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! Compact smooth native H1 tests determine every continuous linear weak functional. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1_CLM_ext_compact_smooth (L M : PlaneHk univ 1 E →L[ℝ] ℝ)
    (h : ∀ (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f),
      L (compactSmoothHilbertH1 f hf hs) = M (compactSmoothHilbertH1 f hf hs)) : L = M := by
  apply ContinuousLinearMap.ext
  intro u
  have hc : IsClosed {z : PlaneHk univ 1 E | L z = M z} := isClosed_eq L.continuous M.continuous
  have hu : u ∈ closure {z : PlaneHk univ 1 E | L z = M z} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨f, hf, hs, hd⟩ := planeH1_exists_compact_smooth_approximation u hε
    exact ⟨compactSmoothHilbertH1 f hf hs, h f hf hs, by rwa [dist_comm]⟩
  rw [hc.closure_eq] at hu
  exact hu

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The summed derivative-array patch energy has a dimension-independent overlap cost. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem spatialPatch_array_l2_integral_budget {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (j : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ k x, ‖coefficientDerivativeArray
      (spatialPatchCoefficient (E := E) ζ N k) j x‖ ≤ D)
    (f : Vec 2 → E) (hm : Measurable f)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube))
    (hp : AVenhance.IsZ2Periodic f) :
    (∑ p : Fin 2 → Fin N, ∫ x,
      ‖coefficientDerivativeArray
        (spatialPatchCoefficient (E := E) ζ N (fun i => (p i : ℤ))) j x (f x)‖ ^ 2 ∂volume) ≤
      (9 * D ^ 2) * ∫ x in AVenhance.unitCube, ‖f x‖ ^ 2 ∂volume := by
  let C : (Fin 2 → Fin N) → Vec 2 → E →L[ℝ] PiLp 2 (fun _ : DerivativeWord2 j => E) :=
    fun p x => coefficientDerivativeArray
      (spatialPatchCoefficient (E := E) ζ N (fun i => (p i : ℤ))) j x
  have hc (p : Fin 2 → Fin N) : Continuous (C p) := by
    exact coefficientDerivativeArray_continuous (E := E) (F := E)
      (spatialPatchCoefficient (E := E) ζ N (fun i => (p i : ℤ))) j
      (spatialPatchCoefficient_smooth hζ N (fun i => (p i : ℤ)) j)
  have hcs (p : Fin 2 → Fin N) : HasCompactSupport (C p) :=
    coefficientDerivativeArray_compact _
      (spatialPatchCoefficient_compact hζ N hN (fun i => (p i : ℤ))) j
  have hi (x : Vec 2) : (∑ p, ∑' n : Fin 2 → ℤ,
      ENNReal.ofReal (‖C p (x + AVenhance.latticeShift n)‖ ^ 2)) ≤
      ENNReal.ofReal (9 * D ^ 2) := by
    simpa only [C, ENNReal.ofReal_mul (show (0 : ℝ) ≤ 9 by norm_num),
      ENNReal.ofReal_ofNat] using
      spatialPatch_array_image_square_budget hζ N hN j x D hD (fun k => hb k x)
  exact periodic_operator_image_integral_budget C hc hcs (9 * D ^ 2)
    (mul_nonneg (by norm_num) (sq_nonneg _)) hi f hm hf hp

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Each finite native transition-jet layer is a genuine smooth field. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def transitionJetTerm (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (I : List (Fin 2)) (r : ℕ) (g : Vec 2 → E) (y : Vec 2) : E :=
  ∑ A : DerivativeWord2 r, transitionT K I (List.ofFn A) y •
    listCoordinateDerivative (List.ofFn A) g y

theorem transitionJetTerm_smooth
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun y => K y a b))
    (I : List (Fin 2)) (r : ℕ) (g : Vec 2 → E) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (transitionJetTerm K I r g) := by
  apply ContDiff.sum
  intro A hA
  exact (transitionT_spatial_smooth K hK I (List.ofFn A)).smul
    (listCoordinateDerivative_smooth (List.ofFn A) g hg)
end

/-! Differentiating a native transition layer separates the coefficient derivative and the next native state derivative. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weightedCoordinateDerivative_transitionJetTerm
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun y => K y a b))
    (i : Fin 2) (I : List (Fin 2)) (r : ℕ) (g : Vec 2 → E)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Vec 2) :
    weightedCoordinateDerivative K i (transitionJetTerm K I r g) y =
      (∑ A : DerivativeWord2 r,
        weightedCoordinateDerivative K i (transitionT K I (List.ofFn A)) y •
          listCoordinateDerivative (List.ofFn A) g y) +
      ∑ a : Fin 2, K y a i •
        (∑ A : DerivativeWord2 r, transitionT K I (List.ofFn A) y •
          listCoordinateDerivative (a :: List.ofFn A) g y) := by
  classical
  unfold transitionJetTerm
  rw [weightedCoordinateDerivative_sum K i Finset.univ (fun A x => transitionT K I (List.ofFn A) x •
      listCoordinateDerivative (List.ofFn A) g x) y
    (fun A _ => ((transitionT_spatial_smooth K hK I (List.ofFn A)).smul
      (listCoordinateDerivative_smooth (List.ofFn A) g hg)).differentiable (by simp) y)]
  have hp : ∀ A : DerivativeWord2 r,
      weightedCoordinateDerivative K i
        (fun x => transitionT K I (List.ofFn A) x • listCoordinateDerivative (List.ofFn A) g x) y =
      weightedCoordinateDerivative K i (transitionT K I (List.ofFn A)) y •
        listCoordinateDerivative (List.ofFn A) g y +
      transitionT K I (List.ofFn A) y •
        weightedCoordinateDerivative K i (listCoordinateDerivative (List.ofFn A) g) y := by
    intro A
    exact weightedCoordinateDerivative_smul K i _ _ y
      ((transitionT_spatial_smooth K hK I (List.ofFn A)).differentiable (by simp) y)
      ((listCoordinateDerivative_smooth (List.ofFn A) g hg).differentiable (by simp) y)
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  congr 1
  simp only [weightedCoordinateDerivative, Finset.smul_sum, listCoordinateDerivative]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro A hA
  exact smul_comm _ _ _
end

end AVRegularity.CycleJointProofs
end
