-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.PlaneH1Readouts
import AVRegularity.CycleEvolution.CellDriftSmoothEnergy
public import AVRegularity.Definitions.CycleEvolution.IsFibreGraph
public import AVRegularity.CoupledEnergyPlane.Variational.GradientTensorOperator
public import AVRegularity.Weighted.PlaneHkTimeFromReadouts
import AVenhance.Infra.Classical.PeriodicCalculus

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Each actual slow Taylor degree consumes exactly its polynomial growth degree. -/

theorem slow_taylor_degree_jet_growth {T : Type*} (r J : ℕ)
    (f : T → Vec 2 → Vec 2 → ℝ)
    (hf : ∀ t, ContDiff ℝ (r + J : ℕ) (Function.uncurry (f t)))
    (X₀ : Vec 2) (δ B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ t (w : DerivativeWord2 r) j, j ≤ J → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z => iteratedFDeriv ℝ r (fun X => f t X z) X₀
        (fun i => basisVec (w i))) x‖ ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t j, j ≤ J → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z => ((r.factorial : ℝ))⁻¹ *
        iteratedFDeriv ℝ r (fun X => f t X z) X₀ (fun _ => δ • z)) x‖ ≤
        A * (1 + ‖x‖) ^ r := by
  let a := fun t z => iteratedFDeriv ℝ r (fun X => f t X z) X₀
  have ha (t : T) : ContDiff ℝ (J : ℕ) (a t) := by
    have hh := joint_partialIteratedFDeriv_left_contDiff J r (Function.uncurry (f t))
      (by simpa only [Nat.add_comm] using hf t)
    exact hh.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨A, hA, hAb⟩ := multilinear_diagonal_jet_growth J a ha δ B hB hb
  refine ⟨|((r.factorial : ℝ))⁻¹| * A, mul_nonneg (abs_nonneg _) hA, ?_⟩
  intro t
  exact growing_scalar_jet_const_mul_bound J r _
    (multilinear_diagonal_contDiff J (a t) (ha t) δ) A ((r.factorial : ℝ))⁻¹ (hAb t)

/-! The literal truncated Taylor coefficient has growth bounded by its slow reserve. -/

theorem taylorSlow_jet_growth {T : Type*} (lo Ks J : ℕ)
    (f : T → Vec 2 → Vec 2 → ℝ)
    (hf : ∀ t, ContDiff ℝ (Ks + J : ℕ) (Function.uncurry (f t)))
    (X₀ : Vec 2) (δ B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ r ≤ Ks, ∀ t (w : DerivativeWord2 r) j, j ≤ J → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z => iteratedFDeriv ℝ r (fun X => f t X z) X₀
        (fun i => basisVec (w i))) x‖ ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t j, j ≤ J → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z => taylorSlow lo Ks (fun X => f t X z) X₀ (δ • z)) x‖ ≤
        A * (1 + ‖x‖) ^ Ks := by
  let term := fun r t z => ((r.factorial : ℝ))⁻¹ *
    iteratedFDeriv ℝ r (fun X => f t X z) X₀ (fun _ => δ • z)
  have ht (r : ℕ) (hr : r ∈ Finset.Icc lo Ks) (t : T) :
      ContDiff ℝ (J : ℕ) (term r t) := by
    have hh := joint_partialIteratedFDeriv_left_contDiff J r (Function.uncurry (f t))
      ((hf t).of_le (by exact_mod_cast (show J + r ≤ Ks + J by
        have := (Finset.mem_Icc.mp hr).2; omega)))
    have ha : ContDiff ℝ (J : ℕ)
        (fun z => iteratedFDeriv ℝ r (fun X => f t X z) X₀) :=
      hh.comp (contDiff_const.prodMk contDiff_id)
    exact contDiff_const.mul (multilinear_diagonal_contDiff J _ ha δ)
  have hbound (r : ℕ) (hr : r ∈ Finset.Icc lo Ks) :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ t j, j ≤ J → ∀ x,
        ‖iteratedFDeriv ℝ j (term r t) x‖ ≤ A * (1 + ‖x‖) ^ r := by
    have hrK := (Finset.mem_Icc.mp hr).2
    exact slow_taylor_degree_jet_growth r J f
      (fun t => (hf t).of_le (by exact_mod_cast Nat.add_le_add_right hrK J))
      X₀ δ B hB (hb r hrK)
  exact finite_scalar_growth_sum_exists (Finset.Icc lo Ks) J Ks term (fun r => r)
    (fun r hr => (Finset.mem_Icc.mp hr).2) ht hbound

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVenhance.Infra.Torus AVenhance.Infra.Classical
namespace AVRegularity.Weighted

/-! The public weak cell drift condition implies classical divergence zero for smooth drifts. -/

theorem cellDrift_classical_divergence_zero {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) :
    ∀ t x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0 := by
  intro t
  let f := fun k : Fin 2 => fun x => v t x k
  have hf (k : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (f k) := (contDiff_pi.mp (hvs t)) k
  have hfp (k : Fin 2) : AVenhance.IsZ2Periodic (f k) :=
    fun n x => congrFun (hv.2.2.1 t n x) k
  let a := fun k : Fin 2 => fun x => AVenhance.spaceGrad (f k) x k
  have ha (k : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (a k) :=
    ((hf k).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hap (k : Fin 2) : AVenhance.IsZ2Periodic (a k) := by
    intro n x
    exact congrArg (fun C => C (basisVec k))
      (fderiv_isZ2Periodic ((hf k).differentiable (by simp)) (hfp k) n x)
  let q := fun x => ∑ k : Fin 2, a k x
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := ContDiff.sum (fun k _ => ha k)
  have hqp : AVenhance.IsZ2Periodic q := by
    intro n x
    simp only [q]
    exact Finset.sum_congr rfl (fun k _ => hap k n x)
  have hli (k : Fin 2) : IntegrableOn (fun x => f k x * AVenhance.spaceGrad q x k)
      (unitCell 2) := PeriodicCalculus.continuous_integrableOn_unitCell
    ((hf k).continuous.mul (((hq.fderiv_right (m := (0 : ℕ)) (by simp)).clm_apply
      contDiff_const).continuous))
  have hri (k : Fin 2) : IntegrableOn (fun x => a k x * q x) (unitCell 2) :=
    PeriodicCalculus.continuous_integrableOn_unitCell ((ha k).continuous.mul hq.continuous)
  have hparts : (∫ x in unitCell 2, ∑ k : Fin 2, f k x * AVenhance.spaceGrad q x k) =
      -(∫ x in unitCell 2, q x ^ 2) := by
    rw [integral_finsetSum _ (fun k _ => hli k)]
    simp_rw [integral_unitCell_coord_ibp_real _ ((hf _).of_le (by simp))
      (hq.of_le (by simp)) (hfp _) hqp]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun k _ => hri k)]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    simp only [q, ← Finset.sum_mul, pow_two]
  have hz := CycleEvolution.cellDrift_smooth_transport_zero hv t q hq hqp
  rw [← integral_unitCell_eq_unitCube] at hz
  have hsq : (∫ x in AVenhance.unitCube, q x ^ 2) = 0 := by
    rw [← integral_unitCell_eq_unitCube]
    have hh : (∫ x in unitCell 2, q x ^ 2) = 0 := by
      have hz' : (∫ x in unitCell 2, ∑ k : Fin 2, f k x * AVenhance.spaceGrad q x k) = 0 := hz
      rw [hparts] at hz'
      exact neg_eq_zero.mp hz'
    exact hh
  have hzero := periodic_scalar_zero_of_cell_square_integral q hq.continuous hqp hsq
  intro x
  have hd := ((hvs t).differentiable (by simp)).differentiableAt (x := x)
  simpa only [q, a, f, AVenhance.spaceGrad, fderiv_apply hd,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using hzero x

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.Weighted

/-! Every stored finite family jet is its literal vector of component readouts. -/

variable {J E : Type*} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeFamilyTensor_jet_ae {K : ℕ} (p : J → PlaneHk Set.univ K E)
    (j : JetIndex2 K) :
    (planeFamilyTensor p).val j =ᵐ[volume.restrict Set.univ] fun x =>
      WithLp.toLp 2 (fun k : J => (p k).val j x) := by
  rw [planeFamilyTensor_jet]
  let u : J → ComponentL2 (volume.restrict (Set.univ : Set (Vec 2))) E :=
    fun k => (p k).val j
  let T : J → E →L[ℝ] PiLp 2 (fun _ : J => E) :=
    fun k => tensorEntryCLM (J := J) (E := E) k
  have hs := Lp.coeFn_finsetSum Finset.univ (fun k : J =>
    (T k).compLpL 2 (volume.restrict (Set.univ : Set (Vec 2))) (u k))
  dsimp only [T, u] at hs
  have ht : ∀ᵐ x ∂volume.restrict Set.univ, ∀ k : J,
      ((tensorEntryCLM (E := E) k).compLpL 2 (volume.restrict Set.univ) ((p k).val j)) x =
        tensorEntryCLM (J := J) (E := E) k ((p k).val j x) :=
    ae_all_iff.mpr (fun k => ContinuousLinearMap.coeFn_compLpL
      (tensorEntryCLM (J := J) (E := E) k) ((p k).val j))
  filter_upwards [hs, ht] with x hx hterms
  rw [hx, Finset.sum_apply]
  apply PiLp.ext
  intro k
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [hterms]
  change (∑ a : J, PiLp.single 2 a ((p a).val j x) k) = _
  simp

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! The Riesz representative of a plane divergence-form weak right-hand side. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The Hilbert carrier of vector-valued `L²` fluxes on the plane. -/
abbrev PlaneFluxL2 (E : Type*) [NormedAddCommGroup E] [MeasurableSpace E] :=
  PiLp 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2)))

/-- The fixed-time weak spatial functional for transport, diffusion and a divergence forcing. -/
def planeWeakRhsFunctional
    (transport : PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (diffusion : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (u : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E) :
    PlaneHk Set.univ 1 E →L[ℝ] ℝ :=
  -((InnerProductSpace.toDual ℝ (Lp E 2 (volume : Measure (Vec 2)))
      (transport (planeH1GradientOperator (E := E) u))).comp
      (planeHkValueOperator (E := E) 1))
    -((InnerProductSpace.toDual ℝ (PlaneFluxL2 E)
      (diffusion (planeH1GradientOperator (E := E) u) + F)).comp
      (planeH1GradientOperator (E := E)))

/-- The `H¹` Riesz representative of the preceding weak functional. -/
def planeWeakDualRepresentative
    (transport : PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (diffusion : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (u : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E) : PlaneHk Set.univ 1 E :=
  (InnerProductSpace.toDual ℝ (PlaneHk Set.univ 1 E)).symm
    (planeWeakRhsFunctional transport diffusion u F)

omit [FiniteDimensional ℝ E] in
/-- Pairing the Riesz representative against an `H¹` test is precisely the weak PDE spatial side. -/
theorem planeWeakDualRepresentative_pair
    (transport : PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (diffusion : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (u z : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E) :
    inner ℝ (planeWeakDualRepresentative transport diffusion u F) z =
      -inner ℝ (transport (planeH1GradientOperator (E := E) u))
        (planeHkValueOperator (E := E) 1 z)
        -inner ℝ (diffusion (planeH1GradientOperator (E := E) u) + F)
          (planeH1GradientOperator (E := E) z) := by
  change inner ℝ
      ((InnerProductSpace.toDual ℝ (PlaneHk Set.univ 1 E)).symm
        (planeWeakRhsFunctional transport diffusion u F)) z =
    planeWeakRhsFunctional transport diffusion u F z
  rw [InnerProductSpace.toDual_symm_apply]

omit [FiniteDimensional ℝ E] in
/-- The weak representative is the sum of the value and gradient adjoint actions. -/
theorem planeWeakDualRepresentative_eq_adjoint
    (transport : PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (diffusion : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (u : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E) :
    planeWeakDualRepresentative transport diffusion u F =
      -(planeHkValueOperator (E := E) 1).adjoint
        (transport (planeH1GradientOperator (E := E) u))
      -(planeH1GradientOperator (E := E)).adjoint
        (diffusion (planeH1GradientOperator (E := E) u) + F) := by
  apply ext_inner_right ℝ
  intro z
  rw [planeWeakDualRepresentative_pair]
  simp only [inner_sub_left, inner_neg_left, ContinuousLinearMap.adjoint_inner_left]

omit [FiniteDimensional ℝ E] in
/-- Spatial `L²` right-hand-side actions give an `L²`-in-time `H¹` dual representative. -/
theorem planeWeakDualRepresentative_memLp
    {T : Type*} [MeasurableSpace T] {μ : Measure T}
    (transport : T → PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (diffusion : T → PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (u : T → PlaneHk Set.univ 1 E) (F : T → PlaneFluxL2 E)
    (ht : MemLp (fun t => transport t (planeH1GradientOperator (E := E) (u t))) 2 μ)
    (hd : MemLp (fun t => diffusion t (planeH1GradientOperator (E := E) (u t))) 2 μ)
    (hF : MemLp F 2 μ) :
    MemLp (fun t => planeWeakDualRepresentative (transport t) (diffusion t) (u t) (F t))
      2 μ := by
  simp_rw [planeWeakDualRepresentative_eq_adjoint]
  exact ((planeHkValueOperator (E := E) 1).adjoint.comp_memLp' ht).neg.sub
    ((planeH1GradientOperator (E := E)).adjoint.comp_memLp' (hd.add hF))

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! Continuous component readout for the actual plane flux forcing. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Exchange the finite Hilbert component array and the spatial `L²` carrier. -/
def planeFluxSplitOperator :
    Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)) →L[ℝ] PlaneFluxL2 E :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2)))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k : Fin 2 =>
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k).compLpL 2 volume)

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- Each readout component is the corresponding component of the original flux almost everywhere. -/
theorem planeFluxSplitOperator_ae
    (F : Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2))) (k : Fin 2) :
    planeFluxSplitOperator (E := E) F k =ᵐ[volume] fun z => F z k :=
  ContinuousLinearMap.coeFn_compLpL _ _

/-- Read the value of a Sobolev flux as the two ambient `L²` components. -/
def planeFluxValueOperator (K : ℕ) :
    PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ] PlaneFluxL2 E :=
  (planeFluxSplitOperator (E := E)).comp
    (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) K)

theorem planeFluxValueOperator_ae (K : ℕ)
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) (k : Fin 2) :
    planeFluxValueOperator (E := E) K F k =ᵐ[volume]
      fun z => F.toFunction.jet (valueIndex2 K) z k := by
  filter_upwards [planeFluxSplitOperator_ae (E := E)
      (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) K F) k,
    univToPlane_ae (F.val (valueIndex2 K))] with z hz hv
  exact hz.trans (congrArg (fun q => q k) hv)

/-- The assumed time `L² H^K` forcing has the `L²` time flux readout required by the weak energy bridge. -/
theorem planeFluxValueOperator_memLp {T : Type*} [MeasurableSpace T] {μ : Measure T}
    (K : ℕ) (F : T → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hF : MemLp F 2 μ) : MemLp (fun t => planeFluxValueOperator (E := E) K (F t)) 2 μ :=
  (planeFluxValueOperator (E := E) K).comp_memLp' hF

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! The true value-plus-divergence source as a Hilbert H1 dual. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeSourceDual (H : Lp E 2 (volume : Measure (Vec 2)))
    (S : PlaneFluxL2 E) : PlaneHk Set.univ 1 E :=
  (planeHkValueOperator (E := E) 1).adjoint H -
    (planeH1GradientOperator (E := E)).adjoint S

theorem planeSourceDual_pair (H : Lp E 2 (volume : Measure (Vec 2)))
    (S : PlaneFluxL2 E) (z : PlaneHk Set.univ 1 E) :
    inner ℝ (planeSourceDual H S) z =
      inner ℝ H (planeHkValueOperator 1 z) - inner ℝ S (planeH1GradientOperator z) := by
  simp only [planeSourceDual, inner_sub_left, ContinuousLinearMap.adjoint_inner_left]

theorem planeSourceDual_memLp {T : Type*} [MeasurableSpace T] {μ : Measure T}
    (H : T → Lp E 2 (volume : Measure (Vec 2))) (hH : MemLp H 2 μ)
    (S : T → PlaneFluxL2 E) (hS : MemLp S 2 μ) :
    MemLp (fun t => planeSourceDual (H t) (S t)) 2 μ :=
  ((planeHkValueOperator (E := E) 1).adjoint.comp_memLp' hH).sub
    ((planeH1GradientOperator (E := E)).adjoint.comp_memLp' hS)

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! Actual value forcing in the scalar weak Hilbert dual. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeValueForcedDual
    (T : PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (D : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (u : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E)
    (g : Lp E 2 (volume : Measure (Vec 2))) : PlaneHk Set.univ 1 E :=
  planeWeakDualRepresentative T D u F + (planeHkValueOperator (E := E) 1).adjoint g

theorem planeValueForcedDual_pair
    (T : PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (D : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (u z : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E)
    (g : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (planeValueForcedDual T D u F g) z =
      inner ℝ (planeWeakDualRepresentative T D u F) z +
        inner ℝ g (planeHkValueOperator (E := E) 1 z) := by
  simp only [planeValueForcedDual, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left]

theorem planeValueForcing_pair_of_value
    (g : Lp E 2 (volume : Measure (Vec 2)))
    (z : PlaneHk Set.univ 1 E) (u : Lp E 2 (volume : Measure (Vec 2)))
    (q : Vec 2 → ℝ)
    (hz : planeHkValueOperator (E := E) 1 z =ᵐ[volume] fun x => q x • u x) :
    inner ℝ ((planeHkValueOperator (E := E) 1).adjoint g) z =
      ∫ x, q x * inner ℝ (g x) (u x) := by
  rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hz] with x hx
  rw [hx, real_inner_smul_right]

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! The actual H1 carrier for any stored derivative word of the energy-class lift. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeWordH1SliceOperator (K : ℕ) (α : JetIndex2 K) :
    PlaneHk Set.univ (K + 1) E →L[ℝ] PlaneHk Set.univ 1 E :=
  (derivativePlaneHk (K := 1) α.2).comp
    (truncatePlaneHk (by have := α.1.isLt; omega : 1 + α.1.val ≤ K + 1))

theorem planeWordH1Slice_value (K : ℕ) (α : JetIndex2 K)
    (W : PlaneHk Set.univ (K + 1) E) :
    planeHkValueOperator 1 (planeWordH1SliceOperator K α W) =
      univToPlane (W.val ⟨⟨α.1.val, Nat.lt_trans α.1.isLt (Nat.lt_succ_self _)⟩, α.2⟩) := by
  simp only [planeWordH1SliceOperator, ContinuousLinearMap.comp_apply,
    planeHkValueOperator_apply, derivativePlaneHk_apply, truncatePlaneHk_apply]
  have hi : truncateJetIndex (by have := α.1.isLt; omega : 1 + α.1.val ≤ K + 1)
      (prefixJetIndex (K := 1) α.2 (valueIndex2 1)) =
      (⟨⟨α.1.val, Nat.lt_trans α.1.isLt (Nat.lt_succ_self _)⟩, α.2⟩ : JetIndex2 (K + 1)) := by
    simp [truncateJetIndex, prefixJetIndex, valueIndex2, valueIndex, Fin.append_elim0]
  rw [hi]

theorem planeWordH1Slice_gradient (K : ℕ) (α : JetIndex2 K)
    (W : PlaneHk Set.univ (K + 1) E) (k : Fin 2) :
    planeH1GradientOperator (planeWordH1SliceOperator K α W) k =
      univToPlane (W.val ⟨⟨α.1.val + 1, Nat.succ_lt_succ α.1.isLt⟩, Fin.snoc α.2 k⟩) := by
  simp only [planeWordH1SliceOperator, ContinuousLinearMap.comp_apply,
    planeH1GradientOperator_apply, derivativePlaneHk_apply, truncatePlaneHk_apply]
  have hi : truncateJetIndex (by have := α.1.isLt; omega : 1 + α.1.val ≤ K + 1)
      (prefixJetIndex (K := 1) α.2 (⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ : JetIndex2 1)) =
      (⟨⟨α.1.val + 1, Nat.succ_lt_succ α.1.isLt⟩, Fin.snoc α.2 k⟩ : JetIndex2 (K + 1)) := by
    simp [truncateJetIndex, prefixJetIndex, Fin.append_right_eq_snoc]
  rw [hi]

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Weighted

/-! Measurable-time divergence-form coefficients give the true energy dual time class. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Inputwise measurable bounded transport and diffusion preserve the energy dual time class. -/
theorem planeWeakDualRepresentative_memLp_of_operator_bounds
    {T : Type*} [MeasurableSpace T] {μ : Measure T}
    (transport : T → PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (diffusion : T → PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (ht : ∀ z, StronglyMeasurable (fun t => transport t z))
    (hd : ∀ z, StronglyMeasurable (fun t => diffusion t z))
    {Mt Md : ℝ} (hMt : 0 ≤ Mt) (hMd : 0 ≤ Md)
    (hbt : ∀ t, ‖transport t‖ ≤ Mt) (hbd : ∀ t, ‖diffusion t‖ ≤ Md)
    (u : T → PlaneHk Set.univ 1 E) (F : T → PlaneFluxL2 E)
    (hu : MemLp u 2 μ) (hF : MemLp F 2 μ) :
    MemLp (fun t => planeWeakDualRepresentative (transport t) (diffusion t) (u t) (F t))
      2 μ := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp E 2 (volume : Measure (Vec 2))) :=
    Lp.SecondCountableTopology
  let : SecondCountableTopology (PlaneFluxL2 E) := PiLp.secondCountableTopology 2 _
  borelize (PlaneFluxL2 E)
  have hgrad := (planeH1GradientOperator (E := E)).comp_memLp' hu
  exact planeWeakDualRepresentative_memLp transport diffusion u F
    (memLp_operator_action transport ht hgrad hMt hbt)
    (memLp_operator_action diffusion hd hgrad hMd hbd) hF

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane
namespace AVRegularity.Weighted

/-! Bounded flux readout of every actual stored source word. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeJetFluxOperator (K : ℕ) (α : JetIndex2 K) :
    PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ] PlaneFluxL2 E :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2)))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun k => (planeJetReadoutOperator K α).comp
        (mapPlaneHkOperator K (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k)))

@[simp] theorem planeJetFluxOperator_apply (K : ℕ) (α : JetIndex2 K)
    (S : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) (k : Fin 2) :
    planeJetFluxOperator K α S k = AVRegularity.Analysis.Convolution.univToPlane
      ((mapPlaneHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) S).val α) := by
  change planeJetReadoutOperator K α
    (mapPlaneHkOperator K (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) S) = _
  rw [mapPlaneHkOperator_apply]
  rfl

end AVRegularity.Weighted
end
