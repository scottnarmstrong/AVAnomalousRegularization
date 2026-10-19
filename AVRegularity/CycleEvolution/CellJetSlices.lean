-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellSliceL2Integrability
public import AVRegularity.CycleEvolution.CellGalerkin
import AVRegularity.CycleEvolution.CellDriftSmoothEnergy
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Quantitative uniformly local bounds for the finite flux sums in cell jet equations. -/

/-- A finite sum of almost measurable cell fields has the sum of their uniformly local norms as a bound. -/
theorem cellUlNorm_finset_sum_le {J E : Type*} [NormedAddCommGroup E]
    (S : Finset J) (f : J → ℝ → Vec 2 → E)
    (hm : ∀ j ∈ S, AEStronglyMeasurable (Function.uncurry (f j))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube))) :
    cellUlNorm Set.univ (∑ j ∈ S, f j) ≤ ∑ j ∈ S, cellUlNorm Set.univ (f j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [cellUlNorm, cellL2Norm]
  | @insert j S hj ih =>
    have hmS : AEStronglyMeasurable (Function.uncurry (∑ k ∈ S, f k))
        ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) := by
      simpa only [Function.uncurry_def, Finset.sum_apply] using
        cellFinite_sum_aestronglyMeasurable S (fun k (z : ℝ × Vec 2) => f k z.1 z.2)
          (fun k hk => hm k (Finset.mem_insert_of_mem hk))
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (cellUlNorm_add Set.univ (f j) (∑ k ∈ S, f k)
      (hm j (Finset.mem_insert_self _ _)) hmS).trans
      (add_le_add le_rfl (ih (fun k hk => hm k (Finset.mem_insert_of_mem hk))))

/-- Finite uniformly local sources are closed under finite sums. -/
theorem cellUlNorm_finset_sum_lt_top {J E : Type*} [NormedAddCommGroup E]
    (S : Finset J) (f : J → ℝ → Vec 2 → E)
    (hm : ∀ j ∈ S, AEStronglyMeasurable (Function.uncurry (f j))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : ∀ j ∈ S, cellUlNorm Set.univ (f j) < ⊤) :
    cellUlNorm Set.univ (∑ j ∈ S, f j) < ⊤ := by
  have hfin : (∑ j ∈ S, cellUlNorm Set.univ (f j)) < ⊤ := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih =>
      rw [Finset.sum_insert hj]
      exact ENNReal.add_lt_top.mpr ⟨hf j (Finset.mem_insert_self _ _),
        ih (fun k hk => hm k (Finset.mem_insert_of_mem hk))
          (fun k hk => hf k (Finset.mem_insert_of_mem hk))⟩
  exact (cellUlNorm_finset_sum_le S f hm).trans_lt hfin

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Finite Fourier initial states constructed directly from arbitrary cell L² data. -/

/-- L² orthogonal initial state defined by the nondegenerate finite mass form. -/
def cellGalerkinL2Initial (N : ℕ)
    (u₀ : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) : CellGalerkinSpace (E := ℂ) N :=
  weakMassSource (cellGalerkinMass N) (cellGalerkinMass_injective N)
    ((innerSL ℝ u₀).comp (cellGalerkinValue N)).toLinearMap

/-- The initial state has exactly the prescribed L² moments in the retained modes. -/
theorem cellGalerkinL2Initial_pairing (N : ℕ)
    (u₀ : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) (z : CellGalerkinSpace (E := ℂ) N) :
    inner ℝ (cellGalerkinValue N (cellGalerkinL2Initial N u₀)) (cellGalerkinValue N z) =
      inner ℝ u₀ (cellGalerkinValue N z) := by
  exact congrArg (fun f => f z)
    (weakMassSource_mass (cellGalerkinMass N) (cellGalerkinMass_injective N)
      ((innerSL ℝ u₀).comp (cellGalerkinValue N)).toLinearMap)

/-- Projection from arbitrary L² initial data is contractive in the cell L² norm. -/
theorem cellGalerkinL2Initial_norm_le (N : ℕ)
    (u₀ : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) :
    ‖cellGalerkinValue N (cellGalerkinL2Initial N u₀)‖ ≤ ‖u₀‖ := by
  have h := cellGalerkinL2Initial_pairing N u₀ (cellGalerkinL2Initial N u₀)
  rw [real_inner_self_eq_norm_sq] at h
  have hb := real_inner_le_norm u₀ (cellGalerkinValue N (cellGalerkinL2Initial N u₀))
  rw [← h] at hb
  nlinarith [norm_nonneg (cellGalerkinValue N (cellGalerkinL2Initial N u₀)), norm_nonneg u₀]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev
open Filter
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Weak scalar measurability implies strong measurability on the periodic H¹ carrier. -/

/-- The finite H¹ Fourier projection with its range carrier. -/
def cellH1InitialCLM (N : ℕ) : TorusHk 1 ℂ →L[ℝ] CellGalerkinSpace (E := ℂ) N :=
  (galerkinProj N).codRestrict (cellGalerkinSubspace N) (fun u => ⟨u, rfl⟩)

/-- Scalar weak measurability suffices for strong measurability of the H¹ curve. -/
theorem cellH1_aestronglyMeasurable_of_pairings
    {μ : Measure ℝ} (f : ℝ → TorusHk 1 ℂ)
    (hf : ∀ z : TorusHk 1 ℂ, AEStronglyMeasurable (fun t => inner ℝ (f t) z) μ) :
    AEStronglyMeasurable f μ := by
  have hproj (N : ℕ) : AEStronglyMeasurable (fun t => galerkinProj N (f t)) μ := by
    let basis := Module.finBasis ℝ (CellGalerkinSpace (E := ℂ) N)
    let L := fun i => (basis.coord i).toContinuousLinearMap.comp (cellH1InitialCLM N)
    have hcoord (i) : AEStronglyMeasurable (fun t => L i (f t)) μ := by
      let z := (InnerProductSpace.toDual ℝ (TorusHk 1 ℂ)).symm (L i)
      apply (hf z).congr
      exact Filter.Eventually.of_forall (fun t =>
        (real_inner_comm _ _).trans InnerProductSpace.toDual_symm_apply)
    have hsum : AEStronglyMeasurable
        (fun t => ∑ i, L i (f t) • basis i) μ := by
      apply AVenhance.Infra.Parabolic.FourierGalerkin.MatrixOperator.aestronglyMeasurable_finset_sum
      intro i _
      exact (hcoord i).smul aestronglyMeasurable_const
    have he : (fun t => ∑ i, L i (f t) • basis i) = fun t => cellH1InitialCLM N (f t) := by
      funext t
      exact basis.sum_repr _
    rw [he] at hsum
    exact (cellGalerkinState N).continuous.comp_aestronglyMeasurable hsum
  apply aestronglyMeasurable_of_tendsto_ae atTop hproj
  exact Filter.Eventually.of_forall (fun t => galerkinProj_tendsto (f t))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVenhance.Infra.ODE
namespace AVRegularity.CycleEvolution

/-! Finite cell Galerkin paths with L² time derivatives. The projected source is
square integrable, and its L¹ integrability is proved on the finite time interval.
The result has spatial H¹ slices and strong H¹-in-time L² traces. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Square-integrable projected forcing is integrable on the finite time interval. -/
theorem cellGalerkin_forcing_intervalIntegrable {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (q : ℝ → CellH1 (E := E) →ₗ[ℝ] ℝ)
    (hq : MemLp (fun t => cellGalerkinForcing N (q t)) 2
      (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun t => cellGalerkinForcing N (q t)) volume a b := by
  have hqI : IntegrableOn (fun t => cellGalerkinForcing N (q t)) (Icc a b) :=
    hq.integrable (by norm_num)
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hab]
  exact hqI.mono_set Ioc_subset_Icc_self

/-- The finite coefficient RHS has a square-integrable cell L² value. -/
theorem cellGalerkin_valueRhs_memLp {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (B : ℝ → CellH1 (E := E) →ₗ[ℝ] CellH1 (E := E) →ₗ[ℝ] ℝ)
    (q : ℝ → CellH1 (E := E) →ₗ[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hA : AEStronglyMeasurable (fun t => cellGalerkinOperator N (B t)) volume)
    (hAbound : ∀ t, ‖cellGalerkinOperator N (B t)‖ ≤ C)
    (hq : MemLp (fun t => cellGalerkinForcing N (q t)) 2
      (volume.restrict (Icc a b)))
    (y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := E) N)) :
    MemLp (fun t => cellGalerkinValue N
      (linearRhs (fun s => cellGalerkinOperator N (B s))
        (fun s => cellGalerkinForcing N (q s)) (extendCurve hab y) t))
      2 (volume.restrict (Icc a b)) := by
  have hcont : ContinuousOn (extendCurve hab y) (Icc a b) :=
    (continuous_extendCurve hab y).continuousOn
  exact linearRhs_map_memLp (fun t => cellGalerkinOperator N (B t))
    hA C hC hAbound (extendCurve hab y) hcont
    (fun t => cellGalerkinForcing N (q t)) hq (cellGalerkinValue N)

/-- Continuous finite states are square integrable as spatial H¹ cell fields. -/
theorem cellGalerkin_state_memLp {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := E) N)) :
    MemLp (fun t => (extendCurve hab y t).val) 2 (volume.restrict (Icc a b)) := by
  have hcont : ContinuousOn (extendCurve hab y) (Icc a b) :=
    (continuous_extendCurve hab y).continuousOn
  exact (cellGalerkinState (E := E) N).comp_memLp'
    (continuousOn_memLp_Icc (extendCurve hab y) hcont)

/-- Solve the finite cell problem and prove square integrability of its strong derivative.
All tests in the variational conclusion are retained Fourier modes. -/
theorem cellGalerkin_exists_timeH1 {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (B : ℝ → CellH1 (E := E) →ₗ[ℝ] CellH1 (E := E) →ₗ[ℝ] ℝ)
    (q : ℝ → CellH1 (E := E) →ₗ[ℝ] ℝ) (u₀ : CellH1 (E := E))
    (C : ℝ) (hC : 0 ≤ C)
    (hA : AEStronglyMeasurable (fun t => cellGalerkinOperator N (B t)) volume)
    (hAbound : ∀ t, ‖cellGalerkinOperator N (B t)‖ ≤ C)
    (hq : MemLp (fun t => cellGalerkinForcing N (q t)) 2
      (volume.restrict (Icc a b))) :
    ∃ y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := E) N),
      StrongVariationalSolution a b (cellGalerkinValue N).toLinearMap
        (fun t => cellGalerkinForm N (B t)) (fun t => cellGalerkinSource N (q t))
        (fun t => cellGalerkinValue N (extendCurve hab y t))
        (fun t => cellGalerkinValue N
          (linearRhs (fun s => cellGalerkinOperator N (B s))
            (fun s => cellGalerkinForcing N (q s)) (extendCurve hab y) t))
        (extendCurve hab y) ∧
      MemLp (fun t => cellGalerkinValue N
        (linearRhs (fun s => cellGalerkinOperator N (B s))
          (fun s => cellGalerkinForcing N (q s)) (extendCurve hab y) t))
        2 (volume.restrict (Icc a b)) ∧
      MemLp (fun t => (extendCurve hab y t).val)
        2 (volume.restrict (Icc a b)) ∧
      cellGalerkinValue N (extendCurve hab y a) =
        cellGalerkinValue N (cellGalerkinInitial N u₀) := by
  have hqi := cellGalerkin_forcing_intervalIntegrable hab N q hq
  obtain ⟨y, hy, hv⟩ := cellGalerkin_exists_strongVariational hab N B q u₀ C hC hA hAbound hqi
  refine ⟨y, hv, cellGalerkin_valueRhs_memLp hab N B q C hC hA hAbound hq y,
    cellGalerkin_state_memLp hab N y, ?_⟩
  have hinit := hy a ⟨le_rfl, hab⟩
  simpa using congrArg (cellGalerkinValue N) hinit

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Arbitrary L² initial states converge through the actual finite cell mass projections. -/

/-- Every cell L² class is a periodic order-zero Sobolev class. -/
def cellL2AsH0 (u : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) : TorusHk 0 ℂ :=
  ⟨WithLp.toLp 2 (fun _ : JetIndex2 0 => u), by simp [torusHkGraph]⟩

/-- Realize the Fourier cutoff of L² data by a retained H¹ state. -/
def cellL2FourierState (N : ℕ) (u : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) :
    CellGalerkinSpace (E := ℂ) N :=
  cellGalerkinInitial N (smoothFourierLift (K := 0) (L := 1) N (cellL2AsH0 u))

/-- The retained H¹ state has the literal L² Fourier cutoff as its value. -/
theorem cellL2FourierState_value (N : ℕ) (u : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) :
    cellGalerkinValue N (cellL2FourierState N u) = cellVectorFourierProjection N u := by
  change (galerkinProj N (smoothFourierLift (K := 0) (L := 1) N (cellL2AsH0 u))).val
    (valueIndex2 1) = _
  rw [galerkinProj_val, cellJetFourierProjection_apply,
    smoothFourierLift_value_eq_projection (by decide : 0 ≤ 1),
    galerkinProj_val, cellJetFourierProjection_apply]
  change cellVectorFourierProjection N (cellVectorFourierProjection N u) = _
  exact cellVectorFourierProjection_idempotent N u

/-- Every retained state's L² value is fixed by the Fourier cutoff. -/
theorem cellGalerkinValue_fourier_fixed (N : ℕ) (z : CellGalerkinSpace (E := ℂ) N) :
    cellVectorFourierProjection N (cellGalerkinValue N z) = cellGalerkinValue N z := by
  have hf := galerkinProj_fixed_of_range N z
  have h := congrArg (fun f : TorusHk 1 ℂ => f.val (valueIndex2 1)) hf
  change cellVectorFourierProjection N (z.val.val (valueIndex2 1)) =
    z.val.val (valueIndex2 1)
  simpa only [galerkinProj_val, cellJetFourierProjection_apply] using h

/-- Mass projection of arbitrary initial data equals its L² Fourier cutoff. -/
theorem cellGalerkinL2Initial_eq_fourier (N : ℕ)
    (u : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) :
    cellGalerkinL2Initial N u = cellL2FourierState N u := by
  apply cellGalerkinMass_injective N
  ext z
  change inner ℝ (cellGalerkinValue N (cellGalerkinL2Initial N u)) (cellGalerkinValue N z) =
    inner ℝ (cellGalerkinValue N (cellL2FourierState N u)) (cellGalerkinValue N z)
  rw [cellGalerkinL2Initial_pairing, cellL2FourierState_value,
    cellVectorFourierProjection_inner, cellGalerkinValue_fourier_fixed]

/-- Finite initial states converge in L² for every L² datum, with no endpoint H¹ premise. -/
theorem cellGalerkinL2Initial_tendsto
    (u : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) :
    Tendsto (fun N => cellGalerkinValue N (cellGalerkinL2Initial N u)) atTop (𝓝 u) := by
  simp only [cellGalerkinL2Initial_eq_fourier, cellL2FourierState_value]
  exact cellVectorFourierProjection_tendsto u

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Continuous finite moment maps for L² traces and H¹-dual time derivatives. -/

/-- Continuous finite initial projection expressed in L² moments. -/
def cellGalerkinL2InitialCLM (N : ℕ) :
    Lp ℂ 2 (volume.restrict AVenhance.unitCube) →L[ℝ] CellGalerkinSpace (E := ℂ) N :=
  let basis := Module.finBasis ℝ (CellGalerkinSpace (E := ℂ) N)
  ∑ i, (innerSL ℝ (cellGalerkinValue N (basis i))).smulRight
    (weakMassSource (cellGalerkinMass N) (cellGalerkinMass_injective N) (basis.coord i))

/-- The continuous moment map is the literal finite mass projection. -/
theorem cellGalerkinL2InitialCLM_apply (N : ℕ)
    (u : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) :
    cellGalerkinL2InitialCLM N u = cellGalerkinL2Initial N u := by
  rw [cellGalerkinL2Initial, weakMassSource_eq_sum
    (Module.finBasis ℝ (CellGalerkinSpace (E := ℂ) N))]
  simp only [cellGalerkinL2InitialCLM, sum_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact real_inner_comm _ _

/-- Finite mass inversion of an H¹ Hilbert representative of a dual derivative. -/
def cellGalerkinDualMomentCLM (N : ℕ) : TorusHk 1 ℂ →L[ℝ] CellGalerkinSpace (E := ℂ) N :=
  let basis := Module.finBasis ℝ (CellGalerkinSpace (E := ℂ) N)
  ∑ i, (innerSL ℝ (basis i).val).smulRight
    (weakMassSource (cellGalerkinMass N) (cellGalerkinMass_injective N) (basis.coord i))

/-- The dual moment map has the intended mass identity against every retained test. -/
theorem cellGalerkinDualMomentCLM_pairing (N : ℕ) (g : TorusHk 1 ℂ)
    (z : CellGalerkinSpace (E := ℂ) N) :
    inner ℝ (cellGalerkinValue N (cellGalerkinDualMomentCLM N g)) (cellGalerkinValue N z) =
      inner ℝ g z.val := by
  have he : cellGalerkinDualMomentCLM N g =
      weakMassSource (cellGalerkinMass N) (cellGalerkinMass_injective N)
        (cellGalerkinSource N (innerSL ℝ g).toLinearMap) := by
    rw [weakMassSource_eq_sum (Module.finBasis ℝ (CellGalerkinSpace (E := ℂ) N))]
    simp only [cellGalerkinDualMomentCLM, sum_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact real_inner_comm _ _
  rw [he]
  exact congrArg (fun f => f z)
    (weakMassSource_mass (cellGalerkinMass N) (cellGalerkinMass_injective N)
      (cellGalerkinSource N (innerSL ℝ g).toLinearMap))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! A weak-time cell Hilbert interface, independent of PDE existence and energy conclusions. -/

/-- An H¹-in-space L² curve whose H⁻¹ time derivative is represented through the H¹ Hilbert
inner product. Fixed-test time increments are the only differential premise. -/
structure CellWeakHilbertCurve (a b : ℝ)
    (u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube))
    (slice g : ℝ → TorusHk 1 ℂ) : Prop where
  trace : ContinuousOn u (Icc a b)
  state : MemLp slice 2 (volume.restrict (Icc a b))
  dual : MemLp g 2 (volume.restrict (Icc a b))
  agrees : ∀ᵐ t ∂volume.restrict (Icc a b), u t = torusHkValueCLM (slice t)
  increment : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → ∀ z : TorusHk 1 ℂ,
    inner ℝ (u t) (torusHkValueCLM z) - inner ℝ (u s) (torusHkValueCLM z) =
      ∫ r in s..t, inner ℝ (g r) z

/-- At H¹ slices, the finite L² mass projection is the usual H¹ Fourier projection. -/
theorem cellGalerkinL2Initial_of_H1 (N : ℕ) (z : TorusHk 1 ℂ) :
    cellGalerkinL2Initial N (torusHkValueCLM z) = cellGalerkinInitial N z := by
  apply Subtype.ext
  apply TorusHk.ext_value
  have hleft : cellGalerkinValue N (cellGalerkinL2Initial N (torusHkValueCLM z)) =
      cellVectorFourierProjection N (torusHkValueCLM z) := by
    rw [cellGalerkinL2Initial_eq_fourier, cellL2FourierState_value]
  have hright : cellGalerkinValue N (cellGalerkinInitial N z) =
      cellVectorFourierProjection N (torusHkValueCLM z) := by
    change (galerkinProj N z).val (valueIndex2 1) = _
    rw [galerkinProj_val, cellJetFourierProjection_apply]
    rfl
  exact hleft.trans hright.symm

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Algebra of the public energy norm on jointly measurable raw cell jets. -/

/-- The gradient representative of a public cell solution is jointly almost measurable. -/
theorem cellSolution_gradient_aestronglyMeasurable {I : Set ℝ} {C : CellCoefficients}
    {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D : ℝ → RawJet2 1 ℂ} (h : IsCellSolution I C src F D) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => cellGradient (D p.1) p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) :=
  cellFiniteArray_aestronglyMeasurable
    (fun (p : ℝ × Vec 2) (j : Fin 2) => cellGradComp (D p.1) j p.2)
    (fun j => h.2.2.2.1 ⟨⟨1, by decide⟩, fun _ => j⟩)

/-- The energy norm obeys the triangle inequality for jointly almost measurable gradients. -/
theorem cellEnergyNorm_add (I : Set ℝ) (D E : ℝ → RawJet2 1 ℂ)
    (hD : AEStronglyMeasurable (fun p : ℝ × Vec 2 => cellGradient (D p.1) p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hE : AEStronglyMeasurable (fun p : ℝ × Vec 2 => cellGradient (E p.1) p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    cellEnergyNorm I (D + E) ≤ cellEnergyNorm I D + cellEnergyNorm I E := by
  have hv : (⨆ t ∈ I, cellL2Norm (cellValue (D + E) t)) ≤
      (⨆ t ∈ I, cellL2Norm (cellValue D t)) + (⨆ t ∈ I, cellL2Norm (cellValue E t)) := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    exact (eLpNorm_add_le (by norm_num) (f := cellValue D t) (g := cellValue E t)).trans
      (add_le_add (le_iSup_of_le t (le_iSup_of_le ht le_rfl))
        (le_iSup_of_le t (le_iSup_of_le ht le_rfl)))
  have hg : cellUlNorm I (fun t => cellGradient ((D + E) t)) ≤
      cellUlNorm I (fun t => cellGradient (D t)) + cellUlNorm I (fun t => cellGradient (E t)) := by
    exact cellUlNorm_add I (fun t => cellGradient (D t)) (fun t => cellGradient (E t)) hD hE
  unfold cellEnergyNorm
  calc
    _ ≤ _ := add_le_add hv hg
    _ = _ := by ac_rfl

/-- Real scaling has the expected bound in the public energy norm. -/
theorem cellEnergyNorm_smul (I : Set ℝ) (r : ℝ) (D : ℝ → RawJet2 1 ℂ)
    (hD : AEStronglyMeasurable (fun p : ℝ × Vec 2 => cellGradient (D p.1) p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    cellEnergyNorm I (r • D) ≤ ‖r‖ₑ * cellEnergyNorm I D := by
  have hv : (⨆ t ∈ I, cellL2Norm (cellValue (r • D) t)) ≤
      ‖r‖ₑ * (⨆ t ∈ I, cellL2Norm (cellValue D t)) := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    change eLpNorm (r • cellValue D t) 2 _ ≤ _
    rw [eLpNorm_const_smul]
    gcongr
    exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)
  have hg : cellUlNorm I (fun t => cellGradient ((r • D) t)) ≤
      ‖r‖ₑ * cellUlNorm I (fun t => cellGradient (D t)) :=
    cellUlNorm_smul I r (fun t => cellGradient (D t)) hD
  unfold cellEnergyNorm
  rw [mul_add]
  exact add_le_add hv hg

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Changes of almost-everywhere H¹ representatives preserve the weak time equation. -/

/-- The H¹ state and dual representative may be replaced by equal almost-everywhere curves. -/
theorem CellWeakHilbertCurve.congr_state_dual {a b : ℝ}
    {u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    {slice g other dual : ℝ → TorusHk 1 ℂ} (h : CellWeakHilbertCurve a b u slice g)
    (hs : slice =ᵐ[volume.restrict (Icc a b)] other)
    (hg : g =ᵐ[volume.restrict (Icc a b)] dual) :
    CellWeakHilbertCurve a b u other dual := by
  refine ⟨h.trace, h.state.ae_eq hs, h.dual.ae_eq hg, ?_, ?_⟩
  · filter_upwards [h.agrees, hs] with t ht hst
    rw [← hst]
    exact ht
  · intro s hs' t ht' hst z
    rw [h.increment s hs' t ht' hst z]
    apply intervalIntegral.integral_congr_ae_restrict
    have hr := hg.filter_mono (ae_mono (Measure.restrict_mono
      (show uIoc s t ⊆ Icc a b by
        rw [uIoc_of_le hst]
        exact Ioc_subset_Icc_self.trans (Icc_subset_Icc hs'.1 ht'.2)) le_rfl))
    filter_upwards [hr] with r hr'
    rw [hr']

/-! Constant compatible Hilbert maps preserve the genuine weak time equation. -/

theorem CellWeakHilbertCurve.map {a b : ℝ}
    {u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → TorusHk 1 ℂ} (h : CellWeakHilbertCurve a b u slice g)
    (T : Lp ℂ 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      Lp ℂ 2 (volume.restrict AVenhance.unitCube))
    (S : TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ)
    (hcomp : ∀ z, T (torusHkValueCLM z) = torusHkValueCLM (S z))
    (hadj : ∀ z, T.adjoint (torusHkValueCLM z) = torusHkValueCLM (S.adjoint z)) :
    CellWeakHilbertCurve a b (fun t => T (u t)) (fun t => S (slice t)) (fun t => S (g t)) := by
  refine ⟨T.continuous.comp_continuousOn h.trace, ?_, ?_, ?_, ?_⟩
  · exact S.comp_memLp' h.state
  · exact S.comp_memLp' h.dual
  · filter_upwards [h.agrees] with t ht
    rw [ht, hcomp]
  · intro s hs t ht hst z
    have he := h.increment s hs t ht hst (S.adjoint z)
    rw [← ContinuousLinearMap.adjoint_inner_right T, ← ContinuousLinearMap.adjoint_inner_right T,
      hadj]
    calc
      _ = ∫ r in s..t, inner ℝ (g r) (S.adjoint z) := he
      _ = ∫ r in s..t, inner ℝ (S (g r)) z := by
        apply intervalIntegral.integral_congr
        intro r _
        exact ContinuousLinearMap.adjoint_inner_right S (g r) z

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Uniform energy bounds near a fixed raw cell state from norm-small differences. -/

/-- The norm of a state is bounded by its difference from a fixed state and the fixed-state norm. -/
theorem cellEnergyNorm_le_sub_add (I : Set ℝ) (D E : ℝ → RawJet2 1 ℂ)
    (hD : ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D p.1 a p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hE : ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => E p.1 a p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    cellEnergyNorm I D ≤ cellEnergyNorm I (D - E) + cellEnergyNorm I E := by
  have hdiff := cellFiniteArray_aestronglyMeasurable
    (fun (p : ℝ × Vec 2) (j : Fin 2) => cellGradComp ((D - E) p.1) j p.2)
    (fun j => (hD ⟨⟨1, by decide⟩, fun _ => j⟩).sub (hE ⟨⟨1, by decide⟩, fun _ => j⟩))
  have hgradE := cellFiniteArray_aestronglyMeasurable
    (fun (p : ℝ × Vec 2) (j : Fin 2) => cellGradComp (E p.1) j p.2)
    (fun j => hE ⟨⟨1, by decide⟩, fun _ => j⟩)
  have h := cellEnergyNorm_add I (D - E) E hdiff hgradE
  rwa [sub_add_cancel] at h

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Triangle and representative-transfer rules for the literal energy seminorm. -/

/-- Coordinatewise joint almost measurability gives joint almost measurability of the raw gradient. -/
theorem cellRawGradient_aestronglyMeasurable (I : Set ℝ) (D : ℝ → RawJet2 1 ℂ)
    (hD : ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D p.1 a p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => cellGradient (D p.1) p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) :=
  cellFiniteArray_aestronglyMeasurable
    (fun (p : ℝ × Vec 2) (j : Fin 2) => cellGradComp (D p.1) j p.2)
    (fun j => hD ⟨⟨1, by decide⟩, fun _ => j⟩)

/-- The energy distance satisfies the triangle inequality on jointly almost measurable raw jets. -/
theorem cellEnergyNorm_sub_triangle (I : Set ℝ) (D E T : ℝ → RawJet2 1 ℂ)
    (hD : ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D p.1 a p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hE : ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => E p.1 a p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hT : ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => T p.1 a p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    cellEnergyNorm I (D - T) ≤ cellEnergyNorm I (D - E) + cellEnergyNorm I (E - T) := by
  have he : D - T = (D - E) + (E - T) := by abel
  rw [he]
  exact cellEnergyNorm_add I _ _
    (cellRawGradient_aestronglyMeasurable I (D - E) (fun a => (hD a).sub (hE a)))
    (cellRawGradient_aestronglyMeasurable I (E - T) (fun a => (hE a).sub (hT a)))

/-- Energy limits transfer across a zero energy distance between two representatives. -/
theorem cellEnergyNorm_transfer_tendsto {P : Type*} (l : Filter P)
    (D : P → ℝ → RawJet2 1 ℂ) (E T : ℝ → RawJet2 1 ℂ)
    (hD : ∀ p a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => D p z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hE : ∀ a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => E z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hT : ∀ a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => T z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (he : cellEnergyNorm univ (E - T) = 0)
    (hd : Tendsto (fun p => cellEnergyNorm univ (D p - E)) l (𝓝 0)) :
    Tendsto (fun p => cellEnergyNorm univ (D p - T)) l (𝓝 0) := by
  have hb (p : P) : cellEnergyNorm univ (D p - T) ≤ cellEnergyNorm univ (D p - E) := by
    have hh := cellEnergyNorm_sub_triangle univ (D p) E T (hD p) hE hT
    simpa only [he, add_zero] using hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hd
    (fun _ => bot_le) hb

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Time reversal preserves the actual weak Hilbert trajectory with the opposite time derivative. -/

theorem CellWeakHilbertCurve.timeReverse {a b : ℝ}
    {u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → TorusHk 1 ℂ} (h : CellWeakHilbertCurve a b u slice g) :
    CellWeakHilbertCurve (-b) (-a) (fun t => u (-t)) (fun t => slice (-t)) (fun t => -g (-t)) := by
  have hmem {t : ℝ} (ht : t ∈ Icc (-b) (-a)) : -t ∈ Icc a b := by
    constructor <;> rcases ht with ⟨h₁, h₂⟩ <;> linarith
  refine ⟨h.trace.comp continuous_neg.continuousOn (fun t ht => hmem ht),
    cellTimeReverse_memLp h.state, (cellTimeReverse_memLp h.dual).neg, ?_, ?_⟩
  · exact (cellTimeReverse_measurePreserving_Icc a b).quasiMeasurePreserving.ae h.agrees
  · intro s hs t ht hst z
    have he := h.increment (-t) (hmem ht) (-s) (hmem hs) (by linarith) z
    have hrev : (∫ r in s..t, inner ℝ (g (-r)) z) =
        ∫ r in -t..-s, inner ℝ (g r) z :=
      intervalIntegral.integral_comp_neg (f := fun r => inner ℝ (g r) z)
    simp only [inner_neg_left]
    rw [intervalIntegral.integral_neg, hrev]
    linarith

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Restricting a proved graph to a smaller disc and increasing its quantitative bound. -/

theorem isFibreGraph_radius_restriction {η R C R' C' : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {r : ℕ × ℕ → ℝ → RawJet2 1 ℂ} {lam : ℕ × ℕ → ℝ → ℂ}
    (h : IsFibreGraph η G v R C r lam) (hR' : 0 < R') (hRR : R' ≤ R)
    (hC : 0 ≤ C) (hCC : C ≤ C') : IsFibreGraph η G v R' C' r lam := by
  have hR : 0 < R := hR'.trans_le hRR
  have hdiv : 2 / R ≤ 2 / R' := div_le_div_of_nonneg_left (by norm_num) hR' hRR
  have hpow (n : ℕ) : (2 / R) ^ n ≤ (2 / R') ^ n :=
    pow_le_pow_left₀ (by positivity) hdiv n
  have hbound (n : ℕ) (ξ : Fin 2 → ℂ) :
      C * (2 / R) ^ n * fibreNorm ξ ^ n ≤ C' * (2 / R') ^ n * fibreNorm ξ ^ n := by
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (fibreNorm_nonneg ξ) n)
    exact mul_le_mul hCC (hpow n) (by positivity) (hC.trans hCC)
  refine ⟨h.1, ?_, ?_, ?_⟩
  · intro ξ hξ
    obtain ⟨ha, hb, hc, hd, he⟩ := h.2.1 ξ (hξ.trans_le hRR)
    refine ⟨ha, hb, hc, hd, he.trans ?_⟩
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCC (fibreNorm_nonneg ξ))
  · intro n ξ
    exact (h.2.2.1 n ξ).trans (ENNReal.ofReal_le_ofReal (hbound n ξ))
  · intro n ξ t
    exact (h.2.2.2 n ξ t).trans (hbound n ξ)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace AVRegularity.CycleEvolution

/-! Uniform scalar and phase bounds on the actual Banach frequency ball. -/

theorem fibreUniformMajorant_series_norm_le (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ≥0)
    (M : ℝ) (hM : 0 ≤ M)
    (hb : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ τ, ‖a p τ‖ₑ) ≤ ENNReal.ofReal M)
    (ξ : Fin 2 → ℂ) (hξ : ‖ξ‖ ≤ R) (t : ℝ) : ‖fibreSeriesC a ξ t‖ ≤ M := by
  have hm p : ENNReal.ofReal ‖fibreMonomial ξ p‖ ≤ fibreCoefficientWeight (R : ENNReal) p := by
    rw [fibreCoefficientWeight, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow R.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal ((fibreMonomial_norm_le_pi ξ p).trans
      (pow_le_pow_left₀ (norm_nonneg _) hξ _))
  have ht p : ‖fibreMonomial ξ p * a p t‖ₑ ≤
      fibreCoefficientWeight (R : ENNReal) p * ⨆ τ, ‖a p τ‖ₑ := by
    rw [enorm_mul, ← ofReal_norm (fibreMonomial ξ p)]
    exact mul_le_mul' (hm p) (le_iSup (fun τ => ‖a p τ‖ₑ) t)
  have he := (enorm_tsum_le_tsum_enorm (f := fun p => fibreMonomial ξ p * a p t)).trans
    ((ENNReal.tsum_le_tsum ht).trans hb)
  rw [← ofReal_norm] at he
  exact (ENNReal.ofReal_le_ofReal_iff hM).mp he

theorem fibreUniformMajorant_phase_norm_le (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ≥0)
    (M : ℝ) (hM : 0 ≤ M)
    (hb : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ τ, ‖a p τ‖ₑ) ≤ ENNReal.ofReal M)
    (ξ : Fin 2 → ℂ) (hξ : ‖ξ‖ ≤ R) (s t : ℝ) (hst : s ≤ t) :
    ‖∫ τ in s..t, fibreSeriesC a ξ τ‖ ≤ M * (t - s) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun τ (_ : τ ∈ Set.uIoc s t) => fibreUniformMajorant_series_norm_le a R M hM hb ξ hξ τ)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using h

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Dual Fourier moments tested against arbitrary H¹ functions. -/

/-- A finite dual moment pairs against the Fourier projection of any H¹ test. -/
theorem cellGalerkinDualMoment_pairing_all (N : ℕ) (g z : TorusHk 1 ℂ) :
    inner ℝ (cellGalerkinValue N (cellGalerkinDualMomentCLM N g)) (torusHkValueCLM z) =
      inner ℝ g (galerkinProj N z) := by
  let w := cellGalerkinDualMomentCLM N g
  have hw := cellGalerkinValue_fourier_fixed N w
  calc
    _ = inner ℝ (cellVectorFourierProjection N (cellGalerkinValue N w))
        (torusHkValueCLM z) := by rw [hw]
    _ = inner ℝ (cellGalerkinValue N w)
        (cellVectorFourierProjection N (torusHkValueCLM z)) :=
      cellVectorFourierProjection_inner N _ _
    _ = inner ℝ (cellGalerkinValue N w) (cellGalerkinValue N (cellGalerkinInitial N z)) := by
      rw [← cellGalerkinL2Initial_of_H1, cellGalerkinL2Initial_eq_fourier,
        cellL2FourierState_value]
    _ = inner ℝ g (galerkinProj N z) := cellGalerkinDualMomentCLM_pairing N g _

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Energy differences of actual bounded inverses stay finite across different coefficients. -/

theorem cellInverse_difference_energy_lt_top
    {C C' : CellCoefficients} {src src' : ℝ → Vec 2 → ℂ}
    {F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D E : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (hE : IsCellInverseValue C' src' F' E) :
    cellEnergyNorm Set.univ (D - E) < ⊤ := by
  have hd := cellSolution_gradient_aestronglyMeasurable hD.1
  have he := cellSolution_gradient_aestronglyMeasurable hE.1
  have hn : cellEnergyNorm Set.univ (-E) ≤ cellEnergyNorm Set.univ E := by
    simpa only [neg_one_smul, enorm_neg, enorm_one, one_mul] using
      cellEnergyNorm_smul Set.univ (-1) E he
  have hb := cellEnergyNorm_add Set.univ D (-E) hd he.neg
  rw [← sub_eq_add_neg] at hb
  exact hb.trans_lt ((add_le_add le_rfl hn).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hD.2.2, hE.2.2⟩))

end AVRegularity.CycleEvolution
end
end

section
/-! Strong measurability of spatial L² slices via finite Fourier projection. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization Filter Topology
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.Analysis.Convolution

local instance sliceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance sliceMeasureIsAddHaar : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance sliceProbabilityCircle : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance sliceProbabilityTorus : IsProbabilityMeasure
    (volume : Measure (UnitAddTorus (Fin 2))) := inferInstance

namespace AVRegularity.CycleEvolution

/-- A Fourier mode with the explicit normalized torus measure. -/
def cellTorusFourierMode (N : ℕ) (i : VectorFourierIndex N ℂ) : Lp ℂ 2 torusMeasure :=
  vectorFourierMode (E := ℂ) N i.1 i.2

/-- A vector-valued real Fourier mode transported to the physical cell. -/
def cellFourierMode (N : ℕ) (i : VectorFourierIndex N ℂ) :
    Lp ℂ 2 (volume.restrict AVenhance.unitCube) :=
  torusToCell (cellTorusFourierMode N i)

/-- Physical cell Fourier projection is a finite sum of physical cell moments. -/
theorem cellFourierProjection_eq_sum (N : ℕ)
    (u : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) :
    cellVectorFourierProjection N u =
      ∑ i : VectorFourierIndex N ℂ, inner ℝ u (cellFourierMode N i) • cellFourierMode N i := by
  have he : vectorFourierProjection (E := ℂ) N (cellToTorus u) =
      ∑ i : VectorFourierIndex N ℂ,
        inner ℝ (cellToTorus u) (cellTorusFourierMode N i) •
          cellTorusFourierMode N i :=
    finiteOrthonormalProjection_apply _ _
  calc
    cellVectorFourierProjection N u = torusToCell
        (∑ i : VectorFourierIndex N ℂ,
          inner ℝ (cellToTorus u) (cellTorusFourierMode N i) •
            cellTorusFourierMode N i) := congrArg torusToCell he
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      have hi := (torusToCell (E := ℂ)).inner_map_map (cellToTorus u)
        (cellTorusFourierMode N i)
      rw [torusToCell_cellToTorus] at hi
      rw [← hi]
      rfl

/-- Product L² fields have strongly measurable spatial L² classes in time. -/
theorem cellSourceSlice_aestronglyMeasurable (I : Set ℝ) (f : ℝ → Vec 2 → ℂ)
    (hf : MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    AEStronglyMeasurable (cellSourceSlice f) (volume.restrict I) := by
  have hpair (z : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) :
      AEStronglyMeasurable (fun t => inner ℝ (cellSourceSlice f t) z) (volume.restrict I) := by
    have hi : AEStronglyMeasurable
        (fun p : ℝ × Vec 2 => inner ℝ (f p.1 p.2) (z p.2))
        ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) :=
      hf.aestronglyMeasurable.inner (Lp.aestronglyMeasurable z).comp_snd
    have hm := hi.integral_prod_right'
    apply hm.congr
    filter_upwards [cellSource_memLp_slices I f hf] with t ht
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [cellSourceSlice_ae f t ht] with x hx
    rw [hx]
  have hproj (N : ℕ) : AEStronglyMeasurable
      (fun t => cellVectorFourierProjection N (cellSourceSlice f t)) (volume.restrict I) := by
    simp only [cellFourierProjection_eq_sum]
    apply AVenhance.Infra.Parabolic.FourierGalerkin.MatrixOperator.aestronglyMeasurable_finset_sum
    intro i _
    exact (hpair (cellFourierMode N i)).smul aestronglyMeasurable_const
  apply aestronglyMeasurable_of_tendsto_ae atTop hproj
  exact Filter.Eventually.of_forall (fun t => cellVectorFourierProjection_tendsto (cellSourceSlice f t))

end AVRegularity.CycleEvolution

namespace AVRegularity.CycleEvolution

/-- Product L² membership yields Bochner L² membership of the spatial source classes. -/
theorem cellSourceSlice_memLp (I : Set ℝ) (f : ℝ → Vec 2 → ℂ)
    (hf : MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    MemLp (cellSourceSlice f) 2 (volume.restrict I) := by
  apply (memLp_two_iff_integrable_sq_norm (cellSourceSlice_aestronglyMeasurable I f hf)).mpr
  have hsq : Integrable (fun p : ℝ × Vec 2 => ‖f p.1 p.2‖ ^ (2 : ℕ))
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
    simpa [Function.uncurry_def, Real.rpow_two] using
      hf.integrable_norm_rpow (by norm_num) (by norm_num)
  apply hsq.integral_prod_left.congr
  filter_upwards [cellSource_memLp_slices I f hf] with t ht
  simp only [cellSourceSlice, dite_eq_left ht]
  exact (AVRegularity.Sobolev.normSq_toLp_eq_integral ht).symm

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Measurable periodic H¹ slice classes for raw product-space weak jets. -/

/-- Inject one spatial L² class into the finite ordered-jet Hilbert product. -/
def cellJetEntryCLM (a : JetIndex2 1) :
    Lp ℂ 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      JetL2 (volume.restrict AVenhance.unitCube) 1 ℂ :=
  let L : Lp ℂ 2 (volume.restrict AVenhance.unitCube) →ₗ[ℝ]
      JetL2 (volume.restrict AVenhance.unitCube) 1 ℂ :=
    { toFun := PiLp.single (β := fun _ : JetIndex2 1 => Lp ℂ 2 (volume.restrict AVenhance.unitCube)) 2 a
      map_add' := by intro x y; exact PiLp.single_add (β := fun _ : JetIndex2 1 => Lp ℂ 2 (volume.restrict AVenhance.unitCube)) 2 a
      map_smul' := by
        intro r x
        apply PiLp.ext
        intro b
        by_cases h : b = a
        · subst b; simp
        · simp [h] }
  L.mkContinuous 1 (by
    intro x
    change ‖PiLp.single (β := fun _ : JetIndex2 1 =>
      Lp ℂ 2 (volume.restrict AVenhance.unitCube)) 2 a x‖ ≤ 1 * ‖x‖
    rw [PiLp.norm_single, one_mul])

/-- Total spatial class of every ordered raw jet component. -/
def cellRawJetSlices (D : ℝ → RawJet2 1 ℂ) (t : ℝ) :
    JetL2 (volume.restrict AVenhance.unitCube) 1 ℂ :=
  ∑ a : JetIndex2 1, cellJetEntryCLM a (cellSourceSlice (fun s x => D s a x) t)

/-- The raw jet class is Bochner L² when every raw component is product L². -/
theorem cellRawJetSlices_memLp (I : Set ℝ) (D : ℝ → RawJet2 1 ℂ)
    (hD : ∀ a, MemLp (fun p : ℝ × Vec 2 => D p.1 a p.2) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    MemLp (cellRawJetSlices D) 2 (volume.restrict I) := by
  apply memLp_finsetSum Finset.univ
  intro a _
  exact (cellJetEntryCLM a).comp_memLp' (cellSourceSlice_memLp I (fun t x => D t a x) (hD a))

/-- At every genuine weak-jet slice this is its literal spatial Sobolev class. -/
theorem cellRawJetSlices_eq_toL2 (D : ℝ → RawJet2 1 ℂ) (t : ℝ)
    (ht : HasPeriodicOrderedWeakJet (D t)) :
    cellRawJetSlices D t = torusJetToL2 (D t) ht.2.1 := by
  apply PiLp.ext
  intro a
  simp [cellRawJetSlices, cellJetEntryCLM, cellSourceSlice, dite_eq_left (ht.2.1 a), torusJetToL2]

/-- Project the total raw class onto the closed periodic H¹ graph. Exceptional slices are harmless. -/
def cellH1Slice (D : ℝ → RawJet2 1 ℂ) (t : ℝ) : TorusHk 1 ℂ :=
  (torusHkGraph (E := ℂ) 1).toSubmodule.orthogonalProjectionOnto (cellRawJetSlices D t)

/-- The periodic H¹ slice classes are Bochner L². -/
theorem cellH1Slice_memLp (I : Set ℝ) (D : ℝ → RawJet2 1 ℂ)
    (hD : ∀ a, MemLp (fun p : ℝ × Vec 2 => D p.1 a p.2) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    MemLp (cellH1Slice D) 2 (volume.restrict I) :=
  (torusHkGraph (E := ℂ) 1).toSubmodule.orthogonalProjectionOnto.comp_memLp'
    (cellRawJetSlices_memLp I D hD)

/-- Projection does not change an actual periodic weak jet. -/
theorem cellH1Slice_eq_toHk (D : ℝ → RawJet2 1 ℂ) (t : ℝ)
    (ht : HasPeriodicOrderedWeakJet (D t)) :
    cellH1Slice D t = (TorusHkFunction.mk (D t) ht).toHk := by
  unfold cellH1Slice
  rw [cellRawJetSlices_eq_toL2 D t ht]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    ((TorusHkFunction.mk (D t) ht).toHk)

end AVRegularity.CycleEvolution
end
end
