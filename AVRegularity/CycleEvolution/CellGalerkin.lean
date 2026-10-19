-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.ScalarEnergyDecay
public import AVRegularity.CoupledEnergy.Variational.PullbackForm
public import AVRegularity.CoupledEnergy.Galerkin.PlainSynthesis
import Mathlib.Algebra.Ring.IsFormallyReal

/-! Finite cell Fourier Galerkin construction for finite-dimensional real Hilbert fibres,
including complex fields viewed over ℝ.
Reuses the Galerkin projection and mass inversion, and the upstream bounded measurable ODE
solver. This constructs finite systems, not their infinite-dimensional limit.
The transformed generator measurability/bound and source integrability are explicit
analytic premises. No assumed energy bound or solution-existence premise occurs. -/

@[expose] public noncomputable section

open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVenhance.Infra.ODE

namespace AVRegularity.CycleEvolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

abbrev CellH1 := TorusHk 1 E

/-- A named subspace keeps typeclass search from unfolding the Fourier construction. -/
def cellGalerkinSubspace (N : ℕ) : Submodule ℝ (CellH1 (E := E)) :=
  (galerkinProj (E := E) (K := 1) N).toLinearMap.range

/-- A finite Fourier subspace of the periodic H¹ cell carrier. -/
def CellGalerkinSpace (N : ℕ) : Type _ := ↥(cellGalerkinSubspace (E := E) N)

noncomputable instance cellGalerkinNormedAddCommGroup (N : ℕ) :
    NormedAddCommGroup (CellGalerkinSpace (E := E) N) :=
  inferInstanceAs (NormedAddCommGroup ↥(cellGalerkinSubspace (E := E) N))

noncomputable instance cellGalerkinInnerProductSpace (N : ℕ) :
    InnerProductSpace ℝ (CellGalerkinSpace (E := E) N) :=
  (cellGalerkinSubspace (E := E) N).innerProductSpace

noncomputable instance cellGalerkin_finite (N : ℕ) :
    FiniteDimensional ℝ (CellGalerkinSpace (E := E) N) :=
  galerkinProj_range_finite (E := E) (K := 1) N

/-- Continuous inclusion of a finite Fourier state into the cell H¹ carrier. -/
def cellGalerkinState (N : ℕ) :
    CellGalerkinSpace (E := E) N →L[ℝ] CellH1 (E := E) :=
  (cellGalerkinSubspace (E := E) N).subtypeL

/-- The L² value map from finite periodic H¹ states. -/
def cellGalerkinValue (N : ℕ) : CellGalerkinSpace (E := E) N →L[ℝ] Lp E 2 (volume.restrict AVenhance.unitCube) :=
  (torusHkValueCLM (E := E) (K := 1)).comp
    (cellGalerkinSubspace N).subtypeL

/-- Literal L² mass form on the finite cell Fourier space. -/
def cellGalerkinMass (N : ℕ) :
    CellGalerkinSpace (E := E) N →ₗ[ℝ] CellGalerkinSpace (E := E) N →ₗ[ℝ] ℝ :=
  pullbackInner (cellGalerkinValue N).toLinearMap (cellGalerkinValue N).toLinearMap

/-- The mass form is nondegenerate because H¹ states are determined by their L² values. -/
theorem cellGalerkinMass_injective (N : ℕ) : Function.Injective (cellGalerkinMass (E := E) N) := by
  intro x y hxy
  have heq : inner ℝ (cellGalerkinValue N x) (cellGalerkinValue N (x - y)) =
      inner ℝ (cellGalerkinValue N y) (cellGalerkinValue N (x - y)) :=
    congrArg (fun f => f (x - y)) hxy
  have hz : inner ℝ (cellGalerkinValue N (x - y))
      (cellGalerkinValue N (x - y)) = 0 := by
    rw [map_sub] at heq
    rw [map_sub, inner_sub_left, heq, sub_self]
  have hv : cellGalerkinValue N x = cellGalerkinValue N y := by
    have hn : ‖cellGalerkinValue N (x - y)‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, hz]
    have hzero := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    rw [map_sub] at hzero
    exact sub_eq_zero.mp hzero
  apply Subtype.ext
  exact TorusHk.ext_value hv

/-- Restrict a spatial generator form to trial and test modes in the finite cell space. -/
def cellGalerkinForm (N : ℕ) (B : (CellH1 (E := E)) →ₗ[ℝ] (CellH1 (E := E)) →ₗ[ℝ] ℝ) :
    CellGalerkinSpace (E := E) N →ₗ[ℝ] CellGalerkinSpace (E := E) N →ₗ[ℝ] ℝ where
  toFun x := (B x.val).comp
    (cellGalerkinSubspace N).subtype
  map_add' := by
    intro x y
    ext z
    change B (x.val + y.val) z.val = B x.val z.val + B y.val z.val
    simp only [map_add, LinearMap.add_apply]
  map_smul' := by
    intro c x
    ext z
    change B (c • x.val) z.val = c • B x.val z.val
    simp only [map_smul, LinearMap.smul_apply]

/-- Restrict a scalar/flux forcing functional to the finite cell space. -/
def cellGalerkinSource (N : ℕ) (q : (CellH1 (E := E)) →ₗ[ℝ] ℝ) : CellGalerkinSpace (E := E) N →ₗ[ℝ] ℝ :=
  q.comp (cellGalerkinSubspace N).subtype

def cellGalerkinOperator (N : ℕ) (B : (CellH1 (E := E)) →ₗ[ℝ] (CellH1 (E := E)) →ₗ[ℝ] ℝ) :
    CellGalerkinSpace (E := E) N →L[ℝ] CellGalerkinSpace (E := E) N :=
  weakMassGeneratorCLM (cellGalerkinMass (E := E) N) (cellGalerkinMass_injective N)
    (cellGalerkinForm N B)

def cellGalerkinForcing (N : ℕ) (q : (CellH1 (E := E)) →ₗ[ℝ] ℝ) : CellGalerkinSpace (E := E) N :=
  weakMassSource (cellGalerkinMass (E := E) N) (cellGalerkinMass_injective N)
    (cellGalerkinSource N q)

/-- Initial H¹ data projected to the finite cell space. -/
def cellGalerkinInitial (N : ℕ) (u₀ : (CellH1 (E := E))) : CellGalerkinSpace (E := E) N :=
  ⟨galerkinProj N u₀, ⟨u₀, rfl⟩⟩

/-- Every bounded measurable finite cell system has a unique absolutely continuous path. -/
theorem cellGalerkin_existsUnique {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (B : ℝ → (CellH1 (E := E)) →ₗ[ℝ] (CellH1 (E := E)) →ₗ[ℝ] ℝ) (q : ℝ → (CellH1 (E := E)) →ₗ[ℝ] ℝ)
    (u₀ : (CellH1 (E := E))) (C : ℝ) (hC : 0 ≤ C)
    (hA : AEStronglyMeasurable (fun t => cellGalerkinOperator N (B t)) volume)
    (hAbound : ∀ t, ‖cellGalerkinOperator N (B t)‖ ≤ C)
    (hq : IntervalIntegrable (fun t => cellGalerkinForcing N (q t)) volume a b) :
    ∃! y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := E) N),
      IsLinearIntegralSolution (fun t => cellGalerkinOperator N (B t))
        (fun t => cellGalerkinForcing N (q t)) (cellGalerkinInitial N u₀) a b
        (extendCurve hab y) ∧
      AbsolutelyContinuousOnInterval (extendCurve hab y) a b := by
  exact weakGalerkinODE_existsUnique hab (cellGalerkinMass (E := E) N)
    (cellGalerkinMass_injective N) (fun t => cellGalerkinForm N (B t))
    (fun t => cellGalerkinSource N (q t)) (cellGalerkinInitial N u₀)
    C hC hA hAbound hq

/-- The mass-inverted generator satisfies the finite weak equation exactly. -/
theorem cellGalerkinOperator_pairing (N : ℕ)
    (B : (CellH1 (E := E)) →ₗ[ℝ] (CellH1 (E := E)) →ₗ[ℝ] ℝ) (x z : CellGalerkinSpace (E := E) N) :
    inner ℝ (cellGalerkinValue N (cellGalerkinOperator N B x))
      (cellGalerkinValue N z) = B x.val z.val := by
  exact congrArg (fun f => f z)
    (weakMassGenerator_mass (cellGalerkinMass (E := E) N) (cellGalerkinMass_injective N)
      (cellGalerkinForm N B) x)

/-- The mass-inverted forcing satisfies the finite weak equation exactly. -/
theorem cellGalerkinForcing_pairing (N : ℕ) (q : (CellH1 (E := E)) →ₗ[ℝ] ℝ)
    (z : CellGalerkinSpace (E := E) N) :
    inner ℝ (cellGalerkinValue N (cellGalerkinForcing N q))
      (cellGalerkinValue N z) = q z.val := by
  exact congrArg (fun f => f z)
    (weakMassSource_mass (cellGalerkinMass (E := E) N) (cellGalerkinMass_injective N)
      (cellGalerkinSource N q))

/-- Recover a strong-time variational path in cell L² from its finite coefficient ODE.
No energy identity or inequality is assumed. -/
theorem cellGalerkin_strongVariational {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (B : ℝ → (CellH1 (E := E)) →ₗ[ℝ] (CellH1 (E := E)) →ₗ[ℝ] ℝ) (q : ℝ → (CellH1 (E := E)) →ₗ[ℝ] ℝ)
    (initial : CellGalerkinSpace (E := E) N) (y : ℝ → CellGalerkinSpace (E := E) N)
    (hy : IsLinearIntegralSolution (fun t => cellGalerkinOperator N (B t))
      (fun t => cellGalerkinForcing N (q t)) initial a b y)
    (hint : IntervalIntegrable
      (linearRhs (fun t => cellGalerkinOperator N (B t))
        (fun t => cellGalerkinForcing N (q t)) y) volume a b) :
    StrongVariationalSolution a b (cellGalerkinValue N).toLinearMap
      (fun t => cellGalerkinForm N (B t)) (fun t => cellGalerkinSource N (q t))
      (fun t => cellGalerkinValue N (y t))
      (fun t => cellGalerkinValue N
        (linearRhs (fun s => cellGalerkinOperator N (B s))
          (fun s => cellGalerkinForcing N (q s)) y t)) y := by
  have htime : StrongTimeRegularity a b y
      (linearRhs (fun t => cellGalerkinOperator N (B t))
        (fun t => cellGalerkinForcing N (q t)) y) := by
    refine ⟨hy.absolutelyContinuousOnInterval hab hint, ?_⟩
    apply (ae_restrict_iff' measurableSet_uIcc).2
    have hd := hy.ae_hasDerivAt hab hint
    filter_upwards [hd] with t ht
    simpa only [uIcc_of_le hab] using ht
  refine ⟨htime.map (cellGalerkinValue N), Filter.Eventually.of_forall (fun _ => rfl), ?_⟩
  filter_upwards with t
  intro z
  change inner ℝ (cellGalerkinValue N
    (cellGalerkinOperator N (B t) (y t) + cellGalerkinForcing N (q t)))
    (cellGalerkinValue N z) = _
  rw [map_add, inner_add_left, cellGalerkinOperator_pairing, cellGalerkinForcing_pairing]
  rfl

/-- Construct the finite cell variational path; RHS integrability is discharged by the
bounded measurable ODE data. This theorem does not require an existing solution. -/
theorem cellGalerkin_exists_strongVariational {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (B : ℝ → (CellH1 (E := E)) →ₗ[ℝ] (CellH1 (E := E)) →ₗ[ℝ] ℝ)
    (q : ℝ → (CellH1 (E := E)) →ₗ[ℝ] ℝ) (u₀ : (CellH1 (E := E)))
    (C : ℝ) (hC : 0 ≤ C)
    (hA : AEStronglyMeasurable (fun t => cellGalerkinOperator N (B t)) volume)
    (hAbound : ∀ t, ‖cellGalerkinOperator N (B t)‖ ≤ C)
    (hq : IntervalIntegrable (fun t => cellGalerkinForcing N (q t)) volume a b) :
    ∃ y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := E) N),
      IsLinearIntegralSolution (fun t => cellGalerkinOperator N (B t))
        (fun t => cellGalerkinForcing N (q t)) (cellGalerkinInitial N u₀) a b
        (extendCurve hab y) ∧
      StrongVariationalSolution a b (cellGalerkinValue N).toLinearMap
        (fun t => cellGalerkinForm N (B t)) (fun t => cellGalerkinSource N (q t))
        (fun t => cellGalerkinValue N (extendCurve hab y t))
        (fun t => cellGalerkinValue N
          (linearRhs (fun s => cellGalerkinOperator N (B s))
            (fun s => cellGalerkinForcing N (q s)) (extendCurve hab y) t))
        (extendCurve hab y) := by
  obtain ⟨y, hy, _⟩ := cellGalerkin_existsUnique hab N B q u₀ C hC hA hAbound hq
  let D := weakGalerkinODEData hab (cellGalerkinMass (E := E) N)
    (cellGalerkinMass_injective N) (fun t => cellGalerkinForm N (B t))
    (fun t => cellGalerkinSource N (q t)) (cellGalerkinInitial N u₀)
    C hC hA hAbound hq
  have hint := (D.toLinearODE hab).rhs_intervalIntegrable y
  exact ⟨y, hy.1,
    cellGalerkin_strongVariational hab N B q (cellGalerkinInitial N u₀)
      (extendCurve hab y) hy.1 hint⟩

end AVRegularity.CycleEvolution
