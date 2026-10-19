-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.PatchBridges
import AVRegularity.CoupledEnergy.Galerkin.PlainWeakSolutionExistence
import AVRegularity.CoupledEnergy.Galerkin.TorusProjectedMassLimit
import AVRegularity.CoupledEnergy.CouplingBounds
public import AVRegularity.CoupledEnergy.Galerkin.PlainClosedTraceIdentity
import AVenhance.Infra.Classical.Drift

section
/-! **Level B of the route to `cycle_joint`: the core from the patch statements**. `rawJoint_of_patches` proves `RawJointStatement` from the one-patch statement, the plane-solution statement (plane
solutions and periodization), periodized sums, centre counting and scalar `L²`
contraction.

The torus operator is the sum over the patches of the periodized patch models,
`Tm g i = Σ_j per(M_j g i)`. The model bound is the periodized-sum bound with the weight of the model bound of the one-patch statement; the
physical error is the periodized-sum bound applied to the patch errors `U_j(t_p) - M_j g` (the torus solution is the
sum of the periodized plane solutions by the plane-solution statement), with the weighted patch errors of the one-patch statement and the patch budget
of the prepared norms; the `L²` near-contraction of an edge-free family is the slot-0 error plus
scalar contraction. Constants: `C_core = √Cc · C`, `CP_core = √(Cc · Cbud) · CP` with `Cbud` the uniform patch
budget at mesh constant `max 1 (9 COld)`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

local instance scalarResidualTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
local instance scalarResidualTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
local instance scalarResidualTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance
local instance scalarResidualPlaneNormed {U : Set (Vec 2)} {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (PlaneHk U K E) := inferInstance
local instance scalarResidualPlaneInner {U : Set (Vec 2)} {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (PlaneHk U K E) := inferInstance
local instance scalarResidualPlaneSpace {U : Set (Vec 2)} {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (PlaneHk U K E) := inferInstance
local instance scalarResidualPiAdd {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (K : ι → ℕ) :
    AddCommMonoid (∀ i, TorusHk (K i) (h i)) := inferInstance
local instance scalarResidualPiModule {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (K : ι → ℕ) :
    Module ℝ (∀ i, TorusHk (K i) (h i)) := inferInstance
local instance scalarResidualPlanePiAdd {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (U : Set (Vec 2)) (K : ι → ℕ) :
    AddCommMonoid (∀ i, PlaneHk U (K i) (h i)) := inferInstance
local instance scalarResidualPlanePiModule {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (U : Set (Vec 2)) (K : ι → ℕ) :
    Module ℝ (∀ i, PlaneHk U (K i) (h i)) := inferInstance

section Identity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {J : Type*} [Fintype J]

/-- The torus error of the periodized patch models is the periodization of the patch errors. -/
theorem periodized_error_identity (y : J → Vec 2) {K L : ℕ} (hKL : K ≤ L)
    (U : J → PlaneHk Set.univ K E) (Mm : J → PlaneHk Set.univ L E)
    (hU : ∀ j, CycleJointProofs.HasRadialPlaneMoments (U j) (y j))
    (hM : ∀ j, CycleJointProofs.HasRadialPlaneMoments (Mm j) (y j)) :
    (∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (U j) (y j) (hU j)) -
        truncateTorusHk hKL (∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (Mm j) (y j) (hM j)) =
      ∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (U j - truncatePlaneHk hKL (Mm j)) (y j)
        ((hU j).sub ((hM j).truncate hKL)) := by
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [CycleJointProofs.periodizeRadialPlaneCarrier_sub,
    ← CycleJointProofs.periodizeRadialPlaneCarrier_truncate]

end Identity

section Clauses

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **Model clause.** The sum of the periodized patch models has the mass-weighted model bound
`√Cc · C` when each patch model has the weighted bound `C` against inputs that partition `‖g‖²`. -/
theorem patch_model_clause (hB3 : PeriodizedRadialSumStatement.{v}) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (K : ι → ℕ) (Mout : ℕ) {N : ℕ} (y' : (Fin 2 → Fin N) → Vec 2) (R Cc C ρm : ℝ) (n : ℕ)
    (hR : 0 < R) (hR1 : R ≤ 1) (hn : 2 ≤ n) (hρm : 0 < ρm) (hCc : 0 ≤ Cc)
    (hcnt : ∀ z : Vec 2, Summable (fun p : (Fin 2 → Fin N) × (Fin 2 → ℤ) =>
        latticeCountWeight R⁻¹ n z (y' p.1) p.2) ∧
      ∑' p : (Fin 2 → Fin N) × (Fin 2 → ℤ), latticeCountWeight R⁻¹ n z (y' p.1) p.2 ≤ Cc)
    (Mj : (Fin 2 → Fin N) → (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout (K i)) (h i)))
    (hMmom : ∀ j g i, CycleJointProofs.HasRadialPlaneMoments (Mj j g i) (y' j))
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Mout (K v)) (h v)))
    (hTm : ∀ g i, Tm g i =
      ∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (Mj j g i) (y' j) (hMmom j g i))
    (b : (Fin 2 → Fin N) → (∀ i, TorusHk 0 (h i)) → ι → ℝ) (hb : ∀ j g i, 0 ≤ b j g i)
    (hmodel : ∀ j g, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n R⁻¹ (y' j) ρm Mout (Mj j g i) ≤
      ENNReal.ofReal (C ^ 2 * ∑ i, (π i)⁻¹ * b j g i))
    (hbsum : ∀ g i, ∑ j, b j g i ≤ ‖g i‖ ^ 2) :
    IsRawMassModel π K Mout ρm (Real.sqrt Cc * C) Tm := by
  intro g
  have key := mass_sum_transfer (fun i => (π i)⁻¹)
    (fun i => factorialNormSq ρm (truncateTorusHk (le_max_left Mout (K i)) (Tm g i)).val)
    (fun i => ‖g i‖ ^ 2) (fun j i => b j g i)
    (fun j i => weightedFactorialNormSq n R⁻¹ (y' j) ρm Mout (Mj j g i)) Cc (C ^ 2)
    (fun i => inv_nonneg.2 (hπ i).le) (fun i => factorialNormSq_nonneg _ _) hCc
    (sq_nonneg C) (fun j i => hb j g i)
    (fun i => by
      rw [hTm g i]
      exact hB3 (E := h i) y' R Cc n hR hR1 hn hcnt (max Mout (K i)) (fun j => Mj j g i)
        (fun j => hMmom j g i) Mout (le_max_left _ _) ρm hρm)
    (fun j => hmodel j g) (fun i => hbsum g i)
  have hsq : ∀ i, torusHkNorm ρm (le_max_left Mout (K i)) (Tm g i) ^ 2 =
      factorialNormSq ρm (truncateTorusHk (le_max_left Mout (K i)) (Tm g i)).val :=
    fun i => Real.sq_sqrt (factorialNormSq_nonneg _ _)
  simp only [hsq, CycleJointProofs.torusHkNorm_zero_input]
  refine key.trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt hCc]

/-- **Patch error sum.** If the torus field at `t_p` is the sum of the periodized plane fields
`U j`, then its difference with the truncated torus model is bounded by the counting constant
times the patchwise weighted errors (at any slots `K' ≤ max Mout K`). -/
theorem patch_error_sum (hB3 : PeriodizedRadialSumStatement.{v}) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (K K' : ι → ℕ) (Mout : ℕ) (hKK : ∀ i, K' i ≤ max Mout (K i)) {N : ℕ}
    (y' : (Fin 2 → Fin N) → Vec 2) (R Cc ε ρs : ℝ) (n : ℕ) (hR : 0 < R) (hR1 : R ≤ 1)
    (hn : 2 ≤ n) (hρs : 0 < ρs) (hCc : 0 ≤ Cc)
    (hcnt : ∀ z : Vec 2, Summable (fun p : (Fin 2 → Fin N) × (Fin 2 → ℤ) =>
        latticeCountWeight R⁻¹ n z (y' p.1) p.2) ∧
      ∑' p : (Fin 2 → Fin N) × (Fin 2 → ℤ), latticeCountWeight R⁻¹ n z (y' p.1) p.2 ≤ Cc)
    (Mj : (Fin 2 → Fin N) → (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout (K i)) (h i)))
    (hMmom : ∀ j g i, CycleJointProofs.HasRadialPlaneMoments (Mj j g i) (y' j))
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Mout (K v)) (h v)))
    (hTm : ∀ g i, Tm g i =
      ∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (Mj j g i) (y' j) (hMmom j g i))
    (g : ∀ i, TorusHk 0 (h i)) (ut : ∀ i, TorusHk (K' i) (h i))
    (U : (Fin 2 → Fin N) → ∀ i, PlaneHk Set.univ (K' i) (h i))
    (hmU : ∀ j i, CycleJointProofs.HasRadialPlaneMoments (U j i) (y' j))
    (hid : ∀ i, ut i = ∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (U j i) (y' j) (hmU j i))
    (b : (Fin 2 → Fin N) → ι → ℝ) (c : ι → ℝ) (hb : ∀ j i, 0 ≤ b j i)
    (herr : ∀ j, ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n R⁻¹ (y' j) ρs (K' i)
        (U j i - truncatePlaneHk (hKK i) (Mj j g i)) ≤
      ENNReal.ofReal (ε ^ 2 * ∑ i, (π i)⁻¹ * b j i))
    (hbsum : ∀ i, ∑ j, b j i ≤ c i) :
    ∑ i, (π i)⁻¹ * factorialNormSq ρs (ut i - truncateTorusHk (hKK i) (Tm g i)).val ≤
      Cc * ε ^ 2 * ∑ i, (π i)⁻¹ * c i := by
  have hdiff : ∀ i, ut i - truncateTorusHk (hKK i) (Tm g i) =
      ∑ j, CycleJointProofs.periodizeRadialPlaneCarrier
        (U j i - truncatePlaneHk (hKK i) (Mj j g i)) (y' j)
        ((hmU j i).sub ((hMmom j g i).truncate (hKK i))) := fun i => by
    rw [hid i, hTm g i]
    exact periodized_error_identity y' (hKK i) _ _ (fun j => hmU j i) (fun j => hMmom j g i)
  exact mass_sum_transfer (fun i => (π i)⁻¹)
    (fun i => factorialNormSq ρs (ut i - truncateTorusHk (hKK i) (Tm g i)).val) c b
    (fun j i => weightedFactorialNormSq n R⁻¹ (y' j) ρs (K' i)
      (U j i - truncatePlaneHk (hKK i) (Mj j g i))) Cc (ε ^ 2)
    (fun i => inv_nonneg.2 (hπ i).le) (fun i => factorialNormSq_nonneg _ _) hCc (sq_nonneg ε) hb
    (fun i => by
      rw [hdiff i]
      have hb3 := hB3 (E := h i) y' R Cc n hR hR1 hn hcnt (K' i)
        (fun j => U j i - truncatePlaneHk (hKK i) (Mj j g i))
        (fun j => (hmU j i).sub ((hMmom j g i).truncate (hKK i))) (K' i) le_rfl ρs hρs
      rwa [truncateTorusHk_self] at hb3)
    herr hbsum

/-- Closing step of the error: a mass sum bounded through the patch budget and the prepared
bounds gives the square-root form of `IsJointError`. -/
theorem sqrt_mass_le_of_budget {ι : Type*} [Fintype ι] (p a f F : ι → ℝ) (Cc Cbud ε : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hCc : 0 ≤ Cc) (hCbud : 0 ≤ Cbud) (hε : 0 ≤ ε)
    (hfF : ∀ i, f i ≤ F i ^ 2)
    (hsum : ∑ i, p i * a i ≤ Cc * ε ^ 2 * ∑ i, p i * (Cbud * f i)) :
    Real.sqrt (∑ i, p i * a i) ≤ Real.sqrt (Cc * Cbud) * ε * Real.sqrt (∑ i, p i * F i ^ 2) := by
  have h1 : ∑ i, p i * a i ≤ (Real.sqrt (Cc * Cbud) * ε) ^ 2 * ∑ i, p i * F i ^ 2 := by
    refine hsum.trans ?_
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hCc hCbud)]
    have hle : ∑ i, p i * (Cbud * f i) ≤ Cbud * ∑ i, p i * F i ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => by
        nlinarith [hfF i, hp i, mul_le_mul_of_nonneg_left (hfF i) (mul_nonneg (hp i) hCbud)]
    calc Cc * ε ^ 2 * ∑ i, p i * (Cbud * f i) ≤ Cc * ε ^ 2 * (Cbud * ∑ i, p i * F i ^ 2) :=
          mul_le_mul_of_nonneg_left hle (mul_nonneg hCc (sq_nonneg ε))
      _ = Cc * Cbud * ε ^ 2 * ∑ i, p i * F i ^ 2 := by ring
  calc Real.sqrt (∑ i, p i * a i)
      ≤ Real.sqrt ((Real.sqrt (Cc * Cbud) * ε) ^ 2 * ∑ i, p i * F i ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt (Cc * Cbud) * ε * Real.sqrt (∑ i, p i * F i ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hε)]

/-- Closing step of the `L²` clause: a contraction plus a small error gives the near-contraction
`1 + √(Cc Cbud) ε` in the mass-weighted `ℓ²` norm. -/
theorem mass_l2_of_contraction {ι : Type*} [Fintype ι] (p x y z n0 : ι → ℝ) (Cc Cbud ε : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hCc : 0 ≤ Cc) (hCbud : 0 ≤ Cbud) (hε : 0 ≤ ε)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (hxyz : ∀ i, x i ≤ y i + z i)
    (hyn : ∀ i, y i ≤ n0 i)
    (hz : ∑ i, p i * z i ^ 2 ≤ Cc * ε ^ 2 * ∑ i, p i * (Cbud * n0 i ^ 2)) :
    ∑ i, p i * x i ^ 2 ≤ (1 + Real.sqrt (Cc * Cbud) * ε) ^ 2 * ∑ i, p i * n0 i ^ 2 := by
  have htri := weighted_sqrt_sum_le p x y z hp hx hxyz
  have hy2 : Real.sqrt (∑ i, p i * y i ^ 2) ≤ Real.sqrt (∑ i, p i * n0 i ^ 2) :=
    Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hy i) (hyn i) 2) (hp i))
  have hz2 := sqrt_mass_le_of_budget p (fun i => z i ^ 2) (fun i => n0 i ^ 2) n0 Cc Cbud ε hp
    hCc hCbud hε (fun i => le_rfl) hz
  have hroot : Real.sqrt (∑ i, p i * x i ^ 2) ≤
      (1 + Real.sqrt (Cc * Cbud) * ε) * Real.sqrt (∑ i, p i * n0 i ^ 2) := by
    calc Real.sqrt (∑ i, p i * x i ^ 2)
        ≤ Real.sqrt (∑ i, p i * y i ^ 2) + Real.sqrt (∑ i, p i * z i ^ 2) := htri
      _ ≤ Real.sqrt (∑ i, p i * n0 i ^ 2) +
          Real.sqrt (Cc * Cbud) * ε * Real.sqrt (∑ i, p i * n0 i ^ 2) := add_le_add hy2 hz2
      _ = (1 + Real.sqrt (Cc * Cbud) * ε) * Real.sqrt (∑ i, p i * n0 i ^ 2) := by ring
  have hnn : 0 ≤ (1 + Real.sqrt (Cc * Cbud) * ε) * Real.sqrt (∑ i, p i * n0 i ^ 2) :=
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  calc ∑ i, p i * x i ^ 2 ≤ ((1 + Real.sqrt (Cc * Cbud) * ε) *
        Real.sqrt (∑ i, p i * n0 i ^ 2)) ^ 2 := (Real.sqrt_le_left hnn).1 hroot
    _ = (1 + Real.sqrt (Cc * Cbud) * ε) ^ 2 * ∑ i, p i * n0 i ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (sq_nonneg _))]

end Clauses

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! The physical error clause and the edge-free `L²` clause of the core at one level and one
patch mesh, from the patch models, the periodization of the plane solutions, the
periodized sums, the patch budget and (for `L²`) the scalar contraction. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly
attribute [local instance] scalarResidualTorusNormed scalarResidualTorusInner
    scalarResidualTorusSpace scalarResidualPlaneNormed scalarResidualPlaneInner
    scalarResidualPlaneSpace scalarResidualPiAdd scalarResidualPiModule scalarResidualPlanePiAdd
    scalarResidualPlanePiModule

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **Error clause** at one mesh: the torus error of the summed patch models. -/
theorem raw_error_clause (hB3 : PeriodizedRadialSumStatement.{v}) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (Mout D : ℕ)
    (ν tS tp ρs ρold R Cc E Pacc CP L : ℝ) (n : ℕ) (hR : 0 < R) (hR1 : R ≤ 1) (hn : 2 ≤ n)
    (hρs : 0 < ρs) (hCc : 0 ≤ Cc)
    (hε : 0 ≤ CP * E ^ Pacc) (hρ0 : 0 ≤ ρold) (hL : 1 ≤ L) {N : ℕ} (hN : 0 < N)
    (hmesh : ρold * (N : ℝ) ≤ L) (y' : (Fin 2 → Fin N) → Vec 2)
    (hcnt : ∀ z : Vec 2, Summable (fun p : (Fin 2 → Fin N) × (Fin 2 → ℤ) =>
        latticeCountWeight R⁻¹ n z (y' p.1) p.2) ∧
      ∑' p : (Fin 2 → Fin N) × (Fin 2 → ℤ), latticeCountWeight R⁻¹ n z (y' p.1) p.2 ≤ Cc)
    (b : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (Mj : (Fin 2 → Fin N) → (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout (K i)) (h i)))
    (hMmom : ∀ j g i, CycleJointProofs.HasRadialPlaneMoments (Mj j g i) (y' j))
    (hMerr : ∀ j, IsPatchError π K Mout D ν tS tp ρs ρold R (CP * E ^ Pacc) n (y' j) b A
      (fun i => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i)) (Mj j))
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Mout (K v)) (h v)))
    (hTm : ∀ g i, Tm g i =
      ∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (Mj j g i) (y' j) (hMmom j g i))
    (hB2 : ∀ f : ∀ i, TorusHk (K i) (h i),
      ∃ (U : (Fin 2 → Fin N) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
        (W : (Fin 2 → Fin N) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
        (∀ j, IsCoupledWeakSolutionPlane ν tS tp b D K A
          (fun i => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i))
          (fun _ _ => 0) (fun _ _ => 0) (U j) (W j)) ∧
        ∃ hmU : ∀ j i, CycleJointProofs.HasRadialPlaneMoments (U j i tp) (y' j),
        ∀ (u : ∀ i, ℝ → TorusHk (K i) (h i)) (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
          IsCoupledWeakSolutionTorus ν tS tp b D K A f (fun _ _ => 0) (fun _ _ => 0) u w →
          ∀ i, u i tp = ∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (U j i tp) (y' j)
            (hmU j i)) :
    IsRawMassError π K Mout D ν tS tp ρs ρold E Pacc
      (Real.sqrt (Cc * patchBudgetUniform hζ Kmax L) * CP) b A Tm := by
  intro f Fv hF u w hsol
  obtain ⟨U, W, hU, hrest⟩ := hB2 f
  obtain ⟨hmU, hid⟩ := hrest
  have hsum := patch_error_sum hB3 π hπ K K Mout (fun i => le_max_right Mout (K i)) y' R Cc
    (CP * E ^ Pacc) ρs n hR hR1 hn hρs hCc hcnt Mj hMmom Tm hTm (fun i => truncateTorusHk (Nat.zero_le _) (f i))
    (fun i => u i tp) (fun j i => U j i tp) hmU (hid u w hsol)
    (fun j i => factorialNormSq ρold
      (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i)).val)
    (fun i => patchBudgetUniform hζ Kmax L * factorialNormSq ρold (f i).val)
    (fun j i => factorialNormSq_nonneg _ _) (fun j => hMerr j f (U j) (W j) (hU j))
    (fun i => patch_localization_factorial_sum_le hζ N hN (hK i) (f i) ρold L hρ0 hL hmesh)
  have hfF : ∀ i, factorialNormSq ρold (f i).val ≤ Fv i ^ 2 := fun i => by
    have h1 := hF i
    have h0 : 0 ≤ torusHkNorm ρold (le_refl (K i)) (f i) := Real.sqrt_nonneg _
    have h2 : torusHkNorm ρold (le_refl (K i)) (f i) ^ 2 = factorialNormSq ρold (f i).val := by
      unfold torusHkNorm
      rw [Real.sq_sqrt (factorialNormSq_nonneg _ _), truncateTorusHk_self]
    rw [← h2]
    exact pow_le_pow_left₀ h0 h1 2
  have hfin := sqrt_mass_le_of_budget (fun i => (π i)⁻¹)
    (fun i => factorialNormSq ρs (u i tp - truncateTorusHk (le_max_right Mout (K i)) (Tm
      (fun i => truncateTorusHk (Nat.zero_le _) (f i)) i)).val)
    (fun i => factorialNormSq ρold (f i).val) Fv Cc (patchBudgetUniform hζ Kmax L)
    (CP * E ^ Pacc) (fun i => inv_nonneg.2 (hπ i).le) hCc (patchBudgetUniform_nonneg hζ Kmax L)
    hε hfF hsum
  refine le_of_le_of_eq hfin ?_
  ring

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The slot-0 patch model of the one-patch statement is the truncation of the patch model. -/
theorem slot_zero_model_eq (Mout : ℕ) (K : ι → ℕ)
    (M : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout (K i)) (h i)))
    (g : ∀ i, TorusHk 0 (h i)) (i : ι) :
    truncatePlaneHk (le_max_right Mout 0)
        ((planeFamilyTruncation (fun _ => max Mout 0) (fun i => max Mout (K i))
          (fun _ => max_le_max le_rfl (Nat.zero_le _)) ∘ₗ M)
          (fun i => truncateTorusHk (Nat.zero_le 0) (g i)) i) =
      truncatePlaneHk (Nat.zero_le _) (M g i) := by
  have hg : (fun i => truncateTorusHk (Nat.zero_le 0) (g i)) = g := by
    funext i
    exact truncateTorusHk_self (g i)
  have hg' : M (fun i => truncateTorusHk (Nat.zero_le 0) (g i)) = M g := congrArg M hg
  calc _ = truncatePlaneHk (le_max_right Mout 0) (truncatePlaneHk
        (max_le_max le_rfl (Nat.zero_le _)) (M (fun i => truncateTorusHk (Nat.zero_le 0) (g i)) i)) :=
        rfl
    _ = truncatePlaneHk (Nat.zero_le _) (M (fun i => truncateTorusHk (Nat.zero_le 0) (g i)) i) :=
        truncatePlaneHk_truncatePlaneHk _ _ _
    _ = truncatePlaneHk (Nat.zero_le _) (M g i) := by rw [hg']

/-- **Edge-free `L²` clause** at one mesh: the slot-0 torus solution is an `L²` contraction and
the summed patch models are within the slot-0 error of it. -/
theorem raw_l2_clause (hB3 : PeriodizedRadialSumStatement.{v}) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (Kmax : ℕ) (Mout D : ℕ)
    (ν tS tp ρs ρold R Cc E Pacc CP L : ℝ) (n : ℕ) (hR : 0 < R) (hR1 : R ≤ 1) (hn : 2 ≤ n)
    (hρs : 0 < ρs) (hCc : 0 ≤ Cc)
    (hε : 0 ≤ CP * E ^ Pacc) (hρ0 : 0 ≤ ρold) (hL : 1 ≤ L) {N : ℕ} (hN : 0 < N)
    (hmesh : ρold * (N : ℝ) ≤ L) (y' : (Fin 2 → Fin N) → Vec 2)
    (hcnt : ∀ z : Vec 2, Summable (fun p : (Fin 2 → Fin N) × (Fin 2 → ℤ) =>
        latticeCountWeight R⁻¹ n z (y' p.1) p.2) ∧
      ∑' p : (Fin 2 → Fin N) × (Fin 2 → ℤ), latticeCountWeight R⁻¹ n z (y' p.1) p.2 ≤ Cc)
    (b : ℝ → Vec 2 → Vec 2)
    (A0 : ∀ (i i' : ι) (d : admissibleOrders (fun _ => 0) D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (Mj : (Fin 2 → Fin N) → (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout (K i)) (h i)))
    (hMmom : ∀ j g i, CycleJointProofs.HasRadialPlaneMoments (Mj j g i) (y' j))
    (hMerr0 : ∀ j, IsPatchError π (fun _ => 0) Mout D ν tS tp ρs ρold R (CP * E ^ Pacc) n (y' j) b
      A0 (fun _ => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) 0)
      ((planeFamilyTruncation (fun _ => max Mout 0) (fun i => max Mout (K i))
        (fun _ => max_le_max le_rfl (Nat.zero_le _))) ∘ₗ Mj j))
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Mout (K v)) (h v)))
    (hTm : ∀ g i, Tm g i =
      ∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (Mj j g i) (y' j) (hMmom j g i))
    (hB2 : ∀ f : ∀ i, TorusHk 0 (h i),
      (∃ (u : ∀ i, ℝ → TorusHk 0 (h i)) (w : ∀ i, ℝ → TorusHk 1 (h i)),
        IsCoupledWeakSolutionTorus ν tS tp b D (fun _ => 0) A0 f (fun _ _ => 0) (fun _ _ => 0)
          u w) ∧
      ∃ (U : (Fin 2 → Fin N) → ∀ i, ℝ → PlaneHk Set.univ 0 (h i))
        (W : (Fin 2 → Fin N) → ∀ i, ℝ → PlaneHk Set.univ 1 (h i)),
        (∀ j, IsCoupledWeakSolutionPlane ν tS tp b D (fun _ => 0) A0
          (fun i => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) 0 (f i))
          (fun _ _ => 0) (fun _ _ => 0) (U j) (W j)) ∧
        ∃ hmU : ∀ j i, CycleJointProofs.HasRadialPlaneMoments (U j i tp) (y' j),
        ∀ (u : ∀ i, ℝ → TorusHk 0 (h i)) (w : ∀ i, ℝ → TorusHk 1 (h i)),
          IsCoupledWeakSolutionTorus ν tS tp b D (fun _ => 0) A0 f (fun _ _ => 0)
            (fun _ _ => 0) u w →
          ∀ i, u i tp = ∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (U j i tp) (y' j)
            (hmU j i))
    (hcontr : ∀ (f : ∀ i, TorusHk 0 (h i)) (u : ∀ i, ℝ → TorusHk 0 (h i))
        (w : ∀ i, ℝ → TorusHk 1 (h i)),
      IsCoupledWeakSolutionTorus ν tS tp b D (fun _ => 0) A0 f (fun _ _ => 0) (fun _ _ => 0) u w →
      ∀ i, ‖u i tp‖ ≤ ‖f i‖) :
    IsRawMassL2 π K Mout (1 + Real.sqrt (Cc * patchBudgetUniform hζ Kmax L) * CP * E ^ Pacc)
      Tm := by
  intro f0
  obtain ⟨hex, hrest⟩ := hB2 f0
  obtain ⟨u0, w0, hsol0⟩ := hex
  obtain ⟨U0, W0, hU0, hrest2⟩ := hrest
  obtain ⟨hmU0, hid0⟩ := hrest2
  have herr0 : ∀ j, ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n R⁻¹ (y' j) ρs 0
      (U0 j i tp - truncatePlaneHk (Nat.zero_le (max Mout (K i))) (Mj j f0 i)) ≤
      ENNReal.ofReal ((CP * E ^ Pacc) ^ 2 * ∑ i, (π i)⁻¹ * factorialNormSq ρold
        (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) 0 (f0 i)).val) := fun j => by
    have he := hMerr0 j f0 (U0 j) (W0 j) (hU0 j)
    simpa only [slot_zero_model_eq] using he
  have hsum := patch_error_sum hB3 π hπ K (fun _ => 0) Mout (fun i => Nat.zero_le _) y' R Cc
    (CP * E ^ Pacc) ρs n hR hR1 hn hρs hCc hcnt Mj hMmom Tm hTm f0 (fun i => u0 i tp)
    (fun j i => U0 j i tp) hmU0 (hid0 u0 w0 hsol0)
    (fun j i => factorialNormSq ρold
      (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) 0 (f0 i)).val)
    (fun i => patchBudgetUniform hζ Kmax L * factorialNormSq ρold (f0 i).val)
    (fun j i => factorialNormSq_nonneg _ _) herr0
    (fun i => patch_localization_factorial_sum_le hζ N hN (Nat.zero_le Kmax) (f0 i) ρold L hρ0 hL
      hmesh)
  have hz : ∑ i, (π i)⁻¹ * ‖u0 i tp - truncateTorusHk (Nat.zero_le _) (Tm f0 i)‖ ^ 2 ≤
      Cc * (CP * E ^ Pacc) ^ 2 *
        ∑ i, (π i)⁻¹ * (patchBudgetUniform hζ Kmax L * ‖f0 i‖ ^ 2) := by
    have h' := hsum
    simp only [CycleJointProofs.factorialNormSq_order_zero_measure] at h'
    exact h'
  have hfin := mass_l2_of_contraction (fun i => (π i)⁻¹)
    (fun i => ‖truncateTorusHk (Nat.zero_le _) (Tm f0 i)‖) (fun i => ‖u0 i tp‖)
    (fun i => ‖u0 i tp - truncateTorusHk (Nat.zero_le _) (Tm f0 i)‖) (fun i => ‖f0 i‖) Cc
    (patchBudgetUniform hζ Kmax L) (CP * E ^ Pacc) (fun i => inv_nonneg.2 (hπ i).le) hCc
    (patchBudgetUniform_nonneg hζ Kmax L) hε (fun i => norm_nonneg _) (fun i => norm_nonneg _)
    (fun i => by
      calc ‖truncateTorusHk (Nat.zero_le _) (Tm f0 i)‖
          = ‖u0 i tp - (u0 i tp - truncateTorusHk (Nat.zero_le _) (Tm f0 i))‖ := by
            rw [sub_sub_cancel]
        _ ≤ ‖u0 i tp‖ + ‖u0 i tp - truncateTorusHk (Nat.zero_le _) (Tm f0 i)‖ :=
            norm_sub_le _ _)
    (fun i => hcontr f0 u0 w0 hsol0 i) hz
  simp only [CycleJointProofs.torusHkNorm_order_zero, truncateTorusHk_self]
  refine hfin.trans (le_of_eq ?_)
  ring

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **Level B of the route to `cycle_joint`**: `rawJoint_of_patches` proves
the core `RawJointStatement` from `PatchJointStatement`, `PlaneTorusStatement`,
`PeriodizedRadialSumStatement`, `CentreCountingStatement` and
`ScalarContractionVanishingStatement`. Constants: `C_core = √Cc · C`,
`CP_core = √(Cc · Cbud) · CP`, where `Cc` is the counting constant of `CentreCountingStatement` at the moment order of `PatchJointStatement`
and `Cbud = patchBudgetUniform hζ Kmax (max 1 (9 COld))`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly
attribute [local instance] scalarResidualTorusNormed scalarResidualTorusInner
    scalarResidualTorusSpace scalarResidualPlaneNormed scalarResidualPlaneInner
    scalarResidualPlaneSpace scalarResidualPiAdd scalarResidualPiModule scalarResidualPlanePiAdd
    scalarResidualPlanePiModule

local instance rawJointTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
local instance rawJointTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
local instance rawJointTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance
local instance rawJointTorusPiAdd {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (K : ι → ℕ) :
    AddCommMonoid (∀ i, TorusHk (K i) (h i)) := inferInstance
local instance rawJointTorusPiModule {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (K : ι → ℕ) :
    Module ℝ (∀ i, TorusHk (K i) (h i)) := inferInstance

section Family

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The patch models of one mesh and their summed torus operator, with the properties delivered
by the one-patch statement (bundled, so that each clause of the core is proved in its own declaration). -/
structure PatchSum {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Mout D : ℕ) (C c ε : ℝ) (n : ℕ)
    (π : ι → ℝ) (K : ι → ℕ) (ν tS tp ρs ρold R : ℝ)
    (y : ∀ N : ℕ, (Fin 2 → Fin N) → Vec 2) (b : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (A0 : ∀ (i i' : ι) (d : admissibleOrders (fun _ => 0) D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (edgeFree : Prop) where
  N : ℕ
  hN : 0 < N
  hN8 : 8 ≤ (N : ℝ) * R
  hN9 : (N : ℝ) * R ≤ 9
  Mj : (Fin 2 → Fin N) → (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout (K i)) (h i))
  model : ∀ j f, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq n R⁻¹ (y N j) (c * R) Mout (Mj j f i) ≤
    ENNReal.ofReal (C ^ 2 * ∑ i, (π i)⁻¹ *
      ‖spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) 0 (f i)‖ ^ 2)
  mom : ∀ j f i, CycleJointProofs.HasRadialPlaneMoments (Mj j f i) (y N j)
  err : ∀ j, IsPatchError π K Mout D ν tS tp ρs ρold R ε n (y N j) b A
    (fun i => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i)) (Mj j)
  err0 : ∀ j, edgeFree →
    IsPatchError π (fun _ => 0) Mout D ν tS tp ρs ρold R ε n (y N j) b A0
      (fun _ => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) 0)
      ((planeFamilyTruncation (fun _ => max Mout 0) (fun i => max Mout (K i))
        (fun _ => max_le_max le_rfl (Nat.zero_le _))) ∘ₗ Mj j)
  Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Mout (K v)) (h v))
  hTm : ∀ g i, Tm g i = ∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (Mj j g i) (y N j)
    (mom j g i)

/-- The patch models of the one-patch statement at the mesh `⌈8/R⌉₊` and their sum. -/
theorem nonempty_patchSum {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) {Mout D : ℕ} {C c ε : ℝ} {n : ℕ}
    {π : ι → ℝ} {K : ι → ℕ} {ν tS tp ρs ρold R : ℝ} {y : ∀ N : ℕ, (Fin 2 → Fin N) → Vec 2}
    {b : ℝ → Vec 2 → Vec 2}
    {A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))}
    {A0 : ∀ (i i' : ι) (d : admissibleOrders (fun _ => 0) D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))}
    {edgeFree : Prop} (hR : 0 < R) (hR1 : R ≤ 1)
    (hB1G : PatchModelsGen hζ Mout D C c ε n π K ν tS tp ρs ρold R y b A A0 edgeFree) :
    Nonempty (PatchSum hζ Mout D C c ε n π K ν tS tp ρs ρold R y b A A0 edgeFree) := by
  obtain ⟨N, hN, hN8, hN9⟩ := exists_patch_mesh hR hR1
  choose Mj hMmodel hMmom hMerr hMerr0 using hB1G N hN hN8 hN9
  obtain ⟨Tm, hTm⟩ : ∃ Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Mout (K v)) (h v)),
      ∀ g i, Tm g i = ∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (Mj j g i) (y N j)
        (hMmom j g i) := by
    refine ⟨LinearMap.pi fun i => ∑ j, (CycleJointProofs.periodizeRadialPlaneLinear
      (max Mout (K i)) (y N j)).comp ((LinearMap.proj (R := ℝ)
        (φ := fun i => PlaneHk Set.univ (max Mout (K i)) (h i)) i ∘ₗ Mj j).codRestrict
          (CycleJointProofs.radialPlaneMomentSubmodule (max Mout (K i)) (y N j))
          (fun g => hMmom j g i)), fun g i => ?_⟩
    simp only [LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    rfl
  exact ⟨⟨N, hN, hN8, hN9, Mj, hMmodel, hMmom, hMerr, fun j hedge => hMerr0 j hedge, Tm, hTm⟩⟩

namespace PatchSum

variable {ζ : ℝ → ℝ} {hζ : IsFastProfile ζ} {Mout D : ℕ} {C c ε E Pacc CP : ℝ} {n : ℕ}
    {π : ι → ℝ} {K : ι → ℕ} {ν tS tp ρs ρold R : ℝ} {y : ∀ N : ℕ, (Fin 2 → Fin N) → Vec 2}
    {b : ℝ → Vec 2 → Vec 2}
    {A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))}
    {A0 : ∀ (i i' : ι) (d : admissibleOrders (fun _ => 0) D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))}
    {edgeFree : Prop}

/-- The model clause of a patch sum. -/
theorem model_clause (S : PatchSum hζ Mout D C c ε n π K ν tS tp ρs ρold R y b A A0 edgeFree)
    (hB3 : PeriodizedRadialSumStatement.{v}) (hπ : ∀ i, 0 < π i) {Cc : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hn : 2 ≤ n) (hc : 0 < c) (hCc : 0 ≤ Cc)
    (hcnt : ∀ z : Vec 2, Summable (fun p : (Fin 2 → Fin S.N) × (Fin 2 → ℤ) =>
        latticeCountWeight R⁻¹ n z (y S.N p.1) p.2) ∧
      ∑' p : (Fin 2 → Fin S.N) × (Fin 2 → ℤ), latticeCountWeight R⁻¹ n z (y S.N p.1) p.2 ≤ Cc) :
    IsRawMassModel π K Mout (c * R) (Real.sqrt Cc * C) S.Tm :=
  patch_model_clause hB3 π hπ K Mout (y S.N) R Cc C (c * R) n hR hR1 hn (mul_pos hc hR) hCc hcnt
    S.Mj S.mom S.Tm
    S.hTm (fun j g i => ‖spatialPatchLocalization hζ S.N S.hN (fun k => (j k : ℤ)) 0 (g i)‖ ^ 2)
    (fun _ _ _ => sq_nonneg _) S.model
    (fun g i => CycleJointProofs.spatialPatchLocalization_norm_sq_sum hζ S.N S.hN (g i))

/-- The error clause of a patch sum. -/
theorem error_clause (S : PatchSum hζ Mout D C c (CP * E ^ Pacc) n π K ν tS tp ρs ρold R y b A A0
      edgeFree)
    (hB3 : PeriodizedRadialSumStatement.{v}) (hπ : ∀ i, 0 < π i) {Kmax : ℕ} (hK : ∀ i, K i ≤ Kmax)
    {Cc L : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hn : 2 ≤ n) (hρs : 0 < ρs) (hCc : 0 ≤ Cc) (hε : 0 ≤ CP * E ^ Pacc)
    (hρ0 : 0 ≤ ρold) (hL : 1 ≤ L) (hmesh : ρold * (S.N : ℝ) ≤ L)
    (hcnt : ∀ z : Vec 2, Summable (fun p : (Fin 2 → Fin S.N) × (Fin 2 → ℤ) =>
        latticeCountWeight R⁻¹ n z (y S.N p.1) p.2) ∧
      ∑' p : (Fin 2 → Fin S.N) × (Fin 2 → ℤ), latticeCountWeight R⁻¹ n z (y S.N p.1) p.2 ≤ Cc)
    (hB2G : PlaneTorusGen hζ D K ν tS tp S.N S.hN (y S.N) b A A0 edgeFree) :
    IsRawMassError π K Mout D ν tS tp ρs ρold E Pacc
      (Real.sqrt (Cc * patchBudgetUniform hζ Kmax L) * CP) b A S.Tm :=
  raw_error_clause hB3 hζ π hπ K Kmax hK Mout D ν tS tp ρs ρold R Cc E Pacc CP L n hR hR1 hn hρs
    hCc hε
    hρ0 hL S.hN hmesh (y S.N) hcnt b A S.Mj S.mom S.err S.Tm S.hTm hB2G.1

/-- The edge-free `L²` clause of a patch sum. -/
theorem l2_clause (S : PatchSum hζ Mout D C c (CP * E ^ Pacc) n π K ν tS tp ρs ρold R y b A A0
      edgeFree)
    (hB3 : PeriodizedRadialSumStatement.{v}) (hπ : ∀ i, 0 < π i) (Kmax : ℕ)
    {Cc L : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hn : 2 ≤ n) (hρs : 0 < ρs) (hCc : 0 ≤ Cc) (hε : 0 ≤ CP * E ^ Pacc)
    (hρ0 : 0 ≤ ρold) (hL : 1 ≤ L) (hmesh : ρold * (S.N : ℝ) ≤ L)
    (hcnt : ∀ z : Vec 2, Summable (fun p : (Fin 2 → Fin S.N) × (Fin 2 → ℤ) =>
        latticeCountWeight R⁻¹ n z (y S.N p.1) p.2) ∧
      ∑' p : (Fin 2 → Fin S.N) × (Fin 2 → ℤ), latticeCountWeight R⁻¹ n z (y S.N p.1) p.2 ≤ Cc)
    (hB2G : PlaneTorusGen hζ D K ν tS tp S.N S.hN (y S.N) b A A0 edgeFree) (hedge : edgeFree)
    (hcontr : ∀ (f : ∀ i, TorusHk 0 (h i)) (u : ∀ i, ℝ → TorusHk 0 (h i))
      (w : ∀ i, ℝ → TorusHk 1 (h i)),
      IsCoupledWeakSolutionTorus ν tS tp b D (fun _ => 0) A0 f (fun _ _ => 0) (fun _ _ => 0) u w →
      ∀ i, ‖u i tp‖ ≤ ‖f i‖) :
    IsRawMassL2 π K Mout (1 + Real.sqrt (Cc * patchBudgetUniform hζ Kmax L) * CP * E ^ Pacc)
      S.Tm :=
  raw_l2_clause hB3 hζ π hπ K Kmax Mout D ν tS tp ρs ρold R Cc E Pacc CP L n hR hR1 hn hρs hCc hε
    hρ0 hL
    S.hN hmesh (y S.N) hcnt b A0 S.Mj S.mom (fun j => S.err0 j hedge) S.Tm S.hTm (hB2G.2 hedge)
    hcontr

end PatchSum

/-- **One family at one level**, over generic window data. -/
theorem rawJoint_family_step (hB3 : PeriodizedRadialSumStatement.{v}) {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) {Mout D Kmax : ℕ} {C c Cc L E Pacc CP ν tS tp ρs ρold R : ℝ} {n : ℕ}
    (hCc : 0 < Cc) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (hK : ∀ i, K i ≤ Kmax)
    (y : ∀ N : ℕ, (Fin 2 → Fin N) → Vec 2) (b : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (A0 : ∀ (i i' : ι) (d : admissibleOrders (fun _ => 0) D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (edgeFree : Prop) (hR : 0 < R) (hR1 : R ≤ 1) (hn : 2 ≤ n) (hc : 0 < c) (hρs : 0 < ρs)
    (hρ0 : 0 < ρold) (hL : 1 ≤ L)
    (hmesh : ∀ N : ℕ, (N : ℝ) * R ≤ 9 → ρold * (N : ℝ) ≤ L) (hε : 0 ≤ CP * E ^ Pacc)
    (hcnt : ∀ N : ℕ, 8 ≤ (N : ℝ) * R → (N : ℝ) * R ≤ 9 → ∀ z : Vec 2,
      Summable (fun p : (Fin 2 → Fin N) × (Fin 2 → ℤ) =>
        latticeCountWeight R⁻¹ n z (y N p.1) p.2) ∧
      ∑' p : (Fin 2 → Fin N) × (Fin 2 → ℤ), latticeCountWeight R⁻¹ n z (y N p.1) p.2 ≤ Cc)
    (hB1G : PatchModelsGen hζ Mout D C c (CP * E ^ Pacc) n π K ν tS tp ρs ρold R y b A A0
      edgeFree)
    (hB2G : ∀ N hN, PlaneTorusGen hζ D K ν tS tp N hN (y N) b A A0 edgeFree)
    (hcontr : edgeFree → ∀ (f : ∀ i, TorusHk 0 (h i)) (u : ∀ i, ℝ → TorusHk 0 (h i))
      (w : ∀ i, ℝ → TorusHk 1 (h i)),
      IsCoupledWeakSolutionTorus ν tS tp b D (fun _ => 0) A0 f (fun _ _ => 0) (fun _ _ => 0) u w →
      ∀ i, ‖u i tp‖ ≤ ‖f i‖) :
    ∃ Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Mout (K v)) (h v)),
      IsRawMassModel π K Mout (c * R) (Real.sqrt Cc * C) Tm ∧
      (edgeFree → IsRawMassL2 π K Mout
        (1 + Real.sqrt (Cc * patchBudgetUniform hζ Kmax L) * CP * E ^ Pacc) Tm) ∧
      IsRawMassError π K Mout D ν tS tp ρs ρold E Pacc
        (Real.sqrt (Cc * patchBudgetUniform hζ Kmax L) * CP) b A Tm := by
  obtain ⟨S⟩ := nonempty_patchSum hζ hR hR1 hB1G
  exact ⟨S.Tm, S.model_clause hB3 hπ hR hR1 hn hc hCc.le (hcnt S.N S.hN8 S.hN9),
    fun hedge => S.l2_clause hB3 hπ Kmax hR hR1 hn hρs hCc.le hε hρ0.le hL (hmesh S.N S.hN9)
      (hcnt S.N S.hN8 S.hN9) (hB2G S.N S.hN) hedge (hcontr hedge),
    S.error_clause hB3 hπ hK hR hR1 hn hρs hCc.le hε hρ0.le hL (hmesh S.N S.hN9)
      (hcnt S.N S.hN8 S.hN9) (hB2G S.N S.hN)⟩


end Family

/-- **The core from the patch statements.** -/
theorem rawJoint_of_patches (hB1 : PatchJointStatement.{u, v, w, x})
    (hB2 : PlaneTorusStatement.{u, v, w, x}) (hB3 : PeriodizedRadialSumStatement.{v})
    (hB3b : CentreCountingStatement) (hB4 : ScalarContractionVanishingStatement.{u, v}) :
    RawJointStatement.{u, v, w, x} := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, hΛ⟩ := hB1 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛΛ => ?_⟩
  obtain ⟨g₀, hg₀, hg₀8, hP⟩ := hΛ Λ hΛΛ
  refine ⟨g₀, hg₀, fun Pacc hPacc Mout H D Kmax hD => ?_⟩
  obtain ⟨Ks, Ls, Jm, qJ, Jchart, hch, hmol, hcst⟩ := hP Pacc hPacc Mout H D Kmax hD
  refine ⟨Ks, Ls, Jm, qJ, Jchart, hch, hmol,
    fun Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad hcMol hcOld => ?_⟩
  obtain ⟨C, CP, c, mStar, n, hc, hC, hCP, hn, hfam⟩ :=
    hcst Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad hcMol hcOld
  obtain ⟨Cc, hCc, hcount⟩ := hB3b n (by omega)
  refine ⟨Real.sqrt Cc * C, Real.sqrt (Cc * patchBudgetUniform hζ Kmax (max 1 (9 * COld))) * CP,
    c, mStar, hc, mul_nonneg (Real.sqrt_nonneg _) hC, mul_nonneg (Real.sqrt_nonneg _) hCP, ?_⟩
  intro ι _ _ h _ _ _ _ _ _ π hπ K hK Φ hΦ M' κ hband m hm2 hmStar hmM ν B hν hB hφ
    tS g a B₀ lam l₀ P y₀ cov P' Ctx F hwmeas hprep actual hdepth hdesc htorus hcover hmeas
    A Θ hΘ₀ hΘ₁ henv hpointwise htrans hquiet T hTcons hTcov hTq ρold hρold hρrat
  have hΛ128 : 128 ≤ Λ := hΛ₀.trans hΛΛ
  have hprem : JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb cMol cOld COld
      Crat Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T ρold :=
    ⟨hπ, hK, hΦ, hband, hm2, hmStar, hmM, hν, hB, cov, hwmeas, hprep, hdepth, hdesc, htorus,
      hcover, hmeas, hΘ₀, hΘ₁, henv, hpointwise, htrans, hquiet, hTcons, hTcov, hTq, hρold,
      hρrat⟩
  obtain ⟨hR, hR1, heR, hρ0, hCOld, hρe, htSp, htpS, hshort⟩ :=
    patch_scale_facts hα₀ hα₁ hs₀ hs₁ hq hζ hΛ128 hband hm2 hmM hν hB cov hcOld hρold
  have hτ : 0 < ocTauPP α q Λ m := Construction.Stream.ocTauPP_pos (le_trans (by norm_num) hΛ128)
  obtain ⟨hadm, -⟩ := hΦ.2 (m + 1) (by omega)
  rw [Nat.add_sub_cancel] at hadm
  have hmeshF : ∀ N : ℕ, (N : ℝ) * Real.sqrt (B * ocTauPP α q Λ m) ≤ 9 →
      ρold * (N : ℝ) ≤ max 1 (9 * COld) := by
    intro N hN9
    calc ρold * (N : ℝ) ≤ COld * Real.sqrt (B * ocTauPP α q Λ m) * N :=
          mul_le_mul_of_nonneg_right (hρe.trans (mul_le_mul_of_nonneg_left heR hCOld.le))
            (Nat.cast_nonneg N)
      _ = COld * (N * Real.sqrt (B * ocTauPP α q Λ m)) := by ring
      _ ≤ COld * 9 := mul_le_mul_of_nonneg_left hN9 hCOld.le
      _ ≤ max 1 (9 * COld) := le_max_of_le_right (by linarith)
  have hz : (∀ v u, IsEmpty (F.Γ v u)) → ∀ v u d t z, edgeCoefficient F ν (ocEpsilon q Λ m)
      (ocEpsilon q Λ (m - 1)) actual (fun _ => 0) v u d t z = 0 := fun hedge v u d t z =>
    edgeCoefficient_eq_zero_of_isEmpty F hedge ν _ _ actual _ v u d t z
  exact rawJoint_family_step hB3 hζ hCc π hπ K hK _ _ _ _ _ hR hR1 (by omega) hc
    (lt_of_lt_of_le cov.pos.2.2 le_rfl) hρ0 (le_max_left _ _) hmeshF
    (mul_nonneg hCP (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos
      (le_trans (by norm_num) hΛ128)).le _))
    (fun N hN8 hN9 => hcount (Φ (m - 1)) hφ tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m)
      (ocTauPP α q Λ m) g (Real.sqrt (B * ocTauPP α q Λ m)) N htSp htpS hτ
      cov.g_range.1 (cov.g_range.2.trans hg₀8) hshort hR hN8 hN9)
    (hfam π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold hprem)
    (hB2 α q Λ ζ hζ hΛ128 g₀ H D Kmax Ks Ls Jm qJ Jchart hD hch hmol Ca Cth Cb cMol
      cOld COld Crat Cm CG Cchart Cpad Cage Npad mStar hcMol π K Φ M' κ m ν B hφ tS g a B₀ lam l₀
      P y₀ F actual A Θ T ρold hprem)
    (fun hedge f u w hs i => hB4 (Φ m) hadm ν tS _ cov.pos.1 D _ (hz hedge) f u w hs i _
      ⟨htSp, le_rfl⟩)

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **Levels A and B at an abstract radius**.

* `jointPremisesGen_of_jointPremises`: the cascade premises give the abstract ones at the radius
  `r = ocRhoMol α q Λ m cMol ν` (`ρold ≤ COld √(B τ'')` from `patch_scale_facts`).
* `jointPremises_of_gen`: conversely, the abstract premises at `(r, ρold)` are the cascade premises
  for the constants `cMol = r / √(ν / A_m)` and `cOld = COld = ρold / ε_m^{1+γ/2+δ}`.
* `planeTorusGen_of`: hence the plane-solution statement at an abstract radius follows from `PlaneTorusStatement` (its constants are all
  universally quantified and its conclusion has no radius).
* `patchJoint_of_gen`: the one-patch statement at the cascade radius is the instance of the one-patch statement at an abstract radius.
* `rawJointGen_of_patches`: the core at an abstract radius from the one-patch statement at an
  abstract radius, the plane-solution statement, periodized sums, centre counting and scalar
  contraction (the glue of `rawJoint_of_patches`, which is generic in the radii inside). -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly
attribute [local instance] scalarResidualTorusNormed scalarResidualTorusInner
    scalarResidualTorusSpace scalarResidualPlaneNormed scalarResidualPlaneInner
    scalarResidualPlaneSpace scalarResidualPiAdd scalarResidualPiModule scalarResidualPlanePiAdd
    scalarResidualPlanePiModule

section Premises

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {ρold : ℝ}

/-- The cascade premises are the abstract premises at the cascade radius. -/
theorem jointPremisesGen_of_jointPremises {s : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ)
    {cMol cOld COld : ℝ} (hcOld : 0 < cOld)
    (hprem : JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb cMol cOld COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T ρold) :
    JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T (ocRhoMol α q Λ m cMol ν) ρold := by
  obtain ⟨-, -, heR, hρ0, hCOld, hρe, -⟩ := patch_scale_facts hα₀ hα₁ hs₀ hs₁ hq hζ hΛ
    hprem.hband hprem.hm2 hprem.hmM hprem.hν hprem.hB hprem.cov hcOld hprem.hρold
  exact
    { hπ := hprem.hπ, hK := hprem.hK, hΦ := hprem.hΦ, hband := hprem.hband, hm2 := hprem.hm2,
      hmStar := hprem.hmStar, hmM := hprem.hmM, hν := hprem.hν, hB := hprem.hB,
      cov := hprem.cov, hwmeas := hprem.hwmeas, hprep := hprem.hprep, hdepth := hprem.hdepth,
      hdesc := hprem.hdesc, htorus := hprem.htorus, hcover := hprem.hcover,
      hmeas := hprem.hmeas, hΘ₀ := hprem.hΘ₀, hΘ₁ := hprem.hΘ₁, henv := hprem.henv,
      hpointwise := hprem.hpointwise, htrans := hprem.htrans, hquiet := hprem.hquiet,
      hTcons := hprem.hTcons, hTcov := hprem.hTcov, hTq := hprem.hTq, hρpos := hρ0,
      hρR := hρe.trans (mul_le_mul_of_nonneg_left heR hCOld.le), hρrat := hprem.hρrat }

/-- The abstract premises at `(r, ρold)` are the cascade premises for the constants
`cMol = r / √(ν / A_m)` and `cOld = COld = ρold / ε_m^{1+γ/2+δ}`. -/
theorem jointPremises_of_gen {COld : ℝ} {r : ℝ} (hΛ : 1 ≤ Λ)
    (hprem : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) :
    JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb
      (r / Real.sqrt (ν / ocA α q Λ m))
      (ρold / ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q))
      (ρold / ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q)) Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T ρold := by
  have he : 0 < ocEpsilon q Λ m := Construction.Stream.ocEpsilon_pos hΛ
  have hA : 0 < ocA α q Λ m := by
    unfold ocA
    exact Real.rpow_pos_of_pos he _
  have hs : Real.sqrt (ν / ocA α q Λ m) ≠ 0 :=
    (Real.sqrt_pos.mpr (div_pos hprem.cov.pos.1 hA)).ne'
  have hrr : ocRhoMol α q Λ m (r / Real.sqrt (ν / ocA α q Λ m)) ν = r := by
    unfold ocRhoMol
    exact div_mul_cancel₀ r hs
  have hp : ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q) ≠ 0 :=
    (Real.rpow_pos_of_pos he _).ne'
  have hρeq : ρold / ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q) *
      ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q) = ρold :=
    div_mul_cancel₀ ρold hp
  exact
    { hπ := hprem.hπ, hK := hprem.hK, hΦ := hprem.hΦ, hband := hprem.hband, hm2 := hprem.hm2,
      hmStar := hprem.hmStar, hmM := hprem.hmM, hν := hprem.hν, hB := hprem.hB,
      cov := by rw [hrr]; exact hprem.cov, hwmeas := hprem.hwmeas, hprep := hprem.hprep,
      hdepth := hprem.hdepth, hdesc := hprem.hdesc, htorus := hprem.htorus,
      hcover := hprem.hcover, hmeas := hprem.hmeas, hΘ₀ := hprem.hΘ₀, hΘ₁ := hprem.hΘ₁,
      henv := by rw [hrr]; exact hprem.henv,
      hpointwise := by rw [hrr]; exact hprem.hpointwise, htrans := hprem.htrans,
      hquiet := hprem.hquiet, hTcons := hprem.hTcons, hTcov := hprem.hTcov, hTq := hprem.hTq,
      hρold := ⟨hρeq.le, hρeq.ge⟩, hρrat := by rw [hrr]; exact hprem.hρrat }

end Premises

/-- **The plane-solution statement at an abstract radius** from `PlaneTorusStatement`. -/
theorem planeTorusGen_of (hB2 : PlaneTorusStatement.{u, v, w, x}) :
    PlaneTorusGenStatement.{u, v, w, x} := by
  intro α q Λ ζ hζ hΛ g₀ H D Kmax Ks Ls Jm qJ Jchart hD hchart hmol Ca Cth Cb COld Crat Cm CG
    Cchart Cpad Cage Npad mStar ι _ _ h _ _ _ _ _ _ π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ P'
    Ctx F actual A Θ T r ρold hprem N hN
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hΛ
  have hA : 0 < ocA α q Λ m := by
    unfold ocA
    exact Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos hΛ1) _
  exact hB2 α q Λ ζ hζ hΛ g₀ H D Kmax Ks Ls Jm qJ Jchart hD hchart hmol Ca Cth Cb _ _ _ Crat Cm
    CG Cchart Cpad Cage Npad mStar
    (div_pos hprem.cov.pos.2.2 (Real.sqrt_pos.mpr (div_pos hprem.cov.pos.1 hA)))
    π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold (jointPremises_of_gen hΛ1 hprem)
    N hN

/-- **The one-patch statement at the cascade radius** is the instance of the one-patch statement at an abstract radius. -/
theorem patchJoint_of_gen (hg : PatchJointGenStatement.{u, v, w, x}) :
    PatchJointStatement.{u, v, w, x} := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, hΛ⟩ := hg α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛΛ => ?_⟩
  obtain ⟨g₀, hg₀, hg₀8, hP⟩ := hΛ Λ hΛΛ
  refine ⟨g₀, hg₀, hg₀8, fun Pacc hPacc Mout H D Kmax hD => ?_⟩
  obtain ⟨Ks, Ls, Jm, qJ, Jchart, hch, hmol, hcst⟩ := hP Pacc hPacc Mout H D Kmax hD
  refine ⟨Ks, Ls, Jm, qJ, Jchart, hch, hmol,
    fun Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad _ hcOld => ?_⟩
  obtain ⟨C, CP, c, mStar, n, hc, hC, hCP, hn, hfam⟩ :=
    hcst Ca Cth Cb COld Crat Cm CG Cchart Cpad Cage Npad
  refine ⟨C, CP, c, mStar, n, hc, hC, hCP, hn, ?_⟩
  intro ι _ _ h _ _ _ _ _ _ π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ P' Ctx F actual A Θ T ρold
    hprem
  exact hfam π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T _ ρold
    (jointPremisesGen_of_jointPremises hα₀ hα₁ hs₀ hs₁ hq hζ (hΛ₀.trans hΛΛ) hcOld hprem)

/-- **The core at an abstract radius** from the patch statements. -/
theorem rawJointGen_of_patches (hB1 : PatchJointGenStatement.{u, v, w, x})
    (hB2 : PlaneTorusStatement.{u, v, w, x}) (hB3 : PeriodizedRadialSumStatement.{v})
    (hB3b : CentreCountingStatement) (hB4 : ScalarContractionVanishingStatement.{u, v}) :
    RawJointGenStatement.{u, v, w, x} := by
  have hB2g := planeTorusGen_of hB2
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, hΛ⟩ := hB1 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛΛ => ?_⟩
  obtain ⟨g₀, hg₀, hg₀8, hP⟩ := hΛ Λ hΛΛ
  refine ⟨g₀, hg₀, fun Pacc hPacc Mout H D Kmax hD => ?_⟩
  obtain ⟨Ks, Ls, Jm, qJ, Jchart, hch, hmol, hcst⟩ := hP Pacc hPacc Mout H D Kmax hD
  refine ⟨Ks, Ls, Jm, qJ, Jchart, hch, hmol,
    fun Ca Cth Cb COld Crat Cm CG Cchart Cpad Cage Npad => ?_⟩
  obtain ⟨C, CP, c, mStar, n, hc, hC, hCP, hn, hfam⟩ :=
    hcst Ca Cth Cb COld Crat Cm CG Cchart Cpad Cage Npad
  obtain ⟨Cc, hCc, hcount⟩ := hB3b n (by omega)
  refine ⟨Real.sqrt Cc * C, Real.sqrt (Cc * patchBudgetUniform hζ Kmax (max 1 (9 * COld))) * CP,
    c, mStar, hc, mul_nonneg (Real.sqrt_nonneg _) hC, mul_nonneg (Real.sqrt_nonneg _) hCP, ?_⟩
  intro ι _ _ h _ _ _ _ _ _ π hπ K hK Φ hΦ M' κ hband m hm2 hmStar hmM ν B hν hB hφ
    tS g a B₀ lam l₀ P y₀ r cov P' Ctx F hwmeas hprep actual hdepth hdesc htorus hcover hmeas
    A Θ hΘ₀ hΘ₁ henv hpointwise htrans hquiet T hTcons hTcov hTq ρold hρpos hρR hρrat
  have hΛ128 : 128 ≤ Λ := hΛ₀.trans hΛΛ
  have hprem : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold :=
    { hπ := hπ, hK := hK, hΦ := hΦ, hband := hband, hm2 := hm2, hmStar := hmStar,
      hmM := hmM, hν := hν, hB := hB, cov := cov, hwmeas := hwmeas, hprep := hprep,
      hdepth := hdepth, hdesc := hdesc, htorus := htorus, hcover := hcover, hmeas := hmeas,
      hΘ₀ := hΘ₀, hΘ₁ := hΘ₁, henv := henv, hpointwise := hpointwise, htrans := htrans,
      hquiet := hquiet, hTcons := hTcons, hTcov := hTcov, hTq := hTq, hρpos := hρpos,
      hρR := hρR, hρrat := hρrat }
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hΛ128
  -- the radius-free scale facts (`patch_scale_facts` at the prepared radius `ε_m^{1+γ/2+δ}`)
  obtain ⟨hR, hR1, -, -, -, -, htSp, htpS, hshort⟩ :=
    patch_scale_facts hα₀ hα₁ hs₀ hs₁ hq hζ hΛ128 hband hm2 hmM hν hB cov one_pos
      (ρold := ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q)) (COld := 1)
      ⟨(one_mul _).le, (one_mul _).ge⟩
  have hτ : 0 < ocTauPP α q Λ m := Construction.Stream.ocTauPP_pos hΛ1
  obtain ⟨hadm, -⟩ := hΦ.2 (m + 1) (by omega)
  rw [Nat.add_sub_cancel] at hadm
  have hCOld : 0 ≤ COld := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg hR
    linarith
  have hmeshF : ∀ N : ℕ, (N : ℝ) * Real.sqrt (B * ocTauPP α q Λ m) ≤ 9 →
      ρold * (N : ℝ) ≤ max 1 (9 * COld) := by
    intro N hN9
    calc ρold * (N : ℝ) ≤ COld * Real.sqrt (B * ocTauPP α q Λ m) * N :=
          mul_le_mul_of_nonneg_right hρR (Nat.cast_nonneg N)
      _ = COld * (N * Real.sqrt (B * ocTauPP α q Λ m)) := by ring
      _ ≤ COld * 9 := mul_le_mul_of_nonneg_left hN9 hCOld
      _ ≤ max 1 (9 * COld) := le_max_of_le_right (by linarith)
  have hz : (∀ v u, IsEmpty (F.Γ v u)) → ∀ v u d t z, edgeCoefficient F ν (ocEpsilon q Λ m)
      (ocEpsilon q Λ (m - 1)) actual (fun _ => 0) v u d t z = 0 := fun hedge v u d t z =>
    edgeCoefficient_eq_zero_of_isEmpty F hedge ν _ _ actual _ v u d t z
  exact rawJoint_family_step hB3 hζ hCc π hπ K hK _ _ _ _ _ hR hR1 (by omega) hc
    cov.pos.2.2 hρpos (le_max_left _ _) hmeshF
    (mul_nonneg hCP (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _))
    (fun N hN8 hN9 => hcount (Φ (m - 1)) hφ tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m)
      (ocTauPP α q Λ m) g (Real.sqrt (B * ocTauPP α q Λ m)) N htSp htpS hτ
      cov.g_range.1 (cov.g_range.2.trans hg₀8) hshort hR hN8 hN9)
    (hfam π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T r ρold hprem)
    (hB2g α q Λ ζ hζ hΛ128 g₀ H D Kmax Ks Ls Jm qJ Jchart hD hch hmol Ca Cth Cb COld Crat Cm CG
      Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T r ρold
      hprem)
    (fun hedge f u w hs i => hB4 (Φ m) hadm ν tS _ cov.pos.1 D _ (hz hedge) f u w hs i _
      ⟨htSp, le_rfl⟩)

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The route to `cycle_joint` through the one-patch statement**. `cycle_joint` follows from the
ingredients other than the core (path reduction, mean conservation, normalization) and the
ingredients of the core (the one-patch statement per patch, plane/torus periodization, periodized sums,
centre counting, scalar contraction, in their stated forms; the bridges of the module
`CycleJoint.Assembly.PatchBridges` give the forms used by `rawJoint_of_patches`). The
patch statements are used at index universe `0` (the core is applied to path families). -/

@[expose] public section

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly
attribute [local instance] scalarResidualTorusNormed scalarResidualTorusInner
    scalarResidualTorusSpace scalarResidualPlaneNormed scalarResidualPlaneInner
    scalarResidualPlaneSpace scalarResidualPiAdd scalarResidualPiModule scalarResidualPlanePiAdd
    scalarResidualPlanePiModule

/-- **`cycle_joint` from its ingredients and the ingredients of its core.** -/
theorem cycle_joint_route (hB1 : PatchJointStatement.{0, v, w, x})
    (hB2 : PlaneTorusStatement.{0, v, w, x}) (hB3 : PeriodizedSumStatement.{v, 0})
    (hB3b : CentreCountingStatement) (hB4 : ScalarContractionStatement.{0, v})
    (hpath : PathReductionStatement.{u, v, w, x}) (hmean : MeanConservationStatement.{u, v})
    (hnorm : NormalizationStatement.{u, v, w, x}) : CycleJointStatement.{u, v, w, x} :=
  cycle_joint_of_ingredients (rawJoint_of_patches hB1 hB2
    (periodizedRadialSum_of_periodizedSum hB3) hB3b
    (scalarContractionVanishing_of_scalarContraction hB4)) hpath hmean hnorm

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs.Assembly

/-! The scalar energy argument bundles its drift inputs and retains the exact order-zero norm. -/

attribute [local instance] scalarResidualTorusNormed scalarResidualTorusInner
    scalarResidualTorusSpace scalarResidualPlaneNormed scalarResidualPlaneInner
    scalarResidualPlaneSpace scalarResidualPiAdd scalarResidualPiModule scalarResidualPlanePiAdd
    scalarResidualPlanePiModule

/-- The finite set of qualitative drift inputs consumed by Fourier energy testing. -/
structure ScalarDriftWindow (v : ℝ → Vec 2 → Vec 2) (a b : ℝ) where
  V : ℝ
  nonneg : 0 ≤ V
  measurable : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2)
  smooth : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t)
  periodic : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t)
  bounded : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V
  divergence : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0

/-- Admissibility proves every drift input; none is an additional premise. -/
theorem scalarDriftWindow_of_stream (φ : ℝ → Vec 2 → ℝ)
    (hφ : AVenhance.IsAdmissibleStream φ) (a b : ℝ) :
    Nonempty (ScalarDriftWindow (AVenhance.streamVel φ) a b) := by
  have hs := AVenhance.Infra.Classical.streamVel_smoothPeriodic φ hφ
  obtain ⟨V, hV, hb⟩ := AVenhance.Infra.Classical.streamVel_global_derivative_bound φ hφ 0
  refine ⟨⟨V, hV, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact hs.smooth.continuous.measurable.comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  · intro t _
    exact hs.smooth.comp (contDiff_const.prodMk contDiff_id)
  · intro t _ k x
    simpa only [Int.cast_zero, add_zero] using hs.periodic 0 k t x
  · intro t _ x
    simpa only [norm_iteratedFDeriv_zero, Function.uncurry_def] using hb (t, x)
  · intro t _ x
    simpa only [AVenhance.Infra.Flow.spatialDivergence,
      AVenhance.Infra.Flow.jointSpatialFDeriv_eq_slice hs, Fin.sum_univ_two,
      AVenhance.Infra.Flow.Liouville.flowBasis0, AVenhance.Infra.Flow.Liouville.flowBasis1, basisVec] using
      AVRegularity.Velocity.Port.Section2FlowIdentities.streamVel_spatialDivergence_eq_zero hφ t x

instance scalarContractionZeroOrdersIsEmpty {ι : Type*} (K : ι → ℕ) (i j : ι) :
    IsEmpty (admissibleOrders K 0 i j) := ⟨fun d => by
      have hd := Finset.mem_Icc.mp (Finset.mem_filter.mp d.property).1
      omega⟩

/-- Integrate the exact energy inequality with a bound from the supplied continuous trace. -/
theorem scalar_bounded_energy_integrated {ν a b S : ℝ} {E R G F : ℝ → ℝ}
    (hab : a ≤ b) (hν : 0 ≤ ν) (hS : 0 ≤ S)
    (hac : AbsolutelyContinuousOnInterval E a b)
    (hr : IntervalIntegrable R volume a b) (hg : IntervalIntegrable G volume a b)
    (hf : IntervalIntegrable F volume a b)
    (hrn : ∀ t ∈ Set.Icc a b, 0 ≤ R t) (hgn : ∀ t, 0 ≤ G t)
    (hb : ∀ t ∈ Set.Icc a b, E t ≤ S ^ 2)
    (hd : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      deriv E t + ν * R t ≤ 2 * G t * Real.sqrt (E t) + (4 / ν) * F t) :
    E b ≤ E a + 2 * S * (∫ t in a..b, G t) + (4 / ν) * (∫ t in a..b, F t) := by
  have hd' : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      deriv E t + ν * R t ≤ 2 * S * G t + (4 / ν) * F t := by
    filter_upwards [hd, ae_restrict_mem measurableSet_Icc] with t hdt ht
    have hsq : Real.sqrt (E t) ≤ S := by
      simpa only [Real.sqrt_sq hS] using Real.sqrt_le_sqrt (hb t ht)
    have hh := mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hgn t))
    have hh' : 2 * G t * Real.sqrt (E t) + (4 / ν) * F t ≤
        2 * G t * S + (4 / ν) * F t := add_le_add hh le_rfl
    exact hdt.trans (hh'.trans_eq (by ring))
  have hi := coupledTimeEnergy_integrated_of_deriv_le hab hac hr hg hf hd'
  have hpos := intervalIntegral.integral_nonneg (μ := volume) hab hrn
  exact (le_add_of_nonneg_right (mul_nonneg hν hpos)).trans hi

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, MeasurableSpace (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Empty coupling orders discharge the Schur condition for every positive mass choice. -/
theorem scalar_zero_schur (ν a b : ℝ) (π : ι → ℝ) :
    SchurCondition (schurMatrix (h := h) ν 1 π (fun _ => 0) 0 a b (fun _ _ _ _ _ => 0)) := by
  simp only [SchurCondition, schurMatrix, Finset.univ_eq_empty, Finset.sum_empty, mul_zero,
    Finset.sum_const_zero]
  constructor <;> intro i <;> norm_num

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- At slot zero the factorial energy is exactly the carrier square norm. -/
theorem scalar_factorial_norm (ρ : ℝ) (i : ι) (U : TorusHk 0 (h i)) :
    factorialNormSq ρ U.val = ‖U‖ ^ 2 := by
  change factorialNormSq ρ U.val = ‖U.val‖ ^ 2
  rw [jet_norm_sq_eq_sum]
  simp only [factorialNormSq, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.val_zero, factorialWeight, Nat.mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, one_pow, div_one, one_mul, add_zero]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- Scalar mass is the ordinary positive weighted sum of component square norms. -/
theorem scalar_mass_norm (ρ : ℝ) (π : ι → ℝ) (U : ∀ i, TorusHk 0 (h i)) :
    massNormSq ρ π (fun i => (U i).val) = ∑ i, (π i)⁻¹ * ‖U i‖ ^ 2 := by
  simp only [massNormSq, scalar_factorial_norm]

/-- Fourier projection is a contraction for every order-zero mass choice. -/
theorem scalar_projected_mass_le (N : ℕ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (U : ∀ i, TorusHk 0 (h i)) :
    massNormSq 1 π (fun i => (galerkinProj N (U i)).val) ≤ massNormSq 1 π (fun i => (U i).val) := by
  rw [scalar_mass_norm, scalar_mass_norm]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (galerkinProj_norm_le N (U i)) 2) (inv_pos.mpr (hπ i)).le

/-- The weak identity permits deleting a coupling whose coefficients are all zero. -/
theorem scalar_weak_solution_no_coupling (ν a b : ℝ) (v : ℝ → Vec 2 → Vec 2) (D : ℕ)
    (f : ∀ i, TorusHk 0 (h i)) (u : ∀ i, ℝ → TorusHk 0 (h i))
    (w : ∀ i, ℝ → TorusHk 1 (h i))
    (hs : IsCoupledWeakSolutionTorus ν a b v D (fun _ => 0) (fun _ _ _ _ _ => 0)
      f (fun _ _ => 0) (fun _ _ => 0) u w) :
    IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => 0) (fun _ _ _ _ _ => 0)
      f (fun _ _ => 0) (fun _ _ => 0) u w := by
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro i t ht φ
  simpa only [zero_apply, Finset.sum_const_zero] using hs.2.2.2.2 i t ht φ

/-- Restrict a source-free scalar solution to an earlier terminal time. -/
theorem scalar_weak_solution_restrict (ν a b t : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (ht : t ≤ b) (f : ∀ i, TorusHk 0 (h i)) (u : ∀ i, ℝ → TorusHk 0 (h i))
    (w : ∀ i, ℝ → TorusHk 1 (h i))
    (hs : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => 0) (fun _ _ _ _ _ => 0)
      f (fun _ _ => 0) (fun _ _ => 0) u w) :
    IsCoupledWeakSolutionTorus ν a t v 0 (fun _ => 0) (fun _ _ _ _ _ => 0)
      f (fun _ _ => 0) (fun _ _ => 0) u w := by
  have hsub : Set.Icc a t ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl ht
  have hm : volume.restrict (Set.Icc a t) ≤ volume.restrict (Set.Icc a b) :=
    Measure.restrict_mono hsub le_rfl
  exact ⟨fun i => (hs.1 i).mono hsub, fun i => (hs.2.1 i).mono_measure hm,
    fun i => (hs.2.2.1 i).filter_mono (ae_mono hm), hs.2.2.2.1,
    fun i s hs' φ => hs.2.2.2.2 i s (hsub hs') φ⟩

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.CycleJointProofs.Assembly

/-! Exact scalar mass contraction follows by vanishing Fourier residual budgets. -/

attribute [local instance] scalarResidualTorusNormed scalarResidualTorusInner
    scalarResidualTorusSpace scalarResidualPlaneNormed scalarResidualPlaneInner
    scalarResidualPlaneSpace scalarResidualPiAdd scalarResidualPiModule scalarResidualPlanePiAdd
    scalarResidualPlanePiModule

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [DecidableEq ι] in
/-- Every source-free scalar weak solution contracts every positive weighted mass. -/
theorem scalar_endpoint_mass_contraction (ν a b : ℝ) (hab : a ≤ b) (hν : 0 < ν)
    (v : ℝ → Vec 2 → Vec 2) (Bv : ScalarDriftWindow v a b)
    (f : ∀ i, TorusHk 0 (h i)) (u : ∀ i, ℝ → TorusHk 0 (h i))
    (w : ∀ i, ℝ → TorusHk 1 (h i))
    (hs : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => 0) (fun _ _ _ _ _ => 0)
      f (fun _ _ => 0) (fun _ _ => 0) u w)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) :
    massNormSq 1 π (fun i => (u i b).val) ≤ massNormSq 1 π (fun i => (f i).val) := by
  classical
  let K : ι → ℕ := fun _ => 0
  let A : ∀ i i', (d : admissibleOrders K 0 i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i) :=
    fun _ _ _ _ _ => 0
  have hA : ∀ i i' d, coefficientSeminorm 1 (K i) a b (A i i' d) ≠ ⊤ :=
    fun _ _ d => isEmptyElim d
  have hmA : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2) :=
    fun _ _ d => isEmptyElim d
  have hc : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t) :=
    fun _ _ _ _ d => isEmptyElim d
  have hp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t) :=
    fun _ _ _ _ d => isEmptyElim d
  let C : ∀ i, Fin (K i + 1) → ℝ := fun _ _ => 2 * Bv.V
  have hC : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ C i l := by
    intro t ht i l x
    have hl : l.val = 0 := by have hh := l.isLt; dsimp only [K] at hh; omega
    rw [hl, coefficientDerivativeArray_zero_norm]
    exact driftCoefficient_norm_le _ Bv.V Bv.nonneg (Bv.bounded t ht) x
  have hF : ∀ i, MemLp (fun _ : ℝ => (0 : TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))))
      2 (volume.restrict (Set.Icc a b)) := fun i => timeMemLp_zero _ _
  have hg : ∀ i, Integrable (fun _ : ℝ => (0 : TorusHk (K i) (h i)))
      (volume.restrict (Set.Icc a b)) := fun i => timeIntegrable_zero _
  let z := fun N i t => w i t - galerkinProj N (w i t)
  let RF := fun N i t => (0 : TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))) +
    torusSpatialFluxPath K 0 a b ν 1 (by norm_num) A hA hc hp (z N) i t
  let Rg := fun N i t => (0 : TorusHk (K i) (h i)) -
    plainTransportCarrierPath K a b v Bv.smooth Bv.periodic C hC (z N) i t
  have hcontinuous : ContinuousOn (fun t => massNormSq 1 π (fun i => (u i t).val)) (Set.Icc a b) := by
    have hu : ContinuousOn (fun t i => u i t) (Set.Icc a b) := continuousOn_pi.mpr hs.1
    have hh := ((massWeightedCarrierCLM (E := h) K 1 π).continuous.comp_continuousOn hu).norm.pow 2
    apply hh.congr
    intro t _
    exact (massWeightedCarrierCLM_normSq K 1 π hπ (fun i => u i t)).symm
  obtain ⟨tmax, htmax, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, le_rfl, hab⟩ hcontinuous
  let S := Real.sqrt (massNormSq 1 π (fun i => (u i tmax).val))
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hbound (t : ℝ) (ht : t ∈ Set.Icc a b) : massNormSq 1 π (fun i => (u i t).val) ≤ S ^ 2 := by
    rw [Real.sq_sqrt (massNormSq_nonneg 1 π hπ _)]
    exact hmax ht
  have hineq (N : ℕ) :
      massNormSq 1 π (fun i => (galerkinProj N (u i b)).val) ≤
        massNormSq 1 π (fun i => (galerkinProj N (f i)).val) +
          2 * S * (∫ t in Set.Icc a b, Real.sqrt (massNormSq 1 π (fun i => (Rg N i t).val))) +
          (4 / ν) * (∫ t in Set.Icc a b, massNormSq 1 π (fun i => (RF N i t).val)) := by
    obtain ⟨y, hycont, hy, hint, hode⟩ := plainWeakSolution_residualODE_exists N K 0 ν 1
      (by norm_num) a b hab v Bv.measurable Bv.smooth Bv.periodic Bv.V Bv.nonneg Bv.bounded
      C hC A hA hmA hc hp (fun _ _ => 0) (fun _ _ => 0) w u f hF hg hs
    have hsyn (t : ℝ) (ht : t ∈ Set.Icc a b) (i : ι) :
        coupledPlainSynthesis N i (K i) (y t) = galerkinProj N (u i t) := by
      rw [hy t ht]
      exact plainInitialCoefficients_synthesis N K (fun j => u j t) i
    have hinit (i : ι) : coupledPlainSynthesis N i (K i) (y a) = galerkinProj N (f i) := by
      rw [hsyn a ⟨le_rfl, hab⟩ i, hs.2.2.2.1 i]
    have hzLp (i : ι) : MemLp (z N i) 2 (volume.restrict (Set.Icc a b)) := by
      simpa only [z, Pi.sub_apply, Function.comp_def] using!
        (hs.2.1 i).sub ((galerkinProj N).comp_memLp' (hs.2.1 i))
    have hRF (i : ι) : MemLp (RF N i) 2 (volume.restrict (Set.Icc a b)) :=
      torusForcedSpatialFluxPath_memLp K 0 a b ν 1 (by norm_num) A hA hc hp hab hmA
        (z N) hzLp (fun _ _ => 0) hF i
    have hRg (i : ι) : Integrable (Rg N i) (volume.restrict (Set.Icc a b)) := by
      have hh := plainTransportCarrierPath_memLp K a b v Bv.smooth Bv.periodic C hC
        hab 1 (by norm_num) Bv.measurable Bv.V Bv.nonneg Bv.bounded (z N) hzLp i
      simpa only [Rg, Pi.sub_apply] using! (hg i).sub (hh.integrable (by norm_num))
    have hd := plainODE_mass_deriv_energy_le N 0 ν 1 (by norm_num) K a b v A hA
      Bv.smooth Bv.periodic hc hp (RF N) (Rg N) hν π hπ 0 (fun _ => le_rfl) 0 1 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simpa using div_nonneg hν.le (by norm_num : (0 : ℝ) ≤ 8))
      Bv.divergence (fun _ _ l hl hl0 => by omega) (scalar_zero_schur ν a b π)
      hab y (plainInitialCoefficients N K f) hode hint
    have hEb (t : ℝ) (ht : t ∈ Set.Icc a b) :
        massNormSq 1 π (fun i => (coupledPlainSynthesis N i (K i) (y t)).val) ≤ S ^ 2 := by
      simp_rw [hsyn t ht]
      exact (scalar_projected_mass_le N π hπ (fun i => u i t)).trans (hbound t ht)
    have hac := plainSynthesis_mass_absolutelyContinuous N K 1 π (hode.absolutelyContinuousOnInterval hab hint)
    have hr := (plainSynthesis_massGrad_continuous N K 1 π hycont).intervalIntegrable (μ := volume) a b
    have hiF := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (massNormSq_integrable 1 π hπ (fun i => torusJet_memLp (K i) (hRF i)))
    have hiG := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (massNorm_integrable 1 π hπ (fun i => torusJet_memLp (K i) (memLp_one_iff_integrable.mpr (hRg i))))
    have he := scalar_bounded_energy_integrated hab hν.le hS hac hr hiG hiF
      (fun t _ => massGradNormSq_nonneg 1 π hπ _) (fun _ => Real.sqrt_nonneg _) hEb hd
    simpa only [hsyn b ⟨hab, le_rfl⟩, hinit, intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc] using he
  have hres := plainResidualSources_mass_limits K 0 ν 1 (by norm_num) a b hab v
    Bv.measurable Bv.smooth Bv.periodic Bv.V Bv.nonneg Bv.bounded C hC A hA hmA hc hp
    (fun _ _ => 0) (fun _ _ => 0) w hs.2.1 hF hg π hπ
  have hRF0 : Tendsto (fun N => ∫ t in Set.Icc a b, massNormSq 1 π (fun i => (RF N i t).val))
      atTop (𝓝 0) := by
    simpa only [RF, z, torusMassNormSq_zero K 1 π hπ, integral_zero] using hres.1
  have hRg0 : Tendsto (fun N => ∫ t in Set.Icc a b, Real.sqrt (massNormSq 1 π (fun i => (Rg N i t).val)))
      atTop (𝓝 0) := by
    simpa only [Rg, z, torusMassNormSq_zero K 1 π hπ, Real.sqrt_zero, integral_zero] using hres.2
  have hlim := ((galerkinProj_massNormSq_tendsto K 1 π hπ f).add
    (hRg0.const_mul (2 * S))).add (hRF0.const_mul (4 / ν))
  have hh := le_of_tendsto_of_tendsto (galerkinProj_massNormSq_tendsto K 1 π hπ (fun i => u i b))
    hlim (Eventually.of_forall hineq)
  simpa only [mul_zero, add_zero] using hh

end AVRegularity.CycleJointProofs.Assembly
end
end
