-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.Tested
public import AVRegularity.CycleComparison.Reconstruction.CoarseModesTested
import AVRegularity.Families.TorusCompatible.WeakStage
public import AVRegularity.CycleComparison.Reconstruction.InvPiola
import AVRegularity.CoupledEnergy.Galerkin.PlainTestedIntegralEquation
public import AVRegularity.Statements.Intermediate.CycleOutput.IsClassicalRep
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.CycleComparison.Coarse.Defect.DFBound
import AVRegularity.CycleComparison.Reconstruction.TailSample
public import AVRegularity.Statements.Intermediate.Families.AtlasIsConsecutiveClosed
public import AVRegularity.Statements.Intermediate.Families.AtlasCoversQuiet
public import AVRegularity.Statements.Intermediate.Families.AtlasIsQuiet
import AVRegularity.CycleComparison.Reconstruction.Orders
public import AVRegularity.CoupledEnergy.Galerkin.IntervalCoefficientSub
public import AVRegularity.Statements.Intermediate.CycleOutput.OcChartInv
import AVRegularity.CycleComparison.LiftSetting.Metric
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVenhance
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The tested label identity** (the physical reconstruction in the chart): if at every label `y`
the label field `V(·, y)` is of integral type with density `dV(·, y)`, and the test is transported
by the moving chart, `φ̃(t, y) = φ(χ(t, y))` with `∂_t χ = W(t, χ)`, then
`t ↦ ∫_{cell} ⟪V(t, y), φ̃(t, y)⟫ dy` is of integral type with density
`∫_{cell} ⟪dV, φ̃⟫ + ⟪V, ∇φ(χ)·W(χ)⟫`. The last term is the transport of the test by the background
flow; after the change of variables `x = χ(t, y)` it is the background drift. -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The tested label identity.** -/
theorem tested_label_prim {a b : ℝ} (hab : a ≤ b) (V dV : ℝ → Vec 2 → F)
    (hV : ∀ y, IsPrimOn a b (fun t => V t y) (fun t => dV t y))
    (χ W : ℝ → Vec 2 → Vec 2) (hχt : ∀ t y, HasDerivAt (fun t' => χ t' y) (W t (χ t y)) t)
    (φ : Vec 2 → F) (hφ : ContDiff ℝ 1 φ)
    (hφc : ∀ y, ContinuousOn (fun t => fderiv ℝ φ (χ t y) (W t (χ t y))) (Icc a b))
    (hint : Integrable (Function.uncurry fun t y =>
        inner ℝ (dV t y) (φ (χ t y)) + inner ℝ (V t y) (fderiv ℝ φ (χ t y) (W t (χ t y))))
      ((volume.restrict (Ioc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hinta : Integrable (fun y => inner ℝ (V a y) (φ (χ a y)))
      (volume.restrict AVenhance.unitCube)) :
    IsPrimOn a b (fun t => ∫ y in AVenhance.unitCube, inner ℝ (V t y) (φ (χ t y)))
      (fun t => ∫ y in AVenhance.unitCube,
        (inner ℝ (dV t y) (φ (χ t y)) + inner ℝ (V t y) (fderiv ℝ φ (χ t y) (W t (χ t y))))) := by
  refine IsPrimOn.integral hab (fun y => ?_) hint hinta
  have hd : ∀ t ∈ Icc a b, HasDerivAt (fun t' => φ (χ t' y))
      (fderiv ℝ φ (χ t y) (W t (χ t y))) t := fun t _ =>
    ((hφ.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t (hχt t y)
  exact IsPrimOn.inner_C1 hab (hV y) hd (hφc y)

/-- **The tested identity in physical coordinates.** Under a family of cell-preserving charts
`χ(t)` with lattice-equivariant inverses `ψ(t)`, the physical field `V(t, ψ(t,x))` tested against a
periodic `C¹` test `φ` is of integral type, with density the sampled label density tested against
`φ` plus the transport `⟪V(ψ), ∇φ · W⟫` of the test by the chart velocity `W`. -/
theorem tested_physical_prim {a b : ℝ} (hab : a ≤ b) (V dV : ℝ → Vec 2 → F)
    (hV : ∀ y, IsPrimOn a b (fun t => V t y) (fun t => dV t y))
    (hVp : ∀ t ∈ Icc a b, IsZ2Periodic (V t)) (hdVp : ∀ t ∈ Icc a b, IsZ2Periodic (dV t))
    (χ ψ W : ℝ → Vec 2 → Vec 2) (hχt : ∀ t y, HasDerivAt (fun t' => χ t' y) (W t (χ t y)) t)
    (hψχ : ∀ t y, ψ t (χ t y) = y)
    (hψp : ∀ t (n : Fin 2 → ℤ) x, ψ t (x + latticeShift n) = ψ t x + latticeShift n)
    (hWp : ∀ t, IsZ2Periodic (W t))
    (hcell : ∀ t (u : Vec 2 → ℝ), IsZ2Periodic u →
      ∫ y in AVenhance.unitCube, u (χ t y) = ∫ x in AVenhance.unitCube, u x)
    (φ : Vec 2 → F) (hφ : ContDiff ℝ 1 φ) (hφp : IsZ2Periodic φ)
    (hφc : ∀ y, ContinuousOn (fun t => fderiv ℝ φ (χ t y) (W t (χ t y))) (Icc a b))
    (hint : Integrable (Function.uncurry fun t y =>
        inner ℝ (dV t y) (φ (χ t y)) + inner ℝ (V t y) (fderiv ℝ φ (χ t y) (W t (χ t y))))
      ((volume.restrict (Ioc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hinta : Integrable (fun y => inner ℝ (V a y) (φ (χ a y)))
      (volume.restrict AVenhance.unitCube)) :
    IsPrimOn a b (fun t => ∫ x in AVenhance.unitCube, inner ℝ (V t (ψ t x)) (φ x))
      (fun t => ∫ x in AVenhance.unitCube,
        (inner ℝ (dV t (ψ t x)) (φ x) + inner ℝ (V t (ψ t x)) (fderiv ℝ φ x (W t x)))) := by
  have hφ'p : IsZ2Periodic (fderiv ℝ φ) := TorusCompatible.isZ2Periodic_fderiv hφp
  refine (tested_label_prim hab V dV hV χ W hχt φ hφ hφc hint hinta).congr hab
    (fun t ht => ?_) (fun t ht => ?_)
  · have hu : IsZ2Periodic (fun x => inner ℝ (V t (ψ t x)) (φ x)) := fun n x => by
      simp only [hψp, hVp t ht n, hφp n x]
    rw [← hcell t _ hu]
    simp only [hψχ]
  · have hu : IsZ2Periodic (fun x =>
        inner ℝ (dV t (ψ t x)) (φ x) + inner ℝ (V t (ψ t x)) (fderiv ℝ φ x (W t x))) :=
      fun n x => by simp only [hψp, hVp t ht n, hdVp t ht n, hφp n x, hφ'p n x, hWp t n x]
    rw [← hcell t _ hu]
    simp only [hψχ]

/-- **The tested identity in the renewal chart.** The specialization of
`tested_physical_prim` to the renewal chart `χ = Φ_{m,l}` (`ocChart`), its labels
`ψ = Φ_{m,l}⁻¹` (`ocChartInv`) and the background velocity `b_{m-1}` of the chart flow. -/
theorem tested_chart_prim (α q : ℝ) (Λ m : ℕ) {φs : ℝ → Vec 2 → ℝ}
    (hφs : IsAdmissibleStream φs) (l : ℤ) {a b : ℝ} (hab : a ≤ b) (V dV : ℝ → Vec 2 → F)
    (hV : ∀ y, IsPrimOn a b (fun t => V t y) (fun t => dV t y))
    (hVp : ∀ t ∈ Icc a b, IsZ2Periodic (V t)) (hdVp : ∀ t ∈ Icc a b, IsZ2Periodic (dV t))
    (φ : Vec 2 → F) (hφ : ContDiff ℝ 1 φ) (hφp : IsZ2Periodic φ)
    (hint : Integrable (Function.uncurry fun t y =>
        inner ℝ (dV t y) (φ (ocChart α q Λ m φs hφs l t y)) +
          inner ℝ (V t y) (fderiv ℝ φ (ocChart α q Λ m φs hφs l t y)
            (streamVel φs t (ocChart α q Λ m φs hφs l t y))))
      ((volume.restrict (Ioc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hinta : Integrable (fun y => inner ℝ (V a y) (φ (ocChart α q Λ m φs hφs l a y)))
      (volume.restrict AVenhance.unitCube)) :
    IsPrimOn a b
      (fun t => ∫ x in AVenhance.unitCube, inner ℝ (V t (ocChartInv α q Λ m φs hφs l t x)) (φ x))
      (fun t => ∫ x in AVenhance.unitCube,
        (inner ℝ (dV t (ocChartInv α q Λ m φs hφs l t x)) (φ x) +
          inner ℝ (V t (ocChartInv α q Λ m φs hφs l t x)) (fderiv ℝ φ x (streamVel φs t x)))) := by
  have hvel := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφs
  refine tested_physical_prim hab V dV hV hVp hdVp (ocChart α q Λ m φs hφs l)
    (ocChartInv α q Λ m φs hφs l) (streamVel φs) (ocChart_hasDerivAt_time α q Λ m hφs l)
    (Charts.ocChartInv_ocChart α q Λ m φs hφs l) (fun t n x => ?_) (fun t n x => ?_)
    (fun t u hu => CycleReference.streamFlow_cell_integral hφs t _ u hu) φ hφ hφp
    (fun y => ?_) hint hinta
  · exact CycleReference.streamFlow_lattice_equivariant hφs _ t x n
  · simpa using hvel.periodic 0 n t x
  · have hχc : Continuous (fun t => ocChart α q Λ m φs hφs l t y) :=
      (Charts.contDiff_ocChart_joint hφs α q Λ m l).continuous.comp
        (continuous_id.prodMk continuous_const)
    have hbc : Continuous (fun t => streamVel φs t (ocChart α q Λ m φs hφs l t y)) :=
      (ocChart_timeDeriv_contDiff α q Λ m hφs l).continuous.comp
        (continuous_id.prodMk continuous_const)
    exact (((hφ.continuous_fderiv one_ne_zero).comp hχc).clm_apply hbc).continuousOn

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Finite-rank Galerkin approximants of the coarse field.** The lift of a pulse acts
classically on the coarse field read in a moving chart, which needs a coarse field that is `C^∞` in
space at every time. The Fourier cutoff `galerkinProj n` of the coupled-energy Galerkin scheme has,
componentwise, the explicit smooth representative
`a_n(x) = ∑_r c_r e_r(x)`, `c_r = ∫_{cell} ⟪U_{r.1}, e_r⟫`,
over the finite index `r ∈ CoupledFourierModeIndex n` (component, real Fourier mode, fiber basis
vector; independent of `U`), with the smooth `ℤ²`-periodic real modes
`e_r = Pi.single r.1 (m_{r.2.1} · b_{r.2.2})` (`coupledModeJet`). Applied to the retained field
`W(t)` of a coarse defect, the coefficients `c_r(t)` are of integral type in time
(`CoarseModesTested`), so `a_n(t, x) = ∑_r c_r(t) e_r(x)` is a `chartField`-ready finite-rank
coarse field, and `a_n(t, ·)` is a classical representative of `galerkinProj n (W(t))` at every
order. -/

/-! ### Modes, coefficients and the approximant -/

/-- The smooth periodic mode `e_r = Pi.single r.1 (m_{r.2.1} · b_{r.2.2})` with values in the
coupled fiber. -/
def coarseMode {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) (r : CoupledFourierModeIndex (h := h) n) :
    Vec 2 → ∀ i, h i :=
  fun x i => coupledModeJet n r i 0 Fin.elim0 x

/-- The Galerkin coefficient `c_r = ∫_{cell} ⟪U_{r.1}, e_r⟫` of a family of torus Sobolev fields. -/
def coarseModeCoeff {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {K : ℕ} (U : ∀ i, TorusHk K (h i))
    (r : CoupledFourierModeIndex (h := h) n) : ℝ :=
  ∫ x in AVenhance.unitCube,
    inner ℝ ((U r.1).toFunction.jet (valueIndex2 K) x) (coupledModeJet n r r.1 0 Fin.elim0 x)

/-- The finite-rank approximant `a_n(x) = ∑_r c_r e_r(x)`. -/
def coarseApprox {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {K : ℕ} (U : ∀ i, TorusHk K (h i)) (x : Vec 2) :
    ∀ i, h i :=
  ∑ r : CoupledFourierModeIndex (h := h) n, coarseModeCoeff n U r • coarseMode n r x

/-- The coefficient trajectories `c_r(t)` of a time-dependent family. -/
def coarseCoeff {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (r : CoupledFourierModeIndex (h := h) n) (t : ℝ) : ℝ :=
  coarseModeCoeff n (fun v => W v t) r

/-- The time density of `c_r` for a coarse defect: the tested right side against `e_r`. -/
def coarseCoeffDot {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) (B : ℝ) (b : ℝ → Vec 2 → Vec 2) (D H : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {K k : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (r : CoupledFourierModeIndex (h := h) n) (s : ℝ) : ℝ :=
  ∫ x in AVenhance.unitCube,
    coarseTestedRhs B b D H AD CE Jm W Fc r.1 (coupledModeJet n r r.1 0 Fin.elim0) s x

/-! ### The modes are smooth, periodic and `Pi.single`-valued -/

theorem coarseMode_contDiff {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) (r : CoupledFourierModeIndex (h := h) n) :
    ContDiff ℝ (⊤ : ℕ∞) (coarseMode n r) :=
  contDiff_pi.2 fun i => coupledModeJet_contDiff n r i 0 Fin.elim0

theorem coarseMode_periodic {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) (r : CoupledFourierModeIndex (h := h) n) :
    AVenhance.IsZ2Periodic (coarseMode n r) :=
  fun z x => funext fun i => coupledModeJet_periodic n r i 0 Fin.elim0 z x

theorem coarseMode_eq_single {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) (r : CoupledFourierModeIndex (h := h) n) (x : Vec 2) :
    coarseMode n r x = Pi.single r.1 (coupledModeJet n r r.1 0 Fin.elim0 x) := by
  funext i
  by_cases hi : i = r.1
  · subst hi
    simp only [coarseMode, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hi]
    simp [coarseMode, coupledModeJet, hi]

/-! ### The coefficients of a coarse defect are of integral type -/

/-- **The coefficients of the approximant of a coarse defect are of integral type** on `[t₀, t₁]`,
with density `coarseCoeffDot` (the tested right side of the defect identity). -/
theorem coarseCoeff_prim {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {t₀ t₁ B : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H k N : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {f : ∀ v, TorusHk N (h v)}
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hW : IsCoarseDefect t₀ t₁ B b D H k N AD CE Jm f W Fc) (ht : t₀ ≤ t₁) (n : ℕ)
    (r : CoupledFourierModeIndex (h := h) n) :
    IsPrimOn t₀ t₁ (coarseCoeff n W r) (coarseCoeffDot n B b D H AD CE Jm W Fc r) :=
  coarseDefect_tested_prim hW ht r.1 (coupledModeJet n r r.1 0 Fin.elim0)
    ((coupledModeJet_contDiff n r r.1 0 Fin.elim0).of_le (by exact_mod_cast le_top))
    (coupledModeJet_periodic n r r.1 0 Fin.elim0)

/-- The approximant of `W(t)` is the finite-rank field `∑_r c_r(t) e_r`. -/
theorem coarseApprox_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v)) (t : ℝ)
    (x : Vec 2) :
    coarseApprox n (fun v => W v t) x =
      ∑ r : CoupledFourierModeIndex (h := h) n, coarseCoeff n W r t • coarseMode n r x :=
  rfl

/-! ### The approximant represents the Galerkin cutoff -/

/-- The coefficient is the scalar Fourier value pairing of the Galerkin scheme. -/
theorem coarseModeCoeff_eq_forcing {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {K : ℕ} (U : ∀ i, TorusHk K (h i))
    (r : CoupledFourierModeIndex (h := h) n) :
    coarseModeCoeff n U r = plainValueForcingCLM n r r.1 K (U r.1) := by
  have e : plainValueForcingCLM n r r.1 K (U r.1) =
      inner ℝ (plainModeCellLp n r r.1 0 Fin.elim0) ((U r.1).val (valueIndex2 K)) := rfl
  rw [e, plainModeCellLp_inner_eq_integral]
  unfold coarseModeCoeff
  refine integral_congr_ae ?_
  filter_upwards [periodicJetRepresentative_ae (U r.1).val (valueIndex2 K)] with x hx
  exact congrArg (fun z => inner ℝ z (coupledModeJet n r r.1 0 Fin.elim0 x)) hx

/-- The coefficient vector is the initial coefficient vector of the Galerkin scheme. -/
theorem coarseModeCoeff_eq_plainInitial {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {K : ℕ} (U : ∀ i, TorusHk K (h i)) :
    coarseModeCoeff n U = plainInitialCoefficients n (fun _ => K) U := by
  funext r
  rw [plainInitialCoefficients_component]
  exact coarseModeCoeff_eq_forcing n U r

/-- **Synthesis of the coefficients is the Galerkin cutoff**, at the order of the field. -/
theorem coarseModeCoeff_synthesis {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {K : ℕ} (U : ∀ i, TorusHk K (h i)) (i : ι) :
    coupledPlainSynthesis n i K (coarseModeCoeff n U) = galerkinProj n (U i) := by
  rw [coarseModeCoeff_eq_plainInitial]
  exact plainInitialCoefficients_synthesis n (fun _ => K) U i

/-- The `i`-component of the approximant is the explicit finite Fourier synthesis. -/
theorem coarseApprox_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {K : ℕ} (U : ∀ i, TorusHk K (h i)) (x : Vec 2)
    (i : ι) :
    coarseApprox n U x i = coupledPlainRawJet n (coarseModeCoeff n U) i 0 Fin.elim0 x := by
  simp only [coarseApprox, coupledPlainRawJet, Finset.sum_apply, Pi.smul_apply, coarseMode]

/-- The ordered derivatives of the finite synthesis are its higher synthesized jets. -/
theorem orderedDerivative_coupledPlainRawJet {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) (c : CoupledPlainCoefficients (h := h) n) (i : ι) :
    ∀ (m : ℕ) (w : DerivativeWord2 m),
      orderedDerivative w (coupledPlainRawJet n c i 0 Fin.elim0) = coupledPlainRawJet n c i m w
  | 0, w => by
      rw [AVRegularity.orderedDerivative_zero]
      exact congrArg (coupledPlainRawJet n c i 0) (funext fun z => Fin.elim0 z)
  | m + 1, w => by
      rw [AVRegularity.orderedDerivative_succ, orderedDerivative_coupledPlainRawJet n c i m]
      funext x
      rw [coupledPlainRawJet_fderiv]
      exact congrArg (fun w' => coupledPlainRawJet n c i (m + 1) w' x) (Fin.snoc_init_self w)

/-- **The approximant is a classical representative of the Galerkin cutoff** at every order
`r ≤ K`: `a_n(·)_i` is `C^r`, periodic, and its ordered derivatives are a.e. the jets of
`galerkinProj n (U i)`. -/
theorem coarseApprox_isClassicalRep {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {K : ℕ} (U : ∀ i, TorusHk K (h i)) (i : ι) {r : ℕ}
    (hr : r ≤ K) :
    IsClassicalRep (galerkinProj n (U i)) (fun x => coarseApprox n U x i) r := by
  have he : (fun x => coarseApprox n U x i) =
      coupledPlainRawJet n (coarseModeCoeff n U) i 0 Fin.elim0 :=
    funext fun x => coarseApprox_apply n U x i
  rw [he]
  refine ⟨hr, (coupledPlainRawJet_contDiff n _ i 0 Fin.elim0).of_le (by exact_mod_cast le_top),
    coupledPlainRawJet_periodic n _ i 0 Fin.elim0, fun m hm w => ?_⟩
  have hmK : m ≤ K := hm.trans hr
  rw [orderedDerivative_coupledPlainRawJet]
  have h1 := AVRegularity.CycleComparison.Assembly.torusJetOrder_ae (galerkinProj n (U i)) hmK w
  have h2 := coupledPlainSynthesis_jet_ae n i K (coarseModeCoeff n U)
    ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩
  rw [coarseModeCoeff_synthesis] at h2
  exact h1.trans h2

/-- **Single field:** the Galerkin cutoff of `U ∈ H^K(𝕋²; E)` has the classical representative
`∑_r (∫_{cell} ⟪U, e_r⟫) e_r` over the fixed finite family `e_r : ℝ² → E` (one component). -/
theorem galerkinProj_isClassicalRep_explicit {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] (n : ℕ) {K : ℕ} (U : TorusHk K E) {r : ℕ} (hr : r ≤ K) :
    IsClassicalRep (galerkinProj n U)
      (fun x => coarseApprox (h := fun _ : Unit => E) n (fun _ => U) x ()) r :=
  coarseApprox_isClassicalRep (h := fun _ : Unit => E) n (fun _ => U) () hr

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Periodic integration by parts on the unit cell** (reconstruction of the weak
identity).

For `C¹` periodic fields on the torus `ℝ²/ℤ²`, read on the cell `AVenhance.unitCube`, with
`∂_k g x = fderiv ℝ g x (basisVec k)`:

* `cell_ibp_div`: `∫ ⟪∑_k ∂_k F_k, φ⟫ = -∫ ∑_k ⟪F_k, ∂_k φ⟫`;
* `cell_ibp_laplacian`: `∫ ⟪∑_k ∂_k ∂_k u, φ⟫ = -∫ ∑_k ⟪∂_k u, ∂_k φ⟫`;
* `cell_ibp_transport`: for a divergence-free `b`, `∫ ⟪u, b·∇φ⟫ = -∫ ⟪b·∇u, φ⟫`;

and the integration by parts of one derivative and of a divergence when the test is the jet of
`φ : TorusHk 1 E` (value jet `φ.toFunction.jet (valueIndex2 1)`, first jets
`φ.toFunction.jet ⟨⟨1, _⟩, fun _ => k⟩`, exactly the form of the test in
`IsCoupledWeakSolutionTorus`): `cell_ibp_partial_H1`, `cell_ibp_div_H1`. The smooth identities wrap
`CoupledEnergy.Variational.periodic_hilbert_partial_ibp`; the `H¹` ones wrap the jet integration
by parts `Coarse.cellInner_torusJetOrder_eq`. Integrability of every integrand is provided
separately (`cell_integrable_inner_continuous`, `cell_integrable_inner_value`,
`cell_integrable_inner_jet`). -/

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The coordinate derivative of a `C¹` field is continuous. -/
theorem cell_continuous_partial {g : Vec 2 → E} (hg : ContDiff ℝ 1 g) (k : Fin 2) :
    Continuous (fun x => fderiv ℝ g x (basisVec k)) :=
  (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The cell pairing of two continuous fields is integrable. -/
theorem cell_integrable_inner_continuous {f g : Vec 2 → E} (hf : Continuous f)
    (hg : Continuous g) :
    Integrable (fun x => inner ℝ (f x) (g x)) (volume.restrict AVenhance.unitCube) :=
  AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable _ (hf.inner hg)

/-- **Periodic integration by parts for a divergence.** For `C¹` periodic `F_k` and `φ`,
`∫ ⟪∑_k ∂_k F_k, φ⟫ = -∫ ∑_k ⟪F_k, ∂_k φ⟫`. -/
theorem cell_ibp_div {F : Vec 2 → Fin 2 → E} (hF : ∀ k, ContDiff ℝ 1 (fun x => F x k))
    (hFp : ∀ k, AVenhance.IsZ2Periodic (fun x => F x k)) {φ : Vec 2 → E}
    (hφ : ContDiff ℝ 1 φ) (hφp : AVenhance.IsZ2Periodic φ) :
    ∫ x in AVenhance.unitCube,
        inner ℝ (∑ k : Fin 2, fderiv ℝ (fun y => F y k) x (basisVec k)) (φ x) =
      -∫ x in AVenhance.unitCube, ∑ k : Fin 2, inner ℝ (F x k) (fderiv ℝ φ x (basisVec k)) := by
  have hl : ∀ k : Fin 2, Integrable
      (fun x => inner ℝ (fderiv ℝ (fun y => F y k) x (basisVec k)) (φ x))
      (volume.restrict AVenhance.unitCube) := fun k =>
    cell_integrable_inner_continuous (cell_continuous_partial (hF k) k) hφ.continuous
  have hr : ∀ k : Fin 2, Integrable
      (fun x => inner ℝ (F x k) (fderiv ℝ φ x (basisVec k)))
      (volume.restrict AVenhance.unitCube) := fun k =>
    cell_integrable_inner_continuous (hF k).continuous (cell_continuous_partial hφ k)
  calc ∫ x in AVenhance.unitCube,
        inner ℝ (∑ k : Fin 2, fderiv ℝ (fun y => F y k) x (basisVec k)) (φ x)
      = ∑ k : Fin 2, ∫ x in AVenhance.unitCube,
          inner ℝ (fderiv ℝ (fun y => F y k) x (basisVec k)) (φ x) := by
        rw [← integral_finsetSum _ fun k _ => hl k]
        exact integral_congr_ae (ae_of_all _ fun x => sum_inner _ _ _)
    _ = ∑ k : Fin 2, -∫ x in AVenhance.unitCube,
          inner ℝ (F x k) (fderiv ℝ φ x (basisVec k)) :=
        Finset.sum_congr rfl fun k _ =>
          AVRegularity.CoupledEnergy.Variational.periodic_hilbert_partial_ibp
            (fun y => F y k) φ (hF k) hφ (hFp k) hφp k
    _ = -∫ x in AVenhance.unitCube, ∑ k : Fin 2,
          inner ℝ (F x k) (fderiv ℝ φ x (basisVec k)) := by
        rw [Finset.sum_neg_distrib, integral_finsetSum _ fun k _ => hr k]

/-- **Periodic integration by parts for the Laplacian.** For `C²` periodic `u` and `C¹` periodic
`φ`, `∫ ⟪∑_k ∂_k ∂_k u, φ⟫ = -∫ ∑_k ⟪∂_k u, ∂_k φ⟫`. -/
theorem cell_ibp_laplacian {u : Vec 2 → E} (hu : ContDiff ℝ 2 u)
    (hup : AVenhance.IsZ2Periodic u) {φ : Vec 2 → E} (hφ : ContDiff ℝ 1 φ)
    (hφp : AVenhance.IsZ2Periodic φ) :
    ∫ x in AVenhance.unitCube, inner ℝ (∑ k : Fin 2,
        fderiv ℝ (fun y => fderiv ℝ u y (basisVec k)) x (basisVec k)) (φ x) =
      -∫ x in AVenhance.unitCube, ∑ k : Fin 2,
        inner ℝ (fderiv ℝ u x (basisVec k)) (fderiv ℝ φ x (basisVec k)) :=
  cell_ibp_div (F := fun x k => fderiv ℝ u x (basisVec k))
    (fun k => (hu.fderiv_right (by norm_num)).clm_apply contDiff_const)
    (fun k => AVRegularity.CycleComparison.Coarse.periodic_partial hup k) hφ hφp

/-- For a divergence-free `b`, `∑_k ∂_k (b_k u) = ∑_k b_k ∂_k u`. -/
theorem sum_partial_smul_of_div {b : Vec 2 → Vec 2} {u : Vec 2 → E}
    (hbk : ∀ k : Fin 2, ContDiff ℝ 1 (fun y => b y k)) (hu : ContDiff ℝ 1 u)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (fun y => b y k) x (basisVec k) = 0) (x : Vec 2) :
    ∑ k : Fin 2, fderiv ℝ (fun y => b y k • u y) x (basisVec k) =
      ∑ k : Fin 2, b x k • fderiv ℝ u x (basisVec k) := by
  have hk : ∀ k : Fin 2, fderiv ℝ (fun y => b y k • u y) x (basisVec k) =
      fderiv ℝ (fun y => b y k) x (basisVec k) • u x + b x k • fderiv ℝ u x (basisVec k) := by
    intro k
    rw [fderiv_fun_smul ((hbk k).differentiable one_ne_zero x) (hu.differentiable one_ne_zero x)]
    simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply]
    exact add_comm _ _
  simp only [hk, Finset.sum_add_distrib]
  rw [← Finset.sum_smul, hdiv x, zero_smul, zero_add]

/-- **Periodic integration by parts for the transport term.** For a `C¹` periodic
divergence-free `b` and `C¹` periodic `u`, `φ`: `∫ ⟪u, b·∇φ⟫ = -∫ ⟪b·∇u, φ⟫`. -/
theorem cell_ibp_transport {b : Vec 2 → Vec 2} (hb : ContDiff ℝ 1 b)
    (hbp : AVenhance.IsZ2Periodic b)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (fun y => b y k) x (basisVec k) = 0)
    {u : Vec 2 → E} (hu : ContDiff ℝ 1 u) (hup : AVenhance.IsZ2Periodic u)
    {φ : Vec 2 → E} (hφ : ContDiff ℝ 1 φ) (hφp : AVenhance.IsZ2Periodic φ) :
    ∫ x in AVenhance.unitCube, inner ℝ (u x) (∑ k : Fin 2, b x k • fderiv ℝ φ x (basisVec k)) =
      -∫ x in AVenhance.unitCube,
        inner ℝ (∑ k : Fin 2, b x k • fderiv ℝ u x (basisVec k)) (φ x) := by
  have hbk : ∀ k : Fin 2, ContDiff ℝ 1 (fun y => b y k) := fun k => contDiff_pi.1 hb k
  have hF : ∀ k : Fin 2, ContDiff ℝ 1 (fun y => b y k • u y) := fun k => (hbk k).fun_smul hu
  have hFp : ∀ k : Fin 2, AVenhance.IsZ2Periodic (fun y => b y k • u y) := fun k n x => by
    simp only [hbp n x, hup n x]
  have hr : ∀ x, inner ℝ (u x) (∑ k : Fin 2, b x k • fderiv ℝ φ x (basisVec k)) =
      ∑ k : Fin 2, inner ℝ (b x k • u x) (fderiv ℝ φ x (basisVec k)) := fun x => by
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
  have hl : ∀ x, inner ℝ (∑ k : Fin 2, fderiv ℝ (fun y => b y k • u y) x (basisVec k)) (φ x) =
      inner ℝ (∑ k : Fin 2, b x k • fderiv ℝ u x (basisVec k)) (φ x) := fun x => by
    rw [sum_partial_smul_of_div hbk hu hdiv x]
  calc ∫ x in AVenhance.unitCube,
        inner ℝ (u x) (∑ k : Fin 2, b x k • fderiv ℝ φ x (basisVec k))
      = ∫ x in AVenhance.unitCube, ∑ k : Fin 2,
          inner ℝ (b x k • u x) (fderiv ℝ φ x (basisVec k)) :=
        integral_congr_ae (ae_of_all _ hr)
    _ = -∫ x in AVenhance.unitCube,
          inner ℝ (∑ k : Fin 2, fderiv ℝ (fun y => b y k • u y) x (basisVec k)) (φ x) :=
        (neg_eq_iff_eq_neg.mpr
          (cell_ibp_div (F := fun y k => b y k • u y) hF hFp hφ hφp)).symm
    _ = -∫ x in AVenhance.unitCube,
          inner ℝ (∑ k : Fin 2, b x k • fderiv ℝ u x (basisVec k)) (φ x) :=
        congrArg Neg.neg (integral_congr_ae (ae_of_all _ hl))

end Smooth

section Torus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A continuous field pairs integrably on the cell with the value jet of `φ : TorusHk 1 E`. -/
theorem cell_integrable_inner_value (φ : TorusHk 1 E) {g : Vec 2 → E} (hg : Continuous g) :
    Integrable (fun x => inner ℝ (g x) (φ.toFunction.jet (valueIndex2 1) x))
      (volume.restrict AVenhance.unitCube) :=
  (AVRegularity.CycleComparison.Coarse.integrable_tval_inner φ hg).congr
    (ae_of_all _ fun _ => real_inner_comm _ _)

omit [FiniteDimensional ℝ E] in
/-- A continuous field pairs integrably on the cell with a first jet of `φ : TorusHk 1 E`. -/
theorem cell_integrable_inner_jet (φ : TorusHk 1 E) (k : Fin 2) {g : Vec 2 → E}
    (hg : Continuous g) :
    Integrable (fun x => inner ℝ (g x) (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x))
      (volume.restrict AVenhance.unitCube) :=
  (AVRegularity.CycleComparison.Coarse.integrable_inner_continuous
    (φ.toFunction.hasPeriodicWeakJet.2.1 ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩) hg).congr
    (ae_of_all _ fun _ => real_inner_comm _ _)

/-- One coordinate of the jet integration by parts: for `C¹` periodic `ψ`,
`∫ ⟪∂_k ψ, φ⟫ = -∫ ⟪ψ, ∂_k φ⟫` with the jets of `φ : TorusHk 1 E`. -/
theorem cell_ibp_partial_H1 (φ : TorusHk 1 E) {ψ : Vec 2 → E} (hψ : ContDiff ℝ 1 ψ)
    (hψp : AVenhance.IsZ2Periodic ψ) (k : Fin 2) :
    ∫ x in AVenhance.unitCube,
        inner ℝ (fderiv ℝ ψ x (basisVec k)) (φ.toFunction.jet (valueIndex2 1) x) =
      -∫ x in AVenhance.unitCube,
        inner ℝ (ψ x) (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x) := by
  have h := AVRegularity.CycleComparison.Coarse.cellInner_torusJetOrder_eq φ (le_refl 1)
    (fun _ => k) (χ := ψ) (by exact_mod_cast hψ) hψp
  rw [AVRegularity.CycleComparison.Coarse.orderedDerivativeRev_one] at h
  have hA : ∫ x in AVenhance.unitCube,
      inner ℝ (fderiv ℝ ψ x (basisVec k)) (φ.toFunction.jet (valueIndex2 1) x) =
      cellInner (AVRegularity.CycleComparison.Coarse.tval φ)
        (fun x => fderiv ℝ ψ x (basisVec k)) :=
    integral_congr_ae (ae_of_all _ fun _ => real_inner_comm _ _)
  have hB : ∫ x in AVenhance.unitCube,
      inner ℝ (ψ x) (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x) =
      cellInner (torusJetOrder φ 1 (fun _ => k)) ψ := by
    rw [AVRegularity.CycleComparison.Coarse.torusJetOrder_of_le φ (le_refl 1) (fun _ => k)]
    exact integral_congr_ae (ae_of_all _ fun _ => real_inner_comm _ _)
  rw [hA, hB, h]
  ring

/-- **Integration by parts of a divergence against an `H¹` test.** For `C¹` periodic `F_k` and
`φ : TorusHk 1 E`: `∫ ⟪∑_k ∂_k F_k, φ⟫ = -∫ ∑_k ⟪F_k, ∂_k φ⟫`. -/
theorem cell_ibp_div_H1 (φ : TorusHk 1 E) {F : Vec 2 → Fin 2 → E}
    (hF : ∀ k, ContDiff ℝ 1 (fun x => F x k))
    (hFp : ∀ k, AVenhance.IsZ2Periodic (fun x => F x k)) :
    ∫ x in AVenhance.unitCube, inner ℝ (∑ k : Fin 2, fderiv ℝ (fun y => F y k) x (basisVec k))
        (φ.toFunction.jet (valueIndex2 1) x) =
      -∫ x in AVenhance.unitCube, ∑ k : Fin 2,
        inner ℝ (F x k) (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x) := by
  have hl : ∀ k : Fin 2, Integrable (fun x => inner ℝ
      (fderiv ℝ (fun y => F y k) x (basisVec k)) (φ.toFunction.jet (valueIndex2 1) x))
      (volume.restrict AVenhance.unitCube) := fun k =>
    cell_integrable_inner_value φ (cell_continuous_partial (hF k) k)
  have hr : ∀ k : Fin 2, Integrable (fun x => inner ℝ (F x k)
      (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x))
      (volume.restrict AVenhance.unitCube) := fun k =>
    cell_integrable_inner_jet φ k (hF k).continuous
  calc ∫ x in AVenhance.unitCube, inner ℝ
        (∑ k : Fin 2, fderiv ℝ (fun y => F y k) x (basisVec k))
        (φ.toFunction.jet (valueIndex2 1) x)
      = ∑ k : Fin 2, ∫ x in AVenhance.unitCube, inner ℝ
          (fderiv ℝ (fun y => F y k) x (basisVec k)) (φ.toFunction.jet (valueIndex2 1) x) := by
        rw [← integral_finsetSum _ fun k _ => hl k]
        exact integral_congr_ae (ae_of_all _ fun x => sum_inner _ _ _)
    _ = ∑ k : Fin 2, -∫ x in AVenhance.unitCube, inner ℝ (F x k)
          (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x) :=
        Finset.sum_congr rfl fun k _ => cell_ibp_partial_H1 φ (hF k) (hFp k) k
    _ = -∫ x in AVenhance.unitCube, ∑ k : Fin 2, inner ℝ (F x k)
          (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x) := by
        rw [Finset.sum_neg_distrib, integral_finsetSum _ fun k _ => hr k]

end Torus

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Uniqueness and slow invariance of cleanup chains**.

`𝒜_z = ∇_z Δ_z^{-1}` is characterized relationally (`IsCellAntidivergence`); the relation is
functional:

* `fderiv_eq_of_laplacian_eq`: two `C²` periodic fields with the same Laplacian have the same
  gradient (energy identity `∫ ⟪Δw, w⟫ = -∫ ∑_k ‖∂_k w‖²` for the difference, continuity and
  periodicity);
* `isCellAntidivergence_unique`: two cell antidivergences of the same field agree (inner product
  values directly; complete normed values through the continuous duals);
* `isCleanupChain_unique_zero`, `isCleanupChain_unique`: two cleanup chains of the same data agree
  at every constrained index (`j = 0` and `j < A`), by induction since `f_j = -div_X V_{j-1}`.

The relations commute with slow translations `X ↦ X + s` (`isBoxSmooth_translate`,
`cleanupSource_translate`, `isCellAntidivergence_translate`, `isCleanupChain_translate`), so the
cleanup chain of `s`-invariant data is `s`-invariant (`isCleanupChain_slow_invariant`). -/

/-- `2 ≤ n` as smoothness orders. -/
theorem two_le_withTop_natCast {n : ℕ} (h : 2 ≤ n) :
    (2 : WithTop ℕ∞) ≤ ((n : ℕ∞) : WithTop ℕ∞) := by
  have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((n : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.2 (by exact_mod_cast h)
  simpa using h1

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Box regularity is invariant under a slow translation. -/
theorem isBoxSmooth_translate {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E} (hf : IsBoxSmooth sX sZ f)
    (s : Vec 2) : IsBoxSmooth sX sZ (fun X => f (X + s)) := by
  refine ⟨fun X => hf.1 (X + s), fun b hb z => ?_, fun a b ha hb => ?_⟩
  · exact (hf.2.1 b hb z).comp (contDiff_id.add contDiff_const)
  · show Continuous (fun p : Vec 2 × Vec 2 =>
      iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b (f (X' + s)) p.2) p.1)
    have he : (fun p : Vec 2 × Vec 2 =>
        iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b (f (X' + s)) p.2) p.1) =
        fun p => iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b (f X') p.2) (p.1 + s) := by
      funext p
      exact iteratedFDeriv_comp_add_right (𝕜 := ℝ)
        (f := fun X' => iteratedFDeriv ℝ b (f X') p.2) a s p.1
    rw [he]
    exact (hf.2.2 a b ha hb).comp ((continuous_fst.add continuous_const).prodMk continuous_snd)

/-- The cleanup source `f_j = -div_X V_{j-1}` depends only on `V_{j-1}`. -/
theorem cleanupSource_congr {V V' : ℕ → Vec 2 → Vec 2 → Fin 2 → E} {j : ℕ}
    (h : V (j - 1) = V' (j - 1)) : cleanupSource V j = cleanupSource V' j := by
  unfold cleanupSource
  rw [h]

/-- The cleanup source commutes with a slow translation. -/
theorem cleanupSource_translate (V : ℕ → Vec 2 → Vec 2 → Fin 2 → E) (j : ℕ) (s : Vec 2) :
    cleanupSource (fun i X => V i (X + s)) j = fun X => cleanupSource V j (X + s) := by
  funext X z
  have h : ∀ k : Fin 2, fderiv ℝ (fun X' => V (j - 1) (X' + s) z k) X =
      fderiv ℝ (fun X' => V (j - 1) X' z k) (X + s) := fun k =>
    fderiv_comp_add_right (𝕜 := ℝ) (f := fun X' => V (j - 1) X' z k) s
  simp only [cleanupSource, slowPartial, h]

/-- A cell antidivergence of slow-translated data is the slow translate of the antidivergence. -/
theorem isCellAntidivergence_translate {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E}
    {V : Vec 2 → Vec 2 → Fin 2 → E} (hV : IsCellAntidivergence sX sZ f V) (s : Vec 2) :
    IsCellAntidivergence sX sZ (fun X => f (X + s)) (fun X => V (X + s)) := by
  obtain ⟨hVb, hVp, φ, hφb, hφp, hφm, hVφ, hdiv⟩ := hV
  exact ⟨isBoxSmooth_translate hVb s, fun X => hVp (X + s), fun X => φ (X + s),
    isBoxSmooth_translate hφb s, fun X => hφp (X + s), fun X => hφm (X + s),
    fun X => hVφ (X + s), fun X => hdiv (X + s)⟩

/-- A cleanup chain of slow-translated data is the slow translate of the chain. -/
theorem isCleanupChain_translate {sX sZ A : ℕ} {f₀ : Vec 2 → Vec 2 → E}
    {F₀ : Vec 2 → Vec 2 → Fin 2 → E} {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E}
    (hV : IsCleanupChain sX sZ A f₀ F₀ V) (s : Vec 2) :
    IsCleanupChain sX sZ A (fun X => f₀ (X + s)) (fun X => F₀ (X + s))
      (fun j X => V j (X + s)) := by
  obtain ⟨⟨W₀, hW₀, hV0⟩, hVj⟩ := hV
  refine ⟨⟨fun X => W₀ (X + s), isCellAntidivergence_translate hW₀ s, ?_⟩,
    fun j hj hjA => ?_⟩
  · funext X z k
    show V 0 (X + s) z k = F₀ (X + s) z k + W₀ (X + s) z k
    rw [hV0]
  · rw [cleanupSource_translate V j s]
    exact isCellAntidivergence_translate (hVj j hj hjA) s

end Normed

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Energy identity on the cell.** A `C²` periodic field with vanishing Laplacian has vanishing
gradient: `0 = ∫ ⟪Δw, w⟫ = -∫ ∑_j ‖∂_j w‖²`, and the continuous periodic `∂_k w` vanishing a.e.
on the cell vanishes everywhere. -/
theorem partial_eq_zero_of_laplacian_eq_zero {w : Vec 2 → E} (hw : ContDiff ℝ 2 w)
    (hwp : AVenhance.IsZ2Periodic w)
    (hΔ : ∀ z, ∑ k : Fin 2, fderiv ℝ (fun y => fderiv ℝ w y (basisVec k)) z (basisVec k) = 0)
    (k : Fin 2) (z : Vec 2) : fderiv ℝ w z (basisVec k) = 0 := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have hL : ∫ x in AVenhance.unitCube, inner ℝ (∑ j : Fin 2,
      fderiv ℝ (fun y => fderiv ℝ w y (basisVec j)) x (basisVec j)) (w x) = 0 := by
    simp only [hΔ, inner_zero_left, integral_zero]
  have h0 := (cell_ibp_laplacian hw hwp hw1 hwp).symm.trans hL
  have hI : ∫ x in AVenhance.unitCube, ∑ j : Fin 2, ‖fderiv ℝ w x (basisVec j)‖ ^ 2 = 0 := by
    simpa only [real_inner_self_eq_norm_sq] using neg_eq_zero.mp h0
  have hcont : Continuous fun x => ∑ j : Fin 2, ‖fderiv ℝ w x (basisVec j)‖ ^ 2 :=
    continuous_finsetSum _ fun j _ => (cell_continuous_partial hw1 j).norm.pow 2
  have hae := (integral_eq_zero_iff_of_nonneg
    (f := fun x => ∑ j : Fin 2, ‖fderiv ℝ w x (basisVec j)‖ ^ 2)
    (fun x => Finset.sum_nonneg fun j _ => sq_nonneg ‖fderiv ℝ w x (basisVec j)‖)
    (AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable _ hcont)).mp hI
  have hk : (fun x => fderiv ℝ w x (basisVec k)) =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
    filter_upwards [hae] with x hx
    have hx' : ∑ j : Fin 2, ‖fderiv ℝ w x (basisVec j)‖ ^ 2 = 0 := hx
    have h2 : ‖fderiv ℝ w x (basisVec k)‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖fderiv ℝ w x (basisVec j)‖).mp
        hx' k (Finset.mem_univ k)
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  exact congrFun (AVRegularity.CycleComparison.Lift.periodicContinuous_zero_of_cell_ae _
    (cell_continuous_partial hw1 k) (AVRegularity.CycleComparison.Coarse.periodic_partial hwp k)
    hk) z

/-- Two `C²` periodic fields with the same Laplacian have the same gradient. -/
theorem fderiv_eq_of_laplacian_eq {u v : Vec 2 → E} (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v) (hup : AVenhance.IsZ2Periodic u) (hvp : AVenhance.IsZ2Periodic v)
    (h : ∀ y, ∑ j : Fin 2, fderiv ℝ (fun y' => fderiv ℝ u y' (basisVec j)) y (basisVec j) =
      ∑ j : Fin 2, fderiv ℝ (fun y' => fderiv ℝ v y' (basisVec j)) y (basisVec j))
    (z : Vec 2) (k : Fin 2) : fderiv ℝ u z (basisVec k) = fderiv ℝ v z (basisVec k) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hdu : ∀ j : Fin 2, Differentiable ℝ (fun y => fderiv ℝ u y (basisVec j)) := fun j =>
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      one_ne_zero
  have hdv : ∀ j : Fin 2, Differentiable ℝ (fun y => fderiv ℝ v y (basisVec j)) := fun j =>
    ((hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      one_ne_zero
  have hg : ∀ y (j : Fin 2), fderiv ℝ (fun x => u x - v x) y (basisVec j) =
      fderiv ℝ u y (basisVec j) - fderiv ℝ v y (basisVec j) := fun y j => by
    rw [fderiv_fun_sub ((hu1.differentiable one_ne_zero) y) ((hv1.differentiable one_ne_zero) y),
      _root_.sub_apply]
  have hΔ : ∀ y, ∑ j : Fin 2, fderiv ℝ (fun y' => fderiv ℝ (fun x => u x - v x) y' (basisVec j))
      y (basisVec j) = 0 := by
    intro y
    have e : ∀ j : Fin 2,
        fderiv ℝ (fun y' => fderiv ℝ (fun x => u x - v x) y' (basisVec j)) y (basisVec j) =
          fderiv ℝ (fun y' => fderiv ℝ u y' (basisVec j)) y (basisVec j) -
            fderiv ℝ (fun y' => fderiv ℝ v y' (basisVec j)) y (basisVec j) := fun j => by
      rw [show (fun y' => fderiv ℝ (fun x => u x - v x) y' (basisVec j)) =
          fun y' => fderiv ℝ u y' (basisVec j) - fderiv ℝ v y' (basisVec j) from
        funext fun y' => hg y' j, fderiv_fun_sub (hdu j y) (hdv j y), _root_.sub_apply]
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_sub_distrib, h y, sub_self]
  have hw := partial_eq_zero_of_laplacian_eq_zero (hu.sub hv)
    (fun n y => by simp only [hup n y, hvp n y]) hΔ k z
  rw [hg z k] at hw
  exact sub_eq_zero.mp hw

/-- The Laplacian of the potential of a cell antidivergence is its source. -/
theorem laplacian_eq_of_potential {φ : Vec 2 → E} {W : Vec 2 → Fin 2 → E} {g : Vec 2 → E}
    (hW : ∀ y j, W y j = fderiv ℝ φ y (basisVec j))
    (hdiv : ∀ y, ∑ j : Fin 2, fderiv ℝ (fun y' => W y' j) y (basisVec j) = g y) (y : Vec 2) :
    ∑ j : Fin 2, fderiv ℝ (fun y' => fderiv ℝ φ y' (basisVec j)) y (basisVec j) = g y := by
  rw [← hdiv y]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (fun y' => fderiv ℝ φ y' (basisVec j)) = fun y' => W y' j from
    funext fun y' => (hW y' j).symm]

/-- Two cell antidivergences of the same field with values in an inner product space agree. -/
theorem isCellAntidivergence_unique_of_inner {sX sZ : ℕ} (hsZ : 1 ≤ sZ)
    {f : Vec 2 → Vec 2 → E} {V V' : Vec 2 → Vec 2 → Fin 2 → E}
    (hV : IsCellAntidivergence sX sZ f V) (hV' : IsCellAntidivergence sX sZ f V') : V = V' := by
  obtain ⟨-, -, φ, hφb, hφp, -, hVφ, hdiv⟩ := hV
  obtain ⟨-, -, φ', hφb', hφp', -, hVφ', hdiv'⟩ := hV'
  funext X z k
  have hφ2 : ContDiff ℝ 2 (φ X) := (hφb.1 X).of_le (two_le_withTop_natCast (by omega))
  have hφ2' : ContDiff ℝ 2 (φ' X) := (hφb'.1 X).of_le (two_le_withTop_natCast (by omega))
  rw [hVφ X z k, hVφ' X z k]
  exact fderiv_eq_of_laplacian_eq hφ2 hφ2' (hφp X) (hφp' X)
    (fun y => (laplacian_eq_of_potential (hVφ X) (hdiv X) y).trans
      (laplacian_eq_of_potential (hVφ' X) (hdiv' X) y).symm) z k

end Inner

section Complete

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Uniqueness of `𝒜_z`.** Two cell antidivergences of the same field agree. -/
theorem isCellAntidivergence_unique {sX sZ : ℕ} (hsZ : 1 ≤ sZ) {f : Vec 2 → Vec 2 → E}
    {V V' : Vec 2 → Vec 2 → Fin 2 → E} (hV : IsCellAntidivergence sX sZ f V)
    (hV' : IsCellAntidivergence sX sZ f V') : V = V' := by
  funext X z k
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr fun L => ?_
  have h := isCellAntidivergence_unique_of_inner hsZ (hV.clm_comp hsZ L) (hV'.clm_comp hsZ L)
  exact congrFun (congrFun (congrFun h X) z) k

/-- Two cleanup chains of the same data have the same first term `V_0`. -/
theorem isCleanupChain_unique_zero {sX sZ A : ℕ} (hsZ : 1 ≤ sZ) {f₀ : Vec 2 → Vec 2 → E}
    {F₀ : Vec 2 → Vec 2 → Fin 2 → E} {V V' : ℕ → Vec 2 → Vec 2 → Fin 2 → E}
    (hV : IsCleanupChain sX sZ A f₀ F₀ V) (hV' : IsCleanupChain sX sZ A f₀ F₀ V') :
    V 0 = V' 0 := by
  obtain ⟨⟨W, hW, hV0⟩, -⟩ := hV
  obtain ⟨⟨W', hW', hV0'⟩, -⟩ := hV'
  rw [hV0, hV0', isCellAntidivergence_unique hsZ hW hW']

/-- **Uniqueness of cleanup chains.** Two cleanup chains of the same data agree below the
length. -/
theorem isCleanupChain_unique {sX sZ A : ℕ} (hsZ : 1 ≤ sZ) {f₀ : Vec 2 → Vec 2 → E}
    {F₀ : Vec 2 → Vec 2 → Fin 2 → E} {V V' : ℕ → Vec 2 → Vec 2 → Fin 2 → E}
    (hV : IsCleanupChain sX sZ A f₀ F₀ V) (hV' : IsCleanupChain sX sZ A f₀ F₀ V') :
    ∀ j < A, V j = V' j := by
  have h0 := isCleanupChain_unique_zero hsZ hV hV'
  obtain ⟨-, hVj⟩ := hV
  obtain ⟨-, hVj'⟩ := hV'
  intro j
  induction j with
  | zero => exact fun _ => h0
  | succ j ih =>
    intro hj
    have hprev : V (j + 1 - 1) = V' (j + 1 - 1) := by
      rw [Nat.add_sub_cancel]
      exact ih (by omega)
    have h1 := hVj (j + 1) (by omega) hj
    rw [cleanupSource_congr hprev] at h1
    exact isCellAntidivergence_unique hsZ h1 (hVj' (j + 1) (by omega) hj)

/-- **Slow invariance of cleanup chains.** The cleanup chain of data invariant under the slow
translation by `s` is invariant under it below the length. -/
theorem isCleanupChain_slow_invariant {sX sZ A : ℕ} (hsZ : 1 ≤ sZ) (s : Vec 2)
    {f₀ : Vec 2 → Vec 2 → E} {F₀ : Vec 2 → Vec 2 → Fin 2 → E}
    {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E} (hf : ∀ X, f₀ (X + s) = f₀ X)
    (hF : ∀ X, F₀ (X + s) = F₀ X) (hV : IsCleanupChain sX sZ A f₀ F₀ V) :
    ∀ j < A, ∀ X, V j (X + s) = V j X := by
  have hT := isCleanupChain_translate hV s
  have hf' : (fun X => f₀ (X + s)) = f₀ := funext hf
  have hF' : (fun X => F₀ (X + s)) = F₀ := funext hF
  rw [hf', hF'] at hT
  intro j hj X
  exact congrFun (isCleanupChain_unique hsZ hT hV j hj) X

end Complete

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization AVRegularity.Sobolev AVenhance Set
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The family edge flux at a weighted time of an observed pulse**. At a time of the window where
the piece `pp k` of an observed pulse is weighted, the physical edge flux of the family is the Piola
transport of the label edge flux of that piece (`obs_family_flux`): either `pp k` is the only
weighted piece, or exactly one neighbouring pulse `j = k ± 2` is weighted at a quiet time, the two
pieces carry equal or consecutive labels (`ocPulseChartIndex_add_two`) and meet in the window, so
they are adjacent in a consecutive-closed atlas, and the quiet transition identifies their
transported fluxes (in either direction, `edgeFlux_quiet_overlap_atlas_right_of_contDiff`). -/

/-- **Consecutive odd pulses carry equal or consecutive chart indices.** -/
theorem ocPulseChartIndex_add_two {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) (k : ℤ) :
    ocPulseChartIndex α q Λ m (k + 2) = ocPulseChartIndex α q Λ m k ∨
      ocPulseChartIndex α q Λ m (k + 2) = ocPulseChartIndex α q Λ m k + 1 := by
  have hT : 0 < ocTauPP α q Λ m := Construction.Stream.ocTauPP_pos hΛ
  have hε : 0 < ocEpsilon q Λ (m - 1) := Construction.Stream.ocEpsilon_pos hΛ
  have hn : 1 ≤ ⌈ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)⌉₊ :=
    Nat.ceil_pos.2 (Real.rpow_pos_of_pos hε _)
  have hL : (5 : ℝ) ≤ (ocL α q Λ m : ℝ) := by
    have h5 : 5 ≤ ocL α q Λ m := by
      unfold ocL
      omega
    exact_mod_cast h5
  have hL2 : (25 : ℝ) ≤ (ocL α q Λ m : ℝ) ^ 2 := by nlinarith
  have hLpos : (0 : ℝ) < (ocL α q Λ m : ℝ) ^ 2 := by linarith
  have hδ0 : 0 < 2 / (ocL α q Λ m : ℝ) ^ 2 := by positivity
  have hδ1 : 2 / (ocL α q Λ m : ℝ) ^ 2 < 1 := by
    rw [div_lt_one hLpos]
    linarith
  have hx : ((k + 2 : ℤ) : ℝ) * ocTau α q Λ m / ocTauPP α q Λ m + 1 / 2 =
      (k : ℝ) * ocTau α q Λ m / ocTauPP α q Λ m + 1 / 2 + 2 / (ocL α q Λ m : ℝ) ^ 2 := by
    have hT0 : ocTauPP α q Λ m ≠ 0 := hT.ne'
    have hL0 : (ocL α q Λ m : ℝ) ≠ 0 := by linarith
    unfold ocTau
    push_cast
    field_simp
    ring
  unfold ocPulseChartIndex
  rw [hx]
  set y : ℝ := (k : ℝ) * ocTau α q Λ m / ocTauPP α q Λ m + 1 / 2 with hy
  have h1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have h2 : y < ⌊y⌋ + 1 := Int.lt_floor_add_one y
  rcases lt_or_ge (y + 2 / (ocL α q Λ m : ℝ) ^ 2) ((⌊y⌋ : ℝ) + 1) with hlt | hge
  · exact Or.inl (Int.floor_eq_iff.2 ⟨by linarith, hlt⟩)
  · refine Or.inr (Int.floor_eq_iff.2 ⟨?_, ?_⟩)
    · push_cast
      linarith
    · push_cast
      linarith

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The quiet overlap identity read through the chart of the second piece. -/
theorem edgeFlux_quiet_overlap_atlas_right_of_contDiff (F : ChartedFamily ι h D P Ctx)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (K : ι → ℕ) (hdesc : F.IsDescending K) (T : F.Atlas)
    {quiet W : Set ℝ} (hTcov : T.CoversQuiet quiet W) (hTq : T.IsQuiet ν e E) {t : ℝ}
    {p q : P} (hpq : p ≠ q) (hadj : T.adjacent p q)
    (hctx : T.sameCtx p q hadj (actual p) (actual q))
    (ht : t ∈ quiet ∩ W ∩ (F.piece p).output ∩ (F.piece q).output)
    (hw : ∀ p', F.weight p' t ≠ 0 → p' = p ∨ p' = q) (hsum : F.weight p t + F.weight q t = 1)
    {r : ℕ} {U : Vec 2 → ∀ i, h i} (hU : ContDiff ℝ (r : ℕ∞) U) (hrD : D ≤ r + 1) (i : ι)
    (x : Vec 2) (a₀ : Fin 2) :
    ∑ i' : ι, ∑ d : admissibleOrders K D i i',
        edgeCoefficient F ν e E actual K i i' d t x
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => U y i') x) a₀ =
      ∑ j : Fin 2, chartInvJacobian ⇑((F.piece q).material t).symm x a₀ j •
        labelEdgeFlux F ν e E q (actual q) t (fun y => U ((F.piece q).material t y)) i
          (((F.piece q).material t).symm x) j := by
  rw [edgeFlux_quiet_overlap_atlas_of_contDiff F ν e E actual K hdesc T hTcov hTq hpq hadj hctx
    ht hw hsum hU hrD i x a₀]
  exact (pieceFlux_transition_of_contDiff F ν e E (hTq p q hadj (actual p) (actual q) hctx) hU
    hrD i x (hTcov p q hadj t ht (((F.piece q).material t).symm x)) a₀).symm

/-- **The family edge flux at a weighted time of an observed pulse** is the Piola transport of
the label edge flux of the piece of that pulse. -/
theorem obs_family_flux {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (actual : ∀ p, Ctx p) (K : ι → ℕ)
    (hdesc : F.IsDescending K) (T : F.Atlas) {tA tZ : ℝ}
    (hTcons : T.IsConsecutiveClosed (Icc tA tZ))
    (hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m) (Icc tA tZ)) (hTq : T.IsQuiet ν e E)
    (hTact : ∀ p q (hpq : T.adjacent p q),
      ((F.piece p).output ∩ (F.piece q).output ∩ Icc tA tZ).Nonempty →
        T.sameCtx p q hpq (actual p) (actual q))
    (pp : ℤ → P)
    (hlabel : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      (F.piece (pp k)).label = ocPulseChartIndex α q Λ m k)
    (hout : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      ocPulseWindow α q Λ m k ∩ Icc tA tZ ⊆ (F.piece (pp k)).output)
    (hppinj : Set.InjOn pp ↑(ocObsPulses α q Λ m tA tZ)) {quiet : Set ℝ} {Cpart : ℝ}
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k))
      (ocPulseWindow α q Λ m) quiet (Icc tA tZ) (ocTau α q Λ m) Cpart)
    (hcov : ∀ t ∈ Icc tA tZ, ∃ p, t ∈ (F.piece p).output)
    {k : ℤ} (hk : k ∈ ocObsPulses α q Λ m tA tZ) {t : ℝ} (ht : t ∈ Icc tA tZ)
    (hw : F.weight (pp k) t ≠ 0) {r : ℕ} {U : Vec 2 → ∀ i, h i}
    (hU : ContDiff ℝ (r : ℕ∞) U) (hrD : D ≤ r + 1) (v : ι) (x : Vec 2) (a₀ : Fin 2) :
    ∑ i' : ι, ∑ d : admissibleOrders K D v i',
        edgeCoefficient F ν e E actual K v i' d t x
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => U y i') x) a₀ =
      ∑ j : Fin 2, chartInvJacobian ⇑((F.piece (pp k)).material t).symm x a₀ j •
        labelEdgeFlux F ν e E (pp k) (actual (pp k)) t
          (fun y => U ((F.piece (pp k)).material t y)) v
          (((F.piece (pp k)).material t).symm x) j := by
  rcases active_pieces hΛ hζ F pp hppinj hpart hcov hk ht hw with
    ⟨hw₀, hwz⟩ | ⟨j, hj, hjk, hq, htj, htk, hsum, honly⟩
  · exact edgeFlux_single_piece_of_contDiff F ν e E actual K hdesc hw₀ hwz hU hrD v x a₀
  · have hne : pp k ≠ pp j := fun h' => hjk (hppinj hj hk h'.symm)
    have hkodd : Odd k := LiftSetting.obsPulse_odd hk
    have hjodd : Odd j := LiftSetting.obsPulse_odd hj
    have houtk : t ∈ (F.piece (pp k)).output := hout k hk ⟨htk, ht⟩
    have houtj : t ∈ (F.piece (pp j)).output := hout j hj ⟨htj, ht⟩
    have hjk2 : j = k + 2 ∨ k = j + 2 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨a, ha⟩ := hkodd
      obtain ⟨b, hb⟩ := hjodd
      rcases lt_or_gt_of_ne hjk with hlt | hgt
      · exact not_mem_two_windows_far hΛ (show j + 4 ≤ k by omega) htj htk
      · exact not_mem_two_windows_far hΛ (show k + 4 ≤ j by omega) htk htj
    rcases hjk2 with hj2 | hk2
    · have hlab : (F.piece (pp j)).label = (F.piece (pp k)).label + 1 ∨
          (F.piece (pp j)).label = (F.piece (pp k)).label := by
        rw [hlabel j hj, hlabel k hk, hj2]
        exact (ocPulseChartIndex_add_two hΛ k).symm
      have hno : ((F.piece (pp k)).output ∩ (F.piece (pp j)).output ∩ Icc tA tZ).Nonempty :=
        ⟨t, ⟨houtk, houtj⟩, ht⟩
      have hadj := hTcons (pp k) (pp j) hne hlab hno
      exact edgeFlux_quiet_overlap_atlas_of_contDiff F ν e E actual K hdesc T hTcov hTq hne hadj
        (hTact _ _ hadj hno) ⟨⟨⟨hq, ht⟩, houtk⟩, houtj⟩ honly hsum hU hrD v x a₀
    · have hlab : (F.piece (pp k)).label = (F.piece (pp j)).label + 1 ∨
          (F.piece (pp k)).label = (F.piece (pp j)).label := by
        rw [hlabel j hj, hlabel k hk, hk2]
        exact (ocPulseChartIndex_add_two hΛ j).symm
      have hno : ((F.piece (pp j)).output ∩ (F.piece (pp k)).output ∩ Icc tA tZ).Nonempty :=
        ⟨t, ⟨houtj, houtk⟩, ht⟩
      have hadj := hTcons (pp j) (pp k) hne.symm hlab hno
      exact edgeFlux_quiet_overlap_atlas_right_of_contDiff F ν e E actual K hdesc T hTcov hTq
        hne.symm hadj (hTact _ _ hadj hno) ⟨⟨⟨hq, ht⟩, houtj⟩, houtk⟩
        (fun p' hp' => (honly p' hp').symm) (by rw [add_comm]; exact hsum) hU hrD v x a₀

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory AVenhance
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Tested label divergences** (the chart transport of the presented residuals). For an
area-preserving chart `χ` with inverse `ψ`, both commuting with the integer translations, a `C¹`
periodic label flux `G` has a label divergence which, read at the labels `ψ x` and tested against a
`C¹` periodic `φ`, is minus the pairing of its Piola transport
`x ↦ ∑_{i₀} (Dψ(x))⁻¹_{a i₀} G_{i₀}(ψ x)` with `∇φ` (`tested_label_div`). -/

/-- A chart commuting with the integer translations has a periodic derivative. -/
theorem fderiv_periodic_of_lattice {χ : Vec 2 → Vec 2}
    (hχl : ∀ y (n : Fin 2 → ℤ), χ (y + latticeShift n) = χ y + latticeShift n) (y : Vec 2)
    (n : Fin 2 → ℤ) : fderiv ℝ χ (y + latticeShift n) = fderiv ℝ χ y := by
  rw [← fderiv_comp_add_right (f := χ) (x := y) (latticeShift n)]
  have hfun : (fun y' => χ (y' + latticeShift n)) = fun y' => χ y' + latticeShift n :=
    funext fun y' => hχl y' n
  rw [hfun, fderiv_add_const]

/-- The inverse of a chart commuting with the integer translations commutes with them. -/
theorem lattice_of_inverse {χ ψ : Vec 2 → Vec 2} (hψχ : ∀ y, ψ (χ y) = y)
    (hχψ : ∀ x, χ (ψ x) = x)
    (hψl : ∀ x (n : Fin 2 → ℤ), ψ (x + latticeShift n) = ψ x + latticeShift n) (y : Vec 2)
    (n : Fin 2 → ℤ) : χ (y + latticeShift n) = χ y + latticeShift n := by
  have h1 : ψ (χ y + latticeShift n) = y + latticeShift n := by rw [hψl, hψχ]
  rw [← h1, hχψ]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Piola transport of a continuous label flux is continuous. -/
theorem continuous_piola {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    {G : Vec 2 → Fin 2 → E} (hG : ∀ l, Continuous (fun y => G y l)) (a : Fin 2) :
    Continuous (fun x => ∑ i₀ : Fin 2, chartInvJacobian ψ x a i₀ • G (ψ x) i₀) := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hK : ∀ x (a i : Fin 2), chartInvJacobian ψ x a i = fderiv ℝ χ (ψ x) (basisVec i) a :=
    fun x a i => by
      rw [chartInvJacobian_eq_of_inverse hχd hψd hψχ hχψ x, chartJacobian_eq_jacMatrix]
      rfl
  simp only [hK]
  refine continuous_finsetSum _ fun i₀ _ => Continuous.smul ?_ ((hG i₀).comp hψ.continuous)
  have h1 : Continuous (fun x => fderiv ℝ χ (ψ x)) :=
    (hχ.continuous_fderiv (by simp)).comp hψ.continuous
  exact (continuous_apply a).comp (h1.clm_apply continuous_const)

/-- **Tested label divergence.** -/
theorem tested_label_div {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    (hd : ∀ y, (jacMatrix χ y).det = 1)
    (hψl : ∀ x (n : Fin 2 → ℤ), ψ (x + latticeShift n) = ψ x + latticeShift n)
    {G : Vec 2 → Fin 2 → E} (hG : ∀ l, ContDiff ℝ 1 (fun y => G y l))
    (hGp : ∀ l, IsZ2Periodic (fun y => G y l)) {φ : Vec 2 → E} (hφ : ContDiff ℝ 1 φ)
    (hφp : IsZ2Periodic φ) :
    ∫ x in unitCube, inner ℝ (∑ i₀ : Fin 2, fderiv ℝ (fun y => G y i₀) (ψ x) (basisVec i₀))
        (φ x) =
      -∫ x in unitCube, ∑ a : Fin 2, inner ℝ (∑ i₀ : Fin 2, chartInvJacobian ψ x a i₀ • G (ψ x) i₀)
        (fderiv ℝ φ x (basisVec a)) := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hK : ∀ x (a i : Fin 2), chartInvJacobian ψ x a i = fderiv ℝ χ (ψ x) (basisVec i) a :=
    fun x a i => by
      rw [chartInvJacobian_eq_of_inverse hχd hψd hψχ hχψ x, chartJacobian_eq_jacMatrix]
      rfl
  have hpt : ∀ x, ∑ i₀ : Fin 2, fderiv ℝ (fun y => G y i₀) (ψ x) (basisVec i₀) =
      ∑ a : Fin 2, fderiv ℝ (fun x' => ∑ i₀ : Fin 2, chartInvJacobian ψ x' a i₀ • G (ψ x') i₀) x
        (basisVec a) := fun x =>
    (chartInvJacobian_piola hχ hψ hψχ hχψ hd (fun l => (hG l).differentiable one_ne_zero) x).symm
  have hχl := lattice_of_inverse hψχ hχψ hψl
  simp only [hpt]
  refine cell_ibp_div (F := fun x a => ∑ i₀ : Fin 2, chartInvJacobian ψ x a i₀ • G (ψ x) i₀)
    (fun a => ?_) (fun a => ?_) hφ hφp
  · simp only [hK]
    refine ContDiff.sum fun i₀ _ => ContDiff.smul ?_ ((hG i₀).comp (hψ.of_le (by simp)))
    have h1 : ContDiff ℝ 1 (fun x => fderiv ℝ χ (ψ x)) :=
      (hχ.fderiv_right (m := 1) (by simp)).comp (hψ.of_le (by simp))
    exact (contDiff_apply ℝ ℝ a).comp (h1.clm_apply contDiff_const)
  · have hGp' : ∀ l y (n : Fin 2 → ℤ), G (y + latticeShift n) l = G y l := fun l y n =>
      hGp l n y
    intro n x
    simp only [hK, hψl, fderiv_periodic_of_lattice hχl, hGp']

end AVRegularity.CycleComparison.Reconstruction
end
