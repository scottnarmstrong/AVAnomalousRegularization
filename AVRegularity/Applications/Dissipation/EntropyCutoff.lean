-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Dissipation.Linear
public import AVenhance.Infra.Parabolic.WeakUniqueness.WeakProjectionConvergence
public import AVenhance.Infra.Parabolic.WeakUniqueness.ModePath
import AVenhance.Infra.Parabolic.WeakUniqueness.WeakEnergyPassage
import AVenhance.Infra.Parabolic.FourierGalerkin.Density
import AVenhance.Infra.Parabolic.FourierGalerkin.ScalarSpace
import AVenhance.Infra.Classical.GalerkinGenerator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! # Convex entropy on the Fourier cutoffs of a weak solution

Unit window, upstream form: `u` solves `IsWeakSolutionGrad B κ f u D`. Its finite real Fourier
cutoffs `u_N(s) = weakFourierModeProjection N u s = Σ_j c_j(s) e_j` have coefficient integral
paths `c_j(s) = c_j(0) - ∫_0^s q_j` (`weak_solution_mode_integral_path`), with forcings
`q_j = weakModeForcing B κ D e_j`. For a smooth `J` with `J'' ≥ 0`:

* `sub_eq_integral_deriv_mul_of_path`: the chain rule `J(v(t)) - J(v(0)) = ∫_0^t J'(v) g` for an
  integral path `v = v(0) + ∫ g`;
* `integral_comp_expansion_sub`: `∫ J(u_N(t)) - ∫ J(u_N(0)) = -∫_0^t Σ_j q_j ⟨J'(u_N), e_j⟩`
  for an abstract finite expansion;
* `tendsto_l2NormSq_sub_cutoff`, `l2NormSq_sub_cutoff_le`: the cutoffs of any cell-`L²` slice
  converge to it, with the Bessel bound;
* the diffusion pairing `Σ_j ⟨h, e_j⟩ ⟨D, ∇e_j⟩ = Σ_k ⟨∂_k u_N, ∂_k h⟩` and its sign for
  `h = J'(u_N)`;
* `integral_comp_cutoff_le`: `∫ J(u_N(t)) ≤ ∫ J(u_N(0)) - ∫_0^t ∫ P_N(B·D) J'(u_N)`. -/

public section

open MeasureTheory Filter Topology Homogenization AVenhance
open AVenhance.Infra.Parabolic.WeakUniqueness AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Classical

namespace AVRegularity.Applications.Dissipation

/-! ### The scalar chain rule along an integral path -/

/-- `J(v(t)) - J(v(0)) = ∫_0^t J'(v(s)) g(s) ds` for `v = v(0) + ∫_0 g` and `J ∈ C¹`. -/
theorem sub_eq_integral_deriv_mul_of_path {J : ℝ → ℝ} (hJ : ContDiff ℝ 1 J) {v g : ℝ → ℝ}
    {t : ℝ} (ht : 0 ≤ t) (hg : IntervalIntegrable g volume 0 t)
    (hv : ∀ s ∈ Set.Icc (0 : ℝ) t, v s = v 0 + ∫ r in (0 : ℝ)..s, g r) :
    J (v t) - J (v 0) = ∫ s in (0 : ℝ)..t, deriv J (v s) * g s := by
  have hPac : AbsolutelyContinuousOnInterval (fun s => ∫ r in (0 : ℝ)..s, g r) 0 t :=
    hg.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc
  obtain ⟨C, hC⟩ := hPac.exists_bound
  have hKc : ContDiff ℝ 1 (fun y => J (v 0 + y)) := hJ.comp (contDiff_const.add contDiff_id)
  obtain ⟨L, hL⟩ := hKc.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_Icc (-C) C)
    isCompact_Icc
  have hmaps : Set.MapsTo (fun s => ∫ r in (0 : ℝ)..s, g r) (Set.uIcc 0 t) (Set.Icc (-C) C) :=
    fun s hs => abs_le.1 (by simpa [Real.norm_eq_abs] using hC s hs)
  have hFTC := (hL.comp_absolutelyContinuousOnInterval hmaps hPac).integral_deriv_eq_sub
  have hJd : ∀ y, HasDerivAt J (deriv J y) y := fun y =>
    ((hJ.differentiable (by simp)) y).hasDerivAt
  have hcongr : ∫ s in (0 : ℝ)..t,
      deriv ((fun y => J (v 0 + y)) ∘ fun s => ∫ r in (0 : ℝ)..s, g r) s =
      ∫ s in (0 : ℝ)..t, deriv J (v s) * g s := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hg.ae_hasDerivAt_integral] with s hs hsI
    have hd := hs (Set.uIoc_subset_uIcc hsI) 0 Set.left_mem_uIcc
    have e : deriv ((fun y => J (v 0 + y)) ∘ fun s => ∫ r in (0 : ℝ)..s, g r) s =
        deriv J (v 0 + ∫ r in (0 : ℝ)..s, g r) * g s :=
      ((hJd _).comp s (hd.const_add (v 0))).deriv
    rw [Set.uIoc_of_le ht] at hsI
    rw [e, ← hv s ⟨hsI.1.le, hsI.2⟩]
  rw [hcongr] at hFTC
  simp only [Function.comp_apply, intervalIntegral.integral_same, add_zero] at hFTC
  rw [hFTC, ← hv t ⟨ht, le_rfl⟩]

/-! ### Cutoffs of a cell-`L²` slice -/

/-- The cell error of a cutoff is its torus `L²` error (upstream
`weakFourierProjection_scalarCellError_normSq`, for any path with an `L²` slice). -/
theorem l2NormSq_sub_cutoff_eq {U : ℝ → Vec 2 → ℝ} {s : ℝ} (hU : MemL2On unitCube (U s))
    (N : ℕ) :
    l2NormSq (fun x => U s x - weakFourierModeProjection N U s x) =
      ‖(weakProjection_realCellToTorus_memLp hU).toLp
          (Infra.Torus.periodicToTorus (U s)) - weakFourierProjectionL2 N U s‖ ^ 2 := by
  let p := weakFourierModeProjection N U s
  have hp : MemL2On unitCube p :=
    weak_continuous_memL2On (realFourierModeAmbientExpansion_contDiff N
      (weakFourierCoefficientPath N U s) |>.continuous)
  have hdiff : MemL2On unitCube (fun x => U s x - p x) := hU.sub hp
  have hclass : (weakProjection_realCellToTorus_memLp hdiff).toLp
      (Infra.Torus.periodicToTorus (fun x => U s x - p x)) =
      (weakProjection_realCellToTorus_memLp hU).toLp (Infra.Torus.periodicToTorus (U s)) -
        weakFourierProjectionL2 N U s := by
    apply Lp.ext
    filter_upwards [(weakProjection_realCellToTorus_memLp hdiff).coeFn_toLp,
      (weakProjection_realCellToTorus_memLp hU).coeFn_toLp,
      (weakProjection_realCellToTorus_memLp hp).coeFn_toLp,
      Lp.coeFn_sub ((weakProjection_realCellToTorus_memLp hU).toLp
        (Infra.Torus.periodicToTorus (U s))) (weakFourierProjectionL2 N U s)]
      with x hdiffX huX hpX hsub
    have hPNclass : weakFourierProjectionL2 N U s =
        (weakProjection_realCellToTorus_memLp hp).toLp (Infra.Torus.periodicToTorus p) := by
      simpa [p, weakFourierModeProjection] using weakFourierProjectionL2_eq_expansionTransfer N U s
    have hPN : weakFourierProjectionL2 N U s x = Infra.Torus.periodicToTorus p x := by
      rw [congrArg (fun v : ScalarTorusL2 => v x) hPNclass, hpX]
    rw [hdiffX, hsub]
    simp only [Pi.sub_apply]
    rw [huX, hPN]
    simp [Infra.Torus.periodicToTorus]
  rw [← hclass]
  exact (weakProjection_scalarTransfer_normSq hdiff).symm

/-- The cutoffs of a cell-`L²` slice converge to it in cell `L²`. -/
theorem tendsto_l2NormSq_sub_cutoff {U : ℝ → Vec 2 → ℝ} {s : ℝ}
    (hU : MemL2On unitCube (U s)) :
    Tendsto (fun N => l2NormSq (fun x => U s x - weakFourierModeProjection N U s x))
      atTop (𝓝 0) := by
  have h := weakFourierProjectionL2_tendsto (u := U) (t := s) hU
  have h2 := ((tendsto_const_nhds (x := (weakProjection_realCellToTorus_memLp hU).toLp
    (Infra.Torus.periodicToTorus (U s)))).sub h).norm.pow 2
  simp only [sub_self, norm_zero] at h2
  rw [show ((0 : ℝ) ^ 2) = 0 by norm_num] at h2
  exact h2.congr fun N => (l2NormSq_sub_cutoff_eq hU N).symm

/-- Bessel: the cell error of a cutoff is at most the cell norm of the slice. -/
theorem l2NormSq_sub_cutoff_le {U : ℝ → Vec 2 → ℝ} {s : ℝ} (hU : MemL2On unitCube (U s))
    (N : ℕ) :
    l2NormSq (fun x => U s x - weakFourierModeProjection N U s x) ≤ l2NormSq (U s) := by
  set v := (weakProjection_realCellToTorus_memLp hU).toLp (Infra.Torus.periodicToTorus (U s))
  have hcoeff : realFourierProjectionCoefficients N v = weakFourierCoefficientPath N U s := by
    rw [WeakProjectionConvergence.weakProjection_scalarL2_coefficients_eq_pairing hU]
    exact WeakProjectionConvergence.weakProjection_scalarCoefficient_eq_pairing
  have hP : weakFourierProjectionL2 N U s =
      realFourierScalarMap N (realFourierProjectionCoefficients N v) := by
    rw [hcoeff]
    rfl
  rw [l2NormSq_sub_cutoff_eq hU N, hP, WeakProjectionConvergence.weakProjection_pythagorean,
    ← weakProjection_scalarTransfer_normSq hU]
  have := sq_nonneg ‖realFourierScalarMap N (realFourierProjectionCoefficients N v)‖
  linarith

/-! ### The chain rule for a finite expansion with integral-path coefficients -/

/-- The unit cell has finite measure. -/
local instance dissipationCutoffFiniteCube : IsFiniteMeasure (volume.restrict unitCube) :=
  isFiniteMeasure_restrict.2 unitCube_measure_ne_top

/-- A continuous function is bounded on a closed time interval times the cell. -/
theorem exists_bound_Icc_cell (a b : ℝ) {F : ℝ × Vec 2 → ℝ} (hF : Continuous F) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc a b, ∀ x ∈ unitCube, ‖F (s, x)‖ ≤ C := by
  have hK : IsCompact (Set.Icc a b ×ˢ Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  exact ⟨C, fun s hs x hx => hC (s, x) ⟨hs, fun i hi => ⟨(hx i hi).1.le, (hx i hi).2.le⟩⟩⟩

/-- A continuous function is integrable on the cell. -/
theorem integrable_continuous_cell {F : Vec 2 → ℝ} (hF : Continuous F) :
    Integrable F (volume.restrict unitCube) :=
  (weak_continuous_memL2On hF).integrable one_le_two

/-- **Cutoff chain rule.** For a finite expansion `Σ_j c_j(s) e_j(x)` with continuous modes and
continuous coefficients that are integral paths `c_j(s) = c_j(0) - ∫_0^s q_j` on `[0, 1]`, and
`J ∈ C¹`: `∫ J(Σ c_j(t) e_j) - ∫ J(Σ c_j(0) e_j) = -∫_0^t Σ_j q_j(s) ∫ J'(Σ_i c_i(s) e_i) e_j`. -/
theorem integral_comp_expansion_sub {n : ℕ} {e : Fin n → Vec 2 → ℝ}
    (he : ∀ j, Continuous (e j)) {c q : Fin n → ℝ → ℝ} (hc : ∀ j, Continuous (c j))
    (hq : ∀ j, IntervalIntegrable (q j) volume 0 1)
    (hpath : ∀ j, ∀ s ∈ Set.Icc (0 : ℝ) 1, c j s = c j 0 - ∫ r in (0 : ℝ)..s, q j r)
    {J : ℝ → ℝ} (hJ : ContDiff ℝ 1 J) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x in unitCube, J (∑ j, c j t * e j x)) - ∫ x in unitCube, J (∑ j, c j 0 * e j x) =
      -∫ s in (0 : ℝ)..t,
        ∑ j, q j s * ∫ x in unitCube, deriv J (∑ i, c i s * e i x) * e j x := by
  have hsub : ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 → Set.uIcc (0 : ℝ) s ⊆ Set.uIcc 0 1 :=
    fun {s} hs => by
      rw [Set.uIcc_of_le hs.1, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc le_rfl hs.2
  have hqt : ∀ j, IntervalIntegrable (q j) volume 0 t := fun j => (hq j).mono_set (hsub ht)
  have hJ' : Continuous (deriv J) := hJ.continuous_deriv le_rfl
  have hwx : ∀ s, Continuous (fun x => ∑ j, c j s * e j x) := fun s =>
    continuous_finsetSum _ fun j _ => continuous_const.mul (he j)
  have hpt : ∀ x, J (∑ j, c j t * e j x) - J (∑ j, c j 0 * e j x) =
      ∫ s in (0 : ℝ)..t, deriv J (∑ i, c i s * e i x) * -(∑ j, q j s * e j x) := by
    intro x
    refine sub_eq_integral_deriv_mul_of_path hJ (v := fun s => ∑ j, c j s * e j x)
      (g := fun s => -(∑ j, q j s * e j x)) ht.1 ?_ ?_
    · have h := IntervalIntegrable.sum Finset.univ fun j _ => (hqt j).mul_const (e j x)
      refine h.neg.congr fun s _ => ?_
      simp [Finset.sum_apply]
    · intro s hs
      have hs1 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
      have hqs : ∀ j, IntervalIntegrable (q j) volume 0 s := fun j => (hq j).mono_set (hsub hs1)
      rw [intervalIntegral.integral_neg,
        intervalIntegral.integral_finsetSum (fun j _ => (hqs j).mul_const _)]
      simp only [intervalIntegral.integral_mul_const]
      have e1 : ∀ j, c j s * e j x = c j 0 * e j x - (∫ r in (0 : ℝ)..s, q j r) * e j x :=
        fun j => by rw [hpath j s hs1]; ring
      simp only [e1, Finset.sum_sub_distrib]
      ring
  refine (integral_sub (integrable_continuous_cell (F := fun x => J (∑ j, c j t * e j x))
    (hJ.continuous.comp (hwx t))) (integrable_continuous_cell
      (F := fun x => J (∑ j, c j 0 * e j x)) (hJ.continuous.comp (hwx 0)))).symm.trans ?_
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  simp only [intervalIntegral.integral_of_le ht.1]
  have hjoint : ∀ j, Continuous (fun p : Vec 2 × ℝ => deriv J (∑ i, c i p.2 * e i p.1) * e j p.1) :=
    fun j => (hJ'.comp (continuous_finsetSum _ fun i _ =>
      ((hc i).comp continuous_snd).mul ((he i).comp continuous_fst))).mul ((he j).comp continuous_fst)
  have hprod : ∀ j, Integrable (fun p : Vec 2 × ℝ =>
      q j p.2 * (deriv J (∑ i, c i p.2 * e i p.1) * e j p.1))
      ((volume.restrict unitCube).prod (volume.restrict (Set.Ioc (0 : ℝ) t))) := by
    intro j
    obtain ⟨C, hC⟩ := exists_bound_Icc_cell 0 t
      ((hjoint j).comp (continuous_snd.prodMk continuous_fst))
    have hqI : Integrable (q j) (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).1 (hqt j)
    refine (hqI.comp_snd _).mul_bdd (hjoint j).aestronglyMeasurable (c := C) ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_unitCube'.prod measurableSet_Ioc)] with p hp
    exact hC p.2 ⟨hp.2.1.le, hp.2.2⟩ p.1 hp.1
  have hswap := integral_integral_swap (μ := volume.restrict unitCube)
    (ν := volume.restrict (Set.Ioc (0 : ℝ) t))
    (f := fun x s => deriv J (∑ i, c i s * e i x) * -(∑ j, q j s * e j x)) (by
      refine ((integrable_finsetSum Finset.univ fun j _ => hprod j).neg).congr
        (Filter.Eventually.of_forall fun p => ?_)
      rcases p with ⟨x, y⟩
      simp only [Function.uncurry_apply_pair, Pi.neg_apply]
      rw [mul_neg, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring)
  rw [hswap, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have hcj : ∀ j, Integrable (fun x => q j s * (deriv J (∑ i, c i s * e i x) * e j x))
      (volume.restrict unitCube) := fun j =>
    (integrable_continuous_cell ((hJ'.comp (hwx s)).mul (he j))).const_mul _
  have e2 : (fun x => deriv J (∑ i, c i s * e i x) * -∑ j, q j s * e j x) =
      fun x => -∑ j, q j s * (deriv J (∑ i, c i s * e i x) * e j x) := by
    funext x
    rw [mul_neg, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [e2, integral_neg, integral_finsetSum _ fun j _ => hcj j, integral_const_mul]

/-- The product of an integrable time coefficient and a continuous space-time factor of the
expansion is integrable on the cell times `(0, t]`. -/
theorem integrable_coeff_mul_mode {n : ℕ} {e : Fin n → Vec 2 → ℝ} (he : ∀ j, Continuous (e j))
    {c : Fin n → ℝ → ℝ} (hc : ∀ j, Continuous (c j)) {J : ℝ → ℝ} (hJ' : Continuous (deriv J))
    {t : ℝ} {q : ℝ → ℝ} (hq : IntegrableOn q (Set.Ioc (0 : ℝ) t)) (j : Fin n) :
    Integrable (fun p : Vec 2 × ℝ => q p.2 * (deriv J (∑ i, c i p.2 * e i p.1) * e j p.1))
      ((volume.restrict unitCube).prod (volume.restrict (Set.Ioc (0 : ℝ) t))) := by
  have hjoint : Continuous (fun p : Vec 2 × ℝ => deriv J (∑ i, c i p.2 * e i p.1) * e j p.1) :=
    (hJ'.comp (continuous_finsetSum _ fun i _ =>
      ((hc i).comp continuous_snd).mul ((he i).comp continuous_fst))).mul
      ((he j).comp continuous_fst)
  obtain ⟨C, hC⟩ := exists_bound_Icc_cell 0 t (hjoint.comp (continuous_snd.prodMk continuous_fst))
  refine (Integrable.comp_snd hq _).mul_bdd hjoint.aestronglyMeasurable (c := C) ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_unitCube'.prod measurableSet_Ioc)] with p hp
  exact hC p.2 ⟨hp.2.1.le, hp.2.2⟩ p.1 hp.1

/-- The time function `q(s) ⟨J'(Σ c_i(s) e_i), e_j⟩` is integrable on `(0, t]`. -/
theorem intervalIntegrable_coeff_mul_pairing {n : ℕ} {e : Fin n → Vec 2 → ℝ}
    (he : ∀ j, Continuous (e j)) {c : Fin n → ℝ → ℝ} (hc : ∀ j, Continuous (c j)) {J : ℝ → ℝ}
    (hJ' : Continuous (deriv J)) {t : ℝ} (ht : 0 ≤ t) {q : ℝ → ℝ}
    (hq : IntervalIntegrable q volume 0 t) (j : Fin n) :
    IntervalIntegrable
      (fun s => q s * ∫ x in unitCube, deriv J (∑ i, c i s * e i x) * e j x) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  have h := (integrable_coeff_mul_mode he hc hJ'
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1 hq) j).integral_prod_right
  refine h.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only
  rw [integral_const_mul]

/-! ### The diffusion pairing on the cutoffs -/

/-- The `j`-th real Fourier mode of the cutoff `N` on Euclidean representatives. -/
noncomputable abbrev cutMode (N : ℕ) (j : Fin (RealFourierDimension N)) : Vec 2 → ℝ :=
  realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j)

theorem cutMode_continuous (N : ℕ) (j : Fin (RealFourierDimension N)) :
    Continuous (cutMode N j) :=
  (realFourierModeAmbient_contDiff N _).continuous

theorem cutMode_contDiff (N : ℕ) (j : Fin (RealFourierDimension N)) :
    ContDiff ℝ (⊤ : ℕ∞) (cutMode N j) :=
  (realFourierModeAmbient_contDiff N _).of_le le_top

theorem cutMode_spaceGrad_continuous (N : ℕ) (j : Fin (RealFourierDimension N)) (k : Fin 2) :
    Continuous (fun x => spaceGrad (cutMode N j) x k) :=
  ((cutMode_contDiff N j).continuous_fderiv (by simp)).clm_apply continuous_const

/-- The entries of a coefficient path are cell pairings with the modes. -/
theorem coefficientPath_apply (N : ℕ) (U : ℝ → Vec 2 → ℝ) (s : ℝ)
    (j : Fin (RealFourierDimension N)) :
    weakFourierCoefficientPath N U s j = ∫ x in unitCube, U s x * cutMode N j x := by
  simp [weakFourierCoefficientPath, weakModePairing]

/-- `∫ g · Σ_j a_j φ_j = Σ_j a_j ∫ g φ_j` for a cell-`L²` `g` and continuous `φ_j`. -/
theorem integral_mul_sum_continuous {n : ℕ} {g : Vec 2 → ℝ} (hg : MemL2On unitCube g)
    {φ : Fin n → Vec 2 → ℝ} (hφ : ∀ j, Continuous (φ j)) (a : Fin n → ℝ) :
    ∫ x in unitCube, g x * ∑ j, a j * φ j x = ∑ j, a j * ∫ x in unitCube, g x * φ j x := by
  have hi : ∀ j, Integrable (fun x => a j * (g x * φ j x)) (volume.restrict unitCube) :=
    fun j => (integrable_mul_continuous_cell hg (hφ j)).const_mul (a j)
  have e : (fun x => g x * ∑ j, a j * φ j x) = fun x => ∑ j, a j * (g x * φ j x) := by
    funext x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, integral_finsetSum _ fun j _ => hi j]
  simp only [integral_const_mul]

/-- The gradient of an expansion is the expansion of the mode gradients. -/
theorem spaceGrad_expansion_eq_sum (N : ℕ) (c : Coefficients (RealFourierDimension N))
    (k : Fin 2) (x : Vec 2) :
    spaceGrad (realFourierModeAmbientExpansion N c) x k =
      ∑ j, c j * spaceGrad (cutMode N j) x k := by
  unfold realFourierModeAmbientExpansion
  rw [GalerkinModeCalculus.spaceGrad_finset_sum Finset.univ
    (fun j y => c j * cutMode N j y)
    (fun j _ => (contDiff_const : ContDiff ℝ ⊤ (fun _ : Vec 2 => (c j : ℝ))).mul
      (realFourierModeAmbient_contDiff N _))]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact GalerkinModeCalculus.spaceGrad_realConstant_mul
    ((realFourierModeAmbient_contDiff N _).of_le le_top) (c j) k x

/-- **Diffusion pairing.** For `u ∈ H¹_per` with gradient `Du` and smooth periodic `h`:
`Σ_j ⟨h, e_j⟩ ⟨Du, ∇e_j⟩ = Σ_k ⟨∂_k P_N u, ∂_k h⟩`. -/
theorem sum_pairing_grad_cutMode_eq {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : IsPeriodicH1With u Du) {h : Vec 2 → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhp : IsZ2Periodic h) (N : ℕ) :
    ∑ j, (∫ x in unitCube, h x * cutMode N j x) *
        ∫ x in unitCube, Homogenization.vecDot (Du x) (spaceGrad (cutMode N j) x) =
      ∑ k : Fin 2, ∫ x in unitCube,
        spaceGrad (weakFourierModeProjection N (fun _ => u) 0) x k * spaceGrad h x k := by
  have hhk : ∀ k : Fin 2, Continuous (fun x => spaceGrad h x k) := fun k =>
    (hh.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDk : ∀ k : Fin 2, MemL2On unitCube (fun x => Du x k) := hu.2.2.2.1
  -- the derivative coefficients of `u` and of `h`
  have hγ : ∀ k : Fin 2, realFourierModeDerivativeCoefficients N
      (weakFourierCoefficientPath N (fun _ => u) 0) k =
      weakFourierCoefficientPath N (fun _ x => Du x k) 0 := by
    intro k
    have h1 := weakGradient_realFourierProjectionCoefficients hu N k
    rw [WeakProjectionConvergence.weakProjection_scalarCoefficient_eq_pairing (u := fun _ => u)
      (t := 0), WeakProjectionConvergence.weakProjection_scalarCoefficient_eq_pairing
      (u := fun _ x => Du x k) (t := 0)] at h1
    exact h1
  have ha : ∀ k : Fin 2, realFourierModeDerivativeCoefficients N
      (weakFourierCoefficientPath N (fun _ => h) 0) k =
      weakFourierCoefficientPath N (fun _ x => spaceGrad h x k) 0 := by
    intro k
    have h1 := realFourierModeDerivativeCoefficients_projection N h hh hhp k
    rw [WeakProjectionConvergence.weakProjection_scalarCoefficient_eq_pairing (u := fun _ => h)
      (t := 0), WeakProjectionConvergence.weakProjection_scalarCoefficient_eq_pairing
      (u := fun _ x => spaceGrad h x k) (t := 0)] at h1
    exact h1
  -- left side, coordinate by coordinate
  have hL : ∀ j, ∫ x in unitCube, Homogenization.vecDot (Du x) (spaceGrad (cutMode N j) x) =
      ∑ k : Fin 2, ∫ x in unitCube, Du x k * spaceGrad (cutMode N j) x k := by
    intro j
    rw [← integral_finsetSum _ fun k _ =>
      integrable_mul_continuous_cell (hDk k) (cutMode_spaceGrad_continuous N j k)]
    rfl
  have hLk : ∀ k : Fin 2, ∑ j, (∫ x in unitCube, h x * cutMode N j x) *
      ∫ x in unitCube, Du x k * spaceGrad (cutMode N j) x k =
      ∑ j, realFourierModeDerivativeCoefficients N
        (weakFourierCoefficientPath N (fun _ => h) 0) k j *
        realFourierModeDerivativeCoefficients N
          (weakFourierCoefficientPath N (fun _ => u) 0) k j := by
    intro k
    have e1 := integral_mul_sum_continuous (hDk k) (fun j => cutMode_spaceGrad_continuous N j k)
      (fun j => weakFourierCoefficientPath N (fun _ => h) 0 j)
    simp only [coefficientPath_apply] at e1
    rw [← e1]
    have e2 : (fun x => Du x k * ∑ j, (∫ y in unitCube, h y * cutMode N j y) *
        spaceGrad (cutMode N j) x k) = fun x => Du x k *
          realFourierModeAmbientExpansion N (realFourierModeDerivativeCoefficients N
            (weakFourierCoefficientPath N (fun _ => h) 0) k) x := by
      funext x
      rw [← congrFun (spaceGrad_realFourierModeAmbientExpansion_eq_derivativeExpansion N _ k) x,
        spaceGrad_expansion_eq_sum]
      simp only [coefficientPath_apply]
    rw [e2]
    unfold realFourierModeAmbientExpansion
    rw [integral_mul_sum_continuous (hDk k) (fun j => cutMode_continuous N j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hγ k, coefficientPath_apply]
  have hRk : ∀ k : Fin 2, ∫ x in unitCube,
      spaceGrad (weakFourierModeProjection N (fun _ => u) 0) x k * spaceGrad h x k =
      ∑ j, realFourierModeDerivativeCoefficients N
          (weakFourierCoefficientPath N (fun _ => u) 0) k j *
        realFourierModeDerivativeCoefficients N
          (weakFourierCoefficientPath N (fun _ => h) 0) k j := by
    intro k
    have e2 : (fun x => spaceGrad (weakFourierModeProjection N (fun _ => u) 0) x k *
        spaceGrad h x k) = fun x => spaceGrad h x k * ∑ j,
          realFourierModeDerivativeCoefficients N
            (weakFourierCoefficientPath N (fun _ => u) 0) k j * cutMode N j x := by
      funext x
      rw [mul_comm]
      congr 1
      exact congrFun (spaceGrad_realFourierModeAmbientExpansion_eq_derivativeExpansion N _ k) x
    rw [e2, integral_mul_sum_continuous (weak_continuous_memL2On (hhk k))
      (fun j => cutMode_continuous N j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ha k, coefficientPath_apply]
  simp only [hL, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hLk k, hRk k]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-! ### The sign of the diffusion term and the cutoff entropy inequality -/

/-- Chain rule for the spatial gradient: `∂_k (F ∘ w) = F'(w) ∂_k w`. -/
theorem spaceGrad_comp_of_differentiable {w : Vec 2 → ℝ} (hw : Differentiable ℝ w)
    {F : ℝ → ℝ} (hF : Differentiable ℝ F) (x : Vec 2) (k : Fin 2) :
    spaceGrad (fun y => F (w y)) x k = deriv F (w x) * spaceGrad w x k := by
  have hd := ((hF (w x)).hasDerivAt).comp_hasFDerivAt x (hw x).hasFDerivAt
  change fderiv ℝ (F ∘ w) x (basisVec k) = deriv F (w x) * fderiv ℝ w x (basisVec k)
  rw [hd.fderiv]
  simp

/-- The derivative of a smooth function is differentiable. -/
theorem differentiable_deriv_of_smooth {J : ℝ → ℝ} (hJ : ContDiff ℝ (⊤ : ℕ∞) J) :
    Differentiable ℝ (deriv J) := by
  have h := hJ.iterate_deriv 1
  simpa using h.differentiable (by simp)

/-- **Sign of the diffusion term:** `Σ_k ∫ ∂_k w ∂_k (J'(w)) = ∫ J''(w) |∇w|² ≥ 0`. -/
theorem sum_integral_grad_mul_grad_deriv_comp_nonneg {w : Vec 2 → ℝ}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) {J : ℝ → ℝ} (hJ : ContDiff ℝ (⊤ : ℕ∞) J)
    (hJ2 : ∀ r, 0 ≤ deriv (deriv J) r) :
    0 ≤ ∑ k : Fin 2, ∫ x in unitCube, spaceGrad w x k * spaceGrad (fun y => deriv J (w y)) x k := by
  refine Finset.sum_nonneg fun k _ => integral_nonneg fun x => ?_
  rw [spaceGrad_comp_of_differentiable (hw.differentiable (by simp))
    (differentiable_deriv_of_smooth hJ) x k]
  have e : spaceGrad w x k * (deriv (deriv J) (w x) * spaceGrad w x k) =
      deriv (deriv J) (w x) * spaceGrad w x k ^ 2 := by ring
  rw [e]
  exact mul_nonneg (hJ2 _) (sq_nonneg _)

/-- **Cutoff entropy inequality** (unit window). For a weak solution with `κ ≥ 0`, a smooth `J`
with `J'' ≥ 0` and every cutoff `N`:
`∫ J(u_N(t)) ≤ ∫ J(u_N(0)) - ∫_0^t ∫ P_N(B·D) J'(u_N)`. -/
theorem integral_comp_cutoff_le {B : ℝ → Vec 2 → Vec 2} {κ : ℝ} (hκ : 0 ≤ κ)
    {f : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : IsWeakSolutionGrad B κ f u D) (hf : MemL2On unitCube f)
    {J : ℝ → ℝ} (hJ : ContDiff ℝ (⊤ : ℕ∞) J) (hJ2 : ∀ r, 0 ≤ deriv (deriv J) r) (N : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x in unitCube, J (weakFourierModeProjection N u t x)) ≤
      (∫ x in unitCube, J (weakFourierModeProjection N u 0 x)) -
        ∫ s in (0 : ℝ)..t, ∫ x in unitCube,
          weakFourierModeProjection N (fun s x => Homogenization.vecDot (B s x) (D s x)) s x *
            deriv J (weakFourierModeProjection N u s x) := by
  classical
  have hJ' : Continuous (deriv J) := (differentiable_deriv_of_smooth hJ).continuous
  have hJ1 : ContDiff ℝ 1 J := hJ.of_le (by simp)
  have ht1 : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc le_rfl ht.2
  -- coefficients, forcings, integral paths
  let c : Fin (RealFourierDimension N) → ℝ → ℝ := fun j s =>
    WeakEnergyPassage.weakEnergyCoefficientExtension N u j s
  let q : Fin (RealFourierDimension N) → ℝ → ℝ := fun j => weakModeForcing B κ D (cutMode N j)
  have hc : ∀ j, Continuous (c j) := fun j =>
    WeakEnergyPassage.weakEnergyCoefficientExtension_continuous hu N j
  have hq : ∀ j, IntervalIntegrable (q j) volume 0 1 := fun j =>
    weak_solution_mode_forcing_intervalIntegrable hu (cutMode_contDiff N j)
  have hcs : ∀ j, ∀ s ∈ Set.Icc (0 : ℝ) 1, c j s = ∫ x in unitCube, u s x * cutMode N j x := by
    intro j s hs
    simp only [c, WeakEnergyPassage.weakEnergyCoefficientExtension_eq N u j hs, weakModePairing]
  have hpath : ∀ j, ∀ s ∈ Set.Icc (0 : ℝ) 1, c j s = c j 0 - ∫ r in (0 : ℝ)..s, q j r := by
    intro j s hs
    have h1 := weak_solution_mode_integral_path hu hf (cutMode_contDiff N j)
      (realFourierModeAmbient_periodic N _) s hs
    have h0 := weak_solution_mode_integral_path hu hf (cutMode_contDiff N j)
      (realFourierModeAmbient_periodic N _) 0 ⟨le_rfl, zero_le_one⟩
    rw [intervalIntegral.integral_same, sub_zero] at h0
    rw [hcs j s hs, hcs j 0 ⟨le_rfl, zero_le_one⟩]
    simp only [weakModePairing] at h0 h1
    rw [h1, h0]
  have hexp : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      ∑ j, c j s * cutMode N j x = weakFourierModeProjection N u s x := by
    intro s hs x
    simp only [weakFourierModeProjection, realFourierModeAmbientExpansion, coefficientPath_apply,
      hcs _ s hs]
  have hB := integral_comp_expansion_sub (fun j => cutMode_continuous N j) hc hq hpath hJ1 ht
  simp only [hexp t ht, hexp 0 ⟨le_rfl, zero_le_one⟩] at hB
  -- the two time functions
  let G : ℝ → Vec 2 → ℝ := fun s x => Homogenization.vecDot (B s x) (D s x)
  let a : Fin (RealFourierDimension N) → ℝ → ℝ := fun j s =>
    ∫ x in unitCube, deriv J (weakFourierModeProjection N u s x) * cutMode N j x
  let γ : Fin (RealFourierDimension N) → ℝ → ℝ := fun j s => ∫ x in unitCube, G s x * cutMode N j x
  have hF2 : ∫ s in (0 : ℝ)..t, ∑ j, q j s * ∫ x in unitCube,
      deriv J (∑ i, c i s * cutMode N i x) * cutMode N j x =
      ∫ s in (0 : ℝ)..t, ∑ j, q j s * a j s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht.1] at hs
    simp only [a, hexp s (ht1 hs)]
  rw [hF2] at hB
  have hF1 : ∀ s, ∫ x in unitCube,
      weakFourierModeProjection N (fun s x => Homogenization.vecDot (B s x) (D s x)) s x *
        deriv J (weakFourierModeProjection N u s x) = ∑ j, γ j s * a j s := by
    intro s
    have hg : MemL2On unitCube (fun x => deriv J (weakFourierModeProjection N u s x)) :=
      weak_continuous_memL2On (hJ'.comp (realFourierModeAmbientExpansion_contDiff N _).continuous)
    have h1 := integral_mul_sum_continuous hg (fun j => cutMode_continuous N j) (fun j => γ j s)
    have e : (fun x => weakFourierModeProjection N G s x *
        deriv J (weakFourierModeProjection N u s x)) =
        fun x => deriv J (weakFourierModeProjection N u s x) * ∑ j, γ j s * cutMode N j x := by
      funext x
      rw [mul_comm]
      simp only [weakFourierModeProjection, realFourierModeAmbientExpansion,
        coefficientPath_apply, γ]
    change ∫ x in unitCube, weakFourierModeProjection N G s x *
      deriv J (weakFourierModeProjection N u s x) = _
    rw [e, h1]
  simp only [hF1]
  -- integrability of the two time functions on `[0, t]`
  have hGe : ∀ j, Integrable (fun p : ℝ × Vec 2 => G p.1 p.2 * cutMode N j p.2)
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (volume.restrict unitCube)) := by
    intro j
    rw [← weakEnergy_timeCube_measure_eq_product]
    obtain ⟨C, hC⟩ := exists_bound_cube (cutMode_continuous N j)
    refine hu.2.2.2.2.2.1.mul_bdd
      ((cutMode_continuous N j).comp continuous_snd).aestronglyMeasurable (c := C) ?_
    filter_upwards [ae_restrict_mem WeakEnergyPassage.weakEnergy_timeCube_measurable] with p hp
    simpa [Real.norm_eq_abs] using hC p.2 hp.2
  have hγint : ∀ j, IntervalIntegrable (γ j) volume 0 t := by
    intro j
    have h1 : IntegrableOn (γ j) (Set.Ioo (0 : ℝ) 1) := (hGe j).integral_prod_left
    have h2 : IntegrableOn (γ j) (Set.Ioc (0 : ℝ) 1) :=
      (integrableOn_Ioc_iff_integrableOn_Ioo).2 h1
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 h2).mono_set (by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
      exact ht1)
  have hint : ∀ {r : Fin (RealFourierDimension N) → ℝ → ℝ},
      (∀ j, IntervalIntegrable (r j) volume 0 t) →
      IntervalIntegrable (fun s => ∑ j, r j s * a j s) volume 0 t := by
    intro r hr
    have h := IntervalIntegrable.sum Finset.univ fun j _ =>
      intervalIntegrable_coeff_mul_pairing (fun i => cutMode_continuous N i) hc hJ' ht.1 (hr j) j
    refine h.congr fun s hs => ?_
    rw [Set.uIoc_of_le ht.1] at hs
    simp only [Finset.sum_apply, a, hexp s (ht1 ⟨hs.1.le, hs.2⟩)]
  have hqt : ∀ j, IntervalIntegrable (q j) volume 0 t := fun j => (hq j).mono_set (by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
    exact ht1)
  -- pointwise comparison for a.e. time
  have hH := (ae_restrict_iff' measurableSet_Ioo).1 hu.2.2.2.2.1
  have hGj : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ j, Integrable (fun x => G s x * cutMode N j x) (volume.restrict unitCube) := by
    have h := fun j => (ae_restrict_iff' measurableSet_Ioo).1 (hGe j).prod_right_ae
    filter_upwards [Filter.eventually_all.2 h] with s hs hs01 j
    exact hs j hs01
  have hne0 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := by simp [ae_iff, measure_singleton]
  have hne1 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 1 := by simp [ae_iff, measure_singleton]
  have hdJ : ContDiff ℝ (⊤ : ℕ∞) (deriv J) := by simpa using hJ.iterate_deriv 1
  have hcomp : (fun s => ∑ j, γ j s * a j s) ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) t)]
      fun s => ∑ j, q j s * a j s := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hH, hGj, hne0, hne1] with s hHs hGs hs0 hs1 hsI
    have hs : s ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hsI.1 (Ne.symm hs0), lt_of_le_of_ne (hsI.2.trans ht.2) hs1⟩
    have hH1 := hHs hs
    have hG1 := hGs hs
    have hq_split : ∀ j, q j s = γ j s + κ * ∫ x in unitCube,
        Homogenization.vecDot (D s x) (spaceGrad (cutMode N j) x) := by
      intro j
      have i2 : Integrable (fun x => Homogenization.vecDot (D s x) (spaceGrad (cutMode N j) x))
          (volume.restrict unitCube) := by
        have h0 := integrable_mul_continuous_cell (hH1.2.2.2.1 0) (cutMode_spaceGrad_continuous N j 0)
        have h1 := integrable_mul_continuous_cell (hH1.2.2.2.1 1) (cutMode_spaceGrad_continuous N j 1)
        refine (h0.add h1).congr (Filter.Eventually.of_forall fun x => ?_)
        simp only [Pi.add_apply, Homogenization.vecDot, Fin.sum_univ_two]
      simp only [q, weakModeForcing]
      rw [integral_add (hG1 j) (i2.const_mul κ), integral_const_mul]
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (weakFourierModeProjection N u s) :=
      (realFourierModeAmbientExpansion_contDiff N _).of_le le_top
    have hhp : IsZ2Periodic (fun y => deriv J (weakFourierModeProjection N u s y)) := by
      intro k x
      change deriv J (realFourierModeAmbientExpansion N _ (x + latticeShift k)) =
        deriv J (realFourierModeAmbientExpansion N _ x)
      rw [realFourierModeAmbientExpansion_periodic N _ k x]
    have hC : ∑ j, a j s * ∫ x in unitCube,
        Homogenization.vecDot (D s x) (spaceGrad (cutMode N j) x) =
        ∑ k : Fin 2, ∫ x in unitCube, spaceGrad (weakFourierModeProjection N u s) x k *
          spaceGrad (fun y => deriv J (weakFourierModeProjection N u s y)) x k :=
      sum_pairing_grad_cutMode_eq hH1 (hdJ.comp hsmooth) hhp N
    have hpos := sum_integral_grad_mul_grad_deriv_comp_nonneg hsmooth hJ hJ2
    rw [← hC] at hpos
    have hsum : ∑ j, q j s * a j s = ∑ j, γ j s * a j s + κ * ∑ j, a j s * ∫ x in unitCube,
        Homogenization.vecDot (D s x) (spaceGrad (cutMode N j) x) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hq_split j]
      ring
    show ∑ j, γ j s * a j s ≤ ∑ j, q j s * a j s
    rw [hsum]
    have := mul_nonneg hκ hpos
    linarith
  have hmono := intervalIntegral.integral_mono_ae_restrict ht.1 (hint hγint) (hint hqt) hcomp
  linarith

end AVRegularity.Applications.Dissipation

end
