-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.GradientCarrierJet
public import AVRegularity.Weighted.MetricWordCoefficientArrayBound
import AVRegularity.CycleEvolution.StrongUniqueness
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Literal scalar Taylor coefficients of a letter have uniform polynomial jet growth almost everywhere. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem letter_taylor_ae_jet_growth (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H)
    (v u : ι) (o : Finset.Icc 2 D) (k : Fin (L.edge v u o).length)
    (hk : ((L.edge v u o).get k).map ≠ 0)
    (w : DerivativeWord2 (o.1 - 1)) (i : Fin 2) (lo : ℕ) (X₀ : Vec 2) (δ : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ t ∂volume, t ∈ Set.Icc a b →
      ∀ j, j ≤ J → ∀ z,
        ‖iteratedFDeriv ℝ j (fun z' => taylorSlow lo L.slow
          (fun X => ((L.edge v u o).get k).coeff w t X z' i) X₀ (δ • z')) z‖ ≤
          A * (1 + ‖z‖) ^ L.slow := by
  obtain ⟨B, hB, hbae⟩ := letter_coefficient_ae_mixed_bound π hπ L (Set.Icc a b)
    J H hL v u o k hk
  let good := fun t => t ∈ Set.Icc a b ∧ ∀ (w : DerivativeWord2 (o.1 - 1)) (r q : ℕ),
    r ≤ L.slow → q ≤ J → ∀ X z,
    ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ q
      (((L.edge v u o).get k).coeff w t X') z) X‖ ≤ B
  let P : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let f := fun (t : {t // good t}) X z => P (((L.edge v u o).get k).coeff w t.val X z)
  have hf (t : {t // good t}) : ContDiff ℝ (L.slow + J : ℕ) (Function.uncurry (f t)) :=
    P.contDiff.comp (letter_coefficient_joint_contDiff π L a b J H hL v u o k w t.val t.property.1)
  have hb' (r : ℕ) (hr : r ≤ L.slow) (t : {t // good t})
      (β : DerivativeWord2 r) (j : ℕ) (hj : j ≤ J) (z : Vec 2) :
      ‖iteratedFDeriv ℝ j (fun z' => iteratedFDeriv ℝ r (fun X => f t X z') X₀
        (fun l => basisVec (β l))) z‖ ≤ ‖P‖ * ((2 : ℝ) ^ J * B) := by
    have hbox : IsBoxSmooth r j (((L.edge v u o).get k).coeff w t.val) :=
      isBoxSmooth_of_joint_contDiff r j _
        ((letter_coefficient_joint_contDiff π L a b J H hL v u o k w t.val t.property.1).of_le
          (by exact_mod_cast Nat.add_le_add hr hj))
    have hpow : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ J := pow_le_pow_right₀ (by norm_num) hj
    exact (slow_basis_projection_fast_jet_bound _ hbox P β X₀ z).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul hpow (t.property.2 w r j hr hj X₀ z) (norm_nonneg _) (by positivity))
        (norm_nonneg P))
  obtain ⟨A, hA, hbound⟩ := taylorSlow_jet_growth lo L.slow J f hf X₀ δ
    (‖P‖ * ((2 : ℝ) ^ J * B)) (by positivity) hb'
  refine ⟨A, hA, ?_⟩
  filter_upwards [hbae] with t ht
  intro hti j hj z
  exact hbound ⟨t, hti, ht hti⟩ j hj z
end

/-! The actual weighted metric commutator has a small factorial source energy at a reduced radius. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem scaledMetricCommutator_factorial_energy_le {K : ℕ} {U : Set (Vec 2)}
    (ρ δ g : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : ρ * δ ≤ 1)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (CG : ℕ → ℝ)
    (hbfull : ∀ (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (hb : ∀ l, 1 ≤ l → l ≤ K → ∀ x k a,
      ‖iteratedFDeriv ℝ l (fun y => G y k a) x‖ ≤ CG l * g * δ ^ l)
    (s : Vec 2 → ℝ) (hs : Continuous s) {C : ℝ} (hC : 0 ≤ C)
    (hsb : ∀ x, |s x| ≤ C) (D : RawJet2 (K + 1) E) (hD : JetMemL2On U D) :
    let D' := scaledRawJet s D
    let hD' := scaledRawJet_memL2 s hs hC hsb D hD
    let hT := scaledMetricMasks_memLp G hG (fun l => metricEntryEnvelope CG g δ l.val)
      hbfull s hs hC hsb D hD
    (∑ j : Fin (K + 1), factorialWeight ρ j.val *
      ‖metricCommutatorL2Array (Nat.le_of_lt_succ j.isLt) G D' (hT j)‖ ^ 2) ≤
      (metricRadiusConstant K CG * g * (ρ * δ)) ^ 2 *
        gradFactorialNormSq ρ (jetToL2 D' hD') := by
  dsimp only
  let M := fun l => |CG l| * g * δ ^ l
  have hM : ∀ l, 0 ≤ M l := fun l => by dsimp only [M]; positivity
  have hordered : ∀ l, 1 ≤ l → l ≤ K → ∀ x w k a,
      |orderedScalarDerivative (fun y => G y k a) l w x| ≤ M l := by
    intro l hl hlK x w k a
    refine (orderedScalarDerivative_norm_le _ l
      ((hG k a).of_le (by exact_mod_cast hlK)) w x).trans ?_
    exact (hb l hl hlK x k a).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hg)
        (pow_nonneg hδ _))
  have he := metricCommutator_factorial_energy_le ρ hρ G (scaledRawJet s D)
    (scaledRawJet_memL2 s hs hC hsb D hD)
    (scaledMetricMasks_memLp G hG (fun l => metricEntryEnvelope CG g δ l.val)
      hbfull s hs hC hsb D hD) M hM hordered
  have hp := metric_positive_jet_price_le K CG ρ δ g hρ hδ hg hscale
  have hn : 0 ≤ ∑ l : Fin (K + 1), factorialRootWeight ρ l.val *
      (if l.val = 0 then 0 else metricMaskPrice M l.val) := by
    apply Finset.sum_nonneg
    intro l _
    apply mul_nonneg
    · unfold factorialRootWeight
      positivity
    · split_ifs
      · exact le_rfl
      · unfold metricMaskPrice
        exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) (hM _))
  have hgrad : 0 ≤ gradFactorialNormSq ρ
      (jetToL2 (scaledRawJet s D) (scaledRawJet_memL2 s hs hC hsb D hD)) := by
    rw [← gradientFactorialSequence_normSq]
    exact sq_nonneg _
  exact he.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hn hp 2) hgrad)
end

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Weighted

/-! Time integrability of bounded weighted spatial energies from the actual L2 curves. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem planeScalarMultiplier_inner_self
    (c : Vec 2 → ℝ) (hc : Continuous c) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |c x| ≤ M)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (planeScalarMultiplier c hc hM hb u) u = ∫ x, c x * ‖u x‖ ^ 2 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [planeScalarMultiplier_ae c hc hM hb u] with x hx
  rw [hx, real_inner_smul_left, real_inner_self_eq_norm_sq]

omit [BorelSpace E] [CompleteSpace E] in
theorem weighted_spatial_energy_time_integrable {T : Type*} [MeasurableSpace T] {μ : Measure T}
    (q : T → Vec 2 → ℝ) (hq : ∀ t, Continuous (q t))
    (hqm : Measurable (Function.uncurry q)) {B : ℝ} (hB : 0 ≤ B)
    (hqb : ∀ t x, |q t x| ≤ B)
    (U : T → Lp E 2 (volume : Measure (Vec 2))) (hU : MemLp U 2 μ) :
    Integrable (fun t => ∫ x, q t x * ‖U t x‖ ^ 2) μ := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp E 2 (volume : Measure (Vec 2))) := Lp.SecondCountableTopology
  borelize ↥(Lp E 2 (volume : Measure (Vec 2)))
  let A := fun t => planeScalarMultiplier (E := E) (q t) (hq t) hB (hqb t)
  have hA := memLp_operator_action A
    (fun z => planeScalarMultiplier_stronglyMeasurable q hq hqm hB hqb z) hU hB
    (fun t => planeScalarMultiplier_norm_le (q t) (hq t) hB (hqb t))
  have hi := L2.integrable_inner (𝕜 := ℝ) (hA.toLp (fun t => A t (U t))) (hU.toLp U)
  apply hi.congr
  filter_upwards [hA.coeFn_toLp, hU.coeFn_toLp] with t hAt hUt
  rw [hAt, hUt]
  exact planeScalarMultiplier_inner_self (q t) (hq t) hB (hqb t) (U t)

omit [BorelSpace E] [CompleteSpace E] in
theorem finite_weighted_spatial_energy_time_integrable {T : Type*} [MeasurableSpace T] {μ : Measure T}
    (q : T → Vec 2 → ℝ) (hq : ∀ t, Continuous (q t))
    (hqm : Measurable (Function.uncurry q)) {B : ℝ} (hB : 0 ≤ B)
    (hqb : ∀ t x, |q t x| ≤ B)
    (U : T → PiLp 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2))))
    (hU : MemLp U 2 μ) :
    Integrable (fun t => ∫ x, q t x * ‖(WithLp.toLp 2 (fun i => U t i x) :
      PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) μ := by
  have hi i : Integrable (fun t => ∫ x, q t x * ‖U t i x‖ ^ 2) μ :=
    weighted_spatial_energy_time_integrable q hq hqm hB hqb (fun t => U t i)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2))) i).comp_memLp' hU)
  have he t : (∫ x, q t x * ‖(WithLp.toLp 2 (fun i => U t i x) :
      PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) = ∑ i : Fin 2, ∫ x, q t x * ‖U t i x‖ ^ 2 := by
    simp_rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    exact integral_finsetSum _ (fun i _ => bounded_scalar_Lp_normSq_integrable (U t i) (q t)
      (hq t).aestronglyMeasurable (Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using hqb t x)))
  simp_rw [he]
  exact integrable_finsetSum _ (fun i _ => hi i)

end AVRegularity.Weighted
end

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CycleEvolution
open AVenhance.Infra.ODE
open scoped Topology
namespace AVRegularity.Weighted

/-! Weak-time energy identity on the plane, obtained by the actual real Fourier cutoffs.

This is the whole-plane counterpart of the finite Fourier-projection argument for the cell.
The derivative is represented in the `H¹` Hilbert carrier, so no strong `L²` time derivative
is assumed for the limiting curve. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Fixed-test weak time data on the plane, with its Riesz representative in `H¹`. -/
structure PlaneWeakHilbertCurve (a b : ℝ)
    (u : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (slice dual : ℝ → PlaneHk Set.univ 1 E) : Prop where
  trace : ContinuousOn u (Icc a b)
  state : MemLp slice 2 (volume.restrict (Icc a b))
  dual_mem : MemLp dual 2 (volume.restrict (Icc a b))
  agrees : ∀ᵐ t ∂volume.restrict (Icc a b),
    u t = planeHkValueOperator 1 (slice t)
  increment : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → ∀ z : PlaneHk Set.univ 1 E,
    inner ℝ (u t) (planeHkValueOperator 1 z) -
      inner ℝ (u s) (planeHkValueOperator 1 z) =
        ∫ r in s..t, inner ℝ (dual r) z

/-- Projected plane state obtained from the real spectral cutoff. -/
def planeWeakProjectedState (N : ℕ) (u : ℝ → Lp E 2 (volume : Measure (Vec 2))) :
    ℝ → Lp E 2 (volume : Measure (Vec 2)) :=
  fun t => hilbertProjection N (u t)

/-- The `L²` representative of the projected `H⁻¹` derivative. -/
def planeWeakProjectedDerivative (N : ℕ) (dual : ℝ → PlaneHk Set.univ 1 E) :
    ℝ → Lp E 2 (volume : Measure (Vec 2)) :=
  fun t => (hilbertBandHkOperator N 1).adjoint (dual t)

theorem planeWeakProjectedDerivative_intervalIntegrable {a b : ℝ} (hab : a ≤ b)
    (N : ℕ) (dual : ℝ → PlaneHk Set.univ 1 E)
    (hdual : MemLp dual 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (planeWeakProjectedDerivative (E := E) N dual) volume a b := by
  let A : PlaneHk Set.univ 1 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
    (hilbertBandHkOperator (E := E) N 1).adjoint
  have hm := A.comp_memLp' hdual
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hab]
  exact (hm.integrable (by norm_num)).mono_measure
    (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)

/-- A fixed-test weak time equation gives a strong integral equation for every plane cutoff. -/
theorem PlaneWeakHilbertCurve.projected_integral_solution {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve (E := E) a b u slice dual) (N : ℕ) :
    IsLinearIntegralSolution (fun _ => (0 :
        Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2))))
      (planeWeakProjectedDerivative N dual) (planeWeakProjectedState N u a) a b
      (planeWeakProjectedState N u) := by
  intro t ht
  let T := hilbertBandHkOperator (E := E) N 1
  let P := hilbertProjection (E := E) N
  let d := planeWeakProjectedState (E := E) N u t -
    planeWeakProjectedState (E := E) N u a -
      ∫ r in a..t, planeWeakProjectedDerivative (E := E) N dual r
  have hpair : ∀ z : Lp E 2 (volume : Measure (Vec 2)), inner ℝ d z = 0 := by
    intro z
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2
    have hinterval : IntervalIntegrable (planeWeakProjectedDerivative (E := E) N dual)
        volume a t := (planeWeakProjectedDerivative_intervalIntegrable hab N dual h.dual_mem).mono_set hsub
    have htest := h.increment a ⟨le_rfl, hab⟩ t ht ht.1 (T z)
    have hproj : inner ℝ (P (u t)) z - inner ℝ (P (u a)) z =
        inner ℝ (u t) (P z) - inner ℝ (u a) (P z) := by
      calc
        _ = inner ℝ (u t) (P z) - inner ℝ (P (u a)) z := by
          rw [hilbertProjection_inner]
        _ = _ := by rw [hilbertProjection_inner]
    have hvalue : planeHkValueOperator 1 (T z) = P z := by
      exact planeHkValueOperator_hilbertBand N 1 z
    let L : Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] ℝ := innerSL ℝ z
    have hdual : ∀ r, inner ℝ (dual r) (T z) =
        L (planeWeakProjectedDerivative (E := E) N dual r) := by
      intro r
      change inner ℝ (dual r) (T z) =
        inner ℝ z ((hilbertBandHkOperator N 1).adjoint (dual r))
      calc
        inner ℝ (dual r) (T z) =
            inner ℝ ((hilbertBandHkOperator N 1).adjoint (dual r)) z :=
              (ContinuousLinearMap.adjoint_inner_left T z (dual r)).symm
        _ = inner ℝ z ((hilbertBandHkOperator N 1).adjoint (dual r)) :=
          real_inner_comm _ _
    have hint : (∫ r in a..t, inner ℝ (dual r) (T z)) =
        inner ℝ (∫ r in a..t, planeWeakProjectedDerivative (E := E) N dual r) z := by
      calc
        _ = ∫ r in a..t, L (planeWeakProjectedDerivative (E := E) N dual r) := by
          apply intervalIntegral.integral_congr
          intro r _
          exact hdual r
        _ = L (∫ r in a..t, planeWeakProjectedDerivative (E := E) N dual r) :=
          L.intervalIntegral_comp_comm hinterval
        _ = _ := by
          simp only [L, innerSL_apply_apply]
          exact real_inner_comm _ _
    have hstep : inner ℝ (P (u t)) z - inner ℝ (P (u a)) z =
        inner ℝ (∫ r in a..t, planeWeakProjectedDerivative (E := E) N dual r) z := by
      calc
        _ = inner ℝ (u t) (P z) - inner ℝ (u a) (P z) := hproj
        _ = ∫ r in a..t, inner ℝ (dual r) (T z) := by
          simpa only [hvalue] using htest
        _ = _ := hint
    change inner ℝ (P (u t) - P (u a) -
      (∫ r in a..t, planeWeakProjectedDerivative (E := E) N dual r)) z = 0
    simp only [inner_sub_left, hstep, sub_self]
  have hdnorm : ‖d‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hpair d
  have hd : d = 0 := by
    apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖d‖]
  dsimp [d] at hd
  have hd' : planeWeakProjectedState N u t - planeWeakProjectedState N u a -
      ∫ r in a..t, planeWeakProjectedDerivative N dual r = 0 := by
    simpa only [planeWeakProjectedState, planeWeakProjectedDerivative] using hd
  have heq : planeWeakProjectedState N u t = planeWeakProjectedState N u a +
      ∫ r in a..t, planeWeakProjectedDerivative N dual r := by
    apply sub_eq_zero.mp
    calc
      planeWeakProjectedState N u t - (planeWeakProjectedState N u a +
          ∫ r in a..t, planeWeakProjectedDerivative N dual r) =
          planeWeakProjectedState N u t - planeWeakProjectedState N u a -
            ∫ r in a..t, planeWeakProjectedDerivative N dual r := by abel
      _ = 0 := hd'
  simpa only [planeWeakProjectedState, planeWeakProjectedDerivative,
    linearRhs, zero_apply, zero_add] using heq

/-- Every cutoff curve is absolutely continuous with the projected weak derivative. -/
theorem PlaneWeakHilbertCurve.projected_strongTime {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve (E := E) a b u slice dual) (N : ℕ) :
    StrongTimeRegularity a b (planeWeakProjectedState N u)
      (planeWeakProjectedDerivative N dual) := by
  have hy := h.projected_integral_solution hab N
  have he : linearRhs (fun _ => (0 :
      Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2))))
      (planeWeakProjectedDerivative N dual) (planeWeakProjectedState N u) =
        planeWeakProjectedDerivative N dual := by
    funext t
    change 0 + planeWeakProjectedDerivative N dual t = _
    exact zero_add _
  have hint : IntervalIntegrable
      (linearRhs (fun _ => (0 :
        Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2))))
        (planeWeakProjectedDerivative N dual) (planeWeakProjectedState N u)) volume a b := by
    rw [he]
    exact planeWeakProjectedDerivative_intervalIntegrable hab N dual h.dual_mem
  refine ⟨hy.absolutelyContinuousOnInterval hab hint, ?_⟩
  apply (ae_restrict_iff' measurableSet_uIcc).mpr
  have hd := hy.ae_hasDerivAt hab hint
  filter_upwards [hd] with t ht
  simpa only [uIcc_of_le hab, he] using ht

/-- The `H¹` plane cutoff is contractive on an actual `H¹` vector. -/
theorem hilbertBandHk_value_norm_le
    (N : ℕ) (z : PlaneHk Set.univ 1 E) :
    ‖hilbertBandHk N 1 (planeHkValueOperator 1 z)‖ ≤ ‖z‖ := by
  change ‖(hilbertBandHk N 1 (planeHkValueOperator 1 z)).val‖ ≤ ‖z.val‖
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [jet_norm_sq_eq_sum, jet_norm_sq_eq_sum]
  unfold derivativeNormSq
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro w _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (hilbertBandHk_component_norm_le N 1 z ⟨j, w⟩)

/-- The full plane weak curve satisfies the exact energy identity. -/
theorem PlaneWeakHilbertCurve.energy_increment {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve (E := E) a b u slice dual) :
    ‖u b‖ ^ 2 - ‖u a‖ ^ 2 = ∫ t in a..b, 2 * inner ℝ (dual t) (slice t) := by
  let bound : ℝ → ℝ := fun t => 2 * (‖dual t‖ * ‖slice t‖)
  have hprod : Integrable (fun t => ‖dual t‖ * ‖slice t‖)
      (volume.restrict (Icc a b)) :=
    memLp_one_iff_integrable.mp (h.dual_mem.norm.mul h.state.norm :
      MemLp _ 1 (volume.restrict (Icc a b)))
  have hbound : IntegrableOn bound (Ioc a b) volume := by
    exact (hprod.const_mul 2).mono_measure
      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have hinc := energy_increment_of_dominated_approximation hab
    (fun N => planeWeakProjectedState N u)
    (fun N => planeWeakProjectedDerivative N dual)
    (fun N => h.projected_strongTime hab N) (u a) (u b)
    (tendsto_hilbertProjection (u a)) (tendsto_hilbertProjection (u b))
    (fun t => 2 * inner ℝ (dual t) (slice t)) bound hbound ?_ ?_
  · exact hinc
  · intro N
    have ha : ∀ᵐ t ∂volume.restrict (Ioc a b),
        u t = planeHkValueOperator 1 (slice t) := h.agrees.filter_mono
          (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
    filter_upwards [ha] with t ht
    have hpoint : 2 * inner ℝ (planeWeakProjectedState N u t)
        (planeWeakProjectedDerivative N dual t) =
      2 * inner ℝ (dual t)
        (hilbertBandHkOperator N 1 (hilbertProjection N (u t))) := by
      change 2 * inner ℝ (hilbertProjection N (u t))
          ((hilbertBandHkOperator N 1).adjoint (dual t)) = _
      rw [real_inner_comm, ContinuousLinearMap.adjoint_inner_left]
    rw [hpoint]
    change ‖2 * inner ℝ (dual t)
        (hilbertBandHkOperator N 1 (hilbertProjection N (u t)))‖ ≤ bound t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 * |inner ℝ (dual t)
          (hilbertBandHkOperator N 1 (hilbertProjection N (u t)))| ≤
        2 * (‖dual t‖ * ‖hilbertBandHkOperator N 1 (hilbertProjection N (u t))‖) := by
          exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
      _ ≤ bound t := by
        have hN : hilbertBandHkOperator N 1 (hilbertProjection N (u t)) =
            hilbertBandHk N 1 (planeHkValueOperator 1 (slice t)) := by
          change hilbertBandHk N 1 (hilbertProjection N (u t)) =
            hilbertBandHk N 1 (planeHkValueOperator 1 (slice t))
          rw [ht]
          exact hilbertBandHk_projection N 1 (planeHkValueOperator 1 (slice t))
        rw [hN]
        have hn := hilbertBandHk_value_norm_le (E := E) N (slice t)
        dsimp [bound]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hn (norm_nonneg _)) (by norm_num)
  · have ha : ∀ᵐ t ∂volume.restrict (Ioc a b),
        u t = planeHkValueOperator 1 (slice t) := h.agrees.filter_mono
          (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
    filter_upwards [ha] with t ht
    have hseq : (fun N : ℕ => 2 * inner ℝ (planeWeakProjectedState N u t)
        (planeWeakProjectedDerivative N dual t)) =
        fun N => 2 * inner ℝ (dual t)
          (hilbertBandHk N 1 (planeHkValueOperator 1 (slice t))) := by
      funext N
      have hpoint : 2 * inner ℝ (planeWeakProjectedState N u t)
          (planeWeakProjectedDerivative N dual t) =
        2 * inner ℝ (dual t)
          (hilbertBandHkOperator N 1 (hilbertProjection N (u t))) := by
        change 2 * inner ℝ (hilbertProjection N (u t))
            ((hilbertBandHkOperator N 1).adjoint (dual t)) = _
        rw [real_inner_comm, ContinuousLinearMap.adjoint_inner_left]
      have hcut : hilbertBandHkOperator N 1 (hilbertProjection N (u t)) =
          hilbertBandHk N 1 (planeHkValueOperator 1 (slice t)) := by
        change hilbertBandHk N 1 (hilbertProjection N (u t)) =
          hilbertBandHk N 1 (planeHkValueOperator 1 (slice t))
        rw [ht]
        exact hilbertBandHk_projection N 1 (planeHkValueOperator 1 (slice t))
      rw [hpoint, hcut]
    rw [hseq]
    have htend := tendsto_hilbertBandHk (E := E) 1 (slice t)
    have hp : Tendsto (fun N => 2 * inner ℝ (dual t)
        (hilbertBandHk N 1 (planeHkValueOperator 1 (slice t)))) atTop
        (𝓝 (2 * inner ℝ (dual t) (slice t))) :=
      (tendsto_const_nhds.inner htend).const_mul 2
    exact hp

omit [FiniteDimensional ℝ E] in
/-- Restricting a plane weak Hilbert curve preserves its fixed-test equation. -/
theorem PlaneWeakHilbertCurve.mono {a b c d : ℝ}
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve (E := E) a b u slice dual)
    (hsub : Icc c d ⊆ Icc a b) : PlaneWeakHilbertCurve c d u slice dual := by
  refine ⟨h.trace.mono hsub,
    h.state.mono_measure (Measure.restrict_mono hsub le_rfl),
    h.dual_mem.mono_measure (Measure.restrict_mono hsub le_rfl),
    h.agrees.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)), ?_⟩
  intro s hs t ht hst z
  exact h.increment s (hsub hs) t (hsub ht) hst z

/-- The full weak energy increment holds between any two endpoints of the interval. -/
theorem PlaneWeakHilbertCurve.energy_increment_between {a b s t : ℝ}
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve (E := E) a b u slice dual)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    ‖u t‖ ^ 2 - ‖u s‖ ^ 2 = ∫ r in s..t, 2 * inner ℝ (dual r) (slice r) := by
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  exact (h.mono hsub).energy_increment hst

/-- A nonpositive weak energy production and zero initial trace force the full curve to vanish. -/
theorem PlaneWeakHilbertCurve.eq_zero_of_nonpositive_production {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve (E := E) a b u slice dual)
    (hinitial : u a = 0)
    (hprod : ∀ᵐ t ∂volume.restrict (Ioc a b),
      2 * inner ℝ (dual t) (slice t) ≤ 0) :
    ∀ t ∈ Icc a b, u t = 0 := by
  intro t ht
  have he := h.energy_increment_between ⟨le_rfl, hab⟩ ht ht.1
  have hprod_t : ∀ᵐ s ∂volume.restrict (Ioc a t),
      2 * inner ℝ (dual s) (slice s) ≤ 0 :=
    hprod.filter_mono (ae_mono (Measure.restrict_mono
      (Ioc_subset_Ioc le_rfl ht.2) le_rfl))
  have hi : (∫ s in a..t, 2 * inner ℝ (dual s) (slice s)) ≤ 0 := by
    rw [intervalIntegral.integral_of_le ht.1]
    apply integral_nonpos_of_ae
    exact hprod_t
  have hz : ‖u t‖ ^ 2 = 0 := by
    rw [← he, hinitial] at hi
    exact le_antisymm (by simpa using hi) (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

omit [FiniteDimensional ℝ E] in
/-- A fixed `H¹` test has an integrable pairing with the weak time representative. -/
theorem planeWeakPair_intervalIntegrable {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (dual : ℝ → PlaneHk Set.univ 1 E)
    (hdual : MemLp dual 2 (volume.restrict (Icc a b)))
    (z : PlaneHk Set.univ 1 E) :
    IntervalIntegrable (fun r => inner ℝ (dual r) z) volume s t := by
  have hm := (innerSL ℝ z).comp_memLp' hdual
  have hi : Integrable (fun r => inner ℝ (dual r) z) (volume.restrict (Icc a b)) := by
    simpa only [Function.comp_def, innerSL_apply_apply, real_inner_comm] using
      hm.integrable (by norm_num)
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hst]
  exact hi.mono_measure (Measure.restrict_mono
    (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)) le_rfl)

omit [FiniteDimensional ℝ E] in
/-- Differences retain the plane weak time equation and their almost everywhere `H¹` lift. -/
theorem PlaneWeakHilbertCurve.sub {a b : ℝ}
    {u u' : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual slice' dual' : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve (E := E) a b u slice dual)
    (h' : PlaneWeakHilbertCurve (E := E) a b u' slice' dual') :
    PlaneWeakHilbertCurve a b (fun t => u t - u' t)
      (fun t => slice t - slice' t) (fun t => dual t - dual' t) := by
  refine ⟨h.trace.sub h'.trace, h.state.sub h'.state,
    h.dual_mem.sub h'.dual_mem, ?_, ?_⟩
  · filter_upwards [h.agrees, h'.agrees] with t ht ht'
    rw [ht, ht', map_sub]
  · intro s hs t ht hst z
    have hi := planeWeakPair_intervalIntegrable hs ht hst dual h.dual_mem z
    have hi' := planeWeakPair_intervalIntegrable hs ht hst dual' h'.dual_mem z
    simp only [inner_sub_left]
    rw [intervalIntegral.integral_sub hi hi']
    linear_combination h.increment s hs t ht hst z - h'.increment s hs t ht hst z

/-- Two weak plane curves with common initial trace agree if their difference has nonpositive production. -/
theorem planeWeakHilbert_unique_of_nonpositive_difference {a b : ℝ} (hab : a ≤ b)
    {u u' : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual slice' dual' : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve (E := E) a b u slice dual)
    (h' : PlaneWeakHilbertCurve (E := E) a b u' slice' dual')
    (hinitial : u a = u' a)
    (hprod : ∀ᵐ t ∂volume.restrict (Ioc a b),
      2 * inner ℝ (dual t - dual' t) (slice t - slice' t) ≤ 0) :
    ∀ t ∈ Icc a b, u t = u' t := by
  have hz := (h.sub h').eq_zero_of_nonpositive_production hab
    (sub_eq_zero.mpr hinitial) hprod
  intro t ht
  exact sub_eq_zero.mp (hz t ht)

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Genuine measurable Taylor coefficients with global polynomial bounds and the literal interval value. -/

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem exists_letter_taylor_measurable_extension (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H)
    (v u : ι) (o : Finset.Icc 2 D) (k : Fin (L.edge v u o).length)
    (hk : ((L.edge v u o).get k).map ≠ 0)
    (w : DerivativeWord2 (o.1 - 1)) (i : Fin 2) (lo : ℕ) (X₀ : Vec 2) (δ : ℝ)
    (hm : ∀ X z, Measurable (fun t => ((L.edge v u o).get k).coeff w t X z)) :
    ∃ c : ℝ → Vec 2 → ℝ, (∀ z, Measurable (fun t => c t z)) ∧
      (∀ t, ContDiff ℝ (J : ℕ) (c t)) ∧
      (∃ A : ℝ, 0 ≤ A ∧ ∀ t j, j ≤ J → ∀ z,
        ‖iteratedFDeriv ℝ j (c t) z‖ ≤ A * (1 + ‖z‖) ^ L.slow) ∧
      ∀ᵐ t ∂volume, t ∈ Set.Icc a b → ∀ z,
        c t z = taylorSlow lo L.slow
          (fun X => ((L.edge v u o).get k).coeff w t X z i) X₀ (δ • z) := by
  classical
  let f := fun t X z => ((L.edge v u o).get k).coeff w t X z i
  let T := fun t z => taylorSlow lo L.slow (fun X => f t X z) X₀ (δ • z)
  obtain ⟨A, hA, hbound⟩ := letter_taylor_ae_jet_growth π hπ L a b J H hL
    v u o k hk w i lo X₀ δ
  obtain ⟨s, hs, hsgood, hsae⟩ := exists_measurable_good_times volume
    (fun t => t ∈ Set.Icc a b → ∀ j, j ≤ J → ∀ z,
      ‖iteratedFDeriv ℝ j (T t) z‖ ≤ A * (1 + ‖z‖) ^ L.slow) hbound
  let c := fun t z => if t ∈ s ∩ Set.Icc a b then T t z else 0
  have hI : MeasurableSet (Set.Icc a b) := measurableSet_Icc
  have hf (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ContDiff ℝ (L.slow + J : ℕ) (Function.uncurry (f t)) :=
    (show Vec 2 →L[ℝ] ℝ from ContinuousLinearMap.proj i).contDiff.comp
      (letter_coefficient_joint_contDiff π L a b J H hL v u o k w t ht)
  have hmt (z : Vec 2) := taylorSlow_time_window_measurable (Set.Icc a b) hI lo L.slow
    f (fun X z => (measurable_pi_iff.mp (hm X z)) i)
    (fun t ht z => ((hf t ht).comp (contDiff_id.prodMk contDiff_const)).of_le
      (by exact_mod_cast Nat.le_add_right L.slow J)) X₀ δ z
  refine ⟨c, ?_, ?_, ⟨A, hA, ?_⟩, ?_⟩
  · intro z
    have hmt' : Measurable (fun t => if t ∈ Set.Icc a b then T t z else 0) := by
      convert hmt z using 1
      funext t
      by_cases ht : t ∈ Set.Icc a b
      · simp only [ite_eq_left ht, T]
      · simp only [ite_eq_right ht]
    have hh : Measurable (fun t => if t ∈ s then
        (if t ∈ Set.Icc a b then T t z else 0) else 0) :=
      hmt'.piecewise hs (measurable_const (a := (0 : ℝ)))
    convert hh using 1
    funext t
    by_cases hts : t ∈ s <;> by_cases htI : t ∈ Set.Icc a b <;>
      simp only [c, Set.mem_inter_iff, hts, htI, and_self, and_false, false_and,
        ite_true, ite_false, T, f]
  · intro t
    by_cases ht : t ∈ s ∩ Set.Icc a b
    · simpa only [c, ite_eq_left ht] using
        taylorSlow_spatial_contDiff lo L.slow J (f t) (hf t ht.2) X₀ δ
    · simpa only [c, ite_eq_right ht] using (contDiff_const : ContDiff ℝ (J : ℕ)
        (fun _ : Vec 2 => (0 : ℝ)))
  · intro t j hj z
    by_cases ht : t ∈ s ∩ Set.Icc a b
    · simpa only [c, ite_eq_left ht] using hsgood t ht.1 ht.2 j hj z
    · simp only [c, ite_eq_right ht]
      simpa using (show ‖iteratedFDeriv ℝ j (fun _ : Vec 2 => (0 : ℝ)) z‖ ≤
        A * (1 + ‖z‖) ^ L.slow by simp; positivity)
  · filter_upwards [hsae] with t ht
    intro htI z
    simp only [c, ite_eq_left (show t ∈ s ∩ Set.Icc a b from ⟨ht, htI⟩), T, f]

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization Filter
open scoped Topology
namespace AVRegularity.Weighted

/-! Remove compact spatial cutoffs from the time-integrated bounded weighted dissipation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] [CompleteSpace E] in
theorem finite_energy_spatial_cutoff_time_tendsto
    (χ : ℕ → Vec 2 → ℝ) (hχc : ∀ n, Continuous (χ n))
    (hχ : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1)
    (hχlim : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (q : ℝ → Vec 2 → ℝ) (hq : ∀ t, Continuous (q t))
    (hqm : Measurable (Function.uncurry q)) {B : ℝ} (hB : 0 ≤ B)
    (hqb : ∀ t x, |q t x| ≤ B) (hq0 : ∀ t x, 0 ≤ q t x)
    (μ : Measure ℝ)
    (U : ℝ → PiLp 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2))))
    (hU : MemLp U 2 μ) :
    Tendsto (fun n => ∫ t, ∫ x, χ n x ^ 2 * q t x * ‖(WithLp.toLp 2
      (fun i => U t i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2 ∂volume ∂μ) atTop
      (𝓝 (∫ t, ∫ x, q t x * ‖(WithLp.toLp 2 (fun i => U t i x) :
        PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2 ∂volume ∂μ)) := by
  let f := fun t x => q t x * ‖(WithLp.toLp 2 (fun i => U t i x) :
    PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2
  let en := fun n t => ∫ x, χ n x ^ 2 * f t x
  let energy := fun t => ∫ x, f t x
  have hf t : Integrable (f t) volume := bounded_scalar_finiteLp_normSq_integrable (U t) (q t)
    (hq t).aestronglyMeasurable (Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using hqb t x))
  have hf0 t x : 0 ≤ f t x := mul_nonneg (hq0 t x) (sq_nonneg _)
  have henergy : Integrable energy μ := finite_weighted_spatial_energy_time_integrable q hq hqm hB hqb U hU
  have hen n : Integrable (en n) μ := by
    have hj : Measurable (Function.uncurry (fun t x => χ n x ^ 2 * q t x)) := by
      convert (((hχc n).measurable.comp measurable_snd).pow_const 2).mul hqm using 1
      funext p
      rfl
    have hi := finite_weighted_spatial_energy_time_integrable (E := E)
      (fun t x => χ n x ^ 2 * q t x) (fun t => ((hχc n).pow 2).mul (hq t)) hj hB
      (fun t x => by
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        have hs : χ n x ^ 2 ≤ 1 := by nlinarith only [(hχ n x).1, (hχ n x).2]
        exact (mul_le_mul hs (hqb t x) (abs_nonneg _) (by norm_num)).trans_eq (one_mul B)) U hU
    convert hi using 1
    funext t
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by dsimp only [f]; ring)
  have hlim t : Tendsto (fun n => en n t) atTop (𝓝 (energy t)) :=
    integral_spatial_cutoff_tendsto χ (f t) (fun n => (hχc n).aestronglyMeasurable) hχ hχlim (hf t)
  have hbound n t : ‖en n t‖ ≤ energy t := by
    obtain ⟨_, h0, hle⟩ := spatial_cutoff_integrable_bound (χ n) (f t)
      (hχc n).aestronglyMeasurable (hχ n) (hf t) (hf0 t)
    rw [Real.norm_of_nonneg h0]
    exact hle
  have ht := tendsto_integral_of_dominated_convergence energy
    (fun n => (hen n).aestronglyMeasurable) henergy
    (fun n => Eventually.of_forall (hbound n)) (Eventually.of_forall hlim)
  convert ht using 1
  funext n
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by dsimp only [en, f]; ring))

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Weighted

/-! Time integrability of the actual weighted value-commutator product. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] [CompleteSpace E] in
theorem weighted_spatial_pair_time_integrable {T : Type*} [MeasurableSpace T] {μ : Measure T}
    (q : T → Vec 2 → ℝ) (hq : ∀ t, Continuous (q t))
    (hqm : Measurable (Function.uncurry q)) {B : ℝ} (hB : 0 ≤ B)
    (hqb : ∀ t x, |q t x| ≤ B)
    (U V : T → Lp E 2 (volume : Measure (Vec 2))) (hU : MemLp U 2 μ) (hV : MemLp V 2 μ) :
    Integrable (fun t => ∫ x, q t x * inner ℝ (U t x) (V t x)) μ := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp E 2 (volume : Measure (Vec 2))) := Lp.SecondCountableTopology
  borelize ↥(Lp E 2 (volume : Measure (Vec 2)))
  let A := fun t => planeScalarMultiplier (E := E) (q t) (hq t) hB (hqb t)
  have hA := memLp_operator_action A
    (fun z => planeScalarMultiplier_stronglyMeasurable q hq hqm hB hqb z) hU hB
    (fun t => planeScalarMultiplier_norm_le (q t) (hq t) hB (hqb t))
  have hi := L2.integrable_inner (𝕜 := ℝ) (hA.toLp (fun t => A t (U t))) (hV.toLp V)
  apply hi.congr
  filter_upwards [hA.coeFn_toLp, hV.coeFn_toLp] with t hAt hVt
  rw [hAt, hVt, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [planeScalarMultiplier_ae (q t) (hq t) hB (hqb t) (U t)] with x hx
  rw [hx, real_inner_smul_left]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem weighted_spatial_value_product_time_integrable
    {T : Type*} [MeasurableSpace T] {μ : Measure T}
    (q : T → Vec 2 → ℝ) (hq : ∀ t, Continuous (q t))
    (hqm : Measurable (Function.uncurry q)) {B : ℝ} (hB : 0 ≤ B)
    (hqb : ∀ t x, |q t x| ≤ B)
    (U V : T → Lp E 2 (volume : Measure (Vec 2))) (hU : MemLp U 2 μ) (hV : MemLp V 2 μ) :
    Integrable (fun t => ∫ x, q t x * (‖U t x‖ * ‖V t x‖)) μ := by
  have hi := weighted_spatial_pair_time_integrable q hq hqm hB hqb
    (fun t => planeLpNorm (U t)) (fun t => planeLpNorm (V t))
    (planeLpNorm_memLp U hU) (planeLpNorm_memLp V hV)
  apply hi.congr
  filter_upwards [] with t
  apply integral_congr_ae
  filter_upwards [planeLpNorm_ae (U t), planeLpNorm_ae (V t)] with x hx hy
  rw [hx, hy]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

end AVRegularity.Weighted
end

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.Weighted

/-! Contractive `H¹` cutoffs also converge on moving `H¹` inputs. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The same actual plane Fourier cutoff, acting on the `H¹` carrier. -/
def planeH1SpectralCutoff (N : ℕ) : PlaneHk Set.univ 1 E →L[ℝ] PlaneHk Set.univ 1 E :=
  (hilbertBandHkOperator (E := E) N 1).comp (planeHkValueOperator (E := E) 1)

theorem planeH1SpectralCutoff_norm_le (N : ℕ) (z : PlaneHk Set.univ 1 E) :
    ‖planeH1SpectralCutoff N z‖ ≤ ‖z‖ := hilbertBandHk_value_norm_le N z

theorem tendsto_planeH1SpectralCutoff (z : PlaneHk Set.univ 1 E) :
    Tendsto (fun N => planeH1SpectralCutoff N z) atTop (𝓝 z) := tendsto_hilbertBandHk 1 z

/-- The cutoff may be applied to a convergent sequence without losing its strong limit. -/
theorem tendsto_planeH1SpectralCutoff_moving
    (z : ℕ → PlaneHk Set.univ 1 E) (z₀ : PlaneHk Set.univ 1 E)
    (hz : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun N => planeH1SpectralCutoff N (z N)) atTop (𝓝 z₀) :=
  tendsto_contractive_operator_moving (planeH1SpectralCutoff (E := E))
    planeH1SpectralCutoff_norm_le tendsto_planeH1SpectralCutoff z z₀ hz

/-- The `H¹` value readout intertwines the actual spatial and Sobolev cutoffs. -/
theorem planeH1SpectralCutoff_value (N : ℕ) (z : PlaneHk Set.univ 1 E) :
    planeHkValueOperator (E := E) 1 (planeH1SpectralCutoff N z) =
      hilbertProjection N (planeHkValueOperator (E := E) 1 z) :=
  planeHkValueOperator_hilbertBand N 1 _

end AVRegularity.Weighted
end
