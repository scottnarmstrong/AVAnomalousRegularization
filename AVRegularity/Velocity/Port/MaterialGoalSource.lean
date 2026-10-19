-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Velocity.Jets.OCData
import AVenhance.Infra.FaaDiBruno.BarNormBridge
import AVenhance.Infra.Classical.Drift
public import AVenhance.Infra.Construction.TimeIncrement.FlowBounds
public import AVenhance.Infra.FaaDiBruno.Seminorm
public import AVenhance.Infra.Flow.Liouville
public import AVenhance.Statements.Section4.VecDiv
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.Flow.InverseC1
import AVenhance.Infra.Flow.SpatialRegularity
import AVenhance.Statements.FlowDefs.FlowIsFlow
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public section
noncomputable section
open Homogenization AVenhance
open scoped ContDiff
namespace AVRegularity.Velocity.Port.MaterialSpatial

theorem streamVel_component0_iterated_eq {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (x : Vec 2)
    (J : Fin n → Fin 2) :
    iteratedFDeriv ℝ n (fun y : Vec 2 => streamVel (fun _ z => f z) 0 y 0)
      x (fun k => basisVec (J k)) =
    -iteratedFDeriv ℝ (n + 1) f x
        (Fin.snoc (fun k => basisVec (J k)) (basisVec 1)) := by
  have hfderiv : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => fderiv ℝ f y) :=
    hf.fderiv_right (by simp)
  have hclm : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec 2 => (fderiv ℝ f y) (basisVec 1)) :=
    hfderiv.clm_apply contDiff_const
  have hclm_n : ContDiff ℝ n (fun y : Vec 2 => (fderiv ℝ f y) (basisVec 1)) :=
    hclm.of_le (by simp)
  have hval := iteratedFDeriv_clm_apply_const_apply hfderiv (i := n)
    (by simp) (x := x) (u := basisVec 1) (m := fun k => basisVec (J k))
  have hnext := iteratedFDeriv_succ_apply_right
    (𝕜 := ℝ) (f := f) (x := x)
    (Fin.snoc (fun k => basisVec (J k)) (basisVec 1))
  have hcoord : (fun y : Vec 2 => streamVel (fun _ z => f z) 0 y 0) =
      fun y => -((fderiv ℝ f y) (basisVec 1)) := by
    funext y
    simp [streamVel, sigmaMat, spaceGrad, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, basisVec]
  rw [hcoord]
  rw [show (fun y : Vec 2 => -((fderiv ℝ f y) (basisVec 1))) =
      fun y => (-1 : ℝ) • ((fderiv ℝ f y) (basisVec 1)) by ext y; simp]
  have hsmul := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (i := n)
    (f := fun y : Vec 2 => (fderiv ℝ f y) (basisVec 1)) (x := x)
    (a := (-1 : ℝ)) hclm_n.contDiffAt
  have hneg : iteratedFDeriv ℝ n
      (fun y : Vec 2 => (-1 : ℝ) • ((fderiv ℝ f y) (basisVec 1))) x
      (fun k => basisVec (J k)) =
      -iteratedFDeriv ℝ n
        (fun y : Vec 2 => (fderiv ℝ f y) (basisVec 1)) x
        (fun k => basisVec (J k)) := by
    have h := congrArg (fun T => T (fun k => basisVec (J k))) hsmul
    simpa [smul_eq_mul] using h
  calc
    _ = -iteratedFDeriv ℝ n
        (fun y : Vec 2 => (fderiv ℝ f y) (basisVec 1)) x
        (fun k => basisVec (J k)) := hneg
    _ = -((iteratedFDeriv ℝ n (fun y => fderiv ℝ f y) x
          (fun k => basisVec (J k))) (basisVec 1)) := by rw [hval]
    _ = -iteratedFDeriv ℝ (n + 1) f x
          (Fin.snoc (fun k => basisVec (J k)) (basisVec 1)) := by
      simpa using congrArg (fun z : ℝ => -z) hnext.symm

theorem streamVel_component1_iterated_eq {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (x : Vec 2)
    (J : Fin n → Fin 2) :
    iteratedFDeriv ℝ n (fun y : Vec 2 => streamVel (fun _ z => f z) 0 y 1)
      x (fun k => basisVec (J k)) =
    iteratedFDeriv ℝ (n + 1) f x
        (Fin.snoc (fun k => basisVec (J k)) (basisVec 0)) := by
  have hfderiv : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => fderiv ℝ f y) :=
    hf.fderiv_right (by simp)
  have hval := iteratedFDeriv_clm_apply_const_apply hfderiv (i := n)
    (by simp) (x := x) (u := basisVec 0) (m := fun k => basisVec (J k))
  have hnext := iteratedFDeriv_succ_apply_right
    (𝕜 := ℝ) (f := f) (x := x)
    (Fin.snoc (fun k => basisVec (J k)) (basisVec 0))
  have hcoord : (fun y : Vec 2 => streamVel (fun _ z => f z) 0 y 1) =
      fun y => (fderiv ℝ f y) (basisVec 0) := by
    funext y
    simp [streamVel, sigmaMat, spaceGrad, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, basisVec]
  calc
    _ = iteratedFDeriv ℝ n (fun y : Vec 2 => (fderiv ℝ f y) (basisVec 0)) x
        (fun k => basisVec (J k)) := by rw [hcoord]
    _ = (iteratedFDeriv ℝ n (fun y => fderiv ℝ f y) x
          (fun k => basisVec (J k))) (basisVec 0) := hval
    _ = iteratedFDeriv ℝ (n + 1) f x
          (Fin.snoc (fun k => basisVec (J k)) (basisVec 0)) := by
      simpa using hnext.symm

theorem basisVec_snoc {n : ℕ} (J : Fin n → Fin 2) (j : Fin 2) :
    Fin.snoc (fun i => basisVec (J i)) (basisVec j) =
      fun k => basisVec ((Fin.snoc (α := fun _ : Fin (n + 1) => Fin 2) J j) k) := by
  funext k
  refine Fin.lastCases ?_ ?_ k
  · simp [Fin.snoc]
  · intro i
    simp [Fin.snoc]

theorem iteratedFDeriv_component {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (x : Vec 2)
    (J : Fin n → Fin 2) (i : Fin 2) :
    iteratedFDeriv ℝ n (fun y : Vec 2 => f y i) x (fun k => basisVec (J k)) =
      iteratedFDeriv ℝ n f x (fun k => basisVec (J k)) i := by
  have hfN : ContDiff ℝ n f := hf.of_le (by simp)
  let P : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hcomp := P.iteratedFDeriv_comp_left
    (f := f) (x := x) hfN.contDiffAt (i := n) le_rfl
  change iteratedFDeriv ℝ n (P ∘ f) x
    (fun k => basisVec (J k)) = _
  rw [hcomp]
  rfl

theorem fderiv_component_apply {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) (i j : Fin 2) :
    fderiv ℝ (fun y : Vec 2 => f y i) x (basisVec j) =
      fderiv ℝ f x (basisVec j) i := by
  have hd : DifferentiableAt ℝ f x := hf.differentiable (by simp) x
  have h := fderiv_apply hd i
  have h' := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec j)) h
  simpa using h'

end AVRegularity.Velocity.Port.MaterialSpatial
end
end
end

section
@[expose] public section
noncomputable section
open Homogenization
namespace AVRegularity.Velocity.Port.ExplicitBarNorm

/-! Explicit seminorm and cutoff interfaces for the OC jet record.

The pointwise seminorm bridge, radius changes, finite sums, and fixed-order
cutoff estimates are already proved in the generic jet modules. This file
binds those results to the names and record fields consumed by the mechanical
port. The upstream `Ingredients`-specific `zetaMK` lemmas are replaced by the
record's fast and slow cutoff derivative fields.
-/

theorem barNorm_eq_snorm {n : ℕ} {R : ℝ} {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ n f) :
    AVenhance.barNorm n R f = AVenhance.FaaDiBruno.snorm f n R :=
  AVenhance.FaaDiBruno.barNorm_eq_snorm hf

theorem barNorm_eq_pointwise (f : Vec 2 → ℝ) (n : ℕ) (R : ℝ)
    (hf : ContDiff ℝ n f) :
    AVenhance.barNorm n R f =
      ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
        (ENNReal.ofReal R)⁻¹ ^ n *
          ⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
            ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ :=
  AVRegularity.Velocity.Jets.barNorm_eq_pointwise f n R hf

theorem barNorm_add_le (f g : Vec 2 → ℝ) (n : ℕ) (R : ℝ)
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    AVenhance.barNorm n R (f + g) ≤
      AVenhance.barNorm n R f + AVenhance.barNorm n R g :=
  AVRegularity.Velocity.Jets.barNorm_add_le f g n R hf hg

theorem barNorm_sum_le {ι : Type*} (S : Finset ι) (f : ι → Vec 2 → ℝ)
    (n : ℕ) (R : ℝ) (hf : ∀ i ∈ S, ContDiff ℝ n (f i)) :
    AVenhance.barNorm n R (∑ i ∈ S, f i) ≤
      ∑ i ∈ S, AVenhance.barNorm n R (f i) :=
  AVRegularity.Velocity.Jets.barNorm_sum_le S f n R hf

theorem barNorm_radius_change {n : ℕ} {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ n f) {R S : ℝ} (hR : 0 < R) (hS : 0 < S) :
    AVenhance.barNorm n S f =
      AVenhance.barNorm n R f * ENNReal.ofReal (R / S) ^ n :=
  AVRegularity.Velocity.Jets.barNorm_radius_change hf hR hS

lemma factorial_coefficient_le_five (n : ℕ) :
    ((n + 1 : ℝ) ^ 2) / (Nat.factorial n : ℝ) ≤ 5 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hfaccast : (Nat.factorial (n + 1) : ℝ) =
        (n + 1 : ℝ) * (Nat.factorial n : ℝ) := by norm_cast
    rw [hfaccast]
    by_cases hn0 : n = 0
    · subst n
      norm_num
    by_cases hn1 : n = 1
    · subst n
      norm_num
    have hn : 2 ≤ n := by omega
    have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnum : ((n + 2 : ℝ) ^ 2) ≤ (n + 1 : ℝ) ^ 3 := by
      have hn0r : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hprod := mul_nonneg (sub_nonneg.mpr hnr) (sq_nonneg (n : ℝ))
      nlinarith [hprod, hn0r]
    have hstep : ((n + 2 : ℝ) ^ 2) /
          ((n + 1 : ℝ) * (Nat.factorial n : ℝ)) ≤
        ((n + 1 : ℝ) ^ 2) / (Nat.factorial n : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hm := mul_le_mul_of_nonneg_right hnum
        (show 0 ≤ (Nat.factorial n : ℝ) from Nat.cast_nonneg _)
      nlinarith [hm]
    have hnumEq : ((↑(n + 1) + 1 : ℝ) ^ 2) = (↑n + 2) ^ 2 := by norm_cast
    calc
      ((↑(n + 1) + 1 : ℝ) ^ 2) /
          ((n + 1 : ℝ) * (Nat.factorial n : ℝ)) =
        ((↑n + 2 : ℝ) ^ 2) /
          ((n + 1 : ℝ) * (Nat.factorial n : ℝ)) := by rw [hnumEq]
      _ ≤ ((n + 1 : ℝ) ^ 2) / (Nat.factorial n : ℝ) := hstep
      _ ≤ 5 := ih

/-- Coordinate derivatives of a sine have their exact frequency power. -/
theorem sine_coordinate_partial_le (A ω : ℝ) (hA : 0 ≤ A) (hω : 0 ≤ ω)
    (i : Fin 2) (n : ℕ) (x : Vec 2) (J : Fin n → Fin 2) :
    ‖iteratedFDeriv ℝ n (fun y : Vec 2 => A * Real.sin (ω * y i)) x
      (fun j => basisVec (J j))‖ ≤ A * ω ^ n := by
  let L : Vec 2 →L[ℝ] ℝ := ω • ContinuousLinearMap.proj i
  have hs : ContDiff ℝ n (fun y : Vec 2 => Real.sin (L y)) :=
    Real.contDiff_sin.comp L.contDiff
  have heq : (fun y : Vec 2 => A * Real.sin (ω * y i)) =
      fun y => A • Real.sin (L y) := by rfl
  rw [heq, iteratedFDeriv_const_smul_apply' hs.contDiffAt]
  change ‖A * (iteratedFDeriv ℝ n (Real.sin ∘ L) x
    (fun j => basisVec (J j)))‖ ≤ _
  have hsin : ContDiff ℝ n Real.sin := Real.contDiff_sin
  rw [L.iteratedFDeriv_comp_right hsin x le_rfl]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul]
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hA]
  apply mul_le_mul_of_nonneg_left _ hA
  calc
    ‖(∏ j, L (basisVec (J j))) * iteratedDeriv n Real.sin (L x)‖ =
        (∏ j, ‖L (basisVec (J j))‖) * |iteratedDeriv n Real.sin (L x)| := by
          rw [norm_mul, norm_prod, Real.norm_eq_abs]
    _ ≤ (∏ _j : Fin n, ω) * 1 := by
      apply mul_le_mul _ (Real.abs_iteratedDeriv_sin_le_one n _) (abs_nonneg _)
        (Finset.prod_nonneg (fun _ _ => hω))
      apply Finset.prod_le_prod₀
      · intro j hj; positivity
      · intro j hj
        simp only [L, smul_apply, ContinuousLinearMap.proj_apply,
          smul_eq_mul, basisVec, Pi.single_apply]
        split_ifs <;> simp [abs_of_nonneg hω, hω]
    _ = ω ^ n := by simp

/-- Pointwise derivative bounds give the corresponding barred seminorm bound. -/
theorem barNorm_le_of_partial_le (f : Vec 2 → ℝ) (n : ℕ) (R B : ℝ)
    (hf : ContDiff ℝ n f)
    (hb : ∀ x (J : Fin n → Fin 2),
      ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ ≤ B) :
    AVenhance.barNorm n R f ≤
      ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
        (ENNReal.ofReal R)⁻¹ ^ n * ENNReal.ofReal B := by
  rw [barNorm_eq_pointwise f n R hf]
  have hsup : (⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
      ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ) ≤ ENNReal.ofReal B := by
    apply iSup_le
    intro J
    apply iSup_le
    intro x
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [Real.norm_eq_abs] using hb x J)
  calc
    ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
        (ENNReal.ofReal R)⁻¹ ^ n *
          (⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
            ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ) ≤
        ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
          (ENNReal.ofReal R)⁻¹ ^ n * ENNReal.ofReal B := by
            gcongr
    _ = _ := by ring

theorem barNorm_le_five_of_partial_le (f : Vec 2 → ℝ) (n : ℕ) {R A : ℝ}
    (hf : ContDiff ℝ n f) (hR : 0 < R) (hA : 0 ≤ A)
    (hb : ∀ x (J : Fin n → Fin 2),
      ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ ≤ A * R ^ n) :
    AVenhance.barNorm n R f ≤ ENNReal.ofReal (5 * A) := by
  refine (barNorm_le_of_partial_le f n R (A * R ^ n) hf hb).trans ?_
  rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_pow hR.le]
  have hcancel : (ENNReal.ofReal R)⁻¹ ^ n * ENNReal.ofReal R ^ n = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by simp [hR]) ENNReal.ofReal_ne_top, one_pow]
  calc
    ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
        (ENNReal.ofReal R)⁻¹ ^ n * (ENNReal.ofReal A * ENNReal.ofReal R ^ n) =
        ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) * ENNReal.ofReal A := by
          calc
            _ = ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
              ENNReal.ofReal A * ((ENNReal.ofReal R)⁻¹ ^ n * ENNReal.ofReal R ^ n) := by ring
            _ = _ := by rw [hcancel, mul_one]
    _ ≤ ENNReal.ofReal 5 * ENNReal.ofReal A := by
      gcongr
      exact factorial_coefficient_le_five n
    _ = ENNReal.ofReal (5 * A) := (ENNReal.ofReal_mul (by norm_num)).symm

/-- A coordinate sine has no dimension loss in the barred seminorm. -/
theorem barNorm_sine_le (A ω : ℝ) (hA : 0 ≤ A) (hω : 0 ≤ ω)
    (i : Fin 2) (n : ℕ) {R : ℝ} (hR : 0 < R) (hωR : ω ≤ R) :
    AVenhance.barNorm n R (fun x : Vec 2 => A * Real.sin (ω * x i)) ≤
      ENNReal.ofReal (5 * A) := by
  apply barNorm_le_five_of_partial_le _ n (by fun_prop) hR hA
  intro x J
  exact (sine_coordinate_partial_le A ω hA hω i n x J).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hω hωR n) hA)

end AVRegularity.Velocity.Port.ExplicitBarNorm
end
end
end

section
@[expose] public section
noncomputable section
open scoped BigOperators
open Finset
namespace AVRegularity.Velocity.Port.Scalars

/-! Scalar bookkeeping for the OC jet induction. -/

/-- Length scales in an OC jet recursion lie in `(0,1]`. -/
theorem epsilon_le_one {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) : D.epsilon m ≤ 1 :=
  D.epsilon_le_one m

/-- Finite geometric sums are bounded by the full convergent series. -/
theorem sum_geometric_le {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) (n : ℕ) :
    ∑ j ∈ range n, r ^ j ≤ (1 - r)⁻¹ := by
  have ha : |r| < 1 := by rwa [abs_of_nonneg hr]
  have hsum := summable_geometric_of_abs_lt_one ha
  simpa only [tsum_geometric_of_abs_lt_one ha] using
    hsum.sum_le_tsum (range n) (fun j _ => pow_nonneg hr j)

/-- Backward geometric summation for a sequence increasing toward later scales. -/
theorem sum_le_last_mul_geometric (u : ℕ → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hu : ∀ j, u j ≤ r * u (j + 1)) (m : ℕ) :
    ∑ j ∈ range (m + 1), u j ≤ u m * ∑ j ∈ range (m + 1), r ^ j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsum : 0 ≤ ∑ j ∈ range (m + 1), r ^ j :=
      sum_nonneg fun j _ => pow_nonneg hr j
    calc
      ∑ j ∈ range (m + 1 + 1), u j =
          (∑ j ∈ range (m + 1), u j) + u (m + 1) := sum_range_succ _ _
      _ ≤ u m * (∑ j ∈ range (m + 1), r ^ j) + u (m + 1) :=
        add_le_add ih le_rfl
      _ ≤ (r * u (m + 1)) * (∑ j ∈ range (m + 1), r ^ j) + u (m + 1) :=
        add_le_add (mul_le_mul_of_nonneg_right (hu m) hsum) le_rfl
      _ = u (m + 1) * (∑ j ∈ range (m + 1 + 1), r ^ j) := by
        rw [geom_sum_succ (x := r) (n := m + 1)]
        ring

/-- The negative velocity-amplitude exponent reverses the scale separation. -/
theorem amplitude_backward_step {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (j : ℕ) :
    D.velocityAmplitude j ≤ (Λ : ℝ) ^ (α - 1) *
      D.velocityAmplitude (j + 1) := by
  have he := D.epsilon_pos (j + 1)
  have hratio := D.epsilon_ratio (j + 1) (by omega)
  have hmul : (Λ : ℝ) * D.epsilon (j + 1) ≤ D.epsilon j := by
    exact (le_div_iff₀ he).mp (by simpa using hratio)
  have hΛ : 0 < (Λ : ℝ) := by
    have hΛlower := D.hΛ
    have hΛnat : 0 < Λ := by omega
    exact_mod_cast hΛnat
  have hej : 0 < D.epsilon j := D.epsilon_pos j
  have hpow := Real.rpow_le_rpow_of_nonpos (mul_pos hΛ he) hmul
    (show α - 1 ≤ 0 by linarith [D.hαlt])
  rw [D.velocityAmplitude_eq, D.velocityAmplitude_eq]
  calc
    D.epsilon j ^ (α - 1) ≤
        ((Λ : ℝ) * D.epsilon (j + 1)) ^ (α - 1) := hpow
    _ = (Λ : ℝ) ^ (α - 1) * D.epsilon (j + 1) ^ (α - 1) := by
      rw [Real.mul_rpow hΛ.le he.le]

/-- The backward geometric estimate for the OC velocity amplitudes. -/
theorem amplitude_sum_bounds {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) :
    (∑ j ∈ range (m + 1), D.velocityAmplitude j) ≤
      D.velocityAmplitude m *
        (∑ j ∈ range (m + 1), ((Λ : ℝ) ^ (α - 1)) ^ j) ∧
    (∑ j ∈ range (m + 1), D.velocityAmplitude j) ≤
      D.velocityAmplitude m / (1 - (Λ : ℝ) ^ (α - 1)) := by
  have hΛ : 1 < (Λ : ℝ) := by
    have hΛlower := D.hΛ
    have hΛnat : 1 < Λ := by omega
    exact_mod_cast hΛnat
  have hr : 0 ≤ (Λ : ℝ) ^ (α - 1) :=
    Real.rpow_nonneg (le_trans (by norm_num) hΛ.le) _
  have hr' : (Λ : ℝ) ^ (α - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hΛ (by linarith [D.hαlt])
  have hsum := sum_le_last_mul_geometric D.velocityAmplitude hr
    (amplitude_backward_step D) m
  refine ⟨hsum, hsum.trans ?_⟩
  rw [D.velocityAmplitude_eq]
  simpa [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_left (sum_geometric_le hr hr' (m + 1))
      (Real.rpow_nonneg (D.epsilon_pos m).le (α - 1))

/-- The source numerical closure is unchanged by replacing its amplitude by the OC one. -/
theorem M_numeric_closure :
    ((2 : ℝ) ^ 8 + 2 ^ 18) / (1 - (2 : ℝ) ^ (-(14 / 3 : ℝ))) ≤ 2 ^ 19 := by
  have he : -(14 / 3 : ℝ) ≤ -2 := by norm_num
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  norm_num at hp
  have hd : 0 < 1 - (2 : ℝ) ^ (-(14 / 3 : ℝ)) := by linarith
  apply (div_le_iff₀ hd).2
  norm_num at hp ⊢
  linarith only [hp]

/-- The OC amplitude ratio has the numerical bound used in the recurrence. -/
theorem amplitude_ratio_bound {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) :
    (Λ : ℝ) ^ (α - 1) ≤ (2 : ℝ) ^ (-(14 / 3 : ℝ)) := by
  have hL : (2 : ℝ) ^ 7 ≤ (Λ : ℝ) := by exact_mod_cast D.hΛ
  calc
    (Λ : ℝ) ^ (α - 1) ≤ ((2 : ℝ) ^ 7) ^ (α - 1) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hL (by linarith [D.hαlt])
    _ = (2 : ℝ) ^ (7 * (α - 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    _ ≤ (2 : ℝ) ^ (-(14 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [D.hαlt])

/-- Closure of the source amplitude sum with the OC velocity amplitudes. -/
theorem amplitude_sum_closure {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) :
    ((2 : ℝ) ^ 8 + 2 ^ 18) *
        (∑ j ∈ range (m + 1), D.velocityAmplitude j) ≤
      2 ^ 19 * D.velocityAmplitude m := by
  have hs := (amplitude_sum_bounds D m).2
  have hr := amplitude_ratio_bound D
  have ha : 0 ≤ D.velocityAmplitude m := by
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_nonneg (D.epsilon_pos m).le _
  have hd : 0 < 1 - (2 : ℝ) ^ (-(14 / 3 : ℝ)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hfrac := div_le_div_of_nonneg_left ha hd (sub_le_sub_left hr 1)
  calc
    ((2 : ℝ) ^ 8 + 2 ^ 18) *
        (∑ j ∈ range (m + 1), D.velocityAmplitude j) ≤
        (2 ^ 8 + 2 ^ 18) *
          (D.velocityAmplitude m / (1 - (2 : ℝ) ^ (-(14 / 3 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (hs.trans hfrac) (by norm_num)
    _ = (((2 : ℝ) ^ 8 + 2 ^ 18) /
        (1 - (2 : ℝ) ^ (-(14 / 3 : ℝ)))) * D.velocityAmplitude m := by ring
    _ ≤ 2 ^ 19 * D.velocityAmplitude m :=
      mul_le_mul_of_nonneg_right M_numeric_closure ha

/-- The OC renewal-window estimate in inverse velocity-amplitude form. -/
theorem tauPP_inverse_amplitude_bound {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) (hm : 1 ≤ m) :
    D.tauPP m ≤ (2 : ℝ) ^ (-25 : ℤ) *
      (D.velocityAmplitude (m - 1))⁻¹ *
        D.epsilon (m - 1) ^ (2 * ocDelta α q) := by
  have hA : 0 < D.velocityAmplitude (m - 1) := by
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_pos_of_pos (D.epsilon_pos _) _
  have hblock := D.block_small m hm
  have hdiv := (le_div_iff₀ hA).2 (by simpa [mul_comm] using hblock)
  calc
    D.tauPP m ≤
        ((2 : ℝ) ^ (-25 : ℤ) *
          D.epsilon (m - 1) ^ (2 * ocDelta α q)) /
          D.velocityAmplitude (m - 1) := by simpa [mul_comm] using hdiv
    _ = (2 : ℝ) ^ (-25 : ℤ) *
        (D.velocityAmplitude (m - 1))⁻¹ *
          D.epsilon (m - 1) ^ (2 * ocDelta α q) := by ring

/-- Abstract conversion from an amplitude bound to a time window. -/
theorem inverse_amplitude_window {A M E : ℝ} (hA : 0 < A) (hM : 0 < M)
    (hE : E ≤ 1) (hbound : M ≤ (2 : ℝ) ^ 19 * A) :
    (2 : ℝ) ^ (-24 : ℤ) * A⁻¹ * E ≤ (2 : ℝ) ^ (-5 : ℤ) * M⁻¹ := by
  have hfirst := mul_le_mul_of_nonneg_left hE
    (show 0 ≤ (2 : ℝ) ^ (-24 : ℤ) * A⁻¹ by positivity)
  have hsecond : (2 : ℝ) ^ (-24 : ℤ) * A⁻¹ ≤
      (2 : ℝ) ^ (-5 : ℤ) * M⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ hA hM).2
    norm_num at hbound ⊢
    linarith only [hbound]
  rw [mul_one] at hfirst
  exact hfirst.trans hsecond

/-- The OC renewal scale satisfies the induction time-window condition. -/
theorem tauPP_induction_window {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) (hm : 1 ≤ m)
    (hM : 0 < D.jetSize (m - 1))
    (hMbound : D.jetSize (m - 1) ≤
      (2 : ℝ) ^ 19 * D.velocityAmplitude (m - 1)) :
    D.tauPP m ≤ (2 : ℝ) ^ (-24 : ℤ) *
        (D.velocityAmplitude (m - 1))⁻¹ *
          D.epsilon (m - 1) ^ (2 * ocDelta α q) ∧
      D.tauPP m ≤ (2 : ℝ) ^ (-5 : ℤ) * (D.jetSize (m - 1))⁻¹ := by
  have hfirst := tauPP_inverse_amplitude_bound D m hm
  have hE : D.epsilon (m - 1) ^ (2 * ocDelta α q) ≤ 1 := by
    have hδ : 0 < ocDelta α q := (AVRegularity.Scales.admissible_exponent_facts
      D.hαpos D.hαlt D.hspos D.hslt D.hq).2.1
    exact Real.rpow_le_one (D.epsilon_pos _).le (D.epsilon_le_one _) (by positivity)
  have hweak : D.tauPP m ≤ (2 : ℝ) ^ (-24 : ℤ) *
      (D.velocityAmplitude (m - 1))⁻¹ *
        D.epsilon (m - 1) ^ (2 * ocDelta α q) := by
    calc
      D.tauPP m ≤ (2 : ℝ) ^ (-25 : ℤ) *
          (D.velocityAmplitude (m - 1))⁻¹ *
            D.epsilon (m - 1) ^ (2 * ocDelta α q) := hfirst
      _ ≤ _ := by
        have hA : 0 < D.velocityAmplitude (m - 1) := by
          rw [D.velocityAmplitude_eq]
          exact Real.rpow_pos_of_pos (D.epsilon_pos _) _
        have hfactor : 0 ≤ (D.velocityAmplitude (m - 1))⁻¹ *
            D.epsilon (m - 1) ^ (2 * ocDelta α q) :=
          mul_nonneg (inv_nonneg.mpr hA.le)
            (Real.rpow_nonneg (D.epsilon_pos _).le _)
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right
          (by norm_num : (2 : ℝ) ^ (-25 : ℤ) ≤ 2 ^ (-24 : ℤ)) hfactor
  have hlast := inverse_amplitude_window
    (show 0 < D.velocityAmplitude (m - 1) by
      rw [D.velocityAmplitude_eq]; exact Real.rpow_pos_of_pos (D.epsilon_pos _) _)
    hM hE hMbound
  exact ⟨hweak, hweak.trans hlast⟩

/-- The normalized-radius recurrence is bounded by `5/4`, as in the
construction source. -/
theorem radius_recurrence_scaled {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) :
    D.epsilon (m + 1) * D.radius m ≤ 5 / 4 := by
  have hnonneg : ∀ j, 0 ≤ D.radius j := by
    intro j
    induction j with
    | zero => rw [D.radius_zero]; norm_num
    | succ j ih =>
        have he := D.epsilon_pos (j + 1)
        rw [D.radius_step j]
        positivity
  have hsep : ∀ j, D.epsilon (j + 1) ≤ D.epsilon j / 128 := by
    intro j
    have hs := D.epsilon_succ_le j
    have hΛ : (128 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast D.hΛ
    have hmul : D.epsilon (j + 1) * (Λ : ℝ) ≤ D.epsilon j :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < (Λ : ℝ))).mp hs
    have hsmall := mul_le_mul_of_nonneg_right hΛ
      (D.epsilon_pos (j + 1)).le
    have h128 : D.epsilon (j + 1) * 128 ≤ D.epsilon j := by
      calc
        D.epsilon (j + 1) * 128 ≤
            D.epsilon (j + 1) * (Λ : ℝ) := by
          simpa [mul_comm] using hsmall
        _ ≤ D.epsilon j := hmul
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 128)).2 h128
  have hstep {E F R : ℝ} (hE : 0 < E) (hR : 0 ≤ R)
      (hsep' : F ≤ E / 128) (hprev : E * R ≤ 5 / 4) :
      F * ((9 / 4) * R + 128 * E⁻¹) ≤ 5 / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hsep'
      (show 0 ≤ (9 / 4) * R + 128 * E⁻¹ by positivity)
    have heq : E / 128 * ((9 / 4) * R + 128 * E⁻¹) =
        (9 / 512) * (E * R) + 1 := by
      field_simp
      ring
    rw [heq] at hmul
    linarith only [hmul, hprev]
  induction m with
  | zero =>
      rw [D.radius_zero]
      have hs := hsep 0
      rw [D.epsilon_zero] at hs
      have hbase : D.epsilon 1 ≤ 5 / 4 := hs.trans (by norm_num)
      simpa using hbase
  | succ m ih =>
      rw [D.radius_step m]
      norm_num only [show (2 : ℝ) ^ 7 = 128 by norm_num]
      exact hstep (D.epsilon_pos (m + 1)) (hnonneg m)
        (hsep (m + 1)) ih

/-- Radius is bounded by `131` times the inverse current wavelength. -/
theorem radius_recurrence_bound {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {m : ℕ} (hm : 1 ≤ m) :
    D.radius m ≤ 131 * (D.epsilon m)⁻¹ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hs := radius_recurrence_scaled D j
  have he := D.epsilon_pos (j + 1)
  have halg {E R : ℝ} (hE : 0 < E) (hER : E * R ≤ 5 / 4) :
      (9 / 4) * R + 128 * E⁻¹ ≤ 131 * E⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv]
    apply (le_div_iff₀ hE).2
    have heq : ((9 / 4) * R + 128 / E) * E = (9 / 4) * (E * R) + 128 := by
      field_simp
    rw [heq]
    linarith only [hER]
  rw [D.radius_step j]
  simpa only [show (2 : ℝ) ^ 7 = 128 by norm_num] using halg he hs

/-- The exact source closure for the full jet-size recurrence. -/
theorem full_amplitude_recurrence_bound {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) :
    D.jetSize m ≤ 2 ^ 19 * D.velocityAmplitude m := by
  have hnonneg : ∀ j, 0 ≤ D.radius j := by
    intro j
    induction j with
    | zero => rw [D.radius_zero]; norm_num
    | succ j ih =>
        have he := D.epsilon_pos (j + 1)
        rw [D.radius_step j]
        positivity
  have hstep : ∀ j, D.jetSize (j + 1) ≤ D.jetSize j +
      ((2 : ℝ) ^ 8 + 2 ^ 18) * D.velocityAmplitude (j + 1) := by
    intro j
    have hs := radius_recurrence_scaled D j
    have he := D.epsilon_pos (j + 1)
    have ha : 0 ≤ D.velocityAmplitude (j + 1) := by
      rw [D.velocityAmplitude_eq]
      exact Real.rpow_nonneg he.le _
    have hER : 0 ≤ D.epsilon (j + 1) * D.radius j :=
      mul_nonneg he.le (hnonneg j)
    have hsq : (D.epsilon (j + 1) * D.radius j) ^ 2 ≤
        (5 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ hER hs 2
    have hmul := mul_le_mul_of_nonneg_left hsq ha
    have hh : (2 : ℝ) ^ 7 * D.velocityAmplitude (j + 1) *
          D.epsilon (j + 1) ^ 2 * D.radius j ^ 2 +
        2 ^ 18 * D.velocityAmplitude (j + 1) ≤
          (2 ^ 8 + 2 ^ 18) * D.velocityAmplitude (j + 1) := by
      nlinarith only [hmul, ha]
    rw [D.jetSize_step j]
    nlinarith only [hh]
  have hsum : D.jetSize m ≤
      ((2 : ℝ) ^ 8 + 2 ^ 18) *
        (∑ j ∈ range (m + 1), D.velocityAmplitude j) := by
    induction m with
    | zero =>
        have ha0 : D.velocityAmplitude 0 = 1 := by
          rw [D.velocityAmplitude_eq, D.epsilon_zero]
          exact Real.one_rpow _
        rw [D.jetSize_zero]
        simp only [Nat.zero_add, Finset.sum_range_succ,
          Finset.sum_range_zero]
        rw [ha0]
        norm_num
    | succ m ih =>
        calc
          D.jetSize (m + 1) ≤ D.jetSize m +
              ((2 : ℝ) ^ 8 + 2 ^ 18) * D.velocityAmplitude (m + 1) := hstep m
          _ ≤ ((2 : ℝ) ^ 8 + 2 ^ 18) *
              (∑ j ∈ range (m + 1), D.velocityAmplitude j) +
              ((2 : ℝ) ^ 8 + 2 ^ 18) * D.velocityAmplitude (m + 1) :=
                add_le_add ih le_rfl
          _ = _ := by
            have hsumEq :
                (∑ j ∈ range (m + 1), D.velocityAmplitude j) +
                    D.velocityAmplitude (m + 1) =
                  ∑ j ∈ range (m + 1 + 1), D.velocityAmplitude j := by
              exact (Finset.sum_range_succ (f := D.velocityAmplitude)
                (n := m + 1)).symm
            rw [← mul_add, hsumEq]
  exact hsum.trans (amplitude_sum_closure D m)

end AVRegularity.Velocity.Port.Scalars
end
end
end

section
@[expose] public section
namespace AVRegularity.Velocity.Port.Section2Scales

/-! OC scale sequences for the Section 2 stream induction. -/

/-- Every radius in the recurrence is positive. -/
theorem section2_radius_pos {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) : 0 < D.radius m := by
  induction m with
  | zero => rw [D.radius_zero]; norm_num
  | succ m ih =>
      rw [D.radius_step m]
      have he : 0 < D.epsilon (m + 1) := D.epsilon_pos _
      positivity

/-- Every jet-size value in the recurrence is positive. -/
theorem section2_amplitude_pos {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) : 0 < D.jetSize m := by
  induction m with
  | zero => rw [D.jetSize_zero]; norm_num
  | succ m ih =>
      rw [D.jetSize_step m]
      have he : 0 < D.epsilon (m + 1) := D.epsilon_pos _
      have hR : 0 < D.radius m := section2_radius_pos D m
      have ha : 0 ≤ D.velocityAmplitude (m + 1) := by
        rw [D.velocityAmplitude_eq]
        exact Real.rpow_nonneg he.le _
      positivity

end AVRegularity.Velocity.Port.Section2Scales
end
end

section
@[expose] public section
noncomputable section
open Homogenization AVenhance
namespace AVRegularity.Velocity.Port.Section2FlowIdentities

/-! Structural identities for the flow generated by an admissible OC stream. -/

/-- The general smooth flow generated by one admissible stream slice. -/
noncomputable def streamFlow (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) : ℝ → Vec 2 → ℝ → Vec 2 :=
  flow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz

/-- The reverse-time flow, matching the recursion's `flowInv` object. -/
noncomputable def streamFlowInv (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) : ℝ → Vec 2 → ℝ → Vec 2 :=
  flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz

/-- Spatial derivative of the forward flow at time offset `t` from `s`. -/
noncomputable def streamFlowJacobian (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (t s : ℝ) (x : Vec 2) :
    Vec 2 →L[ℝ] Vec 2 :=
  fderiv ℝ (fun y => streamFlow φ hφ (s + t) y s) x

/-- Spatial derivative of the reverse flow at time offset `t` from `s`. -/
noncomputable def streamFlowInvJacobian (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (t s : ℝ) (x : Vec 2) :
    Vec 2 →L[ℝ] Vec 2 :=
  fderiv ℝ (fun y => streamFlowInv φ hφ (s + t) y s) x

/-- The forward Jacobian evaluated along the reverse flow. -/
noncomputable def streamComposedFlowJacobian (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (s r : ℝ) (x : Vec 2) :
    Vec 2 →L[ℝ] Vec 2 :=
  streamFlowJacobian φ hφ r s (streamFlowInv φ hφ (s + r) x s)

/-- The forward flow for one term of an OC stream sequence. -/
noncomputable def constructionFlow {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : AVRegularity.Velocity.JetRecursionData α s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) :
    ℝ → Vec 2 → ℝ → Vec 2 :=
  streamFlow (Φ m) (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m)

/-- The inverse flow for one term of an OC stream sequence. -/
noncomputable def constructionFlowInv {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : AVRegularity.Velocity.JetRecursionData α s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) :
    ℝ → Vec 2 → ℝ → Vec 2 :=
  streamFlowInv (Φ m) (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m)

/-- The forward spatial Jacobian for a finite OC stream flow. -/
noncomputable def constructionFlowJacobian {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : AVRegularity.Velocity.JetRecursionData α s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ) (m : ℕ)
    (t s : ℝ) (x : Vec 2) : Vec 2 →L[ℝ] Vec 2 :=
  streamFlowJacobian (Φ m)
    (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m) t s x

/-- The inverse spatial Jacobian for a finite OC stream flow. -/
noncomputable def constructionFlowInvJacobian {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : AVRegularity.Velocity.JetRecursionData α s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ) (m : ℕ)
    (t s : ℝ) (x : Vec 2) : Vec 2 →L[ℝ] Vec 2 :=
  streamFlowInvJacobian (Φ m)
    (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m) t s x

/-- The forward Jacobian pulled back by the inverse finite-stage flow. -/
noncomputable def constructionComposedFlowJacobian {α s q : ℝ} {Λ : ℕ}
    {ζ : ℝ → ℝ} (D : AVRegularity.Velocity.JetRecursionData α s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ) (m : ℕ)
    (s r : ℝ) (x : Vec 2) : Vec 2 →L[ℝ] Vec 2 :=
  streamComposedFlowJacobian (Φ m)
    (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m) s r x

/-- Time translation preserves the flow equation. -/
theorem constructionFlow_shift_isFlow
    {b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : IsFlow b X) (s : ℝ) :
    IsFlow (fun t x => b (s + t) x)
      (fun t x r => X (s + t) x (s + r)) := by
  refine ⟨?_, ?_⟩
  · intro x r
    exact hX.1 x (s + r)
  · intro x r t
    have hbase : HasDerivAt (fun z => X z x (s + r))
        (b (t + s) (X (t + s) x (s + r))) (t + s) := by
      simpa [add_comm] using hX.2 x (s + r) (s + t)
    have hshifted := hbase.comp_add_const t s
    convert hshifted using 1 <;> simp [add_comm]

theorem linearMap_apply_two (A : Vec 2 →L[ℝ] Vec 2) (v : Vec 2) (i : Fin 2) :
    A v i = A (basisVec 0) i * v 0 + A (basisVec 1) i * v 1 := by
  have hv : v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
    ext j
    fin_cases j <;> simp [basisVec]
  rw [hv, map_add, map_smul, map_smul]
  simp [basisVec]
  ring

theorem continuousLinearMap_det_two (J : Vec 2 →L[ℝ] Vec 2) :
    J.det = J (basisVec 0) 0 * J (basisVec 1) 1 -
      J (basisVec 1) 0 * J (basisVec 0) 1 := by
  change LinearMap.det J.toLinearMap = _
  rw [← LinearMap.det_toMatrix' J.toLinearMap, Matrix.det_fin_two]
  simp [LinearMap.toMatrix'_apply, basisVec]

/-- Cofactor entries for a left inverse of a determinant-one map. -/
theorem left_inverse_entries_of_det_one {A B : Vec 2 →L[ℝ] Vec 2}
    (hcomp : A.comp B = ContinuousLinearMap.id ℝ (Vec 2)) (hdet : B.det = 1) :
    A (basisVec 0) 0 = B (basisVec 1) 1 ∧
    A (basisVec 1) 0 = -B (basisVec 1) 0 ∧
    A (basisVec 0) 1 = -B (basisVec 0) 1 ∧
    A (basisVec 1) 1 = B (basisVec 0) 0 := by
  let a := B (basisVec 0) 0
  let b := B (basisVec 1) 0
  let c := B (basisVec 0) 1
  let d := B (basisVec 1) 1
  have hdet' : a * d - b * c = 1 := by
    have h := continuousLinearMap_det_two B
    rw [h] at hdet
    dsimp [a, b, c, d]
    nlinarith
  have h0 : A (B (basisVec 0)) = basisVec 0 := by
    have h := congrArg (fun L : Vec 2 →L[ℝ] Vec 2 => L (basisVec 0)) hcomp
    simpa using h
  have h1 : A (B (basisVec 1)) = basisVec 1 := by
    have h := congrArg (fun L : Vec 2 →L[ℝ] Vec 2 => L (basisVec 1)) hcomp
    simpa using h
  have h00 : A (basisVec 0) 0 * a + A (basisVec 1) 0 * c = 1 := by
    have h := congrArg (fun v : Vec 2 => v 0) h0
    rw [linearMap_apply_two] at h
    simpa [a, b, c, d, basisVec] using h
  have h01 : A (basisVec 0) 0 * b + A (basisVec 1) 0 * d = 0 := by
    have h := congrArg (fun v : Vec 2 => v 0) h1
    rw [linearMap_apply_two] at h
    simpa [a, b, c, d, basisVec] using h
  have h10 : A (basisVec 0) 1 * a + A (basisVec 1) 1 * c = 0 := by
    have h := congrArg (fun v : Vec 2 => v 1) h0
    rw [linearMap_apply_two] at h
    simpa [a, b, c, d, basisVec] using h
  have h11 : A (basisVec 0) 1 * b + A (basisVec 1) 1 * d = 1 := by
    have h := congrArg (fun v : Vec 2 => v 1) h1
    rw [linearMap_apply_two] at h
    simpa [a, b, c, d, basisVec] using h
  constructor
  · linear_combination d * h00 - c * h01 - (A (basisVec 0) 0) * hdet'
  constructor
  · linear_combination -b * h00 + a * h01 - (A (basisVec 1) 0) * hdet'
  constructor
  · linear_combination d * h10 - c * h11 - (A (basisVec 0) 1) * hdet'
  · linear_combination -b * h10 + a * h11 - (A (basisVec 1) 1) * hdet'

/-- The spatial trace in Liouville's formula is the classical divergence. -/
theorem spatialDivergence_eq_vecDiv {b : ℝ → Vec 2 → Vec 2}
    (hb : Infra.Flow.SmoothPeriodicField b) (t : ℝ) (x : Vec 2) :
    Infra.Flow.spatialDivergence b t x = vecDiv (b t) x := by
  rw [Infra.Flow.spatialDivergence, Infra.Flow.jointSpatialFDeriv_eq_slice hb]
  unfold vecDiv
  rw [Fin.sum_univ_two]
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (b t) :=
    hb.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hd : DifferentiableAt ℝ (b t) x := hsmooth.differentiable (by simp) x
  have h0 := fderiv_apply hd 0
  have h1 := fderiv_apply hd 1
  have h0' : fderiv ℝ (fun y => b t y 0) x (basisVec 0) =
      fderiv ℝ (b t) x (basisVec 0) 0 := by rw [h0]; rfl
  have h1' : fderiv ℝ (fun y => b t y 1) x (basisVec 1) =
      fderiv ℝ (b t) x (basisVec 1) 1 := by rw [h1]; rfl
  change fderiv ℝ (b t) x (basisVec 0) 0 +
      fderiv ℝ (b t) x (basisVec 1) 1 =
    fderiv ℝ (fun y => b t y 0) x (basisVec 0) +
      fderiv ℝ (fun y => b t y 1) x (basisVec 1)
  rw [h0', h1']

/-- Every admissible stream velocity has zero spatial divergence. -/
theorem streamVel_spatialDivergence_eq_zero {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t : ℝ) (x : Vec 2) :
    Infra.Flow.spatialDivergence (streamVel φ) t x = 0 := by
  rw [spatialDivergence_eq_vecDiv
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ)]
  exact Infra.Classical.streamVel_vecDiv_eq_zero φ hφ t x

/-- The inverse-flow spatial derivative has determinant one. -/
theorem streamFlowInvJacobian_det_eq_one {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (r s : ℝ) (x : Vec 2) :
    (streamFlowInvJacobian φ hφ r s x).det = 1 := by
  let b := streamVel φ
  let X := streamFlow φ hφ
  have hb : Infra.Flow.SmoothPeriodicField b :=
    AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hX : IsFlow b X := by
    dsimp [X, b, streamFlow]
    exact AVenhance.flow_isFlow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz
  have hdiv : ∀ u y, Infra.Flow.spatialDivergence b u y = 0 :=
    fun u y => streamVel_spatialDivergence_eq_zero hφ u y
  simpa [streamFlowInvJacobian, streamFlowInv, X, b, streamFlow, flowInv] using
    Infra.Flow.flow_spatial_jacobian_det_eq_one_of_divergence_free
      hb hX hdiv x (s + r) s

/-- Forward and reverse flow Jacobians compose to the identity. -/
theorem streamComposedJacobian_comp_inverse_eq_id
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (r s : ℝ) (x : Vec 2) :
    (streamComposedFlowJacobian φ hφ s r x).comp
      (streamFlowInvJacobian φ hφ r s x) =
        ContinuousLinearMap.id ℝ (Vec 2) := by
  let b := streamVel φ
  let X := streamFlow φ hφ
  let H := streamFlowInv φ hφ
  let F : Vec 2 → Vec 2 := fun y => X (s + r) y s
  let G : Vec 2 → Vec 2 := fun y => H (s + r) y s
  have hb : Infra.Flow.SmoothPeriodicField b :=
    AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hX : IsFlow b X := by
    dsimp [X, b, streamFlow]
    exact AVenhance.flow_isFlow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz
  obtain ⟨_, _, _, hright⟩ :=
    Infra.Flow.flow_fixed_time_maps_are_C1_inverses hb hX s (s + r)
  have hmap (y : Vec 2) : F (G y) = y := by
    simpa [F, G, X, H, streamFlow, streamFlowInv, flowInv] using hright y
  have hF : HasFDerivAt F
      (streamFlowJacobian φ hφ r s (G x)) (G x) := by
    have hdiff := Infra.Flow.flow_spatial_contDiff_one hb hX s (s + r)
    simpa [F, streamFlowJacobian, X, streamFlow] using
      (hdiff.differentiable (by norm_num) (G x)).hasFDerivAt
  have hG : HasFDerivAt G (streamFlowInvJacobian φ hφ r s x) x := by
    have hdiff := Infra.Flow.flow_spatial_contDiff_one hb hX (s + r) s
    simpa [G, streamFlowInvJacobian, H, X, streamFlowInv, streamFlow, flowInv] using
      (hdiff.differentiable (by norm_num) x).hasFDerivAt
  have hchain := HasFDerivAt.comp x hF hG
  have hid := hchain.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => (hmap y).symm)
  have hderiv := hid.unique (hasFDerivAt_id x)
  simpa [streamComposedFlowJacobian, streamFlowJacobian, streamFlowInvJacobian,
    G, F, H, X, streamFlowInv, streamFlow, flowInv] using hderiv

/-- The two-dimensional cofactor identity for the composed and inverse
flow Jacobians. -/
theorem streamComposedJacobian_cofactor_entries
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (r s : ℝ) (x : Vec 2) :
    streamComposedFlowJacobian φ hφ s r x (basisVec 0) 0 =
        streamFlowInvJacobian φ hφ r s x (basisVec 1) 1 ∧
    streamComposedFlowJacobian φ hφ s r x (basisVec 1) 0 =
        -streamFlowInvJacobian φ hφ r s x (basisVec 1) 0 ∧
    streamComposedFlowJacobian φ hφ s r x (basisVec 0) 1 =
        -streamFlowInvJacobian φ hφ r s x (basisVec 0) 1 ∧
    streamComposedFlowJacobian φ hφ s r x (basisVec 1) 1 =
        streamFlowInvJacobian φ hφ r s x (basisVec 0) 0 := by
  exact left_inverse_entries_of_det_one
    (streamComposedJacobian_comp_inverse_eq_id hφ r s x)
    (streamFlowInvJacobian_det_eq_one hφ r s x)

end AVRegularity.Velocity.Port.Section2FlowIdentities
end
end
end

section
@[expose] public section
noncomputable section
open Homogenization AVenhance
namespace AVRegularity.Velocity.Port.MaterialGoalSource

/-! Source-form hypotheses for the Section 2 material estimates, expressed
with the OC scale and the construction flow. -/

/-- Coordinatewise material iterates of a vector field, using the scalar
material derivative already used for Jacobian entries. -/
def materialIterateVector (b : ℝ → Vec 2 → Vec 2) (ell : ℕ)
    (F : ℝ → Vec 2 → Vec 2) : ℝ → Vec 2 → Vec 2 :=
  fun t x i => constructionMaterialIterate b ell (fun r y => F r y i) t x

/-- One coordinate of the material derivative of the spatial gradient of a
vector field. -/
def materialIterateGradientEntry (b : ℝ → Vec 2 → Vec 2) (ell : ℕ)
    (F : ℝ → Vec 2 → Vec 2) (i j : Fin 2) : ℝ → Vec 2 → ℝ :=
  constructionMaterialIterate b ell
    (fun r x => fderiv ℝ (F r) x (basisVec j) i)

/-- `p.material.goal` in coordinate Fréchet-derivative form at one scale.
The exponents use the relation `β = 1 + α`. The second line is stated
on its defined range `n ≥ 1`, since the display `∇^(n-1)` is undefined
at `n = 0`. -/
structure PMaterialGoalSourceData {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (Cmat : ℝ) (m : ℕ) : Prop where
  constant_ge_one : 1 ≤ Cmat
  velocity_material_bound : ∀ n ell : ℕ,
    1 ≤ n + ell → n + ell ≤ AVenhance.Nstar (1 + α) → ∀ t : ℝ, ∀ x : Vec 2,
      ∀ J : Fin n → Fin 2,
        ‖iteratedFDeriv ℝ n
          (materialIterateVector (streamVel (Φ m)) ell (streamVel (Φ m)) t)
          x (fun k => basisVec (J k))‖ ≤
            Cmat * D.epsilon m ^ ((1 + α) - 1) *
              (D.epsilon m ^ ((1 + α) - 2)) ^ ell *
              (D.epsilon m)⁻¹ ^ n
  gradient_material_bound : ∀ n ell : ℕ,
    1 ≤ n → n + ell ≤ AVenhance.Nstar (1 + α) → ∀ t : ℝ, ∀ x : Vec 2,
      ∀ i j : Fin 2, ∀ J : Fin (n - 1) → Fin 2,
        ‖iteratedFDeriv ℝ (n - 1)
          (materialIterateGradientEntry (streamVel (Φ m)) ell
            (streamVel (Φ m)) i j t) x (fun k => basisVec (J k))‖ ≤
              Cmat * D.epsilon m ^ ((1 + α) - 2) *
                (D.epsilon m ^ ((1 + α) - 2)) ^ ell *
                (D.epsilon m)⁻¹ ^ (n - 1)

/-- Iteration of an ordinary time derivative, for the displayed
`∂ₜ^ell` in `c.material.goal`. -/
def iteratedTimeDerivative {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ℕ → (ℝ → E) → ℝ → E
  | 0, f => f
  | ell + 1, f => fun t => deriv (iteratedTimeDerivative ell f) t

/-- The inverse Jacobian pulled back along the forward flow, as in the
left-hand side of `c.material.goal`. -/
noncomputable def inverseJacobianPulledBack {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (s r : ℝ)
    (x : Vec 2) : Vec 2 →L[ℝ] Vec 2 :=
  Section2FlowIdentities.constructionFlowInvJacobian D hseq m r s
    (Section2FlowIdentities.constructionFlow D hseq m (s + r) x s)

/-- `c.material.goal` in componentwise form at one scale. Its quantitative
input is recorded separately from `PMaterialGoalSourceData`. -/
structure CMaterialGoalSourceData {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (Cmat : ℝ) (m : ℕ) : Prop where
  pulled_inverse_jacobian_bound : ∀ s r : ℝ,
    |r| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ n ell : ℕ,
      n + ell ≤ AVenhance.Nstar (1 + α) → ∀ i j : Fin 2, ∀ x : Vec 2,
        ∀ J : Fin n → Fin 2,
          ‖iteratedFDeriv ℝ n
            (fun y => iteratedTimeDerivative ell
              (fun r => inverseJacobianPulledBack D hseq m s r y
                (basisVec j) i) r)
            x (fun k => basisVec (J k))‖ ≤
              Cmat * (D.epsilon m)⁻¹ ^ n *
                (D.epsilon m ^ ((1 + α) - 2)) ^ ell

end AVRegularity.Velocity.Port.MaterialGoalSource
end
end
end
