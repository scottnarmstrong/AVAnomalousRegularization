-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.NormalizedCellB1MixedGrading
public import AVRegularity.Definitions.CycleEvolution.IsFibreGraph
public import AVRegularity.CycleComparison.Lift.TransverseModeKernel
public import AVRegularity.Definitions.CycleComparison.IsLiftTailPresentation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

section
@[expose] public section
namespace AVRegularity.CycleComparison.Lift

/-! Uniform slow majorants give a dimension-independent power-of-two bilinear bound. -/

variable {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_bilinear_uniform_graded_le (n r s : ℕ)
    (T : E →L[ℝ] F →L[ℝ] G) (hT : ‖T‖ ≤ 1) (f : X → E) (g : X → F)
    (hf : ContDiff ℝ (n : ℕ∞) f) (hg : ContDiff ℝ (n : ℕ∞) g)
    (x : X) (lam A B : ℝ) (hlam : 0 ≤ lam) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbA : ∀ j ≤ n, ‖iteratedFDeriv ℝ j f x‖ ≤ A * lam ^ (r + j))
    (hbB : ∀ j ≤ n, ‖iteratedFDeriv ℝ j g x‖ ≤ B * lam ^ (s + j)) :
    ‖iteratedFDeriv ℝ n (fun y => T (f y) (g y)) x‖ ≤
      (2 ^ n * A * B) * lam ^ (r + s + n) := by
  have h := norm_iteratedFDeriv_bilinear_graded_le n r s T hT f g hf hg x lam hlam
    (fun _ => A) (fun _ => B) (fun _ _ => hA) (fun _ _ => hB) hbA hbB
  have he : (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * A * B) = 2 ^ n * A * B := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    have hn : (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ)) = 2 ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    rw [hn]
  rwa [he] at h

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Linear exponential tests have exact scale powers in their local slow-jet majorants. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_exp_linear_scaled_le (n : ℕ) (A : E →L[ℝ] ℝ)
    (lam : ℝ) (hlam : 0 ≤ lam) (X : E) :
    ‖iteratedFDeriv ℝ n (fun Y => Real.exp ((lam • A) Y)) X‖ ≤
      Real.exp ((lam • A) X) * ‖A‖ ^ n * lam ^ n := by
  have he : (fun Y => Real.exp ((lam • A) Y)) = Real.exp ∘ (lam • A) := rfl
  rw [he, (lam • A).iteratedFDeriv_comp_right
    (Real.contDiff_exp : ContDiff ℝ (n : ℕ∞) Real.exp) X (i := n) le_rfl]
  apply ((iteratedFDeriv ℝ n Real.exp ((lam • A) X)).norm_compContinuousLinearMap_le
    (fun _ : Fin n => lam • A)).trans_eq
  rw [norm_iteratedFDeriv_real_exp]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
  ring

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Extend local cell coefficients by clamping time to their closed window. -/

def localCellMetric (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  fun t _ => G (Set.projIcc a b hab t)

def localCellDrift (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) : ℝ → Vec 2 → Vec 2 :=
  fun t z => v (Set.projIcc a b hab t) z

theorem localCellMetric_admissible (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hm : ∀ i j, Measurable (fun t => G t i j))
    (hs : ∀ t ∈ Set.Icc a b, (G t).IsSymm)
    (he : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, ξ i * G t i j * ξ j ∧
      (∑ i, ∑ j, ξ i * G t i j * ξ j) ≤ (5 / 4) * ∑ i, ξ i ^ 2) :
    IsCellMetric (localCellMetric a b hab G) := by
  have hproj := (continuous_projIcc (a := a) (b := b) (h := hab)).measurable
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (hm i j).comp (hproj.subtype_val.comp measurable_fst)
  · intro t n z
    rfl
  · intro t z
    exact hs _ (Set.projIcc a b hab t).2
  · intro t z ξ
    have hh := he _ (Set.projIcc a b hab t).2 ξ
    have hn : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    change (1 / 2) * (∑ i, ξ i ^ 2) ≤ _ ∧ _ ≤ 2 * (∑ i, ξ i ^ 2)
    change (1 / 2) * (∑ i, ξ i ^ 2) ≤ (∑ i, ∑ j, ξ i * G (Set.projIcc a b hab t) i j * ξ j) ∧
      (∑ i, ∑ j, ξ i * G (Set.projIcc a b hab t) i j * ξ j) ≤ 2 * (∑ i, ξ i ^ 2)
    constructor <;> linarith

theorem localCellDrift_measurable (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hc : ∀ t ∈ Set.Icc a b, Continuous (v t))
    (hm : ∀ z, Measurable (fun t => v t z)) :
    Measurable (fun p : ℝ × Vec 2 => localCellDrift a b hab v p.1 p.2) := by
  have hproj := (continuous_projIcc (a := a) (b := b) (h := hab)).measurable
  have hjoint := measurable_uncurry_of_continuous_of_measurable
    (u := fun z t => v (Set.projIcc a b hab t) z)
    (fun t => hc _ (Set.projIcc a b hab t).2) (fun z => (hm z).comp hproj.subtype_val)
  exact hjoint.comp measurable_swap

theorem localCellMetric_eq (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    localCellMetric a b hab G t = fun _ => G t := by
  funext z
  change G (Set.projIcc a b hab t) = G t
  rw [Set.projIcc_of_mem hab ht]

theorem localCellDrift_eq (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    localCellDrift a b hab v t = v t := by
  funext z
  change v (Set.projIcc a b hab t) z = v t z
  rw [Set.projIcc_of_mem hab ht]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Positive masses conjugate finite matrix products exactly. -/

variable {ι : Type*} [Fintype ι]

def massConjugatedMatrix (π : ι → ℝ) (A : ι → ι → ℝ) : ι → ι → ℝ :=
  fun v u => Real.sqrt (π u / π v) * A v u

omit [Fintype ι] in
theorem massRatio_sqrt_mul (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (v r u : ι) :
    Real.sqrt (π r / π v) * Real.sqrt (π u / π r) = Real.sqrt (π u / π v) := by
  rw [← Real.sqrt_mul (div_nonneg (hπ r).le (hπ v).le)]
  congr 1
  field_simp [ne_of_gt (hπ r), ne_of_gt (hπ v)]

theorem massConjugatedMatrix_product (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A B : ι → ι → ℝ) :
    massConjugatedMatrix π (finiteMatrixProduct A B) =
      finiteMatrixProduct (massConjugatedMatrix π A) (massConjugatedMatrix π B) := by
  funext v u
  unfold massConjugatedMatrix finiteMatrixProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = (Real.sqrt (π r / π v) * Real.sqrt (π u / π r)) * (A v r * B r u) := by
      rw [massRatio_sqrt_mul π hπ]
    _ = _ := by ring

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
namespace AVRegularity.CycleComparison.Lift

/-! The original fast reserve supports both the weak inverse and the final energy readout. -/

theorem lift_inverse_order_le_ambient_fast_reserve (D N k L n : ℕ)
    (hD : 1 ≤ D) (hn : n ≤ N) :
    max (k + 1) (L + 2) ≤
      ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 n := by
  have hk := Nat.le_max_left k (L + 2)
  have hL := Nat.le_max_right k (L + 2)
  unfold ambientDegreeFastReserve
  omega

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! An independent fast coordinate introduces no quantitative loss in mixed slow jets. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_slow_field_le (r q : ℕ) (f : Vec 2 → E) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (fun _ : Vec 2 => f Y) z) X‖ ≤
      ‖iteratedFDeriv ℝ r f X‖ := by
  cases q with
  | zero => exact (norm_mixed_fast_zero_eq r (fun Y _ => f Y) X z).le
  | succ q =>
    have he : (fun Y => iteratedFDeriv ℝ (q + 1) (fun _ : Vec 2 => f Y) z) =
        fun _ => 0 := by
      funext Y
      rw [iteratedFDeriv_succ_const]
      rfl
    rw [he]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact norm_nonneg _

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Finite currying proves smooth evaluation of variable multilinear coefficients and variable inputs. -/

variable {B F : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_multilinear_evaluation (n : ℕ) :
    ∀ (E : Fin n → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
      (p : ℕ∞) (f : B → ContinuousMultilinearMap ℝ E F) (φ : B → ∀ i, E i),
      ContDiff ℝ p f → ContDiff ℝ p φ → ContDiff ℝ p (fun x => f x (φ x)) := by
  induction n with
  | zero =>
    intro E _ _ p f φ hf _
    let v : ∀ i : Fin 0, E i := fun i => Fin.elim0 i
    have he : (fun x => f x (φ x)) = fun x => multilinearEvaluationMap v (f x) := by
      funext x
      rw [multilinearEvaluationMap_apply]
      congr 1
      funext i
      exact Fin.elim0 i
    rw [he]
    exact (multilinearEvaluationMap v).contDiff.comp hf
  | succ n ih =>
    intro E _ _ p f φ hf hφ
    let C : ContinuousMultilinearMap ℝ E F →L[ℝ]
        (E 0 →L[ℝ] ContinuousMultilinearMap ℝ (fun i : Fin n => E i.succ) F) :=
      LinearMap.mkContinuous
        { toFun := fun g => (continuousMultilinearCurryLeftEquiv ℝ E F) g
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
        1 (fun g => by
          change ‖(continuousMultilinearCurryLeftEquiv ℝ E F) g‖ ≤ 1 * ‖g‖
          rw [(continuousMultilinearCurryLeftEquiv ℝ E F).norm_map, one_mul])
    have hCf : ContDiff ℝ p (fun x => C (f x)) := by
      exact (ContinuousLinearMap.contDiff
        (F := E 0 →L[ℝ] ContinuousMultilinearMap ℝ (fun i : Fin n => E i.succ) F) C).comp hf
    have hC : ContDiff ℝ p (fun x => C (f x) (φ x 0)) :=
      hCf.clm_apply (contDiff_pi.mp hφ 0)
    have htail : ContDiff ℝ p (fun x (i : Fin n) => φ x i.succ) := by
      apply contDiff_pi.mpr
      intro i
      exact contDiff_pi.mp hφ i.succ
    have hh := ih (fun i : Fin n => E i.succ) p (fun x => C (f x) (φ x 0))
      (fun x (i : Fin n) => φ x i.succ) hC htail
    have he : (fun x => C (f x) (φ x 0) (fun i : Fin n => φ x i.succ)) =
        fun x => f x (φ x) := by
      funext x
      change f x (Fin.cons (φ x 0) (fun i : Fin n => φ x i.succ)) = f x (φ x)
      congr 1
      funext i
      exact Fin.cases rfl (fun j => rfl) i
    simpa only [he] using hh

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Directional slow derivatives are measurable in a merely measurable time parameter. -/

variable {T : Type*} [MeasurableSpace T]
  {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem fderiv_apply_parameter_measurable (f : T → D → E)
    (hm : ∀ x, Measurable (fun t => f t x)) (hd : ∀ t, Differentiable ℝ (f t))
    (x ξ : D) : Measurable (fun t => fderiv ℝ (f t) x ξ) := by
  let F := fun t (r : ℝ) => f t (x + r • ξ)
  have hline_diff : Differentiable ℝ (fun r : ℝ => x + r • ξ) :=
    (differentiable_const x).add (differentiable_id.smul_const ξ)
  have hF : ∀ t, Differentiable ℝ (F t) := fun t => (hd t).comp hline_diff
  have hmeas := deriv_parameter_measurable F (fun r => hm (x + r • ξ)) hF 0
  have he : (fun t => deriv (F t) 0) = fun t => fderiv ℝ (f t) x ξ := by
    funext t
    have hline : HasDerivAt (fun r : ℝ => x + r • ξ) ξ 0 := by
      simpa only [Pi.add_apply, zero_add, one_smul, id_eq] using!
        (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const ξ)
    have hbase : HasFDerivAt (f t) (fderiv ℝ (f t) x) (x + (0 : ℝ) • ξ) := by
      simpa only [zero_smul, add_zero] using (hd t x).hasFDerivAt
    have hh := hbase.comp_hasDerivAt 0 hline
    simpa only [zero_smul, add_zero, Function.comp_def, F] using! hh.deriv
  rwa [he] at hmeas

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped Topology
namespace AVRegularity.CycleComparison.Lift

/-! Centered primitives gain one fast derivative and commute with fixed component maps. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem centeredIntervalPrimitive_deriv (f : ℝ → E) (hf : Continuous f) :
    deriv (centeredIntervalPrimitive f) = f := by
  funext r
  exact (centeredIntervalPrimitive_hasDerivAt f hf r).deriv

theorem centeredIntervalPrimitive_contDiff (q : ℕ) (f : ℝ → E)
    (hf : ContDiff ℝ (q : ℕ∞) f) :
    ContDiff ℝ ((q + 1 : ℕ) : ℕ∞) (centeredIntervalPrimitive f) := by
  have hcast : (((q + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) = (q : WithTop ℕ∞) + 1 := by simp
  rw [hcast]
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun r => (centeredIntervalPrimitive_hasDerivAt f hf.continuous r).differentiableAt,
    by simp, ?_⟩
  rw [centeredIntervalPrimitive_deriv f hf.continuous]
  exact hf

theorem intervalPrimitive_continuous (f : ℝ → E) (hf : Continuous f) :
    Continuous (fun r : ℝ => ∫ y in (0 : ℝ)..r, f y) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  exact (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 r)
    (hf.stronglyMeasurableAtFilter volume (𝓝 r)) hf.continuousAt).continuousAt

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem centeredIntervalPrimitive_clm (L : E →L[ℝ] F) (f : ℝ → E)
    (hf : Continuous f) (r : ℝ) :
    centeredIntervalPrimitive (fun y => L (f y)) r = L (centeredIntervalPrimitive f r) := by
  have he (s : ℝ) : (∫ y in (0 : ℝ)..s, L (f y)) = L (∫ y in (0 : ℝ)..s, f y) :=
    L.intervalIntegral_comp_comm (hf.intervalIntegrable 0 s)
  unfold centeredIntervalPrimitive
  simp_rw [he]
  rw [L.intervalIntegral_comp_comm ((intervalPrimitive_continuous f hf).intervalIntegrable 0 1),
    L.map_sub]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Absolute Fourier convergence and its first derivative on the real transverse coordinate. -/

def profileFourierSeries (c : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℤ, fourier n (x : AddCircle (1 : ℝ)) * c n

theorem profileFourierSeries_term_summable (c : ℤ → ℂ) (hc : Summable c) (x : ℝ) :
    Summable (fun n : ℤ => fourier n (x : AddCircle (1 : ℝ)) * c n) := by
  apply hc.norm.of_norm_bounded
  intro n
  simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul, le_refl]

theorem profileFourierSeries_continuous (c : ℤ → ℂ) (hc : Summable c) :
    Continuous (profileFourierSeries c) := by
  apply continuous_tsum (fun n =>
    (((fourier n).continuous.comp (AddCircle.continuous_mk' (1 : ℝ))).mul continuous_const)) hc.norm
  intro n x
  change ‖fourier n (x : AddCircle (1 : ℝ)) * c n‖ ≤ ‖c n‖
  simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul, le_refl]

theorem profileFourierSeries_hasDerivAt (c : ℤ → ℂ) (hc : Summable c)
    (hd : Summable (fun n => profileFourierFrequency n * c n)) (x : ℝ) :
    HasDerivAt (profileFourierSeries c)
      (profileFourierSeries (fun n => profileFourierFrequency n * c n) x) x := by
  apply hasDerivAt_tsum (y₀ := (0 : ℝ)) hd.norm ?_ ?_
    (profileFourierSeries_term_summable c hc 0) x
  · intro n y
    have he := (hasDerivAt_fourier (1 : ℝ) n y).mul_const (c n)
    convert he using 1
    simp only [profileFourierFrequency, Complex.ofReal_one, div_one]
    ring
  · intro n y
    simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul, le_refl]

/-! Two excess Fourier powers make each requested profile jet absolutely summable. -/

theorem profileFourier_jet_summable (c : ℤ → ℂ) (j : ℕ) (M : ℝ)
    (hc : ∀ n : ℤ, n ≠ 0 → ‖profileFourierFrequency n‖ ^ (j + 2) * ‖c n‖ ≤ M) :
    Summable (fun n => profileFourierFrequency n ^ j * c n) := by
  have hp : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  apply (hp.mul_left (M / (4 * Real.pi ^ 2))).of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  have hr : 0 < ‖profileFourierFrequency n‖ := norm_pos_iff.mpr (profileFourierFrequency_ne_zero n hn)
  have he : ‖profileFourierFrequency n‖ ^ 2 *
      (‖profileFourierFrequency n‖ ^ j * ‖c n‖) ≤ M := by
    convert hc n hn using 1
    rw [pow_add]
    ring
  have hd : ‖profileFourierFrequency n‖ ^ j * ‖c n‖ ≤ M / ‖profileFourierFrequency n‖ ^ 2 :=
    (le_div_iff₀ (pow_pos hr 2)).mpr (by simpa only [mul_comm] using he)
  rw [profileFourierFrequency_norm_sq] at hd
  rw [norm_mul, norm_pow]
  apply hd.trans_eq
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Entrywise measurability and integrability of the actual Fourier forcing coefficients. -/

theorem unitProfileFourierCoeff_time_measurable (f : ℝ → ℝ → ℂ)
    (hf : Measurable (Function.uncurry f)) (n : ℤ) :
    Measurable (fun t => unitProfileFourierCoeff (f t) n) := by
  have hmode : Continuous (fun x : ℝ => fourier (-n) (x : AddCircle ((1 : ℝ) - 0))) :=
    (fourier (-n)).continuous.comp (AddCircle.continuous_mk' _)
  have hm : Measurable (fun p : ℝ × ℝ =>
      fourier (-n) (p.2 : AddCircle ((1 : ℝ) - 0)) * f p.1 p.2) :=
    (hmode.measurable.comp measurable_snd).mul hf
  have hi := (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable
  unfold unitProfileFourierCoeff
  simp_rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, div_one, one_smul, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    smul_eq_mul]
  exact hi

theorem unitProfileFourierCoeff_time_intervalIntegrable (f : ℝ → ℝ → ℂ)
    (hf : Measurable (Function.uncurry f)) (a b : ℝ) (C : ℝ)
    (hb : ∀ t ∈ uIcc a b, ∀ x ∈ Icc (0 : ℝ) 1, ‖f t x‖ ≤ C) (n : ℤ) :
    IntervalIntegrable (fun t => unitProfileFourierCoeff (f t) n) volume a b := by
  apply IntegrableOn.intervalIntegrable
  apply Measure.integrableOn_of_bounded isCompact_uIcc.measure_lt_top.ne
    (unitProfileFourierCoeff_time_measurable f hf n).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIcc] with t ht
  exact unitProfileFourierCoeff_norm_le (f t) n C (hb t ht)

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Reserved classical profile jets are measurable in the time parameter and jointly with the coordinate. -/

variable {T : Type*} [MeasurableSpace T]

theorem profile_iteratedDeriv_parameter_measurable (f : T → ℝ → ℂ)
    (hm : ∀ x, Measurable (fun t => f t x)) (q : ℕ)
    (hf : ∀ t, ContDiff ℝ (q : ℕ∞) (f t)) (j : ℕ) (hjq : j ≤ q) (x : ℝ) :
    Measurable (fun t => iteratedDeriv j (f t) x) := by
  induction j generalizing x with
  | zero => simpa using hm x
  | succ j ih =>
    have hmj (y : ℝ) : Measurable (fun t => iteratedDeriv j (f t) y) :=
      ih (by omega) y
    have hd (t : T) : Differentiable ℝ (iteratedDeriv j (f t)) :=
      (hf t).differentiable_iteratedDeriv j (by exact_mod_cast (show j < q by omega))
    simpa only [iteratedDeriv_succ] using
      profile_deriv_parameter_measurable (fun t => iteratedDeriv j (f t)) hmj hd x

theorem profile_iteratedDeriv_joint_measurable (f : T → ℝ → ℂ)
    (hm : ∀ x, Measurable (fun t => f t x)) (q : ℕ)
    (hf : ∀ t, ContDiff ℝ (q : ℕ∞) (f t)) (j : ℕ) (hjq : j ≤ q) :
    Measurable (fun p : T × ℝ => iteratedDeriv j (f p.1) p.2) := by
  have hh : Measurable (fun p : ℝ × T => iteratedDeriv j (f p.2) p.1) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun t => (hf t).continuous_iteratedDeriv j (by exact_mod_cast hjq))
      (fun x => profile_iteratedDeriv_parameter_measurable f hm q hf j hjq x)
  exact hh.comp measurable_swap

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Two excess Fourier powers give one summable majorant valid throughout the time window. -/

def profileJetMajorant (M R : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then R else M / (4 * Real.pi ^ 2) * (1 / (n : ℝ) ^ 2)

theorem profileJetMajorant_summable (M R : ℝ) : Summable (profileJetMajorant M R) := by
  have hs := (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left
    (M / (4 * Real.pi ^ 2))
  apply hs.congr_cofinite
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  simp only [profileJetMajorant, hn, ite_false]

theorem profileJetMajorant_bound {T : Type*} (I : Set T) (c : T → ℤ → ℂ)
    (j : ℕ) (M R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ t ∈ I, ∀ n : ℤ, n ≠ 0 →
      ‖profileFourierFrequency n‖ ^ (j + 2) * ‖c t n‖ ≤ M)
    (hzero : ∀ t ∈ I, ‖c t 0‖ ≤ R) (n : ℤ) (t : T) (ht : t ∈ I) :
    ‖profileFourierFrequency n ^ j * c t n‖ ≤ profileJetMajorant M R n := by
  by_cases hn : n = 0
  · subst n
    cases j with
    | zero => simpa only [pow_zero, one_mul, profileJetMajorant, ite_true] using hzero t ht
    | succ j => simpa [profileFourierFrequency, profileJetMajorant] using hR
  · have hr : 0 < ‖profileFourierFrequency n‖ :=
      norm_pos_iff.mpr (profileFourierFrequency_ne_zero n hn)
    have he : ‖profileFourierFrequency n‖ ^ 2 *
        (‖profileFourierFrequency n‖ ^ j * ‖c t n‖) ≤ M := by
      convert hc t ht n hn using 1
      rw [pow_add]
      ring
    have hd : ‖profileFourierFrequency n‖ ^ j * ‖c t n‖ ≤
        M / ‖profileFourierFrequency n‖ ^ 2 :=
      (le_div_iff₀ (pow_pos hr 2)).mpr (by simpa only [mul_comm] using he)
    rw [profileFourierFrequency_norm_sq] at hd
    rw [norm_mul, norm_pow, profileJetMajorant, ite_eq_right hn]
    apply hd.trans_eq
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
namespace AVRegularity.CycleComparison.Lift

/-! Nonzero unit-period Fourier frequencies dominate the polynomial Wiener weight. -/

theorem profileFourierFrequency_norm (n : ℤ) :
    ‖profileFourierFrequency n‖ = 2 * Real.pi * |(n : ℝ)| := by
  simp [profileFourierFrequency, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]

theorem profile_wiener_weight_le_frequency (L : ℕ) (n : ℤ) (hn : n ≠ 0) :
    (1 + |(n : ℝ)|) ^ L ≤ ‖profileFourierFrequency n‖ ^ L := by
  have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
    have hi : (1 : ℤ) ≤ |n| := abs_pos.mpr hn
    exact_mod_cast hi
  have hpi : (1 : ℝ) ≤ Real.pi := (by norm_num : (1 : ℝ) ≤ 2).trans Real.two_le_pi
  apply pow_le_pow_left₀ (by positivity)
  rw [profileFourierFrequency_norm]
  calc
    1 + |(n : ℝ)| ≤ 2 * |(n : ℝ)| := by linarith
    _ ≤ 2 * Real.pi * |(n : ℝ)| := by
      exact mul_le_mul_of_nonneg_right
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpi (by norm_num : (0 : ℝ) ≤ 2))
        (abs_nonneg _)

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift

/-! The cosine and sine coefficients in the Wiener definition are the real and imaginary parts. -/

theorem cosine_cell_coefficient_eq_re (f : Vec 2 → ℝ) (hf : Continuous f) (k : Fin 2 → ℤ) :
    (∫ z in AVenhance.unitCube,
      Real.cos (2 * Real.pi * ∑ i : Fin 2, (k i : ℝ) * z i) • f z) =
      (smoothFourierCoeff (fun z => (f z : ℂ)) k).re := by
  rw [← integral_unitCell_eq_unitCube]
  have hi : IntegrableOn (fun z => torusCharacter k z * (f z : ℂ)) (unitCell 2) :=
    Calculus.continuous_integrableOn_unitCell
      ((torusCharacter_contDiff k).continuous.mul (Complex.ofRealCLM.continuous.comp hf))
  have hh := integral_re hi
  change (∫ z in unitCell 2, (torusCharacter k z * (f z : ℂ)).re) =
    (∫ z in unitCell 2, torusCharacter k z * (f z : ℂ)).re at hh
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    torusCharacter_re_phase, smul_eq_mul, smoothFourierCoeff] using! hh

theorem sine_cell_coefficient_eq_neg_im (f : Vec 2 → ℝ) (hf : Continuous f) (k : Fin 2 → ℤ) :
    (∫ z in AVenhance.unitCube,
      Real.sin (2 * Real.pi * ∑ i : Fin 2, (k i : ℝ) * z i) • f z) =
      -(smoothFourierCoeff (fun z => (f z : ℂ)) k).im := by
  rw [← integral_unitCell_eq_unitCube]
  have hi : IntegrableOn (fun z => torusCharacter k z * (f z : ℂ)) (unitCell 2) :=
    Calculus.continuous_integrableOn_unitCell
      ((torusCharacter_contDiff k).continuous.mul (Complex.ofRealCLM.continuous.comp hf))
  have hh := integral_im hi
  change (∫ z in unitCell 2, (torusCharacter k z * (f z : ℂ)).im) =
    (∫ z in unitCell 2, torusCharacter k z * (f z : ℂ)).im at hh
  have he : -(∫ z in unitCell 2,
      Real.sin (2 * Real.pi * ∑ i : Fin 2, (k i : ℝ) * z i) * f z) =
      (smoothFourierCoeff (fun z => (f z : ℂ)) k).im := by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      torusCharacter_im_phase, neg_mul, integral_neg, smoothFourierCoeff] using! hh
  simpa only [smul_eq_mul] using neg_eq_iff_eq_neg.mp he

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Slow scale powers survive the exponential chain rule. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_exp_scaled_le (n : ℕ) (u : E → ℝ)
    (hu : ContDiff ℝ (n : ℕ∞) u) (x : E) (lam M : ℝ) (hlam : 0 ≤ lam)
    (hb : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j u x‖ ≤ M * lam ^ j) :
    ‖iteratedFDeriv ℝ n (fun y => Real.exp (u y)) x‖ ≤
      n.factorial * Real.exp (u x) * (max 1 M) ^ n * lam ^ n := by
  have hh := norm_iteratedFDeriv_exp_comp_le n u hu x (lam * max 1 M)
    (fun j hj hjn => (hb j hj hjn).trans (by
      rw [mul_pow, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hlam j)
      exact (le_max_right 1 M).trans (by
        simpa using pow_le_pow_right₀ (le_max_left 1 M) hj)))
  apply hh.trans_eq
  rw [mul_pow]
  ring

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Positive Schur sums are subadditive over any finite collection of entry matrices. -/

section
variable {ι κ : Type*} [Fintype ι]

theorem schurSums_finset_sum_le (π : ι → ℝ) (s : Finset κ) (M : κ → ι → ι → ℝ≥0∞) :
    schurSums π (fun v u => ∑ j ∈ s, M j v u) ≤ ∑ j ∈ s, schurSums π (M j) := by
  unfold schurSums
  refine max_le (iSup_le fun v => ?_) (iSup_le fun u => ?_)
  · calc
      _ = ∑ j ∈ s, ∑ u, ENNReal.ofReal (Real.sqrt (π u / π v)) * M j v u := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum fun j _ => le_max_of_le_left
        (le_iSup (fun v => ∑ u, ENNReal.ofReal (Real.sqrt (π u / π v)) * M j v u) v)
  · calc
      _ = ∑ j ∈ s, ∑ v, ENNReal.ofReal (Real.sqrt (π u / π v)) * M j v u := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum fun j _ => le_max_of_le_right
        (le_iSup (fun u => ∑ v, ENNReal.ofReal (Real.sqrt (π u / π v)) * M j v u) u)
end

/-! Positive Schur algebra. -/

section
variable {ι : Type*} [Fintype ι]

theorem schurSums_entry_mono (π : ι → ℝ) {M M' : ι → ι → ℝ≥0∞}
    (h : ∀ v u, M v u ≤ M' v u) : schurSums π M ≤ schurSums π M' := by
  unfold schurSums
  refine max_le_max (iSup_mono fun v => Finset.sum_le_sum fun u _ => ?_)
    (iSup_mono fun u => Finset.sum_le_sum fun v _ => ?_)
  · exact mul_le_mul' le_rfl (h v u)
  · exact mul_le_mul' le_rfl (h v u)

theorem schurSums_scalar_mul_le (π : ι → ℝ) (C : ℝ≥0∞) (M : ι → ι → ℝ≥0∞) :
    schurSums π (fun v u => C * M v u) ≤ C * schurSums π M := by
  unfold schurSums
  refine max_le ?_ ?_
  · refine iSup_le fun v => ?_
    have he : ∑ u, ENNReal.ofReal (Real.sqrt (π u / π v)) * (C * M v u) =
        C * ∑ u, ENNReal.ofReal (Real.sqrt (π u / π v)) * M v u := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [he]
    exact mul_le_mul_right (le_max_of_le_left (le_iSup (fun v => ∑ u,
      ENNReal.ofReal (Real.sqrt (π u / π v)) * M v u) v)) C
  · refine iSup_le fun u => ?_
    have he : ∑ v, ENNReal.ofReal (Real.sqrt (π u / π v)) * (C * M v u) =
        C * ∑ v, ENNReal.ofReal (Real.sqrt (π u / π v)) * M v u := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [he]
    exact mul_le_mul_right (le_max_of_le_right (le_iSup (fun u => ∑ v,
      ENNReal.ofReal (Real.sqrt (π u / π v)) * M v u) u)) C
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
open Homogenization Set
namespace AVRegularity.CycleComparison.Lift

/-! Exact factorization through the transverse coordinate, without a regularity premise. -/

theorem transverse_coordinate_projection (par : Fin 2) (z : Vec 2) :
    z + (-z par) • basisVec par = (z par.rev) • basisVec par.rev := by
  funext i
  fin_cases par <;> fin_cases i <;> simp [basisVec_apply]

theorem transverse_field_factorization {E : Type*} (par : Fin 2) (S : Set ℝ)
    (f : ℝ → Vec 2 → Vec 2 → E) (hf : IsTransverseOn par S f)
    (t : ℝ) (ht : t ∈ S) (X z : Vec 2) :
    f t X z = f t X ((z par.rev) • basisVec par.rev) := by
  have he := hf t ht X z (-z par)
  rw [transverse_coordinate_projection] at he
  exact he.symm

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Factorization of the finite-past kernel into an endpoint damping and a scalar integrating factor. -/

theorem transverseModeKernel_factor (rate : ℝ) (g : ℝ → ℝ) (a b s : ℝ)
    (hi : IntervalIntegrable g volume a b) (hs : s ∈ uIcc a b) :
    transverseModeKernel rate g s b =
      transverseModeKernel rate g a b * transverseModeKernel (-rate) g a s := by
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hi.mono_set (uIcc_subset_uIcc_left hs)) (hi.mono_set (uIcc_subset_uIcc_right hs))
  unfold transverseModeKernel
  rw [← Real.exp_add, ← he]
  congr 1
  ring

@[simp] theorem transverseModeKernel_opposite_rates (rate : ℝ) (g : ℝ → ℝ) (a b : ℝ) :
    transverseModeKernel rate g a b * transverseModeKernel (-rate) g a b = 1 := by
  unfold transverseModeKernel
  rw [← Real.exp_add]
  simp only [neg_neg, ← add_mul, neg_add_cancel, zero_mul, Real.exp_zero]

end AVRegularity.CycleComparison.Lift
end
end
