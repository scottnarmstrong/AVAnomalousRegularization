-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.WeightedRawProductAlgebra
import AVRegularity.Weighted.PeriodicScalarZeroEnergy
public import AVRegularity.CycleComparison.Residual.FastJets.Sampling
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsSmoothOn
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Integer character modulation agrees exactly in physical and Hilbert coordinates. -/

def integerHilbertFrequency (n : Fin 2 → ℤ) : HilbertTwo :=
  WithLp.toLp 2 (fun i => (n i : ℝ))

theorem integerHilbertFrequency_inner (n : Fin 2 → ℤ) (x : HilbertTwo) :
    inner ℝ x (integerHilbertFrequency n) = vecDot (fun i => (n i : ℝ)) (WithLp.ofLp x) := by
  rw [PiLp.inner_apply]
  simp only [integerHilbertFrequency, PiLp.toLp_apply, Real.inner_apply, vecDot]
  change (∑ i : Fin 2, (WithLp.ofLp x i) * (n i : ℝ)) =
    ∑ i : Fin 2, (n i : ℝ) * (WithLp.ofLp x i)
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem integerHilbertModulationCharacter_eq (n : Fin 2 → ℤ) (x : HilbertTwo) :
    hilbertModulationCharacter (integerHilbertFrequency n) x =
      cellComplexFourierMode n (WithLp.ofLp x) := by
  simp only [hilbertModulationCharacter, Real.fourierChar_apply, cellComplexFourierMode,
    cellComplexFourierPhase, smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, seamDotPairing_apply]
  rw [integerHilbertFrequency_inner]
  push_cast
  congr 1
  ring

theorem coordinate_integerModulation (n : Fin 2 → ℤ)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    coordinateL2Equiv (planeIntegerModulationOperator n f) =
      hilbertCharacterModulationOperator (integerHilbertFrequency n) (coordinateL2Equiv f) := by
  apply Lp.ext
  filter_upwards [coordinateL2Equiv_ae (planeIntegerModulationOperator n f),
    (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving.ae
      (planeIntegerModulationOperator_ae n f),
    hilbertCharacterModulationOperator_ae (integerHilbertFrequency n) (coordinateL2Equiv f),
    coordinateL2Equiv_ae f] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, integerHilbertModulationCharacter_eq]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.FastJets
namespace AVRegularity.CycleWords

/-! Joint regularity of mixed coordinate words with a total derivative reserve. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joint_partialFDeriv_left_contDiff (n : ℕ) (f : Vec 2 × Vec 2 → E)
    (hf : ContDiff ℝ (n + 1 : ℕ) f) :
    ContDiff ℝ (n : ℕ) (fun p : Vec 2 × Vec 2 => fderiv ℝ (fun x => f (x, p.2)) p.1) := by
  let D := fun p => (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2))
  have hD : ContDiff ℝ (n : ℕ) D :=
    (hf.fderiv_right (by norm_cast)).clm_comp contDiff_const
  have he (p : Vec 2 × Vec 2) : fderiv ℝ (fun x => f (x, p.2)) p.1 = D p := by
    rcases p with ⟨x, z⟩
    exact ((hf.differentiable (by norm_cast) (x, z)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) x z)).fderiv
  simpa only [he] using hD

theorem joint_slowPartial_contDiff (n : ℕ) (i : Fin 2) (f : Vec 2 → Vec 2 → E)
    (hf : ContDiff ℝ (n + 1 : ℕ) (Function.uncurry f)) :
    ContDiff ℝ (n : ℕ) (Function.uncurry (slowPartial i f)) :=
  (joint_partialFDeriv_left_contDiff n _ hf).clm_apply contDiff_const

theorem joint_fastPartial_contDiff (n : ℕ) (i : Fin 2) (f : Vec 2 → Vec 2 → E)
    (hf : ContDiff ℝ (n + 1 : ℕ) (Function.uncurry f)) :
    ContDiff ℝ (n : ℕ) (Function.uncurry (fastPartial i f)) :=
  (Weighted.joint_partialFDeriv_right_contDiff n _ hf).clm_apply contDiff_const

theorem joint_slowL_contDiff (n : ℕ) (γ : List (Fin 2)) (f : Vec 2 → Vec 2 → E)
    (hf : ContDiff ℝ (n + γ.length : ℕ) (Function.uncurry f)) :
    ContDiff ℝ (n : ℕ) (Function.uncurry (slowL γ f)) := by
  induction γ generalizing f with
  | nil => simpa using hf
  | cons i γ ih =>
    rw [slowL_cons]
    apply ih
    apply joint_slowPartial_contDiff
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf

theorem joint_fastL_contDiff (n : ℕ) (δ : List (Fin 2)) (f : Vec 2 → Vec 2 → E)
    (hf : ContDiff ℝ (n + δ.length : ℕ) (Function.uncurry f)) :
    ContDiff ℝ (n : ℕ) (Function.uncurry (fastL δ f)) := by
  induction δ generalizing f with
  | nil => simpa using hf
  | cons i δ ih =>
    rw [fastL_cons]
    apply ih
    apply joint_fastPartial_contDiff
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf

theorem joint_mixL_contDiff (n : ℕ) (γ δ : List (Fin 2)) (f : Vec 2 → Vec 2 → E)
    (hf : ContDiff ℝ (n + γ.length + δ.length : ℕ) (Function.uncurry f)) :
    ContDiff ℝ (n : ℕ) (Function.uncurry (mixL γ δ f)) :=
  joint_slowL_contDiff n γ _ (joint_fastL_contDiff (n + γ.length) δ f hf)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! A whole slow-label time slice of the declared domain gives global joint coefficient regularity. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem molecular_joint_contDiff (F : ChartedFamily ι h D P Ctx) (dom : F.Domain)
    (E : ℝ) (hE : E ≠ 0) (N : ι → ℕ) (hs : F.IsSmoothOn dom E N)
    (p : P) (c : Ctx p) (t : ℝ) (ht : ∀ Y : Vec 2, (t, Y) ∈ dom p c)
    (v u : ι) (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) :
    ContDiff ℝ (N v : ℕ) (fun w : Vec 2 × Vec 2 => F.flux p c v u γ d I t w.1 w.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro w
  have hh := hs p c v u γ d I (t, E • w.1) (ht (E • w.1)) w.2
  simpa only [smul_smul, inv_mul_cancel₀ hE, one_smul] using hh

theorem molecular_cell_coefficient_contDiff (F : ChartedFamily ι h D P Ctx) (dom : F.Domain)
    (E : ℝ) (hE : E ≠ 0) (N : ι → ℕ) (hs : F.IsSmoothOn dom E N)
    (p : P) (c : Ctx p) (t : ℝ) (ht : ∀ Y : Vec 2, (t, Y) ∈ dom p c)
    (v u : ι) (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (φ : Vec 2) (k : Fin 2) :
    ContDiff ℝ (N v : ℕ) (fun w : Vec 2 × Vec 2 => F.flux p c v u γ d I t w.1 (w.2 + φ) k) := by
  have hh := (molecular_joint_contDiff F dom E hE N hs p c t ht v u γ d I).comp
    (contDiff_fst.prodMk (contDiff_snd.add (contDiff_const (c := φ))))
  exact (ContinuousLinearMap.proj k).contDiff.comp hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The four kinematic properties of a native finite response error. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  {L : Type*} [Fintype L]

def nativeErrorCurve {K : ℕ} (U : ℝ → PlaneHk Set.univ K E)
    (Z : L → ℝ → PlaneHk Set.univ K E) : ℝ → PlaneHk Set.univ K E :=
  fun t => U t - ∑ j, Z j t

def nativeErrorDatum {K : ℕ} (f : PlaneHk Set.univ K E)
    (fz : L → PlaneHk Set.univ K E) : PlaneHk Set.univ K E := f - ∑ j, fz j

theorem nativeError_kinematics {K : ℕ} (a b : ℝ)
    (f : PlaneHk Set.univ K E) (fz : L → PlaneHk Set.univ K E)
    (U : ℝ → PlaneHk Set.univ K E) (Z : L → ℝ → PlaneHk Set.univ K E)
    (Uw : ℝ → PlaneHk Set.univ (K + 1) E) (Zw : L → ℝ → PlaneHk Set.univ (K + 1) E)
    (hc : ContinuousOn U (Set.Icc a b)) (hzc : ∀ j, ContinuousOn (Z j) (Set.Icc a b))
    (hm : MemLp Uw 2 (volume.restrict (Set.Icc a b)))
    (hzm : ∀ j, MemLp (Zw j) 2 (volume.restrict (Set.Icc a b)))
    (hr : ∀ᵐ t ∂volume.restrict (Set.Icc a b), truncatePlaneHk (Nat.le_succ K) (Uw t) = U t)
    (hzr : ∀ j, ∀ᵐ t ∂volume.restrict (Set.Icc a b), truncatePlaneHk (Nat.le_succ K) (Zw j t) = Z j t)
    (hi : U a = f) (hzi : ∀ j, Z j a = fz j) :
    ContinuousOn (fun t => U t - ∑ j, Z j t) (Set.Icc a b) ∧
    MemLp (fun t => Uw t - ∑ j, Zw j t) 2 (volume.restrict (Set.Icc a b)) ∧
    (∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncatePlaneHk (Nat.le_succ K) (Uw t - ∑ j, Zw j t) = U t - ∑ j, Z j t) ∧
    U a - ∑ j, Z j a = f - ∑ j, fz j := by
  classical
  refine ⟨hc.sub (continuousOn_finsetSum Finset.univ (fun j _ => hzc j)),
    nativeTime_sub_sum_memLp _ Uw Zw hm hzm, ?_, native_sub_sum_congr _ _ _ _ hi hzi⟩
  filter_upwards [hr, ae_all_iff.mpr hzr] with t ht hzt
  exact truncatePlaneHk_sub_sum_eq (Uw t) (fun j => Zw j t) (U t) (fun j => Z j t) ht hzt

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! A normalized coefficient derivative consumes no radius from its Sobolev factor. -/

theorem normalizedProduct_square_budget (l r : ℕ) {ρ A q a u : ℝ}
    (hρ : 0 ≤ ρ) (ha : 0 ≤ a)
    (hb : ρ ^ l * a ≤ A * q * u) :
    factorialWeight ρ (l + r) * a ^ 2 ≤
      A ^ 2 * q ^ 2 * (factorialWeight ρ r * u ^ 2) := by
  have hs := pow_le_pow_left₀ (mul_nonneg (pow_nonneg hρ l) ha) hb 2
  calc
    _ ≤ ((ρ ^ l) ^ 2 * factorialWeight ρ r) * a ^ 2 :=
      mul_le_mul_of_nonneg_right (factorialWeight_product_le hρ l r) (sq_nonneg a)
    _ = factorialWeight ρ r * (ρ ^ l * a) ^ 2 := by ring
    _ ≤ factorialWeight ρ r * (A * q * u) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (factorialWeight_nonneg _ _)
    _ = _ := by ring

end AVRegularity.CycleWords
end
end
