-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.QuietMean.EpsPoly
import AVRegularity.CycleComparison.Lift.TruncatedMeanCoefficientRegularity
import AVRegularity.CycleComparison.Lift.SecondCrossMean
public import AVRegularity.CycleComparison.Lift.TransverseModeKernel
import AVRegularity.CycleComparison.Lift.LiftApplyFiniteVectorSynthesis
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom
import AVRegularity.CycleEvolution.CellComplexH1Carrier
public import AVRegularity.CycleEvolution.CellConjugateClass

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! A weighted cell mean of an actual lift acts through its weighted operator coefficients. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem weighted_lift_component_mean_action (n : ℕ) (c : LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (X : Vec 2) (v : ι)
    (w : Vec 2 → ℝ) (hw : Continuous w)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u,
      Continuous (fun z => c m α t X z v u)) :
    fieldCellMean (fun z => w z • liftApply n c f t X z v) =
      ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m, ∑ u,
        (fieldCellMean (fun z => w z • c m α t X z v u))
          (orderedDerivative α (f t) X u) := by
  let T := fun m (α : DerivativeWord2 m) (u : ι) z =>
    w z • c m α t X z v u (orderedDerivative α (f t) X u)
  have hT m (hm : m ≤ n) α u : Continuous (T m α u) :=
    hw.smul ((ContinuousLinearMap.apply ℝ (h v) (orderedDerivative α (f t) X u)).continuous.comp
      (hc m hm α u))
  have hsum m (hm : m ≤ n) α : Continuous (fun z => ∑ u, T m α u z) :=
    continuous_finsetSum _ (fun u _ => hT m hm α u)
  simp only [liftApply, Finset.smul_sum]
  rw [AVRegularity.fieldCellMean_sum (Finset.range (n + 1))
    (fun m hm => continuous_finsetSum _ (fun α _ => hsum m
      (by have hh := Finset.mem_range.mp hm; omega) α))]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := by have hh := Finset.mem_range.mp hm; omega
  rw [AVRegularity.fieldCellMean_sum Finset.univ (fun α _ => hsum m hmn α)]
  apply Finset.sum_congr rfl
  intro α _
  rw [AVRegularity.fieldCellMean_sum Finset.univ (fun u _ => hT m hmn α u)]
  apply Finset.sum_congr rfl
  intro u _
  change (∫ z in AVenhance.unitCube,
    (w z • c m α t X z v u) (orderedDerivative α (f t) X u)) = _
  exact (ContinuousLinearMap.integral_apply
    (AVRegularity.integrableOn_unitCube
      (hw.smul (hc m hmn α u))) (orderedDerivative α (f t) X u)).symm

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Uniform estimates on the actual fast cell control the literal cell slow-jet norm. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance cellL2JetUnitBoundProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using AVRegularity.CycleEvolution.cellCube_volume_one⟩

omit [NormedSpace ℝ E] in
theorem cellL2Norm_le_unit_bound (f : Vec 2 → E) (hf : Continuous f)
    (B : ℝ) (hb : ∀ z ∈ AVenhance.unitCube, ‖f z‖ ≤ B) :
    cellL2Norm f ≤ ENNReal.ofReal B := by
  have hcube : MeasurableSet AVenhance.unitCube := by
    exact (measurableSet_pi Set.countable_univ).2 (Or.inl (fun _ _ => measurableSet_Ioo))
  have ha : ∀ᵐ z ∂volume.restrict AVenhance.unitCube, ‖f z‖ ≤ B :=
    (ae_restrict_mem hcube).mono (fun z hz => hb z hz)
  have hi := eLpNorm_le_of_ae_bound (p := (2 : ENNReal))
    (hf.aestronglyMeasurable : AEStronglyMeasurable f (volume.restrict AVenhance.unitCube)) ha
  simpa only [measure_univ, ENNReal.one_rpow, one_mul, cellL2Norm] using hi

theorem cellL2Jet_le_unit_bound (I : Set ℝ) (j : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → E) (B : ℝ)
    (hc : ∀ t ∈ I, ∀ X,
      Continuous (fun z => iteratedFDeriv ℝ j (fun Y => f t Y z) X))
    (hb : ∀ t ∈ I, ∀ X, ∀ z ∈ AVenhance.unitCube,
      ‖iteratedFDeriv ℝ j (fun Y => f t Y z) X‖ ≤ B) :
    cellL2Jet I j f ≤ ENNReal.ofReal B := by
  unfold cellL2Jet
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  apply iSup_le
  intro X
  exact cellL2Norm_le_unit_bound _ (hc t ht X) B (hb t ht X)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Cell mean projection and fast continuity are proved once for plain finite vectors. -/

section
theorem good_field_fast_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ) (f : Vec 2 → Vec 2 → E) (hf : GoodField r f) (X : Vec 2) :
    Continuous (f X) :=
  hf.1.continuous.comp (continuous_const.prodMk continuous_id)


variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, CompleteSpace (h i)]

theorem fieldCellMean_pi_apply (f : Vec 2 → ∀ i, h i) (hf : Continuous f) (v : ι) :
    fieldCellMean (fun z => f z v) = fieldCellMean f v :=
  AVRegularity.fieldCellMean_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) hf
end

/-! Covariant differentiation is linear on finite smooth field sums. -/

section
variable {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem goodField_dEps {r : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : GoodField (r + 1) f) (η ε : ℝ) (i : Fin 2) :
    GoodField r (dEps η ε i f) :=
  (hf.fastPartial i).add ((hf.slowPartial i).smul (Real.sqrt η * ε))

theorem dEps_finset_sum_smul (s : Finset α) (c : α → ℝ)
    (f : α → Vec 2 → Vec 2 → E) (hf : ∀ a ∈ s, GoodField 1 (f a))
    (η ε : ℝ) (i : Fin 2) :
    dEps η ε i (fun X z => ∑ a ∈ s, c a • f a X z) =
      fun X z => ∑ a ∈ s, c a • dEps η ε i (f a) X z := by
  funext X z
  simp only [dEps]
  rw [fastPartial_sum_smul s c f hf, slowPartial_sum_smul s c f hf]
  simp only [Finset.smul_sum, smul_add, Finset.sum_add_distrib, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  ring
end

/-! Fast divergences average to zero; the covariant mean is exactly its slow divergence. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem fieldCellMean_dEps (η ε : ℝ) (q : Fin 2)
    (Φ : Vec 2 → Vec 2 → E) (hΦ : GoodField 1 Φ) (X : Vec 2) :
    fieldCellMean (fun z => dEps η ε q Φ X z) =
      (Real.sqrt η * ε) • fderiv ℝ (fun Y => fieldCellMean (Φ Y)) X (basisVec q) := by
  have hf := hΦ.cent_fastPartial (c := True) (r := 0) q
  have hs := hΦ.slowPartial (r := 0) q
  change fieldCellMean (fun z => fastPartial q Φ X z +
    (Real.sqrt η * ε) • slowPartial q Φ X z) = _
  have hc : Continuous (fun z => (Real.sqrt η * ε) • slowPartial q Φ X z) := by
    simpa using! continuous_const.smul (hs.continuous_slice X)
  rw [AVRegularity.fieldCellMean_add (hf.1.continuous_slice X) hc,
    hf.2 trivial X, zero_add,
    AVRegularity.fieldCellMean_smul, AVRegularity.fieldCellMean_slowPartial hΦ.1 X q]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Nonzero constituent maps have finite reserved coefficient jets; zero maps contribute nothing. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem scaledEnvelope_constituent_jet_finite (π : ι → ℝ) (edge : ConstituentEdges D h)
    (I : Set ℝ) (lam : ℝ) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ)
    (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (v u : ι) (hv : 0 < π v) (hu : 0 < π u)
    (d : Finset.Icc 2 D) (γ : Constituent d.val (h u) (h v))
    (hγ : γ ∈ edge v u d) (hmap : γ.map ≠ 0) (α : DerivativeWord2 (d.val - 1))
    (r q : ℕ) (hr : r ≤ qs) (hq : q ≤ qf) : jetSup I r q (γ.coeff α) < ⊤ := by
  have hmass : ENNReal.ofReal (Real.sqrt (π u / π v)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (div_pos hu hv)))
  have hnorm : ENNReal.ofReal ‖γ.map‖ ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hmap))
  have hb := scaledEnvelope_constituent_jet_le π edge I lam Cj qs qf b Θ he
    v u d γ hγ α r q hr hq
  by_contra hn
  have htop : jetSup I r q (γ.coeff α) = ⊤ := eq_top_iff.mpr (not_lt.mp hn)
  rw [htop, ENNReal.mul_top hnorm, ENNReal.mul_top hmass] at hb
  exact (not_le_of_gt ENNReal.ofReal_lt_top) hb

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Finite sums preserve literal centered cell fields. -/

variable {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fieldCellMean_finset_sum_zero (s : Finset α) (f : α → Vec 2 → E)
    (hc : ∀ a ∈ s, Continuous (f a)) (hm : ∀ a ∈ s, fieldCellMean (f a) = 0) :
    fieldCellMean (fun z => ∑ a ∈ s, f a z) = 0 := by
  simpa only [one_smul] using fieldCellMean_finset_sum_smul_zero s (fun _ => 1) f hc hm

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The finite coefficient synthesis identity applies to a finite set of coarse inputs. -/

section
variable {J ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_input_finset_synthesis (S : Finset J) (n : ℕ) (c : LiftCoeff ι h)
    (w : J → ℝ) (f : J → Vec 2 → ∀ i, h i)
    (hf : ∀ j ∈ S, ContDiff ℝ (n : ℕ∞) (f j)) (t : ℝ) (X z : Vec 2) :
    liftApply n c (fun _ Y => ∑ j ∈ S, w j • f j Y) t X z =
      ∑ j ∈ S, w j • liftApply n c (fun _ => f j) t X z := by
  classical
  have he := liftApply_input_finite_synthesis n c (fun j : S => w j.val)
    (fun j : S => f j.val) (fun j => hf j.val j.property) t X z
  have hfield : (fun Y => ∑ j : S, w j.val • f j.val Y) =
      fun Y => ∑ j ∈ S, w j • f j Y := by
    funext Y
    exact Finset.sum_coe_sort S (fun j => w j • f j Y)
  have hout : (∑ j : S, w j.val • liftApply n c (fun _ => f j.val) t X z) =
      ∑ j ∈ S, w j • liftApply n c (fun _ => f j) t X z :=
    Finset.sum_coe_sort S (fun j => w j • liftApply n c (fun _ => f j) t X z)
  rw [hfield, hout] at he
  exact he
end

/-! Cell averaging of block coefficients commutes with their literal coarse action. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def liftCoefficientCellMean (c : LiftCoeff ι h) : LiftCoeff ι h :=
  fun m α t X _ v u => fieldCellMean (fun z => c m α t X z v u)

omit [Fintype ι] in
theorem liftCoefficientCellMean_perm (c : LiftCoeff ι h) (m : ℕ)
    (hc : ∀ α (σ : Equiv.Perm (Fin m)), c m (α ∘ σ) = c m α)
    (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    liftCoefficientCellMean c m (α ∘ σ) = liftCoefficientCellMean c m α := by
  unfold liftCoefficientCellMean
  rw [hc]

theorem liftCoefficientCellMean_apply (n : ℕ) (c : LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (X z : Vec 2) (v : ι)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u,
      Continuous (fun z => c m α t X z v u)) :
    liftApply n (liftCoefficientCellMean c) f t X z v =
      fieldCellMean (fun z => liftApply n c f t X z v) := by
  have he := weighted_lift_component_mean_action n c f t X v (fun _ => 1) continuous_const hc
  simpa only [one_smul, liftApply, liftCoefficientCellMean] using he.symm
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Taking real parts of full mixed jets costs at most one. -/

theorem norm_mixed_jet_realPart_le (p q r j : ℕ) (hr : r ≤ p) (hj : j ≤ q)
    (f : Vec 2 → Vec 2 → ℂ) (hf : IsBoxSmooth p q f) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (fun y => (f Y y).re) z) X‖ ≤
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f Y) z) X‖ := by
  have hh := norm_mixed_jet_postcomposition_le p q r j hr hj f hf.1 (hf.2.1 j hj)
    Complex.reCLM X z
  exact hh.trans (mul_le_of_le_one_left (norm_nonneg _) complex_reCLM_norm_le_one)

/-! Applying operator coefficients to a fixed vector costs exactly its norm majorant. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_mixed_operator_apply_le (p q : ℕ) (f : Vec 2 → Vec 2 → (E →L[ℝ] F))
    (hf : IsBoxSmooth p q f) (ξ : E) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (fun y => f Y y ξ) z) X‖ ≤
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖ * ‖ξ‖ := by
  let L : (E →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F ξ
  have hL : ‖L‖ ≤ ‖ξ‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg ξ)
    intro T
    simpa only [L, ContinuousLinearMap.apply_apply, mul_comm] using! T.le_opNorm ξ
  have hh := norm_mixed_jet_postcomposition_le p q p q le_rfl le_rfl f hf.1
    (hf.2.1 q le_rfl) L X z
  simpa only [L, ContinuousLinearMap.apply_apply, mul_comm] using! hh.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory
open scoped ComplexConjugate
namespace AVRegularity.CycleComparison.Lift

/-! Conjugate symmetry of the literal Fourier coefficients of real profiles. -/

theorem fourierCoeff_conj_unit (f : AddCircle (1 : ℝ) → ℂ) (n : ℤ) :
    fourierCoeff (fun x => conj (f x)) n = conj (fourierCoeff f (-n)) := by
  unfold fourierCoeff
  rw [neg_neg, ← integral_conj]
  simp only [smul_eq_mul, map_mul, fourier_neg]

theorem unitProfileFourierCoeff_conj (f : ℝ → ℂ) (hp : Function.Periodic f 1) (n : ℤ) :
    unitProfileFourierCoeff (fun x => conj (f x)) n = conj (unitProfileFourierCoeff f (-n)) := by
  let hpc : Function.Periodic (fun x => conj (f x)) 1 := fun x => congrArg conj (hp x)
  rw [unitProfileFourierCoeff_eq_lift_coeff _ hpc, unitProfileFourierCoeff_eq_lift_coeff f hp]
  have he : hpc.lift = fun x => conj (hp.lift x) := by
    funext x
    induction x using Quotient.inductionOn with
    | h y => simp only [Function.Periodic.lift_coe]
  rw [he]
  exact fourierCoeff_conj_unit hp.lift n

theorem unitProfileFourierCoeff_neg_of_real (f : ℝ → ℂ) (hp : Function.Periodic f 1)
    (hreal : ∀ x, conj (f x) = f x) (n : ℤ) :
    unitProfileFourierCoeff f (-n) = conj (unitProfileFourierCoeff f n) := by
  have hh := unitProfileFourierCoeff_conj f hp (-n)
  simp_rw [hreal, neg_neg] at hh
  exact hh

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Weighted block means give the actual drift flux coefficient array. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def weightedLiftCoefficientMean (c : LiftCoeff ι h) (w : ℝ → Vec 2 → ℝ) : LiftCoeff ι h :=
  fun m α t X _ v u => fieldCellMean (fun z => w t z • c m α t X z v u)

omit [Fintype ι] in
theorem weightedLiftCoefficientMean_perm (c : LiftCoeff ι h) (w : ℝ → Vec 2 → ℝ) (m : ℕ)
    (hc : ∀ α (σ : Equiv.Perm (Fin m)), c m (α ∘ σ) = c m α)
    (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    weightedLiftCoefficientMean c w m (α ∘ σ) = weightedLiftCoefficientMean c w m α := by
  unfold weightedLiftCoefficientMean
  rw [hc]

theorem weightedLiftCoefficientMean_apply (n : ℕ) (c : LiftCoeff ι h)
    (w : ℝ → Vec 2 → ℝ) (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (X z : Vec 2) (v : ι) (hw : Continuous (w t))
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u,
      Continuous (fun z => c m α t X z v u)) :
    liftApply n (weightedLiftCoefficientMean c w) f t X z v =
      fieldCellMean (fun z => w t z • liftApply n c f t X z v) :=
  (weighted_lift_component_mean_action n c f t X v (w t) hw hc).symm

omit [Fintype ι] in
theorem weightedLiftCoefficientMean_zero_order (c : LiftCoeff ι h) (w : ℝ → Vec 2 → ℝ)
    (α : DerivativeWord2 0) (t : ℝ) (X z : Vec 2) (v u : ι)
    (hc : ∀ y, c 0 α t X y v u = 0) :
    weightedLiftCoefficientMean c w 0 α t X z v u = 0 := by
  simp only [weightedLiftCoefficientMean, hc, smul_zero, fieldCellMean, MeasureTheory.integral_zero]
end

/-! Centered left coefficients annihilate the fast mean of every tested coarse field. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_component_mean_zero_of_centered_coefficients
    (n : ℕ) (c : LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (t : ℝ) (X : Vec 2) (v : ι)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u,
      Continuous (fun z => c m α t X z v u))
    (hm : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u, ∀ ξ : h u,
      fieldCellMean (fun z => c m α t X z v u ξ) = 0) :
    fieldCellMean (fun z => liftApply n c f t X z v) = 0 := by
  let T := fun m (α : DerivativeWord2 m) (u : ι) z =>
    c m α t X z v u (orderedDerivative α (f t) X u)
  have hT m (hmn : m ≤ n) α u : Continuous (T m α u) :=
    (ContinuousLinearMap.apply ℝ (h v) (orderedDerivative α (f t) X u)).continuous.comp
      (hc m hmn α u)
  have hsum m (hmn : m ≤ n) α : Continuous (fun z => ∑ u, T m α u z) :=
    continuous_finsetSum _ (fun u _ => hT m hmn α u)
  simp only [liftApply]
  apply fieldCellMean_finset_sum_zero (Finset.range (n + 1))
  · intro m hmn
    exact continuous_finsetSum _ (fun α _ => hsum m (by have hh := Finset.mem_range.mp hmn; omega) α)
  · intro m hmn
    have hmn' : m ≤ n := by have hh := Finset.mem_range.mp hmn; omega
    apply fieldCellMean_finset_sum_zero Finset.univ
    · intro α _
      exact hsum m hmn' α
    · intro α _
      apply fieldCellMean_finset_sum_zero Finset.univ
      · intro u _
        exact hT m hmn' α u
      · intro u _
        exact hm m hmn' α u _
end

/-! Ordered coefficient/input differences preserve the multiplication order of the literal lift action. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_paired_difference (n : ℕ) (c ci : LiftCoeff ι h)
    (a ai : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (ha : ContDiff ℝ (n : ℕ∞) (a t)) (hai : ContDiff ℝ (n : ℕ∞) (ai t))
    (X z : Vec 2) (v : ι) :
    liftApply n c a t X z v - liftApply n ci ai t X z v =
      liftApply n (fun m α s Y y i j => c m α s Y y i j - ci m α s Y y i j) a t X z v +
        liftApply n ci (fun s Y => a s Y - ai s Y) t X z v := by
  have hc := congrArg (fun F => F t X z v) (liftApply_coefficient_sub n c ci a)
  have hi := congrArg (fun F => F X z v) (liftApply_input_sub_at_time n ci a ai t ha hai)
  rw [hc, hi]
  simp only [Pi.sub_apply]
  abel
end

/-! Weighted coefficient means commute with subtraction of genuine continuous entries. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

omit [Fintype ι] in
theorem weightedLiftCoefficientMean_sub (c d : LiftCoeff ι h)
    (w : ℝ → Vec 2 → ℝ) (m : ℕ) (α : DerivativeWord2 m)
    (t : ℝ) (X z : Vec 2) (v u : ι)
    (hw : Continuous (w t))
    (hc : Continuous (fun y => c m α t X y v u))
    (hd : Continuous (fun y => d m α t X y v u)) :
    weightedLiftCoefficientMean (fun n β s Y y i j => c n β s Y y i j - d n β s Y y i j)
      w m α t X z v u =
      weightedLiftCoefficientMean c w m α t X z v u - weightedLiftCoefficientMean d w m α t X z v u := by
  unfold weightedLiftCoefficientMean
  simp_rw [smul_sub]
  exact fieldCellMean_sub (hw.smul hc) (hw.smul hd)
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The actual cross operators preserve the common transverse source profile class. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellB1_transverse (par : Fin 2) (I : Set ℝ) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (Φ : ℝ → Vec 2 → Vec 2 → E) (hΦ : IsTransverseOn par I Φ)
    (hv : IsTransverseOn par I (fun t (_ : Vec 2) z => v t z)) :
    IsTransverseOn par I (fun t => cellB1 η G v t (Φ t)) := by
  have hslow (k : Fin 2) := transverse_slowPartial par k I Φ hΦ
  have hfast (k : Fin 2) := transverse_fastPartial par k I Φ hΦ
  have hfastslow (i j : Fin 2) := transverse_fastPartial par i I
    (fun t => slowPartial j (Φ t)) (hslow j)
  have hgp (i j : Fin 2) : IsTransverseOn par I
      (fun t X z => G t X i j • fastPartial j (Φ t) X z) :=
    transverse_bilinear par I (fun t X (_ : Vec 2) => G t X i j)
      (fun t => fastPartial j (Φ t)) (transverse_slow_field par I _) (hfast j) (fun a b => a • b)
  have hgps (i j : Fin 2) := transverse_slowPartial par i I _ (hgp i j)
  intro t ht X z s
  change (∑ k : Fin 2, (Real.sqrt η * v t (z + s • basisVec par) k) •
      slowPartial k (Φ t) X (z + s • basisVec par)) -
    Real.sqrt η • ∑ i : Fin 2, ∑ j : Fin 2,
      (G t X i j • fastPartial i (slowPartial j (Φ t)) X (z + s • basisVec par) +
        slowPartial i (fun Y y => G t Y i j • fastPartial j (Φ t) Y y) X (z + s • basisVec par)) = _
  have hvEq : v t (z + s • basisVec par) = v t z := hv t ht X z s
  rw [hvEq]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun x => (Real.sqrt η * v t z k) • x) (hslow k t ht X z s)
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg₂ (fun a b => G t X i j • a + b)
      (hfastslow i j t ht X z s) (hgps i j t ht X z s)

theorem cellB2_transverse (par : Fin 2) (I : Set ℝ) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (Φ : ℝ → Vec 2 → Vec 2 → E) (hΦ : IsTransverseOn par I Φ) :
    IsTransverseOn par I (fun t => cellB2 η G t (Φ t)) := by
  have hprod (i j : Fin 2) : IsTransverseOn par I
      (fun t X z => G t X i j • slowPartial j (Φ t) X z) :=
    transverse_bilinear par I (fun t X (_ : Vec 2) => G t X i j)
      (fun t => slowPartial j (Φ t)) (transverse_slow_field par I _)
      (transverse_slowPartial par j I Φ hΦ) (fun a b => a • b)
  have hpartial (i j : Fin 2) := transverse_slowPartial par i I _ (hprod i j)
  have hsum := transverse_finset_sum Finset.univ par I
    (fun i t X z => ∑ j : Fin 2,
      slowPartial i (fun Y y => G t Y i j • slowPartial j (Φ t) Y y) X z)
    (fun i _ => transverse_finset_sum Finset.univ par I _ (fun j _ => hpartial i j))
  exact transverse_comp par I _ hsum (fun x => -(η • x))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift

/-! A surviving transverse cell Fourier coefficient equals its literal profile coefficient. -/

theorem smoothFourierCoeff_transverse_profile (par : Fin 2) (f : ℝ → ℂ)
    (hf : Continuous f) (hp : Function.Periodic f 1)
    (k : Fin 2 → ℤ) (hk : k par = 0) :
    smoothFourierCoeff (fun z : Vec 2 => f (z par.rev)) k =
      unitProfileFourierCoeff f (k par.rev) := by
  unfold smoothFourierCoeff
  rw [integral_unitCell_eq_unitCube]
  have he : (fun z : Vec 2 => torusCharacter k z * f (z par.rev)) =
      fun z => (fourier (-(k par.rev)) (z par.rev : AddCircle (1 : ℝ))) * f (z par.rev) := by
    funext z
    rw [torusCharacter_eq_transverse_fourier par k hk z]
  rw [he]
  have hc := integral_coordinate_eq_intervalIntegral par.rev
    (fun s => fourier (-(k par.rev)) (s : AddCircle (1 : ℝ)) * f s)
    (((fourier (-(k par.rev))).continuous.comp (AddCircle.continuous_mk' (1 : ℝ))).mul hf)
  trans ∫ s in (0 : ℝ)..1, fourier (-(k par.rev)) (s : AddCircle (1 : ℝ)) * f s
  · exact hc
  · rw [unitProfileFourierCoeff_eq_lift_coeff f hp,
      fourierCoeff_eq_intervalIntegral _ _ (0 : ℝ)]
    simp only [one_div, inv_one, one_smul, zero_add, smul_eq_mul, Function.Periodic.lift_coe]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Box-smooth fields with unit-cell slow-jet bounds control the literal cell norm. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellL2Jet_le_box_unit_bound (I : Set ℝ) (p q j : ℕ) (hj : j ≤ p)
    (f : ℝ → Vec 2 → Vec 2 → E) (B : ℝ)
    (hf : ∀ t ∈ I, IsBoxSmooth p q (f t))
    (hb : ∀ t ∈ I, ∀ X, ∀ z ∈ AVenhance.unitCube,
      ‖iteratedFDeriv ℝ j (fun Y => f t Y z) X‖ ≤ B) :
    cellL2Jet I j f ≤ ENNReal.ofReal B := by
  apply cellL2Jet_le_unit_bound I j f B
  · intro t ht X
    exact (boxSmooth_slow_jet_continuous (hf t ht) j hj).comp
      (continuous_const.prodMk continuous_id)
  · exact hb

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Earlier centered coefficient fields alone center the literal recurrence source; no completed sequence is assumed. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftCellSource_component_mean_zero_of_predecessors (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (X : Vec 2) (v : ι)
    (hcoef : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      ∀ m ≤ j, ∀ α : DerivativeWord2 m, ∀ u,
        Continuous (fun z => Cc p.1 j m α t X z v u) ∧
        ∀ ξ : h u, fieldCellMean (fun z => Cc p.1 j m α t X z v u ξ) = 0)
    (hA : Continuous (fun z => liftA Q Cc f hh n t X z)) :
    fieldCellMean (fun z => liftCellSource Q Cc f hh n t X z v) = 0 := by
  let T := fun j (p : ℕ × ℕ) z =>
    liftApply j (Cc p.1 j) (liftMean Q Cc f p.2 (n - j)) t X z v
  have hT j (hj : j ∈ Finset.Icc 1 (n - 2)) p (hp : p ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      Continuous (T j p) := by
    apply liftApply_component_fast_continuous
    intro m hm α u
    exact (hcoef j hj p hp m hm α u).1
  have hmT j (hj : j ∈ Finset.Icc 1 (n - 2)) p (hp : p ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      fieldCellMean (T j p) = 0 := by
    apply liftApply_component_mean_zero_of_centered_coefficients j (Cc p.1 j) _ t X v
    · intro m hm α u
      exact (hcoef j hj p hp m hm α u).1
    · intro m hm α u ξ
      exact (hcoef j hj p hp m hm α u).2 ξ
  have hsum j (hj : j ∈ Finset.Icc 1 (n - 2)) :
      Continuous (fun z => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, T j p z) :=
    continuous_finsetSum _ (fun p hp => hT j hj p hp)
  have hcorr : Continuous (fun z => ∑ j ∈ Finset.Icc 1 (n - 2),
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, T j p z) :=
    continuous_finsetSum _ hsum
  have hmcorr : fieldCellMean (fun z => ∑ j ∈ Finset.Icc 1 (n - 2),
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, T j p z) = 0 := by
    apply fieldCellMean_finset_sum_zero _ _ hsum
    intro j hj
    exact fieldCellMean_finset_sum_zero _ _ (hT j hj) (hmT j hj)
  have hAc : Continuous (fun z => liftA Q Cc f hh n t X z v) :=
    (continuous_apply v).comp hA
  have hmA := AVRegularity.fieldCellMean_clm
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) hA
  change fieldCellMean (fun z => liftA Q Cc f hh n t X z v) = liftMean Q Cc f hh n t X v at hmA
  simp only [liftCellSource, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Finset.sum_apply]
  change fieldCellMean (fun z => -(liftA Q Cc f hh n t X z v - liftMean Q Cc f hh n t X v) +
    ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, T j p z) = 0
  rw [AVRegularity.fieldCellMean_add
      (f := fun z => -(liftA Q Cc f hh n t X z v - liftMean Q Cc f hh n t X v))
      (g := fun z => ∑ j ∈ Finset.Icc 1 (n - 2),
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, T j p z)
      (hAc.sub (continuous_const : Continuous (fun _ : Vec 2 => liftMean Q Cc f hh n t X v))).neg hcorr,
    AVRegularity.fieldCellMean_neg, AVRegularity.fieldCellMean_sub
      (f := fun z => liftA Q Cc f hh n t X z v)
      (g := fun _ => liftMean Q Cc f hh n t X v) hAc continuous_const,
    AVRegularity.fieldCellMean_const, hmA, hmcorr]
  simp only [sub_self, neg_zero, add_zero]

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The prescribed zero-mean shear gives zero first diagonal cross mean. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)


include P in
theorem setting_drift_mean_zero (t : ℝ) (ht : t ∈ Set.Icc a b) (q : Fin 2) :
    (∫ z in AVenhance.unitCube, Q.v t z q) = 0 := by
  have he : (fun z => Q.v t z q) = fun z => V t (z par.rev) * basisVec par q := by
    funext z
    rw [P.v_shear t z]
    rfl
  rw [he, integral_mul_const, integral_coordinate_mean_zero par.rev (V t)
    (P.V_smooth t ht).continuous (P.V_mean t ht), zero_mul]

include P in
theorem setting_first_cross_mean {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (f : Vec 2 → F) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    fieldCellMean (fun z => cellB1 Q.η Q.G Q.v t (fun X _ => f X) X z) = 0 :=
  fieldCellMean_cellB1_independent Q.η Q.G Q.v t (setting_drift_continuous P t ht)
    (setting_drift_mean_zero P t ht) f X

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! Absolutely bounded Fourier weak Hilbert curves can be summed on the actual finite time window. -/

theorem cellWeakHilbert_series {J : Type*} [Countable J] (a b : ℝ)
    (u : J → ℝ → ComplexCellL2) (w g : J → ℝ → TorusHk 1 ℂ)
    (h : ∀ j, CellWeakHilbertCurve a b (u j) (w j) (g j))
    (Bu Bw Bg : J → ℝ) (hu : Summable Bu) (hw : Summable Bw) (hg : Summable Bg)
    (hBu : ∀ j t, t ∈ Icc a b → ‖u j t‖ ≤ Bu j)
    (hBw : ∀ j t, t ∈ Icc a b → ‖w j t‖ ≤ Bw j)
    (hBg : ∀ j t, t ∈ Icc a b → ‖g j t‖ ≤ Bg j) :
    CellWeakHilbertCurve a b (fun t => ∑' j, u j t)
      (fun t => ∑' j, w j t) (fun t => ∑' j, g j t) := by
  let : MeasurableSpace (TorusHk 1 ℂ) := borel _
  let : BorelSpace (TorusHk 1 ℂ) := ⟨rfl⟩
  let : TopologicalSpace.SeparableSpace (TorusHk 1 ℂ) :=
    AVRegularity.CoupledEnergy.Variational.torusHkSeparableSpace 1
  have hus t ht : Summable (fun j => u j t) := hu.of_norm_bounded (fun j => hBu j t ht)
  have hws t ht : Summable (fun j => w j t) := hw.of_norm_bounded (fun j => hBw j t ht)
  have hgs t ht : Summable (fun j => g j t) := hg.of_norm_bounded (fun j => hBg j t ht)
  refine ⟨boundedTimeSeries_continuousOn u Bu hu a b (fun j => (h j).trace) hBu,
    boundedTimeSeries_memLp w Bw hw a b (fun j => (h j).state.aestronglyMeasurable) hBw,
    boundedTimeSeries_memLp g Bg hg a b (fun j => (h j).dual.aestronglyMeasurable) hBg, ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr (fun j => (h j).agrees), ae_restrict_mem measurableSet_Icc] with t ht hti
    rw [torusHkValueCLM.map_tsum (hws t hti)]
    exact tsum_congr ht
  · intro s hs t ht hst z
    have hip (r : ℝ) (hr : r ∈ Icc a b) : inner ℝ (∑' j, u j r) (torusHkValueCLM z) =
        ∑' j, inner ℝ (u j r) (torusHkValueCLM z) := by
      simpa only [coe_innerSL_apply, real_inner_comm] using (innerSL ℝ (torusHkValueCLM z)).map_tsum (hus r hr)
    have hig (r : ℝ) (hr : r ∈ Icc a b) : inner ℝ (∑' j, g j r) z = ∑' j, inner ℝ (g j r) z := by
      simpa only [coe_innerSL_apply, real_inner_comm] using (innerSL ℝ z).map_tsum (hgs r hr)
    have hiu (r : ℝ) (hr : r ∈ Icc a b) : Summable (fun j => inner ℝ (u j r) (torusHkValueCLM z)) := by
      simpa only [coe_innerSL_apply, real_inner_comm] using (innerSL ℝ (torusHkValueCLM z)).summable (hus r hr)
    have he := boundedTimeSeries_intervalIntegral_tsum
      (fun j r => inner ℝ (g j r) z) (fun j => Bg j * ‖z‖) (hg.mul_right ‖z‖) a b
      (fun j => (h j).dual.aestronglyMeasurable.inner (𝕜 := ℝ) aestronglyMeasurable_const)
      (fun j r hr => (norm_inner_le_norm (g j r) z).trans
        (mul_le_mul_of_nonneg_right (hBg j r hr) (norm_nonneg z))) s t hs ht hst
    rw [hip t ht, hip s hs, ← Summable.tsum_sub (hiu t ht) (hiu s hs)]
    rw [tsum_congr (fun j => (h j).increment s hs t ht hst z), ← he]
    apply intervalIntegral.integral_congr
    intro r hr
    exact (hig r (Icc_subset_Icc hs.1 ht.2 (by simpa only [uIcc_of_le hst] using hr))).symm

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The first diagonal mean vanishes by the zero-mean pulse assumption. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
   [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)



include P in
theorem liftMean_first_diagonal_zero_of_initial_action (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : Vec 2 → ∀ i, h i) 
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2)
    (he : liftApply 0 (Cc 0 0) (fun _ => f) t = fun Y _ => f Y) :
    liftMean Q Cc (fun _ => f) 0 1 t X = 0 := by
  have hb := setting_first_cross_mean P f t ht X
  simpa [liftMean, liftA, he] using hb

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Pointwise value and gradient bounds control the literal unit-cell energy norm. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance fieldEnergyPointwiseBoundProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using AVRegularity.CycleEvolution.cellCube_volume_one⟩

omit [NormedSpace ℝ E] in
theorem cellL2Norm_le_pointwise_bound (f : Vec 2 → E) (hf : Continuous f)
    (B : ℝ) (hb : ∀ z, ‖f z‖ ≤ B) : cellL2Norm f ≤ ENNReal.ofReal B := by
  have hh := eLpNorm_le_of_ae_bound (p := (2 : ENNReal))
    (hf.aestronglyMeasurable : AEStronglyMeasurable f (volume.restrict AVenhance.unitCube))
    (ae_of_all _ hb)
  simpa only [measure_univ, ENNReal.one_rpow, one_mul, cellL2Norm] using hh

theorem fieldEnergyNorm_le_pointwise_bounds (I : Set ℝ) (hI : MeasurableSet I)
    (f : ℝ → Vec 2 → E) (B₀ B₁ : ℝ) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hc : ∀ t ∈ I, Continuous (f t))
    (hg : ∀ t ∈ I, Continuous (fderiv ℝ (f t)))
    (hb₀ : ∀ t ∈ I, ∀ z, ‖f t z‖ ≤ B₀)
    (hb₁ : ∀ t ∈ I, ∀ z, ‖fderiv ℝ (f t) z‖ ≤ B₁) :
    fieldEnergyNorm I f ≤ ENNReal.ofReal (B₀ + B₁) := by
  have hvalue : (⨆ t ∈ I, cellL2Norm (f t)) ≤ ENNReal.ofReal B₀ := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    exact cellL2Norm_le_pointwise_bound (f t) (hc t ht) B₀ (hb₀ t ht)
  have hgrad : cellUlNorm I (fun t z => fderiv ℝ (f t) z) ≤ ENNReal.ofReal B₁ := by
    apply AVRegularity.CycleEvolution.cellUlNorm_le_of_window_sq_bound
    intro a
    have hwindow : MeasurableSet (Icc a (a + 1) ∩ I) := measurableSet_Icc.inter hI
    have hmeasure : volume (Icc a (a + 1) ∩ I) ≤ 1 := by
      apply (measure_mono inter_subset_left).trans_eq
      rw [Real.volume_Icc, show a + 1 - a = 1 by ring, ENNReal.ofReal_one]
    calc
      _ ≤ ∫⁻ _ in Icc a (a + 1) ∩ I, (ENNReal.ofReal B₁) ^ 2 := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hwindow] with t ht
        exact pow_le_pow_left' (cellL2Norm_le_pointwise_bound _ (hg t ht.2) B₁ (hb₁ t ht.2)) 2
      _ ≤ (ENNReal.ofReal B₁) ^ 2 := by
        rw [lintegral_const, Measure.restrict_apply_univ]
        simpa only [mul_one] using mul_le_mul' (le_refl ((ENNReal.ofReal B₁) ^ 2)) hmeasure
  exact (add_le_add hvalue hgrad).trans_eq (ENNReal.ofReal_add hB₀ hB₁).symm

end AVRegularity.CycleComparison.Lift
end

section
open AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! The realified periodic H¹ carrier has the exact complex scalar modulus law. -/

theorem cellH1Scalar_norm (c : ℂ) (z : TorusHk 1 ℂ) :
    ‖cellH1Scalar c z‖ = ‖c‖ * ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [cellH1_norm_sq, mul_pow, cellH1_norm_sq]
  simp_rw [cellH1Scalar_value, cellH1Scalar_derivative, cellScalarCLM_smul, norm_smul, mul_pow]
  rw [mul_add, Finset.mul_sum]

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The first diagonal mean vanishes by the zero-mean pulse assumption. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)



include P in
theorem liftMean_first_diagonal_zero (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    liftMean Q Cc (fun _ => f) 0 1 t X = 0 := by
  have he : liftApply 0 (Cc 0 0) (fun _ => f) t = fun X _ => f X := by
    funext X z
    exact hseq.1 f hf t ht X z
  have hb := setting_first_cross_mean P f t ht X
  simpa [liftMean, liftA, he] using hb

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The first diagonal inverse is forced only by the prescribed shear times a slow derivative. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftCellSource_first_diagonal (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftCellSource Q Cc (fun _ => f) 0 1 t X z =
      -(∑ q : Fin 2, (Real.sqrt Q.η * Q.v t z q) • fderiv ℝ f X (basisVec q)) := by
  have hid : liftApply 0 (Cc 0 0) (fun _ => f) t = fun Y _ => f Y := by
    funext Y y
    exact hseq.1 f hf t ht Y y
  have hb := congrFun (cellB1_independent Q.η Q.G Q.v t f X) z
  have hm := liftMean_first_diagonal_zero P sX sZ Cc hseq f hf t ht X
  simpa [liftCellSource, liftA, hid, hm] using congrArg Neg.neg hb


include P in
theorem liftCellSource_first_diagonal_profile (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftCellSource Q Cc (fun _ => f) 0 1 t X z =
      -(Real.sqrt Q.η * V t (z par.rev)) • fderiv ℝ f X (basisVec par) := by
  rw [liftCellSource_first_diagonal P sX sZ Cc hseq f hf t ht X z, P.v_shear t z]
  simp [basisVec_apply, mul_ite]

end AVRegularity.CycleComparison.Lift
end
