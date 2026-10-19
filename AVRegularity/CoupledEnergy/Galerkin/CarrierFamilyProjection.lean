-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Galerkin.TorusProjection
import AVenhance.Infra.Classical.GalerkinGenerator
import Homogenization.Sobolev.H1.BasicLemmas

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
open AVenhance.Infra.Torus AVenhance.Infra.Classical
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Parabolic.WeakUniqueness
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Promote a finite Fourier cutoff to any higher periodic weak-jet carrier. -/

local instance smoothLiftMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance smoothLiftAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance smoothLiftCircleProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance smoothLiftTorusProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
local instance smoothLiftCellFinite : IsFiniteMeasure
    (volume.restrict AVenhance.unitCube) := by
  exact ⟨by
    simpa only [Measure.restrict_apply_univ] using
      AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra.weak_unitCube_volume_lt_top⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Directions of a finite word in the order used by the classical derivative recursion. -/
def smoothLiftWord : (n : ℕ) → DerivativeWord2 n → List (Fin 2)
  | 0, _ => []
  | n + 1, w => w (Fin.last n) :: smoothLiftWord n (Fin.init w)

theorem smoothLiftWord_snoc (n : ℕ) (w : DerivativeWord2 n) (i : Fin 2) :
    smoothLiftWord (n + 1) (Fin.snoc w i) = i :: smoothLiftWord n w := by
  simp [smoothLiftWord, Fin.init_snoc, Fin.snoc_last]

/-- A scalar coordinate of the smooth finite-frequency synthesis, differentiated along a word. -/
noncomputable def smoothFourierCoordinate {K L : ℕ} (N : ℕ)
    (f : TorusHk K E) (j : Fin (L + 1)) (w : DerivativeWord2 j.val) (e : E) :
    Vec 2 → ℝ :=
  AVenhance.Infra.Classical.classicalWordDerivative (smoothLiftWord j.val w)
    (torusJetCoordinateFourierPolynomial N f (valueIndex2 K) e)

/-- The full vector-valued smooth finite-frequency jet of a torus Sobolev element. -/
noncomputable def smoothFourierJet {K L : ℕ} (N : ℕ) (f : TorusHk K E) : RawJet2 L E :=
  fun a x => ∑ k : Fin (Module.finrank ℝ E),
    smoothFourierCoordinate N f a.1 a.2 ((stdOrthonormalBasis ℝ E) k) x •
      (stdOrthonormalBasis ℝ E) k

omit [FiniteDimensional ℝ E] in
theorem smoothFourierCoordinate_contDiff {K L : ℕ} (N : ℕ) (f : TorusHk K E)
    (j : Fin (L + 1)) (w : DerivativeWord2 j.val) (e : E) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (smoothFourierCoordinate N f j w e) := by
  have hbase : ContDiff ℝ (↑(⊤ : ℕ∞))
      (torusJetCoordinateFourierPolynomial N f (valueIndex2 K) e) :=
    (torusJetCoordinateFourierPolynomial_contDiff N f (valueIndex2 K) e).of_le le_top
  exact AVenhance.Infra.Classical.GalerkinGenerator.classicalWordDerivative_smooth
    (smoothLiftWord j.val w)
    (torusJetCoordinateFourierPolynomial N f (valueIndex2 K) e)
    hbase

omit [FiniteDimensional ℝ E] in
theorem smoothFourierCoordinate_periodic {K L : ℕ} (N : ℕ) (f : TorusHk K E)
    (j : Fin (L + 1)) (w : DerivativeWord2 j.val) (e : E) :
    AVenhance.IsZ2Periodic (smoothFourierCoordinate N f j w e) := by
  exact AVenhance.Infra.Classical.GalerkinGenerator.classicalWordDerivative_periodic
    (smoothLiftWord j.val w)
    (torusJetCoordinateFourierPolynomial N f (valueIndex2 K) e)
    (torusJetCoordinateFourierPolynomial_periodic N f (valueIndex2 K) e)

theorem smoothFourierJet_periodic {K L : ℕ} (N : ℕ) (f : TorusHk K E)
    (a : JetIndex2 L) : AVenhance.IsZ2Periodic (smoothFourierJet N f a) := by
  intro n x
  simp only [smoothFourierJet]
  apply Finset.sum_congr rfl
  intro k hk
  rw [smoothFourierCoordinate_periodic]

theorem smoothFourierJet_inner_eq_sum {K L : ℕ} (N : ℕ) (f : TorusHk K E)
    (a : JetIndex2 L) (e : E) (x : Vec 2) :
    inner ℝ e (smoothFourierJet N f a x) =
      ∑ k : Fin (Module.finrank ℝ E),
        smoothFourierCoordinate N f a.1 a.2 ((stdOrthonormalBasis ℝ E) k) x *
          inner ℝ e ((stdOrthonormalBasis ℝ E) k) := by
  simp only [smoothFourierJet, inner_sum, real_inner_smul_right]

theorem smoothFourierJet_inner_contDiff {K L : ℕ} (N : ℕ) (f : TorusHk K E)
    (a : JetIndex2 L) (e : E) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => inner ℝ e (smoothFourierJet N f a x)) := by
  rw [show (fun x => inner ℝ e (smoothFourierJet N f a x)) =
      fun x => ∑ k : Fin (Module.finrank ℝ E),
        smoothFourierCoordinate N f a.1 a.2 ((stdOrthonormalBasis ℝ E) k) x *
          inner ℝ e ((stdOrthonormalBasis ℝ E) k) by
    funext x
    exact smoothFourierJet_inner_eq_sum N f a e x]
  apply ContDiff.sum
  intro k hk
  exact (smoothFourierCoordinate_contDiff N f a.1 a.2
    ((stdOrthonormalBasis ℝ E) k)).mul contDiff_const

theorem smoothFourierJet_inner_derivative {K L : ℕ} (N : ℕ) (f : TorusHk K E)
    (j : Fin L) (w : DerivativeWord2 j.val) (e : E) (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => inner ℝ e
      (smoothFourierJet N f (lowerIndex2 j w) y)) x i =
      inner ℝ e (smoothFourierJet N f (nextIndex2 j w i) x) := by
  rw [show (fun y => inner ℝ e (smoothFourierJet N f (lowerIndex2 j w) y)) =
      fun y => ∑ k : Fin (Module.finrank ℝ E),
        smoothFourierCoordinate N f (lowerIndex2 j w).1 (lowerIndex2 j w).2
          ((stdOrthonormalBasis ℝ E) k) y *
          inner ℝ e ((stdOrthonormalBasis ℝ E) k) by
    funext y
    exact smoothFourierJet_inner_eq_sum N f (lowerIndex2 j w) e y]
  have hsum : AVenhance.spaceGrad (fun y =>
      ∑ k : Fin (Module.finrank ℝ E),
        smoothFourierCoordinate N f (lowerIndex2 j w).1 (lowerIndex2 j w).2
          ((stdOrthonormalBasis ℝ E) k) y *
          inner ℝ e ((stdOrthonormalBasis ℝ E) k)) x i =
      ∑ k : Fin (Module.finrank ℝ E),
        AVenhance.spaceGrad (fun y =>
          smoothFourierCoordinate N f (lowerIndex2 j w).1 (lowerIndex2 j w).2
            ((stdOrthonormalBasis ℝ E) k) y *
            inner ℝ e ((stdOrthonormalBasis ℝ E) k)) x i := by
    change (fderiv ℝ (fun y => ∑ k : Fin (Module.finrank ℝ E),
      smoothFourierCoordinate N f (lowerIndex2 j w).1 (lowerIndex2 j w).2
        ((stdOrthonormalBasis ℝ E) k) y *
        inner ℝ e ((stdOrthonormalBasis ℝ E) k)) x) (basisVec i) = _
    rw [fderiv_fun_sum]
    simp only [sum_apply]
    · rfl
    · intro k hk
      have hcoord := smoothFourierCoordinate_contDiff N f (lowerIndex2 j w).1
        (lowerIndex2 j w).2 ((stdOrthonormalBasis ℝ E) k)
      have hcoord1 : ContDiff ℝ (1 : WithTop ℕ∞)
          (smoothFourierCoordinate N f (lowerIndex2 j w).1 (lowerIndex2 j w).2
            ((stdOrthonormalBasis ℝ E) k)) := hcoord.of_le (by norm_num)
      exact (hcoord1.differentiable (by norm_num) x).mul_const _
  rw [hsum, smoothFourierJet_inner_eq_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change AVenhance.spaceGrad (fun y =>
      AVenhance.Infra.Classical.classicalWordDerivative
        (smoothLiftWord j.val w)
        (torusJetCoordinateFourierPolynomial N f (valueIndex2 K)
          ((stdOrthonormalBasis ℝ E) k)) y *
        inner ℝ e ((stdOrthonormalBasis ℝ E) k)) x i = _
  have hcoord := smoothFourierCoordinate_contDiff N f (lowerIndex2 j w).1
    (lowerIndex2 j w).2 ((stdOrthonormalBasis ℝ E) k)
  have hcoord1 : ContDiff ℝ 1 (smoothFourierCoordinate N f
      (lowerIndex2 j w).1 (lowerIndex2 j w).2 ((stdOrthonormalBasis ℝ E) k)) :=
    hcoord.of_le (by simp)
  rw [show (fun y => AVenhance.Infra.Classical.classicalWordDerivative
      (smoothLiftWord j.val w)
      (torusJetCoordinateFourierPolynomial N f (valueIndex2 K)
        ((stdOrthonormalBasis ℝ E) k)) y *
      inner ℝ e ((stdOrthonormalBasis ℝ E) k)) =
      fun y => inner ℝ e ((stdOrthonormalBasis ℝ E) k) *
        AVenhance.Infra.Classical.classicalWordDerivative
          (smoothLiftWord j.val w)
          (torusJetCoordinateFourierPolynomial N f (valueIndex2 K)
            ((stdOrthonormalBasis ℝ E) k)) y by
    funext y
    ring]
  change AVenhance.spaceGrad (fun y => inner ℝ e ((stdOrthonormalBasis ℝ E) k) *
      smoothFourierCoordinate N f (lowerIndex2 j w).1 (lowerIndex2 j w).2
        ((stdOrthonormalBasis ℝ E) k) y)
      x i = _
  rw [GalerkinModeCalculus.spaceGrad_realConstant_mul hcoord1]
  simp [smoothFourierCoordinate, lowerIndex2, lowerIndex, nextIndex2, nextIndex,
    smoothLiftWord_snoc, AVenhance.Infra.Classical.classicalWordDerivative]; ring

noncomputable def smoothFourierCoordinateCellLp {K L : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 L) (e : E) :
    Lp ℝ 2 (volume.restrict AVenhance.unitCube) :=
  (AVenhance.Infra.Parabolic.WeakUniqueness.weak_continuous_memL2On
    (smoothFourierCoordinate_contDiff N f a.1 a.2 e).continuous).toLp
      (smoothFourierCoordinate N f a.1 a.2 e)

noncomputable def smoothFourierJetCellLp {K L : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 L) :
    Lp E 2 (volume.restrict AVenhance.unitCube) :=
  ∑ k : Fin (Module.finrank ℝ E),
    ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      ((stdOrthonormalBasis ℝ E) k)).compLpL 2
        (volume.restrict AVenhance.unitCube))
      (smoothFourierCoordinateCellLp N f a ((stdOrthonormalBasis ℝ E) k))

theorem smoothFourierJet_cellLp_ae {K L : ℕ} (N : ℕ) (f : TorusHk K E)
    (a : JetIndex2 L) :
    smoothFourierJetCellLp N f a =ᵐ[volume.restrict AVenhance.unitCube]
      smoothFourierJet N f a := by
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun k : Fin (Module.finrank ℝ E) =>
    ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      ((stdOrthonormalBasis ℝ E) k)).compLpL 2
        (volume.restrict AVenhance.unitCube))
      (smoothFourierCoordinateCellLp N f a ((stdOrthonormalBasis ℝ E) k)))
  have hterms : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
      ∀ k : Fin (Module.finrank ℝ E),
        (((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
          ((stdOrthonormalBasis ℝ E) k)).compLpL 2
            (volume.restrict AVenhance.unitCube))
          (smoothFourierCoordinateCellLp N f a ((stdOrthonormalBasis ℝ E) k))) x =
        smoothFourierCoordinate N f a.1 a.2 ((stdOrthonormalBasis ℝ E) k) x •
          (stdOrthonormalBasis ℝ E) k := by
    apply ae_all_iff.2
    intro k
    have hmap := ContinuousLinearMap.coeFn_compLpL
      (L := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
        ((stdOrthonormalBasis ℝ E) k))
      (smoothFourierCoordinateCellLp N f a ((stdOrthonormalBasis ℝ E) k))
    have hq := (AVenhance.Infra.Parabolic.WeakUniqueness.weak_continuous_memL2On
      (smoothFourierCoordinate_contDiff N f a.1 a.2
        ((stdOrthonormalBasis ℝ E) k)).continuous).coeFn_toLp
    filter_upwards [hmap, hq] with x hmap hq
    rw [hmap]
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
    change ((weak_continuous_memL2On
      (smoothFourierCoordinate_contDiff N f a.1 a.2
        ((stdOrthonormalBasis ℝ E) k)).continuous).toLp
        (smoothFourierCoordinate N f a.1 a.2 ((stdOrthonormalBasis ℝ E) k))) x •
          (stdOrthonormalBasis ℝ E) k = _
    rw [hq]
  filter_upwards [hsum, hterms] with x hsum hterms
  change (∑ k : Fin (Module.finrank ℝ E),
      ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
        ((stdOrthonormalBasis ℝ E) k)).compLpL 2
        (volume.restrict AVenhance.unitCube))
        (smoothFourierCoordinateCellLp N f a ((stdOrthonormalBasis ℝ E) k))) x =
    ∑ k : Fin (Module.finrank ℝ E),
      smoothFourierCoordinate N f a.1 a.2 ((stdOrthonormalBasis ℝ E) k) x •
        (stdOrthonormalBasis ℝ E) k
  rw [hsum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  exact hterms k

theorem smoothFourierJet_memLp {K L : ℕ} (N : ℕ) (f : TorusHk K E)
    (a : JetIndex2 L) :
    MemLp (smoothFourierJet N f a) 2 (volume.restrict AVenhance.unitCube) := by
  exact (memLp_congr_ae (smoothFourierJet_cellLp_ae N f a)).1
    (Lp.memLp (smoothFourierJetCellLp N f a))

theorem smoothFourierJet_value_eq_polynomial {K L : ℕ} (N : ℕ)
    (f : TorusHk K E) :
    smoothFourierJet N f (valueIndex2 L) =
      torusJetFourierPolynomial N f (valueIndex2 K) := by
  funext x
  simp [smoothFourierJet, smoothFourierCoordinate, smoothLiftWord, valueIndex2,
    valueIndex, torusJetFourierPolynomial,
    AVenhance.Infra.Classical.classicalWordDerivative]

theorem smoothFourierJet_hasWeakJet {K L : ℕ} (N : ℕ) (f : TorusHk K E) :
  HasOrderedWeakJetOn (K := L) Set.univ (smoothFourierJet (K := K) (L := L) N f) := by
  intro j w i e
  have hcont := smoothFourierJet_inner_contDiff (K := K) (L := L) N f (lowerIndex2 j w) e
  have hcont1 : ContDiff ℝ (1 : WithTop ℕ∞)
      (fun x => inner ℝ e (smoothFourierJet N f (lowerIndex2 j w) x)) :=
    hcont.of_le (by simp)
  have hweak := HasWeakPartialDerivOn.of_contDiff (U := Set.univ) (i := i) hcont1
  have hderiv : (fun x =>
      (fderiv ℝ (fun y => inner ℝ e
        (smoothFourierJet (K := K) (L := L) N f (lowerIndex2 j w) y)) x) (basisVec i)) =
      fun x => inner ℝ e (smoothFourierJet (K := K) (L := L) N f (nextIndex2 j w i) x) := by
    funext x
    simpa [AVenhance.spaceGrad] using
      smoothFourierJet_inner_derivative (K := K) (L := L) N f j w e i x
  intro φ hφ hc hs
  rw [← hderiv]
  exact hweak φ hφ hc hs

/-- The smooth lift is a torus Sobolev element of every requested finite order. -/
noncomputable def smoothFourierLift {K L : ℕ} (N : ℕ) (f : TorusHk K E) :
    TorusHk L E :=
  (TorusHkFunction.toHk (K := L)
    { jet := smoothFourierJet N f
      hasPeriodicWeakJet := ⟨smoothFourierJet_periodic N f,
        smoothFourierJet_memLp N f, smoothFourierJet_hasWeakJet N f⟩ })

end AVRegularity.CoupledEnergy.Galerkin
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
open AVenhance.Infra.Classical AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Scalar Fourier modes tensored with the finite-dimensional fibers of a coupled system. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- A basis label consists of a component, a retained real Fourier mode, and a fiber basis
coordinate. -/
abbrev CoupledFourierModeIndex (N : ℕ) :=
  Σ i : ι, Fin (RealFourierDimension N) × Fin (Module.finrank ℝ (h i))

noncomputable def coupledModeScalar (N : ℕ) (a : CoupledFourierModeIndex (h := h) N) :
    Vec 2 → ℝ :=
  realFourierModeAmbient N ((realFourierIndexEquivFin N).symm a.2.1)

noncomputable def coupledModeScalarDerivative (N : ℕ)
    (a : CoupledFourierModeIndex (h := h) N) (m : ℕ)
    (w : DerivativeWord2 m) : Vec 2 → ℝ :=
  classicalWordDerivative (smoothLiftWord m w) (coupledModeScalar N a)

noncomputable def coupledModeJet (N : ℕ)
    (a : CoupledFourierModeIndex (h := h) N) (i : ι) (m : ℕ)
    (w : DerivativeWord2 m) : Vec 2 → h i :=
  if hi : i = a.1 then
    fun x => hi.symm ▸
      (coupledModeScalarDerivative N a m w x •
        (stdOrthonormalBasis ℝ (h a.1) a.2.2))
  else fun _ => 0

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] in
theorem coupledModeScalarDerivative_contDiff (N : ℕ)
    (a : CoupledFourierModeIndex (h := h) N) (m : ℕ)
    (w : DerivativeWord2 m) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (coupledModeScalarDerivative N a m w) := by
  have hbase : ContDiff ℝ (↑(⊤ : ℕ∞)) (coupledModeScalar N a) :=
    (realFourierModeAmbient_contDiff N
      ((realFourierIndexEquivFin N).symm a.2.1)).of_le le_top
  exact GalerkinGenerator.classicalWordDerivative_smooth (smoothLiftWord m w)
    (coupledModeScalar N a) hbase

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    [∀ i, MeasurableSpace (h i)] in
theorem coupledModeScalarDerivative_periodic (N : ℕ)
    (a : CoupledFourierModeIndex (h := h) N) (m : ℕ)
    (w : DerivativeWord2 m) :
    AVenhance.IsZ2Periodic (coupledModeScalarDerivative N a m w) := by
  exact GalerkinGenerator.classicalWordDerivative_periodic (smoothLiftWord m w)
    (coupledModeScalar N a) (realFourierModeAmbient_periodic N
      ((realFourierIndexEquivFin N).symm a.2.1))

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] in
theorem coupledModeScalarDerivative_spaceGrad (N : ℕ)
    (a : CoupledFourierModeIndex (h := h) N) (m : ℕ)
    (w : DerivativeWord2 m) (k : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (coupledModeScalarDerivative N a m w) x k =
      coupledModeScalarDerivative N a (m + 1) (Fin.snoc w k) x := by
  change AVenhance.spaceGrad
      (classicalWordDerivative (smoothLiftWord m w) (coupledModeScalar N a)) x k =
    classicalWordDerivative (smoothLiftWord (m + 1) (Fin.snoc w k))
      (coupledModeScalar N a) x
  rw [smoothLiftWord_snoc]
  rfl

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] in
theorem coupledModeJet_fderiv (N : ℕ)
    (a : CoupledFourierModeIndex (h := h) N) (i : ι) (m : ℕ)
    (w : DerivativeWord2 m) (k : Fin 2) (x : Vec 2) :
    fderiv ℝ (coupledModeJet N a i m w) x (basisVec k) =
      coupledModeJet N a i (m + 1) (Fin.snoc w k) x := by
  by_cases hi : i = a.1
  · subst i
    simp only [coupledModeJet, dite_true]
    change fderiv ℝ (fun y => coupledModeScalarDerivative N a m w y •
      (stdOrthonormalBasis ℝ (h a.1) a.2.2)) x (basisVec k) = _
    have hdiff := (coupledModeScalarDerivative_contDiff N a m w).differentiable
      (by simp) x
    rw [fderiv_smul_const hdiff]
    change AVenhance.spaceGrad (coupledModeScalarDerivative N a m w) x k •
        (stdOrthonormalBasis ℝ (h a.1) a.2.2) = _
    rw [coupledModeScalarDerivative_spaceGrad]
  · simp [coupledModeJet, hi]

end AVRegularity.CoupledEnergy.Galerkin
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Parabolic.FourierGalerkin AVenhance.Infra.Torus
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The scalar cell mass matrix of the explicit real Fourier modes is the identity. -/

local instance plainOrthogonalityMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance plainOrthogonalityAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- Orthonormality is unchanged when normalized torus modes are read on the unit cell. -/
theorem plainScalarMode_cell_orthonormal (N : ℕ)
    (r c : Fin (RealFourierDimension N)) :
    (∫ x in AVenhance.unitCube,
      realFourierModeAmbient N ((realFourierIndexEquivFin N).symm r) x *
      realFourierModeAmbient N ((realFourierIndexEquivFin N).symm c) x) =
        if r = c then 1 else 0 := by
  have h := realFourierModeFin_orthonormal N r c
  rw [realFourierModeFin_eq_periodicToTorus, realFourierModeFin_eq_periodicToTorus] at h
  change (∫ x : UnitAddTorus (Fin 2), periodicToTorus
    (fun y => realFourierModeAmbient N ((realFourierIndexEquivFin N).symm r) y *
      realFourierModeAmbient N ((realFourierIndexEquivFin N).symm c) y) x) = _ at h
  rw [integral_periodicToTorus_eq_unitCell, integral_unitCell_eq_unitCube] at h
  exact h

/-- Tensoring a real Fourier mode with a fiber basis vector preserves orthonormality. -/
theorem plainVectorMode_cell_orthonormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (N : ℕ)
    (r c : Fin (RealFourierDimension N)) (e f : Fin (Module.finrank ℝ E)) :
    (∫ x in AVenhance.unitCube, inner ℝ
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm r) x •
        (stdOrthonormalBasis ℝ E) e)
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm c) x •
        (stdOrthonormalBasis ℝ E) f)) =
      if (r, e) = (c, f) then 1 else 0 := by
  simp only [real_inner_smul_left, real_inner_smul_right]
  simp_rw [← mul_assoc]
  rw [integral_mul_const, plainScalarMode_cell_orthonormal,
    OrthonormalBasis.inner_eq_ite]
  by_cases hr : r = c <;> by_cases he : e = f <;> simp [hr, he, eq_comm]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

/-- Component, Fourier and fiber coordinates give an identity value mass matrix. -/
theorem plainCoupledMode_cell_orthonormal (N : ℕ)
    (r c : CoupledFourierModeIndex (h := h) N) :
    (∑ i, ∫ x in AVenhance.unitCube, inner ℝ (coupledModeJet N r i 0 Fin.elim0 x)
      (coupledModeJet N c i 0 Fin.elim0 x)) = if r = c then 1 else 0 := by
  rcases r with ⟨ri, rf, re⟩
  rcases c with ⟨ci, cf, ce⟩
  rw [Finset.sum_eq_single ri]
  · by_cases hrc : ri = ci
    · subst ci
      simp only [coupledModeJet, dite_true]
      simp only [coupledModeScalarDerivative, smoothLiftWord,
        AVenhance.Infra.Classical.classicalWordDerivative]
      simpa only [coupledModeScalar, Sigma.mk.inj_iff, heq_eq_eq, true_and] using
        plainVectorMode_cell_orthonormal (E := h ri) N rf cf re ce
    · simp [coupledModeJet, hrc]
  · intro i _ hi
    simp [coupledModeJet, hi]
  · simp

end AVRegularity.CoupledEnergy.Galerkin
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory AVRegularity.Sobolev
open Filter
open scoped Topology
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Graph-restricted Fourier Galerkin projections on the periodic Sobolev carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  {K r : ℕ}

/-- Fourier truncation on every ordered jet component, restricted to the periodic weak-jet
carrier. -/
noncomputable def galerkinProj (N : ℕ) :
    TorusHk K E →L[ℝ] TorusHk K E :=
  ((cellJetFourierProjection (E := E) K N).comp
    (torusHkGraph (E := E) K).toSubmodule.subtypeL).codRestrict
      (torusHkGraph (E := E) K).toSubmodule
      (fun f => by
        change cellJetFourierProjection (E := E) K N f.val ∈
          (torusHkGraph (E := E) K).toSubmodule
        rw [cellJetFourierProjection_eq_polynomialToHk]
        exact (torusJetFourierPolynomialToHk N f).property)

@[simp] theorem galerkinProj_val (N : ℕ) (f : TorusHk K E) :
    (galerkinProj (E := E) (K := K) N f).val =
      cellJetFourierProjection (E := E) K N f.val := rfl

/-- The graph-restricted Fourier cutoff is idempotent. -/
theorem galerkinProj_idempotent (N : ℕ) (f : TorusHk K E) :
    galerkinProj (E := E) (K := K) N (galerkinProj N f) = galerkinProj N f := by
  apply Subtype.ext
  rw [galerkinProj_val, galerkinProj_val]
  exact cellJetFourierProjection_idempotent K N f.val

theorem galerkinProj_factorialNormSq_le (N : ℕ) (ρ : ℝ) (f : TorusHk K E) :
    factorialNormSq ρ (galerkinProj (E := E) (K := K) N f).val ≤
      factorialNormSq ρ f.val := by
  rw [galerkinProj_val]
  exact cellJetFourierProjection_factorialNormSq_le K N ρ f.val

/-- Fourier truncation is contractive in the Hilbert graph norm. -/
theorem galerkinProj_norm_le (N : ℕ) (f : TorusHk K E) :
    ‖galerkinProj (E := E) (K := K) N f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  change ‖(galerkinProj (E := E) (K := K) N f).val‖ ^ 2 ≤ ‖f.val‖ ^ 2
  rw [AVRegularity.Sobolev.jet_norm_sq_eq_sum,
    AVRegularity.Sobolev.jet_norm_sq_eq_sum]
  unfold AVRegularity.Sobolev.derivativeNormSq
  rw [galerkinProj_val]
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro w hw
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    (cellJetFourierProjection_component_norm_le (E := E) K N f.val ⟨j, w⟩)

theorem galerkinProj_derivative_commute (N : ℕ) (a : DerivativeWord2 r)
    (f : TorusHk (K + r) E) :
    galerkinProj (E := E) (K := K) N (derivativeTorusHk a f) =
      derivativeTorusHk a (galerkinProj (E := E) (K := K + r) N f) := by
  ext b
  simp [galerkinProj_val, derivativeTorusHk_apply,
    cellJetFourierProjection_apply]

theorem galerkinProj_range_finite (N : ℕ) :
    FiniteDimensional ℝ (galerkinProj (E := E) (K := K) N).toLinearMap.range := by
  have hfinite : FiniteDimensional ℝ
      (cellJetFourierProjection (E := E) K N).toLinearMap.range :=
    cellJetFourierProjection_range_finite (E := E) K N
  let T : (galerkinProj (E := E) (K := K) N).toLinearMap.range →ₗ[ℝ]
      (cellJetFourierProjection (E := E) K N).toLinearMap.range :=
    LinearMap.codRestrict
      ((cellJetFourierProjection (E := E) K N).toLinearMap.range)
      ((torusHkGraph (E := E) K).toSubmodule.subtype.comp
        (Submodule.subtype ((galerkinProj (E := E) (K := K) N).toLinearMap.range)))
      (by
        intro y
        rcases y.property with ⟨x, hx⟩
        refine ⟨x.val, ?_⟩
        change cellJetFourierProjection (E := E) K N x.val = y.val.val
        have h := congrArg (fun z : TorusHk K E => z.val) hx
        change cellJetFourierProjection (E := E) K N x.val = y.val.val at h
        exact h)
  have hT : Function.Injective T := by
    intro x y hxy
    have h' := congrArg (fun z :
        (cellJetFourierProjection (E := E) K N).toLinearMap.range => z.val) hxy
    change x.val.val = y.val.val at h'
    apply Subtype.ext
    apply Subtype.ext
    exact h'
  exact @FiniteDimensional.of_injective ℝ _ _ _ _ _ _ _ T hT hfinite

theorem galerkinProj_tendsto (f : TorusHk K E) :
    Tendsto (fun N => galerkinProj (E := E) (K := K) N f) atTop (𝓝 f) := by
  apply tendsto_subtype_rng.mpr
  simpa only [Function.comp_def, galerkinProj_val] using
    cellJetFourierProjection_tendsto (E := E) K f.val

end AVRegularity.CoupledEnergy.Galerkin
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Fourier projections on the finite family of genuine Sobolev carriers.
This family norm controls all coupling residuals simultaneously. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def carrierFamilyProjection (K : ι → ℕ) (N : ℕ) :
    (∀ i, TorusHk (K i) (h i)) →L[ℝ] (∀ i, TorusHk (K i) (h i)) :=
  ContinuousLinearMap.pi (fun i => (galerkinProj N).comp (ContinuousLinearMap.proj i))

omit [Fintype ι] in
@[simp] theorem carrierFamilyProjection_apply (K : ι → ℕ) (N : ℕ)
    (w : ∀ i, TorusHk (K i) (h i)) (i : ι) :
    carrierFamilyProjection K N w i = galerkinProj N (w i) := rfl

theorem carrierFamilyProjection_norm_le (K : ι → ℕ) (N : ℕ)
    (w : ∀ i, TorusHk (K i) (h i)) : ‖carrierFamilyProjection K N w‖ ≤ ‖w‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
  intro i
  exact (galerkinProj_norm_le N (w i)).trans (norm_le_pi_norm w i)

omit [Fintype ι] in
theorem carrierFamilyProjection_tendsto (K : ι → ℕ) (w : ∀ i, TorusHk (K i) (h i)) :
    Tendsto (fun N => carrierFamilyProjection K N w) atTop (𝓝 w) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact galerkinProj_tendsto (w i)

end AVRegularity.CoupledEnergy.Galerkin
end
end
