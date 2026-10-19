-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.KernelEnergy.DerivFactorialNormSq
import AVRegularity.Analysis.Schur.Finite
import AVRegularity.CoupledEnergy.Variational.WeightedJetMap
public import AVRegularity.CoupledEnergy.Variational.FactorialPairing
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.KernelEnergy

/-! Constant fiber maps and finite tensor assembly on the weak Sobolev carriers. -/

def derivativeWordOneEquiv : Fin 2 ≃ DerivativeWord2 1 where
  toFun q := fun _ => q
  invFun w := w 0
  left_inv q := rfl
  right_inv w := by
    funext i
    fin_cases i
    rfl

def derivativeWordHeadTailEquiv (n : ℕ) :
    (Fin 2 × DerivativeWord2 n) ≃ DerivativeWord2 (1 + n) :=
  (derivativeWordOneEquiv.prodCongr (Equiv.refl _)).trans (wordAppendEquiv 1 n)

def derivativeWordArrayIsometry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b : ℕ} (e : DerivativeWord2 a ≃ DerivativeWord2 b) :
    (PiLp 2 (fun _ : DerivativeWord2 a => E)) ≃ₗᵢ[ℝ]
      PiLp 2 (fun _ : DerivativeWord2 b => E) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ E e

theorem planeDerivFactorialNormSq_succ {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {K m : ℕ} (ρ : ℝ)
    (Y : PlaneHk Set.univ (K + m + 1) E) (g : Fin 2 → PlaneHk Set.univ (K + m) E)
    (hg : ∀ q, derivativePlaneHk (K := K + m) (r := 1)
      (fun _ : Fin 1 => q) Y = g q) :
    derivFactorialNormSq (m + 1) ρ Y.val =
      ∑ q, derivFactorialNormSq m ρ (g q).val := by
  classical
  let lowOrder (n : Fin (K + 1)) : Fin (K + m + 1) := ⟨n.val + m, by omega⟩
  let highOrder (n : Fin (K + 1)) : Fin (K + m + 2) :=
    ⟨1 + (n.val + m), by omega⟩
  have hwords (n : Fin (K + 1)) :
      (∑ q : Fin 2, ∑ v : DerivativeWord2 (n.val + m),
        ‖(g q).val (⟨lowOrder n, v⟩ : JetIndex2 (K + m))‖ ^ 2) =
      ∑ w : DerivativeWord2 (1 + (n.val + m)),
        ‖Y.val (⟨highOrder n, w⟩ : JetIndex2 (K + m + 1))‖ ^ 2 := by
    let jl : Fin (K + m + 1) := ⟨n.val + m, by omega⟩
    let jh : Fin (K + m + 2) := ⟨1 + (n.val + m), by omega⟩
    calc
      (∑ q : Fin 2, ∑ v : DerivativeWord2 (n.val + m),
          ‖(g q).val (⟨jl, v⟩ : JetIndex2 (K + m))‖ ^ 2) =
        ∑ p : Fin 2 × DerivativeWord2 (n.val + m),
          ‖(g p.1).val (⟨jl, p.2⟩ : JetIndex2 (K + m))‖ ^ 2 := by
            rw [Fintype.sum_prod_type]
      _ = ∑ w : DerivativeWord2 (1 + (n.val + m)),
          ‖Y.val (⟨jh, w⟩ : JetIndex2 (K + m + 1))‖ ^ 2 := by
        apply Fintype.sum_equiv (derivativeWordHeadTailEquiv (n.val + m))
        intro p
        have hidx : prefixJetIndex (fun _ : Fin 1 => p.1)
            (⟨jl, p.2⟩ : JetIndex2 (K + m)) =
            (⟨jh, Fin.append (fun _ : Fin 1 => p.1) p.2⟩ : JetIndex2 (K + m + 1)) := by
          apply Sigma.ext
          · apply Fin.ext
            simp [prefixJetIndex, jl, jh]
          · rfl
        have h := congrArg (fun z : PlaneHk Set.univ (K + m) E =>
          z.val (⟨jl, p.2⟩ : JetIndex2 (K + m))) (hg p.1)
        rw [derivativePlaneHk_apply] at h
        rw [hidx] at h
        exact (congrArg (fun z : Lp E 2 (volume.restrict Set.univ) => ‖z‖ ^ 2) h).symm
  unfold derivFactorialNormSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  have hlen : n.val + (m + 1) = 1 + (n.val + m) := by omega
  let hfun : DerivativeWord2 (n.val + (m + 1)) =
      DerivativeWord2 (1 + (n.val + m)) := congrArg DerivativeWord2 hlen
  let e : DerivativeWord2 (n.val + (m + 1)) ≃ DerivativeWord2 (1 + (n.val + m)) :=
    Equiv.cast hfun
  have hcast :
    ∑ w : DerivativeWord2 (n.val + (m + 1)),
        ‖Y.val ⟨⟨n.val + (m + 1), by omega⟩, w⟩‖ ^ 2 =
      ∑ w : DerivativeWord2 (1 + (n.val + m)),
        ‖Y.val ⟨⟨1 + (n.val + m), by omega⟩, w⟩‖ ^ 2 := by
          apply Fintype.sum_equiv e
          intro w
          let jlo : Fin (K + (m + 1) + 1) := ⟨n.val + (m + 1), by omega⟩
          let jhi : Fin (K + (m + 1) + 1) := ⟨1 + (n.val + m), by omega⟩
          have hidx :
              (⟨jlo, w⟩ : JetIndex2 (K + (m + 1))) = ⟨jhi, e w⟩ := by
            have hfirst : jlo = jhi := Fin.ext hlen
            refine Sigma.ext hfirst ?_
            exact (cast_heq hfun w).symm
          rw [hidx]
  rw [hcast, ← Finset.mul_sum, ← hwords n]

theorem finiteRootSchur {ι : Type*} [Fintype ι] (b : ι → ι → ℝ)
    (x y : ι → ℝ) (ν θ : ℝ) (hν : 0 < ν)
    (hb : ∀ i j, 0 ≤ b i j)
    (hrow : ∀ i, ∑ j, b i j ≤ θ) (hcol : ∀ j, ∑ i, b i j ≤ θ)
    (hy : ∀ i, 0 ≤ y i ∧ y i ≤ ν * ∑ j, b i j * x j) :
    (∑ i, y i ^ 2) ≤ (ν * θ) ^ 2 * (∑ j, x j ^ 2) := by
  classical
  by_cases he : IsEmpty ι
  · simp
  ·
    have hθ : 0 ≤ θ := by
      obtain ⟨i⟩ := not_isEmpty_iff.mp he
      exact (le_trans (Finset.sum_nonneg fun j _ => hb i j) (hrow i))
    have hbil := AVRegularity.Analysis.Schur.finiteSchurBilinear
      Finset.univ Finset.univ b y x θ hθ
      (by intro i hi j hj; exact hb i j)
      (by intro i hi; exact hrow i) (by intro j hj; exact hcol j)
    let Ysq := ∑ i, y i ^ 2
    let Xsq := ∑ j, x j ^ 2
    have hnonY : 0 ≤ Ysq := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hnonX : 0 ≤ Xsq := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hrowBound : Ysq ≤ ν * θ * Real.sqrt Ysq * Real.sqrt Xsq := by
      calc
        Ysq ≤ ∑ i, y i * (ν * ∑ j, b i j * x j) := by
          apply Finset.sum_le_sum
          intro i _
          rcases hy i with ⟨hyi, hbound⟩
          nlinarith [mul_le_mul_of_nonneg_left hbound hyi]
        _ = ν * (∑ i, ∑ j, b i j * y i * x j) := by
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ ≤ ν * (θ * Real.sqrt Ysq * Real.sqrt Xsq) := by
          apply mul_le_mul_of_nonneg_left _ hν.le
          simpa [Ysq, Xsq] using hbil
        _ = ν * θ * Real.sqrt Ysq * Real.sqrt Xsq := by ring
    by_cases hY : Real.sqrt Ysq = 0
    · have : Ysq = 0 := (Real.sqrt_eq_zero hnonY).mp hY
      change Ysq ≤ (ν * θ) ^ 2 * Xsq
      rw [this]
      positivity
    · have hYpos : 0 < Real.sqrt Ysq := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hY)
      have hroot : Real.sqrt Ysq ≤ ν * θ * Real.sqrt Xsq := by
        have hsquare : (Real.sqrt Ysq) ^ 2 ≤ ν * θ * Real.sqrt Ysq * Real.sqrt Xsq := by
          simpa [Real.sq_sqrt hnonY] using hrowBound
        nlinarith
      have hrootSq' : (Real.sqrt Ysq) ^ 2 ≤ (ν * θ * Real.sqrt Xsq) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg Ysq)]
      have hright : (ν * θ * Real.sqrt Xsq) ^ 2 = (ν * θ) ^ 2 * Xsq := by
        rw [mul_pow, Real.sq_sqrt hnonX]
      simpa [Ysq, Xsq, Real.sq_sqrt hnonY] using hrootSq'.trans_eq hright

def factorialWeightedJet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] {μ : Measure (Vec 2)} {K : ℕ}
    (ρ : ℝ) (D : JetL2 μ K E) : JetL2 μ K E :=
  WithLp.toLp 2 (fun a => factorialRootWeight ρ a.1.val • D a)

theorem factorialWeightedJet_normSq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {μ : Measure (Vec 2)} {K : ℕ} (ρ : ℝ) (D : JetL2 μ K E) :
    ‖factorialWeightedJet ρ D‖ ^ 2 = factorialNormSq ρ D := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ a : JetIndex2 K,
    ‖factorialRootWeight ρ a.1.val • D a‖ ^ 2) = factorialNormSq ρ D
  unfold factorialNormSq derivativeNormSq
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ w : DerivativeWord2 j.val,
        ‖factorialRootWeight ρ j.val • D ⟨j, w⟩‖ ^ 2) =
      ∑ w : DerivativeWord2 j.val,
        factorialWeight ρ j.val * ‖D ⟨j, w⟩‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro w _
          rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
            factorialRootWeight_sq]
    _ = factorialWeight ρ j.val *
        ∑ w : DerivativeWord2 j.val, ‖D ⟨j, w⟩‖ ^ 2 := by rw [Finset.mul_sum]

theorem factorialWeightedJet_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {μ : Measure (Vec 2)} {K : ℕ} (ρ : ℝ) (D : JetL2 μ K E) :
    ‖factorialWeightedJet ρ D‖ = Real.sqrt (factorialNormSq ρ D) := by
  rw [← factorialWeightedJet_normSq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem factorialNorm_root_add_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {μ : Measure (Vec 2)} {K : ℕ} (ρ : ℝ) (D F : JetL2 μ K E) :
    Real.sqrt (factorialNormSq ρ (D + F)) ≤
      Real.sqrt (factorialNormSq ρ D) + Real.sqrt (factorialNormSq ρ F) := by
  rw [← factorialWeightedJet_norm ρ (D + F), ← factorialWeightedJet_norm ρ D,
    ← factorialWeightedJet_norm ρ F]
  have hsum : factorialWeightedJet ρ (D + F) =
      factorialWeightedJet ρ D + factorialWeightedJet ρ F := by
    apply PiLp.ext
    intro a
    simp [factorialWeightedJet, smul_add]
  rw [hsum]
  exact norm_add_le _ _

theorem factorialNorm_root_sum_le {α E : Type*} [Fintype α] [DecidableEq α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] {μ : Measure (Vec 2)} {K : ℕ} (ρ : ℝ)
    (s : Finset α) (f : α → JetL2 μ K E) :
    Real.sqrt (factorialNormSq ρ (∑ a ∈ s, f a)) ≤
      ∑ a ∈ s, Real.sqrt (factorialNormSq ρ (f a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [factorialNormSq, derivativeNormSq]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      calc
        Real.sqrt (factorialNormSq ρ (f a + ∑ b ∈ s, f b)) ≤
            Real.sqrt (factorialNormSq ρ (f a)) +
              Real.sqrt (factorialNormSq ρ (∑ b ∈ s, f b)) :=
          factorialNorm_root_add_le ρ (f a) (∑ b ∈ s, f b)
        _ ≤ Real.sqrt (factorialNormSq ρ (f a)) +
            ∑ b ∈ s, Real.sqrt (factorialNormSq ρ (f b)) := by
          nlinarith [ih]

theorem truncatePlane_derivative_commute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {K L : ℕ} (hKL : K ≤ L) (Y : PlaneHk Set.univ (L + 1) E)
    (q : Fin 2) :
    derivativePlaneHk (K := K) (r := 1) (fun _ : Fin 1 => q)
        (truncatePlaneHk (Nat.succ_le_succ hKL) Y) =
      truncatePlaneHk hKL
        (derivativePlaneHk (K := L) (r := 1) (fun _ : Fin 1 => q) Y) := by
  apply PlaneHk.ext_value isOpen_univ
  have hidx :
      truncateJetIndex (Nat.succ_le_succ hKL)
          (prefixJetIndex (fun _ : Fin 1 => q) (valueIndex2 K)) =
        prefixJetIndex (fun _ : Fin 1 => q) (truncateJetIndex hKL (valueIndex2 K)) := by
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · rfl
  simp only [derivativePlaneHk_apply, truncatePlaneHk_apply]
  rw [hidx]

def mapRawPlaneJet {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {K : ℕ}
    (L : E →L[ℝ] F) (D : RawJet2 K E) : RawJet2 K F := fun a x => L (D a x)

theorem mapRawPlaneJet_weak {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ}
    (L : E →L[ℝ] F) (D : RawJet2 K E) (hD : HasOrderedWeakJetOn Set.univ D) :
    HasOrderedWeakJetOn Set.univ (mapRawPlaneJet L D) := by
  intro j w i e
  have h := hD j w i (L.adjoint e)
  simpa only [mapRawPlaneJet, ← ContinuousLinearMap.adjoint_inner_left] using h

def mapRawPlaneFunction {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ}
    (L : E →L[ℝ] F) (f : PlaneHkFunction Set.univ K E) : PlaneHkFunction Set.univ K F :=
  ⟨mapRawPlaneJet L f.jet, fun a => L.comp_memLp' (f.memL2 a),
    mapRawPlaneJet_weak L f.jet f.hasWeakJet⟩

def mapPlaneHk {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ}
    (L : E →L[ℝ] F) (f : PlaneHk Set.univ K E) : PlaneHk Set.univ K F :=
  (mapRawPlaneFunction L f.toFunction).toHk

theorem mapPlaneHk_jet_eq_compLp {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ}
    (L : E →L[ℝ] F) (f : PlaneHk Set.univ K E) (a : JetIndex2 K) :
    (mapPlaneHk L f).val a =
      (L.compLpL 2 (volume.restrict Set.univ)) (f.val a) := by
  apply Lp.ext
  have hround := congrArg Subtype.val (PlaneHk.toFunction_toHk f)
  change jetToL2 f.toFunction.jet f.toFunction.memL2 = f.val at hround
  have hsrc : f.toFunction.jet a =ᵐ[volume.restrict Set.univ] (fun x => f.val a x) :=
    (jetToL2_ae f.toFunction.jet f.toFunction.memL2 a).symm.trans
      (Lp.ext_iff.mp (congrArg (fun z => z a) hround))
  have hout := jetToL2_ae (mapRawPlaneJet L f.toFunction.jet)
    (fun b => L.comp_memLp' (f.toFunction.memL2 b)) a
  have hmap := ContinuousLinearMap.coeFn_compLpL L (f.val a)
  filter_upwards [hout, hsrc, hmap] with x ho hs hm
  exact ho.trans ((congrArg L hs).trans hm.symm)

theorem mapPlaneHk_factorialNormSq_le {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ} (ρ : ℝ)
    (L : E →L[ℝ] F) (f : PlaneHk Set.univ K E) :
    factorialNormSq ρ (mapPlaneHk L f).val ≤ ‖L‖ ^ 2 * factorialNormSq ρ f.val := by
  unfold factorialNormSq derivativeNormSq
  calc
    (∑ j : Fin (K + 1), factorialWeight ρ j.val *
        ∑ w : DerivativeWord2 j.val, ‖(mapPlaneHk L f).val ⟨j, w⟩‖ ^ 2) ≤
      ∑ j : Fin (K + 1), factorialWeight ρ j.val *
        (‖L‖ ^ 2 * ∑ w : DerivativeWord2 j.val, ‖f.val ⟨j, w⟩‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (factorialWeight_nonneg ρ j.val)
      calc
        (∑ w : DerivativeWord2 j.val, ‖(mapPlaneHk L f).val ⟨j, w⟩‖ ^ 2) ≤
            ∑ w : DerivativeWord2 j.val, ‖L‖ ^ 2 * ‖f.val ⟨j, w⟩‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro w _
          have hmap := mapPlaneHk_jet_eq_compLp L f ⟨j, w⟩
          have hnorm : ‖(mapPlaneHk L f).val ⟨j, w⟩‖ ≤
              ‖L‖ * ‖f.val ⟨j, w⟩‖ := by
            rw [hmap]
            calc
              ‖(L.compLpL 2 (volume.restrict Set.univ)) (f.val ⟨j, w⟩)‖ ≤
                  ‖L.compLpL 2 (volume.restrict Set.univ)‖ * ‖f.val ⟨j, w⟩‖ :=
                    (L.compLpL 2 (volume.restrict Set.univ)).le_opNorm _
              _ ≤ ‖L‖ * ‖f.val ⟨j, w⟩‖ := by
                exact mul_le_mul_of_nonneg_right
                  (ContinuousLinearMap.norm_compLpL_le (L := L)) (norm_nonneg _)
          have hs := (sq_le_sq₀ (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
          simpa [mul_pow] using hs
        _ = ‖L‖ ^ 2 *
            (∑ w : DerivativeWord2 j.val, ‖f.val ⟨j, w⟩‖ ^ 2) := by rw [Finset.mul_sum]
    _ = ‖L‖ ^ 2 * (∑ j : Fin (K + 1), factorialWeight ρ j.val *
        ∑ w : DerivativeWord2 j.val, ‖f.val ⟨j, w⟩‖ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

def mapRawTorusJet {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {K : ℕ}
    (L : E →L[ℝ] F) (D : RawJet2 K E) : RawJet2 K F := fun a x => L (D a x)

theorem mapRawTorusJet_weak {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ}
    (L : E →L[ℝ] F) (D : RawJet2 K E) (hD : HasPeriodicOrderedWeakJet D) :
    HasPeriodicOrderedWeakJet (mapRawTorusJet L D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a n x
    change L (D a (x + AVenhance.latticeShift n)) = L (D a x)
    rw [hD.1 a n x]
  · intro a
    exact L.comp_memLp' (hD.2.1 a)
  · intro j w i e
    have h := hD.2.2 j w i (L.adjoint e)
    simpa only [mapRawTorusJet, ← ContinuousLinearMap.adjoint_inner_left] using h

def mapRawTorusFunction {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ}
    (L : E →L[ℝ] F) (f : TorusHkFunction K E) : TorusHkFunction K F :=
  ⟨mapRawTorusJet L f.jet, mapRawTorusJet_weak L f.jet f.hasPeriodicWeakJet⟩

def mapTorusHk {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ}
    (L : E →L[ℝ] F) (f : TorusHk K E) : TorusHk K F :=
  (mapRawTorusFunction L f.toFunction).toHk

theorem mapTorusHk_jet_eq_compLp {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ}
    (L : E →L[ℝ] F) (f : TorusHk K E) (a : JetIndex2 K) :
    (mapTorusHk L f).val a =
      (L.compLpL 2 (volume.restrict AVenhance.unitCube)) (f.val a) := by
  apply Lp.ext
  have hround := congrArg Subtype.val (TorusHk.toFunction_toHk f)
  change torusJetToL2 f.toFunction.jet f.toFunction.hasPeriodicWeakJet.2.1 = f.val at hround
  have hsrc : f.toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube] (fun x => f.val a x) :=
    (torusJetToL2_ae f.toFunction.jet f.toFunction.hasPeriodicWeakJet.2.1 a).symm.trans
      (Lp.ext_iff.mp (congrArg (fun z => z a) hround))
  have hout := torusJetToL2_ae (mapRawTorusJet L f.toFunction.jet)
    (mapRawTorusJet_weak L f.toFunction.jet f.toFunction.hasPeriodicWeakJet).2.1 a
  have hmap := ContinuousLinearMap.coeFn_compLpL L (f.val a)
  filter_upwards [hout, hsrc, hmap] with x ho hs hm
  exact ho.trans ((congrArg L hs).trans hm.symm)

theorem mapTorusHk_factorialNormSq_le {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ} (ρ : ℝ)
    (L : E →L[ℝ] F) (f : TorusHk K E) :
    factorialNormSq ρ (mapTorusHk L f).val ≤ ‖L‖ ^ 2 * factorialNormSq ρ f.val := by
  unfold factorialNormSq derivativeNormSq
  calc
    (∑ j : Fin (K + 1), factorialWeight ρ j.val *
        ∑ w : DerivativeWord2 j.val, ‖(mapTorusHk L f).val ⟨j, w⟩‖ ^ 2) ≤
      ∑ j : Fin (K + 1), factorialWeight ρ j.val *
        (‖L‖ ^ 2 * ∑ w : DerivativeWord2 j.val, ‖f.val ⟨j, w⟩‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (factorialWeight_nonneg ρ j.val)
      calc
        (∑ w : DerivativeWord2 j.val, ‖(mapTorusHk L f).val ⟨j, w⟩‖ ^ 2) ≤
            ∑ w : DerivativeWord2 j.val, ‖L‖ ^ 2 * ‖f.val ⟨j, w⟩‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro w _
          have hmap := mapTorusHk_jet_eq_compLp L f ⟨j, w⟩
          have hnorm : ‖(mapTorusHk L f).val ⟨j, w⟩‖ ≤
              ‖L‖ * ‖f.val ⟨j, w⟩‖ := by
            rw [hmap]
            calc
              ‖(L.compLpL 2 (volume.restrict AVenhance.unitCube)) (f.val ⟨j, w⟩)‖ ≤
                  ‖L.compLpL 2 (volume.restrict AVenhance.unitCube)‖ * ‖f.val ⟨j, w⟩‖ :=
                    (L.compLpL 2 (volume.restrict AVenhance.unitCube)).le_opNorm _
              _ ≤ ‖L‖ * ‖f.val ⟨j, w⟩‖ := by
                exact mul_le_mul_of_nonneg_right
                  (ContinuousLinearMap.norm_compLpL_le (L := L)) (norm_nonneg _)
          have hs := (sq_le_sq₀ (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
          simpa [mul_pow] using hs
        _ = ‖L‖ ^ 2 *
            (∑ w : DerivativeWord2 j.val, ‖f.val ⟨j, w⟩‖ ^ 2) := by rw [Finset.mul_sum]
    _ = ‖L‖ ^ 2 * (∑ j : Fin (K + 1), factorialWeight ρ j.val *
        ∑ w : DerivativeWord2 j.val, ‖f.val ⟨j, w⟩‖ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem mapPlaneHk_toFunction_jet_ae {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ}
    (L : E →L[ℝ] F) (f : PlaneHk Set.univ K E) (a : JetIndex2 K) :
    (mapPlaneHk L f).toFunction.jet a =ᵐ[volume.restrict Set.univ]
      fun x => L (f.toFunction.jet a x) := by
  change (mapPlaneHk L f).toFunction.jet a =ᵐ[volume.restrict Set.univ]
    mapRawPlaneJet L f.toFunction.jet a
  have h := PlaneHkFunction.toHk_toFunction_ae (mapRawPlaneFunction L f.toFunction) a
  exact h

theorem mapTorusHk_toFunction_jet_ae {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ}
    (L : E →L[ℝ] F) (f : TorusHk K E) (a : JetIndex2 K) :
    (mapTorusHk L f).toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => L (f.toFunction.jet a x) := by
  change (mapTorusHk L f).toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube]
    mapRawTorusJet L f.toFunction.jet a
  have h := TorusHkFunction.toHk_toFunction_ae (mapRawTorusFunction L f.toFunction) a
  exact h

theorem planeMulCoefficient_toFunction_value_ae {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ}
    (w : PlaneHk Set.univ K E) (C : Vec 2 → E →L[ℝ] F)
    (hC : ContDiff ℝ (K : ℕ) C) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) :
    (w.mulCoefficient C hC hb).toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict Set.univ]
      fun x => C x (w.toFunction.jet (valueIndex2 K) x) := by
  have h := PlaneHkFunction.toHk_toFunction_ae
    (w.toFunction.mulCoefficient C hC hb) (valueIndex2 K)
  have hraw : (w.mulCoefficient C hC hb).toFunction.jet (valueIndex2 K) =ᵐ[
      volume.restrict Set.univ]
      multiplicationRawJet C w.toFunction.jet (valueIndex2 K) := by
    simpa [PlaneHk.mulCoefficient, PlaneHkFunction.mulCoefficient] using h
  filter_upwards [hraw] with x hx
  exact hx.trans (multiplicationRawJet_value C w.toFunction.jet x)

theorem torusMulCoefficient_toFunction_value_ae {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ}
    (w : TorusHk K E) (C : Vec 2 → E →L[ℝ] F)
    (hC : ContDiff ℝ (K : ℕ) C) (hp : AVenhance.IsZ2Periodic C)
    {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) :
    (w.mulCoefficient C hC hp hb).toFunction.jet (valueIndex2 K) =ᵐ[
      volume.restrict AVenhance.unitCube]
      fun x => C x (w.toFunction.jet (valueIndex2 K) x) := by
  have h := TorusHkFunction.toHk_toFunction_ae
    (w.toFunction.mulCoefficient C hC hp hb) (valueIndex2 K)
  have hraw : (w.mulCoefficient C hC hp hb).toFunction.jet (valueIndex2 K) =ᵐ[
      volume.restrict AVenhance.unitCube]
      multiplicationRawJet C w.toFunction.jet (valueIndex2 K) := by
    simpa [TorusHk.mulCoefficient, TorusHkFunction.mulCoefficient] using h
  filter_upwards [hraw] with x hx
  exact hx.trans (multiplicationRawJet_value C w.toFunction.jet x)

def castPlaneHk {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K L : ℕ} (h : K = L) (f : PlaneHk Set.univ K E) : PlaneHk Set.univ L E :=
  cast (congrArg (fun n => PlaneHk Set.univ n E) h) f

theorem castPlaneHk_valueIndex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K L : ℕ} (h : K = L) (f : PlaneHk Set.univ K E) :
    (castPlaneHk h f).val (valueIndex2 L) = f.val (valueIndex2 K) := by
  cases h
  rfl

theorem castPlaneHk_toFunction_jet {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K L : ℕ} (h : K = L) (f : PlaneHk Set.univ K E) (a : JetIndex2 L) :
    (castPlaneHk h f).toFunction.jet a =
      f.toFunction.jet (cast (congrArg JetIndex2 h.symm) a) := by
  cases h
  rfl

def castTorusHk {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K L : ℕ} (h : K = L) (f : TorusHk K E) : TorusHk L E :=
  cast (congrArg (fun n => TorusHk n E) h) f

theorem castTorusHk_valueIndex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K L : ℕ} (h : K = L) (f : TorusHk K E) :
    (castTorusHk h f).val (valueIndex2 L) = f.val (valueIndex2 K) := by
  cases h
  rfl

theorem castTorusHk_toFunction_jet {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K L : ℕ} (h : K = L) (f : TorusHk K E) (a : JetIndex2 L) :
    (castTorusHk h f).toFunction.jet a =
      f.toFunction.jet (cast (congrArg JetIndex2 h.symm) a) := by
  cases h
  rfl

theorem planeHk_toFunction_jet_ae {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K : ℕ} (f : PlaneHk Set.univ K E) (a : JetIndex2 K) :
    f.toFunction.jet a =ᵐ[volume.restrict Set.univ] fun x => f.val a x := by
  rfl

theorem torusHk_toFunction_jet_ae {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K : ℕ} (f : TorusHk K E) (a : JetIndex2 K) :
    f.toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube] fun x => f.val a x := by
  simpa only [TorusHk.toFunction] using periodicJetRepresentative_ae f.val a

theorem truncatePlaneHk_toFunction_jet_ae {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K L : ℕ} (hKL : K ≤ L) (f : PlaneHk Set.univ L E) (a : JetIndex2 K) :
    (truncatePlaneHk hKL f).toFunction.jet a =ᵐ[volume.restrict Set.univ]
      f.toFunction.jet (truncateJetIndex hKL a) := by
  change (fun x => (truncatePlaneHk hKL f).val a x) =ᵐ[volume.restrict Set.univ]
    fun x => f.val (truncateJetIndex hKL a) x
  exact Lp.ext_iff.mp (truncatePlaneHk_apply hKL f a)

theorem truncateTorusHk_toFunction_jet_ae {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K L : ℕ} (hKL : K ≤ L) (f : TorusHk L E) (a : JetIndex2 K) :
    (truncateTorusHk hKL f).toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube]
      f.toFunction.jet (truncateJetIndex hKL a) := by
  have hleft := periodicJetRepresentative_ae (truncateTorusHk hKL f).val a
  have hmid := Lp.ext_iff.mp (truncateTorusHk_apply hKL f a)
  have hright := (periodicJetRepresentative_ae f.val (truncateJetIndex hKL a)).symm
  simpa only [TorusHk.toFunction] using hleft.trans (hmid.trans hright)

def tensorEntryLinearMap {J E : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (j : J) :
    E →ₗ[ℝ] PiLp 2 (fun _ : J => E) where
  toFun := fun x => PiLp.single (β := fun _ : J => E) 2 j x
  map_add' := by intro x y; exact PiLp.single_add (β := fun _ : J => E) 2 j
  map_smul' := by
    intro c x
    apply PiLp.ext
    intro k
    by_cases hkj : k = j
    · subst k
      simp
    · simp [hkj]

def tensorEntryCLM {J E : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (j : J) :
    E →L[ℝ] PiLp 2 (fun _ : J => E) :=
  (tensorEntryLinearMap (J := J) (E := E) j).mkContinuous 1 (by
    intro x
    change ‖PiLp.single (β := fun _ : J => E) 2 j x‖ ≤ 1 * ‖x‖
    rw [PiLp.norm_single, one_mul])

def planeFamilyTensor {J E : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {K : ℕ}
    (w : J → PlaneHk Set.univ K E) : PlaneHk Set.univ K (PiLp 2 (fun _ : J => E)) :=
  ∑ a, mapPlaneHk (tensorEntryCLM (J := J) (E := E) a) (w a)

theorem planeFamilyTensor_jet {J E : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {K : ℕ}
    (w : J → PlaneHk Set.univ K E) (a : JetIndex2 K) :
    (planeFamilyTensor w).val a =
      ∑ j, (tensorEntryCLM (J := J) (E := E) j).compLpL 2
        (volume.restrict Set.univ) ((w j).val a) := by
  simp [planeFamilyTensor, mapPlaneHk_jet_eq_compLp]

theorem planeFamilyTensor_jet_normSq {J E : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {K : ℕ}
    (w : J → PlaneHk Set.univ K E) (a : JetIndex2 K) :
    ‖(planeFamilyTensor w).val a‖ ^ 2 = ∑ j, ‖(w j).val a‖ ^ 2 := by
  rw [planeFamilyTensor_jet, ← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum]
  have horth (j k : J) (u v : ComponentL2 (volume.restrict Set.univ) E) :
      inner ℝ ((tensorEntryCLM (J := J) (E := E) j).compLpL 2
          (volume.restrict Set.univ) u)
          ((tensorEntryCLM (J := J) (E := E) k).compLpL 2
          (volume.restrict Set.univ) v) = if j = k then inner ℝ u v else 0 := by
    rw [L2.inner_def]
    have hp : (fun x => inner ℝ
        (((tensorEntryCLM (J := J) (E := E) j).compLpL 2
          (volume.restrict Set.univ) u) x)
        (((tensorEntryCLM (J := J) (E := E) k).compLpL 2
          (volume.restrict Set.univ) v) x)) =ᵐ[volume.restrict Set.univ]
        fun x => if j = k then inner ℝ (u x) (v x) else 0 := by
      filter_upwards [ContinuousLinearMap.coeFn_compLpL
        (tensorEntryCLM (J := J) (E := E) j) u,
        ContinuousLinearMap.coeFn_compLpL (tensorEntryCLM (J := J) (E := E) k) v] with x hu hv
      rw [hu, hv]
      change inner ℝ (PiLp.single (β := fun _ : J => E) 2 j (u x))
        (PiLp.single (β := fun _ : J => E) 2 k (v x)) = _
      rw [PiLp.inner_apply]
      simp only [PiLp.ofLp_single, Pi.single_apply]
      change (∑ l : J, inner ℝ (if l = j then u x else 0) (if l = k then v x else 0)) = _
      have hs (l : J) : inner ℝ (if l = j then u x else 0) (if l = k then v x else 0) =
          if l = j then (if j = k then inner ℝ (u x) (v x) else 0) else 0 := by
        by_cases hlj : l = j <;> by_cases hlk : l = k <;> simp_all
      simp_rw [hs]
      simp
    rw [integral_congr_ae hp]
    by_cases hjk : j = k <;> simp [hjk, L2.inner_def]
  simp_rw [horth]
  simp

theorem planeFamilyTensor_factorialNormSq {J E : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {K : ℕ}
    (ρ : ℝ) (w : J → PlaneHk Set.univ K E) :
    factorialNormSq ρ (planeFamilyTensor w).val = ∑ j, factorialNormSq ρ (w j).val := by
  unfold factorialNormSq derivativeNormSq
  simp_rw [planeFamilyTensor_jet_normSq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm, Finset.mul_sum]

def torusFamilyTensor {J E : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {K : ℕ}
    (w : J → TorusHk K E) : TorusHk K (PiLp 2 (fun _ : J => E)) :=
  ∑ a, mapTorusHk (tensorEntryCLM (J := J) (E := E) a) (w a)

theorem torusFamilyTensor_jet {J E : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {K : ℕ}
    (w : J → TorusHk K E) (a : JetIndex2 K) :
    (torusFamilyTensor w).val a =
      ∑ j, (tensorEntryCLM (J := J) (E := E) j).compLpL 2
        (volume.restrict AVenhance.unitCube) ((w j).val a) := by
  simp [torusFamilyTensor, mapTorusHk_jet_eq_compLp]

theorem torusTensorEntryLp_inner {J E : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (a b : J) (u v : ComponentL2 (volume.restrict AVenhance.unitCube) E) :
    inner ℝ ((tensorEntryCLM (J := J) (E := E) a).compLpL 2
      (volume.restrict AVenhance.unitCube) u)
      ((tensorEntryCLM (J := J) (E := E) b).compLpL 2
      (volume.restrict AVenhance.unitCube) v) = if a = b then inner ℝ u v else 0 := by
  rw [L2.inner_def]
  have hpoint : (fun x => inner ℝ
      (((tensorEntryCLM (J := J) (E := E) a).compLpL 2
        (volume.restrict AVenhance.unitCube) u) x)
      (((tensorEntryCLM (J := J) (E := E) b).compLpL 2
        (volume.restrict AVenhance.unitCube) v) x)) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => if a = b then inner ℝ (u x) (v x) else 0 := by
    filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (tensorEntryCLM (J := J) (E := E) a) u,
      ContinuousLinearMap.coeFn_compLpL (tensorEntryCLM (J := J) (E := E) b) v] with x hu hv
    rw [hu, hv]
    change inner ℝ (PiLp.single (β := fun _ : J => E) 2 a (u x))
      (PiLp.single (β := fun _ : J => E) 2 b (v x)) = _
    rw [PiLp.inner_apply]
    simp only [PiLp.ofLp_single, Pi.single_apply]
    change (∑ j : J, inner ℝ (if j = a then u x else 0) (if j = b then v x else 0)) = _
    have hs (j : J) : inner ℝ (if j = a then u x else 0) (if j = b then v x else 0) =
        if j = a then (if a = b then inner ℝ (u x) (v x) else 0) else 0 := by
      by_cases hja : j = a <;> by_cases hjb : j = b <;> simp_all
    simp_rw [hs]
    simp
  rw [integral_congr_ae hpoint]
  by_cases hab : a = b <;> simp [hab, L2.inner_def]

theorem torusFamilyTensor_jet_normSq {J E : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {K : ℕ}
    (w : J → TorusHk K E) (a : JetIndex2 K) :
    ‖(torusFamilyTensor w).val a‖ ^ 2 = ∑ j, ‖(w j).val a‖ ^ 2 := by
  rw [torusFamilyTensor_jet, ← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, torusTensorEntryLp_inner]
  simp

theorem torusFamilyTensor_factorialNormSq {J E : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {K : ℕ}
    (ρ : ℝ) (w : J → TorusHk K E) :
    factorialNormSq ρ (torusFamilyTensor w).val = ∑ j, factorialNormSq ρ (w j).val := by
  unfold factorialNormSq derivativeNormSq
  simp_rw [torusFamilyTensor_jet_normSq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm, Finset.mul_sum]

def planeDerivativeTensor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
    {K r : ℕ} (f : PlaneHk Set.univ (K + r) E) :
    PlaneHk Set.univ K (PiLp 2 (fun _ : DerivativeWord2 r => E)) :=
  planeFamilyTensor fun a => derivativePlaneHk a f

theorem planeDerivativeTensor_factorialNormSq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {K r : ℕ} (ρ : ℝ)
    (f : PlaneHk Set.univ (K + r) E) :
    factorialNormSq ρ (planeDerivativeTensor (K := K) (r := r) f).val =
      derivFactorialNormSq r ρ f.val := by
  rw [planeDerivativeTensor, planeFamilyTensor_factorialNormSq]
  change (∑ a : DerivativeWord2 r,
    factorialNormSq ρ (derivativeJet a f.val)) = derivFactorialNormSq r ρ f.val
  rw [derivativeArray_factorialNormSq]
  unfold derivFactorialNormSq derivativeNormSq
  apply Finset.sum_congr rfl
  intro j _
  have hidx : shiftedJetOrder (K := K) (r := r) j =
      ⟨j.val + r, by have := j.isLt; omega⟩ := by
    apply Fin.ext
    simp [shiftedJetOrder, Nat.add_comm]
  rw [hidx]

theorem planeDerivativeTensor_base_ae {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {K r : ℕ} (f : PlaneHk Set.univ (K + r) E) :
    (planeDerivativeTensor (K := K) (r := r) f).toFunction.jet (valueIndex2 K) =ᵐ[
      volume.restrict Set.univ] fun x => WithLp.toLp 2
        (fun a : DerivativeWord2 r => f.toFunction.jet
          (prefixJetIndex a (valueIndex2 K)) x) := by
  classical
  let T := planeDerivativeTensor (K := K) (r := r) f
  have hval : T.val (valueIndex2 K) =
      ∑ a : DerivativeWord2 r,
        (tensorEntryCLM (J := DerivativeWord2 r) (E := E) a).compLpL 2
          (volume.restrict Set.univ)
          ((derivativePlaneHk (K := K) a f).val (valueIndex2 K)) := by
    simpa [T, planeDerivativeTensor] using
      (planeFamilyTensor_jet (fun a : DerivativeWord2 r => derivativePlaneHk a f)
        (valueIndex2 K))
  have hvalAE := Lp.ext_iff.mp hval
  have hcomp (a : DerivativeWord2 r) :
      (tensorEntryCLM (J := DerivativeWord2 r) (E := E) a).compLpL 2
          (volume.restrict Set.univ)
          ((derivativePlaneHk (K := K) a f).val (valueIndex2 K)) =ᵐ[
        volume.restrict Set.univ] fun x =>
          tensorEntryCLM (J := DerivativeWord2 r) (E := E) a
            ((derivativePlaneHk (K := K) a f).val (valueIndex2 K) x) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  have hderiv (a : DerivativeWord2 r) :
      (derivativePlaneHk (K := K) a f).toFunction.jet (valueIndex2 K) =ᵐ[
        volume.restrict Set.univ] fun x => f.toFunction.jet
          (prefixJetIndex a (valueIndex2 K)) x := by
    have hleft := planeHk_toFunction_jet_ae
      (derivativePlaneHk (K := K) a f) (valueIndex2 K)
    have hright := planeHk_toFunction_jet_ae f (prefixJetIndex a (valueIndex2 K))
    filter_upwards [hleft, hright] with x hl hr
    calc
      (derivativePlaneHk (K := K) a f).toFunction.jet (valueIndex2 K) x =
          (derivativePlaneHk (K := K) a f).val (valueIndex2 K) x := hl
      _ = f.val (prefixJetIndex a (valueIndex2 K)) x := by rw [derivativePlaneHk_apply]
      _ = f.toFunction.jet (prefixJetIndex a (valueIndex2 K)) x := hr.symm
  have hall : ∀ᵐ x ∂(volume.restrict Set.univ), ∀ a : DerivativeWord2 r,
      (tensorEntryCLM (J := DerivativeWord2 r) (E := E) a).compLpL 2
        (volume.restrict Set.univ) ((derivativePlaneHk (K := K) a f).val (valueIndex2 K)) x =
      tensorEntryCLM (J := DerivativeWord2 r) (E := E) a
        (f.toFunction.jet (prefixJetIndex a (valueIndex2 K)) x) := by
    apply ae_all_iff.2
    intro a
    have hrep := planeHk_toFunction_jet_ae
      (derivativePlaneHk (K := K) a f) (valueIndex2 K)
    filter_upwards [hcomp a, hrep, hderiv a] with x hc hr hd
    calc
      (tensorEntryCLM (J := DerivativeWord2 r) (E := E) a).compLpL 2
          (volume.restrict Set.univ)
          ((derivativePlaneHk (K := K) a f).val (valueIndex2 K)) x =
        tensorEntryCLM (J := DerivativeWord2 r) (E := E) a
          ((derivativePlaneHk (K := K) a f).val (valueIndex2 K) x) := hc
      _ = tensorEntryCLM (J := DerivativeWord2 r) (E := E) a
          ((derivativePlaneHk (K := K) a f).toFunction.jet (valueIndex2 K) x) := by rw [hr]
      _ = tensorEntryCLM (J := DerivativeWord2 r) (E := E) a
          (f.toFunction.jet (prefixJetIndex a (valueIndex2 K)) x) := by rw [hd]
  have hsumAE : (fun x =>
      (∑ a : DerivativeWord2 r,
        (tensorEntryCLM (J := DerivativeWord2 r) (E := E) a).compLpL 2
          (volume.restrict Set.univ)
          ((derivativePlaneHk (K := K) a f).val (valueIndex2 K))) x) =ᵐ[
        volume.restrict Set.univ] fun x =>
        ∑ a : DerivativeWord2 r,
          (tensorEntryCLM (J := DerivativeWord2 r) (E := E) a).compLpL 2
            (volume.restrict Set.univ)
            ((derivativePlaneHk (K := K) a f).val (valueIndex2 K)) x :=
    Lp.coeFn_fun_finsetSum Finset.univ _
  have hT := planeHk_toFunction_jet_ae T (valueIndex2 K)
  filter_upwards [hvalAE, hsumAE, hall, hT] with x hv hs ha ht
  calc
    T.toFunction.jet (valueIndex2 K) x = T.val (valueIndex2 K) x := ht
    _ = ∑ a : DerivativeWord2 r,
        (tensorEntryCLM (J := DerivativeWord2 r) (E := E) a).compLpL 2
          (volume.restrict Set.univ)
          ((derivativePlaneHk (K := K) a f).val (valueIndex2 K)) x := hv.trans hs
    _ = ∑ a : DerivativeWord2 r, tensorEntryCLM (J := DerivativeWord2 r)
          (E := E) a (f.toFunction.jet (prefixJetIndex a (valueIndex2 K)) x) := by
      apply Finset.sum_congr rfl
      intro a _
      exact ha a
    _ = WithLp.toLp 2 (fun a : DerivativeWord2 r =>
          f.toFunction.jet (prefixJetIndex a (valueIndex2 K)) x) := by
      apply PiLp.ext
      intro b
      change (∑ a : DerivativeWord2 r,
          tensorEntryCLM (J := DerivativeWord2 r) (E := E) a
            (f.toFunction.jet (prefixJetIndex a (valueIndex2 K)) x)) b = _
      simp [tensorEntryCLM, tensorEntryLinearMap]

theorem planeGradientFactorialNormSq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {K : ℕ} (ρ : ℝ) (V : PlaneHk Set.univ (K + 1) E) :
    ∑ q : Fin 2, factorialNormSq ρ
        (derivativePlaneHk (K := K) (r := 1) (fun _ : Fin 1 => q) V).val =
      gradFactorialNormSq ρ V.val := by
  have hArray := derivativeArray_factorialNormSq (K := K) (r := 1) ρ V.val
  have hval : ∀ q : Fin 2,
      (derivativePlaneHk (K := K) (r := 1) (fun _ : Fin 1 => q) V).val =
        derivativeJet (fun _ : Fin 1 => q) V.val := by intro q; rfl
  have hq : (∑ q : Fin 2, factorialNormSq ρ
      (derivativePlaneHk (K := K) (r := 1) (fun _ : Fin 1 => q) V).val) =
        ∑ a : DerivativeWord2 1, factorialNormSq ρ (derivativeJet a V.val) := by
    apply Fintype.sum_equiv derivativeWordOneEquiv
    intro q
    rw [hval]
    rfl
  rw [hq, hArray]
  unfold gradFactorialNormSq derivativeNormSq
  apply Finset.sum_congr rfl
  intro j _
  have hidx : shiftedJetOrder (K := K) (r := 1) j =
      ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
    apply Fin.ext
    simp [shiftedJetOrder, Nat.add_comm]
  rw [hidx]

theorem torusDerivFactorialNormSq_succ {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {K m : ℕ} (ρ : ℝ)
    (Y : TorusHk (K + m + 1) E) (g : Fin 2 → TorusHk (K + m) E)
    (hg : ∀ q, derivativeTorusHk (K := K + m) (r := 1)
      (fun _ : Fin 1 => q) Y = g q) :
    derivFactorialNormSq (m + 1) ρ Y.val =
      ∑ q, derivFactorialNormSq m ρ (g q).val := by
  classical
  let lowOrder (n : Fin (K + 1)) : Fin (K + m + 1) := ⟨n.val + m, by omega⟩
  let highOrder (n : Fin (K + 1)) : Fin (K + m + 2) :=
    ⟨1 + (n.val + m), by omega⟩
  have hwords (n : Fin (K + 1)) :
      (∑ q : Fin 2, ∑ v : DerivativeWord2 (n.val + m),
        ‖(g q).val (⟨lowOrder n, v⟩ : JetIndex2 (K + m))‖ ^ 2) =
      ∑ w : DerivativeWord2 (1 + (n.val + m)),
        ‖Y.val (⟨highOrder n, w⟩ : JetIndex2 (K + m + 1))‖ ^ 2 := by
    let jl : Fin (K + m + 1) := ⟨n.val + m, by omega⟩
    let jh : Fin (K + m + 2) := ⟨1 + (n.val + m), by omega⟩
    calc
      (∑ q : Fin 2, ∑ v : DerivativeWord2 (n.val + m),
          ‖(g q).val (⟨jl, v⟩ : JetIndex2 (K + m))‖ ^ 2) =
        ∑ p : Fin 2 × DerivativeWord2 (n.val + m),
          ‖(g p.1).val (⟨jl, p.2⟩ : JetIndex2 (K + m))‖ ^ 2 := by
            rw [Fintype.sum_prod_type]
      _ = ∑ w : DerivativeWord2 (1 + (n.val + m)),
          ‖Y.val (⟨jh, w⟩ : JetIndex2 (K + m + 1))‖ ^ 2 := by
        apply Fintype.sum_equiv (derivativeWordHeadTailEquiv (n.val + m))
        intro p
        have hidx : prefixJetIndex (fun _ : Fin 1 => p.1)
            (⟨jl, p.2⟩ : JetIndex2 (K + m)) =
            (⟨jh, Fin.append (fun _ : Fin 1 => p.1) p.2⟩ : JetIndex2 (K + m + 1)) := by
          apply Sigma.ext
          · apply Fin.ext
            simp [prefixJetIndex, jl, jh]
          · rfl
        have h := congrArg (fun z : TorusHk (K + m) E =>
          z.val (⟨jl, p.2⟩ : JetIndex2 (K + m))) (hg p.1)
        rw [derivativeTorusHk_apply] at h
        rw [hidx] at h
        exact (congrArg (fun z : Lp E 2 (volume.restrict AVenhance.unitCube) => ‖z‖ ^ 2) h).symm
  unfold derivFactorialNormSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  have hlen : n.val + (m + 1) = 1 + (n.val + m) := by omega
  let hfun : DerivativeWord2 (n.val + (m + 1)) =
      DerivativeWord2 (1 + (n.val + m)) := congrArg DerivativeWord2 hlen
  let e : DerivativeWord2 (n.val + (m + 1)) ≃ DerivativeWord2 (1 + (n.val + m)) :=
    Equiv.cast hfun
  have hcast :
    ∑ w : DerivativeWord2 (n.val + (m + 1)),
        ‖Y.val ⟨⟨n.val + (m + 1), by omega⟩, w⟩‖ ^ 2 =
      ∑ w : DerivativeWord2 (1 + (n.val + m)),
        ‖Y.val ⟨⟨1 + (n.val + m), by omega⟩, w⟩‖ ^ 2 := by
          apply Fintype.sum_equiv e
          intro w
          let jlo : Fin (K + (m + 1) + 1) := ⟨n.val + (m + 1), by omega⟩
          let jhi : Fin (K + (m + 1) + 1) := ⟨1 + (n.val + m), by omega⟩
          have hidx :
              (⟨jlo, w⟩ : JetIndex2 (K + (m + 1))) = ⟨jhi, e w⟩ := by
            have hfirst : jlo = jhi := Fin.ext hlen
            refine Sigma.ext hfirst ?_
            exact (cast_heq hfun w).symm
          rw [hidx]
  rw [hcast, ← Finset.mul_sum, ← hwords n]

theorem truncateTorus_derivative_commute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {K L : ℕ} (hKL : K ≤ L)
    (Y : TorusHk (L + 1) E) (q : Fin 2) :
    derivativeTorusHk (K := K) (r := 1) (fun _ : Fin 1 => q)
        (truncateTorusHk (Nat.succ_le_succ hKL) Y) =
      truncateTorusHk hKL
        (derivativeTorusHk (K := L) (r := 1) (fun _ : Fin 1 => q) Y) := by
  apply TorusHk.ext_value
  have hidx :
      truncateJetIndex (Nat.succ_le_succ hKL)
          (prefixJetIndex (fun _ : Fin 1 => q) (valueIndex2 K)) =
        prefixJetIndex (fun _ : Fin 1 => q) (truncateJetIndex hKL (valueIndex2 K)) := by
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · rfl
  simp only [derivativeTorusHk_apply, truncateTorusHk_apply]
  rw [hidx]

theorem torusGradientFactorialNormSq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {K : ℕ} (ρ : ℝ) (V : TorusHk (K + 1) E) :
    ∑ q : Fin 2, factorialNormSq ρ
        (derivativeTorusHk (K := K) (r := 1) (fun _ : Fin 1 => q) V).val =
      gradFactorialNormSq ρ V.val := by
  have hArray := derivativeArray_factorialNormSq (K := K) (r := 1) ρ V.val
  have hval : ∀ q : Fin 2,
      (derivativeTorusHk (K := K) (r := 1) (fun _ : Fin 1 => q) V).val =
        derivativeJet (fun _ : Fin 1 => q) V.val := by intro q; rfl
  have hq : (∑ q : Fin 2, factorialNormSq ρ
      (derivativeTorusHk (K := K) (r := 1) (fun _ : Fin 1 => q) V).val) =
        ∑ a : DerivativeWord2 1, factorialNormSq ρ (derivativeJet a V.val) := by
    apply Fintype.sum_equiv derivativeWordOneEquiv
    intro q
    rw [hval]
    rfl
  rw [hq, hArray]
  unfold gradFactorialNormSq derivativeNormSq
  apply Finset.sum_congr rfl
  intro j _
  have hidx : shiftedJetOrder (K := K) (r := 1) j =
      ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
    apply Fin.ext
    simp [shiftedJetOrder, Nat.add_comm]
  rw [hidx]

def torusDerivativeTensor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
    {K r : ℕ} (f : TorusHk (K + r) E) :
    TorusHk K (PiLp 2 (fun _ : DerivativeWord2 r => E)) :=
  torusFamilyTensor fun a => derivativeTorusHk a f

theorem torusDerivativeTensor_factorialNormSq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {K r : ℕ} (ρ : ℝ)
    (f : TorusHk (K + r) E) :
    factorialNormSq ρ (torusDerivativeTensor (K := K) (r := r) f).val =
      derivFactorialNormSq r ρ f.val := by
  rw [torusDerivativeTensor, torusFamilyTensor_factorialNormSq]
  change (∑ a : DerivativeWord2 r,
    factorialNormSq ρ (derivativeJet a f.val)) = derivFactorialNormSq r ρ f.val
  rw [derivativeArray_factorialNormSq]
  unfold derivFactorialNormSq derivativeNormSq
  apply Finset.sum_congr rfl
  intro j _
  have hidx : shiftedJetOrder (K := K) (r := r) j =
      ⟨j.val + r, by have := j.isLt; omega⟩ := by
    apply Fin.ext
    simp [shiftedJetOrder, Nat.add_comm]
  rw [hidx]

theorem torusDerivativeTensor_base_ae {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {K r : ℕ} (f : TorusHk (K + r) E) :
    (torusDerivativeTensor (K := K) (r := r) f).toFunction.jet (valueIndex2 K) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => WithLp.toLp 2
        (fun a : DerivativeWord2 r => f.toFunction.jet
          (prefixJetIndex a (valueIndex2 K)) x) := by
  classical
  let T := torusDerivativeTensor (K := K) (r := r) f
  have hval : T.val (valueIndex2 K) =
      ∑ a : DerivativeWord2 r,
        (tensorEntryCLM (J := DerivativeWord2 r) (E := E) a).compLpL 2
          (volume.restrict AVenhance.unitCube)
          ((derivativeTorusHk (K := K) a f).val (valueIndex2 K)) := by
    simpa [T, torusDerivativeTensor] using
      (torusFamilyTensor_jet (fun a : DerivativeWord2 r => derivativeTorusHk a f)
        (valueIndex2 K))
  have hvalAE := Lp.ext_iff.mp hval
  have hcomp (a : DerivativeWord2 r) :
      (tensorEntryCLM (J := DerivativeWord2 r) (E := E) a).compLpL 2
          (volume.restrict AVenhance.unitCube)
          ((derivativeTorusHk (K := K) a f).val (valueIndex2 K)) =ᵐ[
        volume.restrict AVenhance.unitCube] fun x =>
          tensorEntryCLM (J := DerivativeWord2 r) (E := E) a
            ((derivativeTorusHk (K := K) a f).val (valueIndex2 K) x) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  have hderiv (a : DerivativeWord2 r) :
      (derivativeTorusHk (K := K) a f).toFunction.jet (valueIndex2 K) =ᵐ[
        volume.restrict AVenhance.unitCube] fun x => f.toFunction.jet
          (prefixJetIndex a (valueIndex2 K)) x := by
    have hleft := torusHk_toFunction_jet_ae
      (derivativeTorusHk (K := K) a f) (valueIndex2 K)
    have hright := torusHk_toFunction_jet_ae f (prefixJetIndex a (valueIndex2 K))
    filter_upwards [hleft, hright] with x hl hr
    calc
      (derivativeTorusHk (K := K) a f).toFunction.jet (valueIndex2 K) x =
          (derivativeTorusHk (K := K) a f).val (valueIndex2 K) x := hl
      _ = f.val (prefixJetIndex a (valueIndex2 K)) x := by rw [derivativeTorusHk_apply]
      _ = f.toFunction.jet (prefixJetIndex a (valueIndex2 K)) x := hr.symm
  have hall : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ a : DerivativeWord2 r,
      (tensorEntryCLM (J := DerivativeWord2 r) (E := E) a).compLpL 2
        (volume.restrict AVenhance.unitCube)
        ((derivativeTorusHk (K := K) a f).val (valueIndex2 K)) x =
      tensorEntryCLM (J := DerivativeWord2 r) (E := E) a
        (f.toFunction.jet (prefixJetIndex a (valueIndex2 K)) x) := by
    apply ae_all_iff.2
    intro a
    have hrep := torusHk_toFunction_jet_ae
      (derivativeTorusHk (K := K) a f) (valueIndex2 K)
    filter_upwards [hcomp a, hrep, hderiv a] with x hc hr hd
    calc
      (tensorEntryCLM (J := DerivativeWord2 r) (E := E) a).compLpL 2
          (volume.restrict AVenhance.unitCube)
          ((derivativeTorusHk (K := K) a f).val (valueIndex2 K)) x =
        tensorEntryCLM (J := DerivativeWord2 r) (E := E) a
          ((derivativeTorusHk (K := K) a f).val (valueIndex2 K) x) := hc
      _ = tensorEntryCLM (J := DerivativeWord2 r) (E := E) a
          ((derivativeTorusHk (K := K) a f).toFunction.jet (valueIndex2 K) x) := by rw [hr]
      _ = tensorEntryCLM (J := DerivativeWord2 r) (E := E) a
          (f.toFunction.jet (prefixJetIndex a (valueIndex2 K)) x) := by rw [hd]
  have hsumAE : (fun x =>
      (∑ a : DerivativeWord2 r,
        (tensorEntryCLM (J := DerivativeWord2 r) (E := E) a).compLpL 2
          (volume.restrict AVenhance.unitCube)
          ((derivativeTorusHk (K := K) a f).val (valueIndex2 K))) x) =ᵐ[
        volume.restrict AVenhance.unitCube] fun x =>
        ∑ a : DerivativeWord2 r,
          (tensorEntryCLM (J := DerivativeWord2 r) (E := E) a).compLpL 2
            (volume.restrict AVenhance.unitCube)
            ((derivativeTorusHk (K := K) a f).val (valueIndex2 K)) x :=
    Lp.coeFn_fun_finsetSum Finset.univ _
  have hT := torusHk_toFunction_jet_ae T (valueIndex2 K)
  filter_upwards [hvalAE, hsumAE, hall, hT] with x hv hs ha ht
  calc
    T.toFunction.jet (valueIndex2 K) x = T.val (valueIndex2 K) x := ht
    _ = ∑ a : DerivativeWord2 r,
        (tensorEntryCLM (J := DerivativeWord2 r) (E := E) a).compLpL 2
          (volume.restrict AVenhance.unitCube)
          ((derivativeTorusHk (K := K) a f).val (valueIndex2 K)) x := hv.trans hs
    _ = ∑ a : DerivativeWord2 r, tensorEntryCLM (J := DerivativeWord2 r)
          (E := E) a (f.toFunction.jet (prefixJetIndex a (valueIndex2 K)) x) := by
      apply Finset.sum_congr rfl
      intro a _
      exact ha a
    _ = WithLp.toLp 2 (fun a : DerivativeWord2 r =>
          f.toFunction.jet (prefixJetIndex a (valueIndex2 K)) x) := by
      apply PiLp.ext
      intro b
      change (∑ a : DerivativeWord2 r,
          tensorEntryCLM (J := DerivativeWord2 r) (E := E) a
            (f.toFunction.jet (prefixJetIndex a (valueIndex2 K)) x)) b = _
      simp [tensorEntryCLM, tensorEntryLinearMap]

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! The Sobolev coefficient product as a bounded linear map.
This packages the multiplier for the kernel operator construction. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ}
variable (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
  (hp : AVenhance.IsZ2Periodic C) (A : Fin (K + 1) → ℝ)
  (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l)

def torusMultiplierLinearMap : TorusHk K E →ₗ[ℝ] TorusHk K F where
  toFun w := w.mulCoefficient C hC hp hb
  map_add' w z := by
    apply TorusHk.ext_value
    apply Lp.ext
    have hi : (w + z).val (valueIndex2 K) = w.val (valueIndex2 K) + z.val (valueIndex2 K) := rfl
    have ho : (w.mulCoefficient C hC hp hb + z.mulCoefficient C hC hp hb).val (valueIndex2 K) =
        (w.mulCoefficient C hC hp hb).val (valueIndex2 K) +
          (z.mulCoefficient C hC hp hb).val (valueIndex2 K) := rfl
    rw [ho]
    filter_upwards [torusMulCoefficient_value_ae (w + z) C hC hp hb,
      torusMulCoefficient_value_ae w C hC hp hb, torusMulCoefficient_value_ae z C hC hp hb,
      Lp.coeFn_add (w.val (valueIndex2 K)) (z.val (valueIndex2 K)),
      Lp.coeFn_add ((w.mulCoefficient C hC hp hb).val (valueIndex2 K))
        ((z.mulCoefficient C hC hp hb).val (valueIndex2 K))] with x hx hw hz hin hout
    rw [hx, hi, hin, hout]
    simp only [Pi.add_apply]
    rw [hw, hz]
    exact (C x).map_add _ _
  map_smul' q w := by
    simp only [RingHom.id_apply]
    apply TorusHk.ext_value
    apply Lp.ext
    have hi : (q • w).val (valueIndex2 K) = q • w.val (valueIndex2 K) := rfl
    have ho : (q • w.mulCoefficient C hC hp hb).val (valueIndex2 K) =
        q • (w.mulCoefficient C hC hp hb).val (valueIndex2 K) := rfl
    rw [ho]
    filter_upwards [torusMulCoefficient_value_ae (q • w) C hC hp hb,
      torusMulCoefficient_value_ae w C hC hp hb,
      Lp.coeFn_smul q (w.val (valueIndex2 K)),
      Lp.coeFn_smul q ((w.mulCoefficient C hC hp hb).val (valueIndex2 K))] with x hx hw hin hout
    rw [hx, hi, hin, hout]
    simp only [Pi.smul_apply]
    rw [hw]
    exact (C x).map_smul _ _

omit [FiniteDimensional ℝ F] in
theorem torusMultiplier_norm_bound (ρ : ℝ) (hρ : 0 < ρ) (w : TorusHk K E) :
    ‖w.mulCoefficient C hC hp hb‖ ≤
      ((∑ l : Fin (K + 1), factorialRootWeight ρ l.val * A l) *
        Real.sqrt (factorialWeightMax ρ K) / Real.sqrt (factorialWeightMin ρ K)) * ‖w‖ := by
  have hA (l) : 0 ≤ A l := (norm_nonneg (coefficientDerivativeArray C l.val 0)).trans (hb l 0)
  have hsum : 0 ≤ ∑ l : Fin (K + 1), factorialRootWeight ρ l.val * A l :=
    Finset.sum_nonneg (fun l _ => mul_nonneg (by unfold factorialRootWeight; positivity) (hA l))
  have hm : 0 ≤ factorialWeightMax ρ K :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (K + 1)))
  have hs := Real.sqrt_le_sqrt (factorialNormSq_upper ρ w.val)
  rw [Real.sqrt_mul hm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hs
  have hx := (w.mulCoefficient_factorialNorm_le hC hp hb hρ.le).trans
    (mul_le_mul_of_nonneg_left hs hsum)
  have hn := (jetNorm_le_factorialRoot ρ hρ (w.mulCoefficient C hC hp hb).val).trans
    (div_le_div_of_nonneg_right hx (Real.sqrt_nonneg _))
  have hw : ‖w.val‖ = ‖w‖ := rfl
  rw [hw] at hn
  change ‖w.mulCoefficient C hC hp hb‖ ≤ _ at hn
  convert hn using 1; ring

def torusMultiplierCLM (ρ : ℝ) (hρ : 0 < ρ) : TorusHk K E →L[ℝ] TorusHk K F :=
  (torusMultiplierLinearMap C hC hp A hb).mkContinuous
    ((∑ l : Fin (K + 1), factorialRootWeight ρ l.val * A l) *
      Real.sqrt (factorialWeightMax ρ K) / Real.sqrt (factorialWeightMin ρ K))
    (torusMultiplier_norm_bound C hC hp A hb ρ hρ)

end AVRegularity.KernelEnergy
end
