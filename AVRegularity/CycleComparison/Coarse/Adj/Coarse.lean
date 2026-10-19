-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Coarse.Adj.MulOp
public import AVRegularity.Statements.Intermediate.CycleComparison.CovPolyQ
public import AVRegularity.Statements.Intermediate.CycleComparison.CoarseFluxAdjoint
import AVenhance.Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy
public import AVenhance.Statements.Roots.IsPeriodicH1With
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import AVenhance.Infra.Classical.GalerkinGenerator
import AVenhance.Infra.Classical.PeriodicCalculus

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Filter Topology
open AVenhance.Infra.Classical
open AVenhance.Infra.Torus AVenhance.Infra.Parabolic.WeakUniqueness
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! Periodic integration by parts for first weak derivatives against `C^1` periodic test fields.

The Fourier-projection argument behind `periodicH1_smooth_cell_ibp` only uses `C^1` regularity of
the test function (the finite-mode identity is classical and the pairings converge in `L²`);
here it is re-run with a `C^1` hypothesis, then promoted to vector-valued jets of `TorusHk`. -/

/-- Scalar periodic `H¹` integration by parts against a `C¹` periodic test function. -/
theorem periodicH1_cell_ibp_c1 {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : IsPeriodicH1With u Du) {η : Vec 2 → ℝ}
    (hη : ContDiff ℝ 1 η) (hpη : IsZ2Periodic η) (i : Fin 2) :
    (∫ x in unitCube, u x * spaceGrad η x i) =
      -∫ x in unitCube, Du x i * η x := by
  let upath : ℝ → Vec 2 → ℝ := fun _ => u
  let Dpath : ℝ → Vec 2 → Vec 2 := fun _ => Du
  let P (N : ℕ) : Vec 2 → ℝ := weakFourierModeProjection N upath 0
  let GradP (N : ℕ) : Vec 2 → ℝ := fun x => spaceGrad (P N) x i
  have hs (N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (P N) := by
    exact (realFourierModeAmbientExpansion_contDiff N
      (weakFourierCoefficientPath N upath 0)).of_le (by simp)
  have hp (N : ℕ) : IsZ2Periodic (P N) := realFourierModeAmbientExpansion_periodic N _
  have hpm (N : ℕ) : MemL2On unitCube (P N) := weak_continuous_memL2On (hs N).continuous
  have hgm (N : ℕ) : MemL2On unitCube (GradP N) :=
    weak_continuous_memL2On ((hs N).continuous_fderiv (by simp) |>.clm_apply continuous_const)
  have hηm : MemL2On unitCube η := weak_continuous_memL2On hη.continuous
  have hdηm : MemL2On unitCube (fun x => spaceGrad η x i) :=
    weak_continuous_memL2On (hη.continuous_fderiv (by simp) |>.clm_apply continuous_const)
  have hprojVal : Tendsto (fun N =>
      (weakProjection_realCellToTorus_memLp (hpm N)).toLp (periodicToTorus (P N))) atTop
      (𝓝 ((weakProjection_realCellToTorus_memLp hu.2.2.1).toLp (periodicToTorus u))) := by
    have h := weakFourierProjectionL2_tendsto (u := upath) (t := 0) hu.2.2.1
    simpa [P, weakFourierProjectionL2_eq_expansionTransfer] using h
  have hprojGrad : Tendsto (fun N =>
      (weakProjection_realCellToTorus_memLp (hgm N)).toLp (periodicToTorus (GradP N))) atTop
      (𝓝 ((weakProjection_realCellToTorus_memLp (hu.2.2.2.1 i)).toLp
        (periodicToTorus (fun x => Du x i)))) := by
    have hu' : IsPeriodicH1With (upath 0) (Dpath 0) := hu
    have h := weakFourierProjectionGradientL2_tendsto hu' i
    have h' : Tendsto (fun N => weakFourierProjectionGradientL2 N upath 0 i) atTop
        (𝓝 ((weakProjection_realCellToTorus_memLp (hu.2.2.2.1 i)).toLp
          (periodicToTorus (fun x => Du x i)))) := by
      simpa [weakFourierProjectionGradientL2] using h
    simpa [P, GradP, weakFourierProjectionGradientL2_eq_expansionTransfer] using h'
  have hl := DivergenceFreeEnergy.divFree_cell_pairing_tendsto hpm hu.2.2.1 hdηm hprojVal
  have hr := DivergenceFreeEnergy.divFree_cell_pairing_tendsto hgm (hu.2.2.2.1 i) hηm hprojGrad
  have hfinite (N : ℕ) :
      (∫ x in unitCell 2, P N x * spaceGrad η x i) =
      -∫ x in unitCell 2, GradP N x * η x := by
    exact AVenhance.Infra.Classical.integral_unitCell_coord_ibp_real i
      ((hs N).of_le (by simp)) hη (hp N) hpη
  have he := tendsto_nhds_unique hl
    (by simpa only [← hfinite] using hr.neg)
  rw [integral_unitCell_eq_unitCube, integral_unitCell_eq_unitCube] at he
  exact he

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- The derivative of a scalar component of a `C^1` field. -/
theorem fderiv_inner_const_apply {ψ : Vec 2 → E} (hψ : ContDiff ℝ 1 ψ) (c : E) (x v : Vec 2) :
    fderiv ℝ (fun y => inner ℝ c (ψ y)) x v = inner ℝ c (fderiv ℝ ψ x v) := by
  rw [fderiv_inner_apply ℝ (differentiableAt_const c) (hψ.differentiable one_ne_zero x) v]
  simp

/-- The value and first-derivative classes of an order-`K+1` torus jet, tested against a fixed
vector, form a periodic `H¹` pair. -/
theorem torusHk_isPeriodicH1With {K : ℕ} (U : TorusHk (K + 1) E) (e : E) :
    IsPeriodicH1With (fun x => inner ℝ e (tval U x))
      (fun x j => inner ℝ e (U.toFunction.jet
        (nextIndex2 (⟨0, Nat.succ_pos K⟩ : Fin (K + 1)) Fin.elim0 j) x)) := by
  have hraw := U.toFunction.hasPeriodicWeakJet
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    change inner ℝ e (U.toFunction.jet (valueIndex2 (K + 1)) (x + latticeShift n)) = _
    rw [hraw.1 _ n x]
    rfl
  · intro n x
    funext j
    change inner ℝ e (U.toFunction.jet _ (x + latticeShift n)) = _
    rw [hraw.1 _ n x]
  · exact (InnerProductSpace.toDual ℝ E e).comp_memLp' (hraw.2.1 _)
  · intro j
    exact (InnerProductSpace.toDual ℝ E e).comp_memLp' (hraw.2.1 _)
  · intro j
    exact hraw.2.2 (⟨0, Nat.succ_pos K⟩ : Fin (K + 1)) Fin.elim0 j e

/-- Periodic integration by parts for the first derivative class of a torus jet against a
`C^1` periodic vector-valued test field. -/
theorem cellInner_firstDerivative_eq_neg [FiniteDimensional ℝ E] {K : ℕ}
    (U : TorusHk (K + 1) E) (i : Fin 2) {ψ : Vec 2 → E} (hψ : ContDiff ℝ 1 ψ)
    (hp : IsZ2Periodic ψ) :
    cellInner (U.toFunction.jet
        (nextIndex2 (⟨0, Nat.succ_pos K⟩ : Fin (K + 1)) Fin.elim0 i)) ψ =
      -cellInner (tval U) (fun x => fderiv ℝ ψ x (basisVec i)) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let D := U.toFunction.jet (nextIndex2 (⟨0, Nat.succ_pos K⟩ : Fin (K + 1)) Fin.elim0 i)
  have hsum : ∀ v w : E, inner ℝ v w = ∑ k, inner ℝ (b k) v * inner ℝ (b k) w := by
    intro v w
    rw [← b.sum_inner_mul_inner v w]
    exact Finset.sum_congr rfl fun k _ => by rw [real_inner_comm (b k) v]
  let η : Fin (Module.finrank ℝ E) → Vec 2 → ℝ := fun k x => inner ℝ (b k) (ψ x)
  have hη : ∀ k, ContDiff ℝ 1 (η k) := fun k => contDiff_const.inner ℝ hψ
  have hηp : ∀ k, IsZ2Periodic (η k) := fun k n x => by
    change inner ℝ (b k) (ψ (x + latticeShift n)) = _
    rw [hp n x]
  have hdη : ∀ k x, spaceGrad (η k) x i = inner ℝ (b k) (fderiv ℝ ψ x (basisVec i)) :=
    fun k x => fderiv_inner_const_apply hψ (b k) x _
  have hdcont : Continuous (fun x => fderiv ℝ ψ x (basisVec i)) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcomp : ∀ k, Continuous (fun x => inner ℝ (b k) (fderiv ℝ ψ x (basisVec i))) :=
    fun k => continuous_const.inner hdcont
  have hL1 : ∀ k, Integrable (fun x => inner ℝ (b k) (D x) * η k x)
      (volume.restrict unitCube) := fun k =>
    ((torusHk_isPeriodicH1With U (b k)).2.2.2.1 i).integrable_mul
      (weak_continuous_memL2On (continuous_const.inner hψ.continuous))
  have hR1 : ∀ k, Integrable (fun x => inner ℝ (b k) (tval U x) *
      inner ℝ (b k) (fderiv ℝ ψ x (basisVec i))) (volume.restrict unitCube) := fun k =>
    (torusHk_isPeriodicH1With U (b k)).2.2.1.integrable_mul (weak_continuous_memL2On (hcomp k))
  have e1 : (∫ x in unitCube, inner ℝ (D x) (ψ x)) =
      ∑ k, ∫ x in unitCube, inner ℝ (b k) (D x) * η k x := by
    rw [← integral_finsetSum _ (fun k _ => hL1 k)]
    exact integral_congr_ae (ae_of_all _ fun x => hsum (D x) (ψ x))
  have e2 : (∫ x in unitCube, inner ℝ (tval U x) (fderiv ℝ ψ x (basisVec i))) =
      ∑ k, ∫ x in unitCube, inner ℝ (b k) (tval U x) *
        inner ℝ (b k) (fderiv ℝ ψ x (basisVec i)) := by
    rw [← integral_finsetSum _ (fun k _ => hR1 k)]
    exact integral_congr_ae (ae_of_all _ fun x => hsum _ _)
  unfold cellInner
  rw [e1, e2, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := periodicH1_cell_ibp_c1 (torusHk_isPeriodicH1With U (b k)) (hη k) (hηp k) i
  have h2 : (∫ x in unitCube, inner ℝ (b k) (tval U x) *
      inner ℝ (b k) (fderiv ℝ ψ x (basisVec i))) =
      -∫ x in unitCube, inner ℝ (b k) (D x) * inner ℝ (b k) (ψ x) := by
    simpa only [hdη] using h
  rw [h2, neg_neg]

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! The coordinate derivative as a `TorusAdj`: `T ψ = ∂_i ψ`, of order one, with adjoint
`-(derivativeTorusHk (single letter i))`, constant one, by periodic integration by parts. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- The coordinate derivative `∂_i` on fields `Vec 2 → E`. -/
def partialOp (i : Fin 2) (ψ : Vec 2 → E) : Vec 2 → E :=
  fun x => fderiv ℝ ψ x (basisVec i)

theorem prefixJetIndex_single_value (K : ℕ) (i : Fin 2) :
    prefixJetIndex (K := K) (r := 1) (fun _ => i) (valueIndex2 K) =
      nextIndex2 (⟨0, Nat.succ_pos K⟩ : Fin (K + 1)) Fin.elim0 i := by
  have h : (Fin.append (fun _ : Fin 1 => i) (Fin.elim0 : Fin 0 → Fin 2)) =
      (Fin.snoc (Fin.elim0 : Fin 0 → Fin 2) i : Fin 1 → Fin 2) := by
    funext z
    obtain ⟨z, hz⟩ := z
    have hz0 : z = 0 := by omega
    subst hz0
    simp [Fin.append, Fin.addCases, Fin.snoc]
  exact Sigma.ext rfl (heq_of_eq h)

/-- The value jet of a derivative is the first-derivative jet. -/
theorem tval_derivativeTorusHk_single {K : ℕ} (U : TorusHk (K + 1) E) (i : Fin 2) :
    tval (derivativeTorusHk (K := K) (r := 1) (fun _ => i) U) =
      U.toFunction.jet (nextIndex2 (⟨0, Nat.succ_pos K⟩ : Fin (K + 1)) Fin.elim0 i) := by
  rw [← prefixJetIndex_single_value]
  rfl

/-- The coordinate derivative has adjoint `-∂_i`, order one and constant one. -/
def TorusAdj.coordDeriv [FiniteDimensional ℝ E] (i : Fin 2) (R Kc : ℕ) :
    TorusAdj (partialOp (E := E) i) 1 R Kc 1 where
  adj K _ := -(derivativeTorusHk (K := K) (r := 1) (fun _ => i))
  bound K _ := by
    rw [ContinuousLinearMap.opNorm_neg]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun f => by simpa using derivativeTorusHk_norm_le (fun _ => i) f)
  maps r _ ψ hψ hp := by
    have hψ' : ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) ψ := hψ
    have hd : ContDiff ℝ (r : ℕ∞) (fderiv ℝ ψ) :=
      hψ'.fderiv_right (by exact_mod_cast le_refl (r + 1))
    refine ⟨hd.clm_apply contDiff_const, fun n x => ?_⟩
    have hdiff : Differentiable ℝ ψ :=
      hψ'.differentiable (by exact_mod_cast Nat.succ_ne_zero r)
    exact congrArg (fun A => A (basisVec i)) (fderiv_isZ2Periodic hdiff hp n x)
  ident K _ U ψ hψ hp := by
    change cellInner (tval (-(derivativeTorusHk (K := K) (r := 1) (fun _ => i) U))) ψ = _
    rw [cellInner_tval_neg, tval_derivativeTorusHk_single,
      cellInner_firstDerivative_eq_neg U i (by exact_mod_cast hψ) hp, neg_neg]
    rfl
end

/-! Iterated derivatives: second derivatives and ordered words `orderedDerivativeRev α`, as
`TorusAdj` of order equal to the word length and constant one. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The second derivative `∂_i ∂_j ψ` has order two and constant one. -/
def TorusAdj.secondDeriv (i j : Fin 2) (R Kc : ℕ) :
    TorusAdj (fun ψ : Vec 2 → E => fun x =>
      fderiv ℝ (fun y => fderiv ℝ ψ y (basisVec j)) x (basisVec i)) 2 R Kc 1 :=
  ((TorusAdj.coordDeriv (E := E) i R Kc).comp (TorusAdj.coordDeriv (E := E) j (R + 1) Kc)
    le_rfl le_rfl).mono le_rfl le_rfl (le_of_eq (one_mul 1))

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem orderedDerivativeRev_succ {m : ℕ} (α : DerivativeWord2 (m + 1)) (g : Vec 2 → E) :
    AVRegularity.orderedDerivativeRev α g =
      AVRegularity.orderedDerivativeRev (Fin.init α) (partialOp (α (Fin.last m)) g) := by
  unfold AVRegularity.orderedDerivativeRev
  rw [List.ofFn_succ', List.concat_eq_append, List.foldr_append]
  rfl

/-- Ordered derivative words: `∂_{α_0} ⋯ ∂_{α_{m-1}}` has order `m` and constant one. -/
def TorusAdj.orderedDerivativeRev : ∀ {m : ℕ} (α : DerivativeWord2 m) (R Kc : ℕ),
    TorusAdj (AVRegularity.orderedDerivativeRev (E := E) α) m R Kc 1
  | 0, α, R, Kc => (TorusAdj.id (E := E) R Kc).mono le_rfl le_rfl le_rfl |>.ofOp
      (by funext g; rfl)
  | m + 1, α, R, Kc =>
    (((TorusAdj.orderedDerivativeRev (Fin.init α) R Kc).comp
      (TorusAdj.coordDeriv (E := E) (α (Fin.last m)) (R + m) Kc) le_rfl le_rfl).mono
      le_rfl le_rfl (le_of_eq (one_mul 1))).ofOp
      (by funext g; exact (orderedDerivativeRev_succ α g).symm)
end

/-! The covariance operator `𝒞 = H_cov : D²`, its iterates and the polynomials `𝖯_p`, `𝖰_p` as
`TorusAdj`. With `M ≥ ∑_{ij} |H_{ij}|`, `𝒞` has order two and constant `M`, `𝒞^l` has order `2l`
and constant `M^l`, and `𝖯_p`, `𝖰_p` have order `2p` and constant `∑_{l ≤ p} M^l / l!`. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The `ℓ¹` size `∑_{ij} |H_{ij}|` of a covariance matrix. -/
def covBound (Hc : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := ∑ i, ∑ j, |Hc i j|

/-- The constant `∑_{l ≤ p} M^l / l!` of the covariance polynomials. -/
def covPolyConst (M : ℝ) (p : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (p + 1), M ^ l / (l.factorial : ℝ)

/-- The covariance operator has order two and constant `M ≥ ∑ |H_{ij}|`. -/
def TorusAdj.covOp (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M) (R Kc : ℕ) :
    TorusAdj (AVRegularity.covOperator (E := E) Hc) 2 R Kc M :=
  (TorusAdj.sum (Finset.univ : Finset (Fin 2)) (fun i =>
    TorusAdj.sum (Finset.univ : Finset (Fin 2)) (fun j =>
      (TorusAdj.secondDeriv (E := E) i j R Kc).smul (Hc i j)))).mono le_rfl le_rfl
    (by simpa [covBound] using hM) |>.ofOp (by funext ψ x; rfl)

/-- Iterates `𝒞^l`: order `2l`, constant `M^l`. -/
def TorusAdj.covIter (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M) :
    ∀ (l R Kc : ℕ), TorusAdj ((AVRegularity.covOperator (E := E) Hc)^[l]) (2 * l) R Kc (M ^ l)
  | 0, R, Kc => ((TorusAdj.id (E := E) R Kc).mono le_rfl le_rfl (by simp)).ofOrder (by simp)
  | l + 1, R, Kc =>
    (((TorusAdj.covOp (E := E) Hc hM R Kc).comp (TorusAdj.covIter Hc hM l (R + 2) Kc)
      le_rfl le_rfl).mono le_rfl le_rfl (by rw [pow_succ']))
      |>.ofOrder (by omega)
      |>.ofOp (by funext ψ; exact (Function.iterate_succ_apply' _ l ψ).symm)

theorem covBound_nonneg (Hc : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ covBound Hc :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- `𝖯_p`: order `2p`, constant `∑_{l ≤ p} M^l / l!`. -/
def TorusAdj.covPolyP (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (p R Kc : ℕ) :
    TorusAdj (AVRegularity.covPolyP (E := E) Hc p) (2 * p) R Kc (covPolyConst M p) :=
  (TorusAdj.sumMem (Finset.range (p + 1)) (fun l hl =>
    ((TorusAdj.covIter (E := E) Hc hM l R Kc).liftOrder
      (Nat.mul_le_mul_left 2 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)))).smul ((l.factorial : ℝ)⁻¹)))
    |>.mono le_rfl le_rfl (le_of_eq (by
      unfold covPolyConst
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)), div_eq_mul_inv, mul_comm]))
    |>.ofOp (by funext ψ x; simp [AVRegularity.covPolyP])

/-- `𝖰_p`: order `2p`, constant `∑_{l ≤ p} M^l / l!`. -/
def TorusAdj.covPolyQ (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (p R Kc : ℕ) :
    TorusAdj (AVRegularity.covPolyQ (E := E) Hc p) (2 * p) R Kc (covPolyConst M p) :=
  (TorusAdj.sumMem (Finset.range (p + 1)) (fun l hl =>
    ((TorusAdj.covIter (E := E) Hc hM l R Kc).liftOrder
      (Nat.mul_le_mul_left 2 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)))).smul
        (((-1 : ℝ) ^ l / (l.factorial : ℝ)))))
    |>.mono le_rfl le_rfl (le_of_eq (by
      unfold covPolyConst
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ l.factorial), div_mul_eq_mul_div,
        one_mul]))
    |>.ofOp (by funext ψ x; simp [AVRegularity.covPolyQ])
end

/-! Constant pointwise operators and the word adjoint `wordAdjoint m` as `TorusAdj`.

A constant bounded linear map `L : F →L E` with a pointwise adjoint `L'` is a `TorusAdj` of
order zero, via `TorusAdj.mulOp` with a constant coefficient (all derivative arrays of order
at least one vanish), with constant `Kc! · ‖L'‖`. The word adjoint `wordAdjoint m` is
`(-1)^m ∑_α ∂^{rev α} ∘ (G ↦ G_α)`, of order `m` and constant `2^m · Kc!`. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- The coefficient bounds of a constant coefficient: `a` at order zero and `0` above. -/
def constBound (a : ℝ) : ℕ → ℝ := fun l => if l = 0 then a else 0

theorem mulConst_constBound (a : ℝ) (Kc : ℕ) :
    mulConst (constBound a) Kc = (Kc.factorial : ℝ) * a := by
  unfold mulConst
  rw [Finset.sum_range_succ']
  simp [constBound]

/-- A constant pointwise operator `ψ ↦ L ∘ ψ`, of order zero. -/
def TorusAdj.constOp (L : F →L[ℝ] E) (L' : E →L[ℝ] F)
    (hLL : ∀ v w, inner ℝ (L' v) w = inner ℝ v (L w)) {a : ℝ} (ha : ‖L'‖ ≤ a) (R Kc : ℕ) :
    TorusAdj (fun (ψ : Vec 2 → F) (x : Vec 2) => L (ψ x)) 0 R Kc ((Kc.factorial : ℝ) * a) :=
  (TorusAdj.mulOp (M := fun _ => L) (N := fun _ => L') R Kc contDiff_const (fun _ _ => rfl)
    contDiff_const (fun _ _ => rfl) (fun _ => hLL) (constBound a) (by
      intro l _ x
      cases l with
      | zero =>
        refine norm_array_le_card_mul (fun _ : Vec 2 => L') 0 x (B := ‖L'‖) (fun w => le_of_eq rfl) |>.trans ?_
        simpa [constBound] using ha
      | succ j =>
        rw [coefficientDerivativeArray_const_succ, ContinuousLinearMap.opNorm_zero]
        simp [constBound])).mono le_rfl le_rfl (le_of_eq (mulConst_constBound a Kc))

section Words

/-- The embedding of the `α`-th component into `PiLp 2`, as a bounded linear map. -/
def piSingleCLM {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (α : ι) : E →L[ℝ] PiLp 2 (fun _ : ι => E) :=
  LinearMap.mkContinuous
    { toFun := fun v => PiLp.single 2 α v
      map_add' := fun v w => PiLp.single_add 2 α
      map_smul' := fun c v => by
        ext j
        by_cases h : j = α
        · subst h; simp
        · simp [h] } 1 (fun v => by simp [PiLp.norm_single])

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem piSingleCLM_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι) (v : E) :
    piSingleCLM E α v = PiLp.single 2 α v := rfl

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem norm_piSingleCLM_le {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι) :
    ‖piSingleCLM E α‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem inner_piSingleCLM {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι) (v : E)
    (w : PiLp 2 (fun _ : ι => E)) : inner ℝ (piSingleCLM E α v) w = inner ℝ v (w α) := by
  rw [piSingleCLM_apply, PiLp.inner_apply, Finset.sum_eq_single α]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- The `α`-th component, as a `TorusAdj` of order zero and constant `Kc!`. -/
def TorusAdj.componentOp {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι) (R Kc : ℕ) :
    TorusAdj (fun (G : Vec 2 → PiLp 2 (fun _ : ι => E)) (x : Vec 2) => G x α) 0 R Kc
      ((Kc.factorial : ℝ) * 1) :=
  TorusAdj.constOp (PiLp.proj 2 (fun _ : ι => E) α) (piSingleCLM E α)
    (fun v w => inner_piSingleCLM α v w) (norm_piSingleCLM_le α) R Kc

/-- The word adjoint `wordAdjoint m`: order `m`, constant `2^m · Kc!`. -/
def TorusAdj.wordAdj (m R Kc : ℕ) :
    TorusAdj (AVRegularity.wordAdjoint (E := E) m) m R Kc (2 ^ m * (Kc.factorial : ℝ)) :=
  ((TorusAdj.sumMem (Finset.univ : Finset (DerivativeWord2 m)) (fun α _ =>
    ((TorusAdj.orderedDerivativeRev (E := E) α R Kc).comp
      (TorusAdj.componentOp (E := E) α (R + m) Kc) le_rfl le_rfl).ofOrder (Nat.add_zero m))).smul
      ((-1 : ℝ) ^ m)).mono le_rfl le_rfl (le_of_eq (by
    simp [Finset.sum_const, Finset.card_univ, mul_comm])) |>.ofOp
    (by funext G x; rfl)

end Words
end

/-! The flux operators with flux-valued coefficients as `TorusAdj` at a fixed time:
the pointwise tensor flux `ψ ↦ tensorFluxAdjoint (A y) (ψ y)`, the pointwise operator-adjoint
`ψ ↦ (C y)^* (ψ y)` (used for the edge flux), and the diagonal flux `diagonalFluxAdjoint`. -/

section
/-- The adjoint of operators, as a bounded real-linear map. -/
def adjointCLM (X Y : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] :
    (X →L[ℝ] Y) →L[ℝ] (Y →L[ℝ] X) :=
  LinearMap.mkContinuous
    { toFun := ContinuousLinearMap.adjoint
      map_add' := fun T T' => map_add _ T T'
      map_smul' := fun c T => by
        rw [map_smulₛₗ]
        simp } 1
    (fun T => by
      change ‖ContinuousLinearMap.adjoint T‖ ≤ 1 * ‖T‖
      rw [LinearIsometryEquiv.norm_map, one_mul])

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem contDiff_clm_comp {X₁ Y₁ X₂ Y₂ : Type*} [NormedAddCommGroup X₁] [NormedSpace ℝ X₁]
    [NormedAddCommGroup Y₁] [NormedSpace ℝ Y₁] [NormedAddCommGroup X₂] [NormedSpace ℝ X₂]
    [NormedAddCommGroup Y₂] [NormedSpace ℝ Y₂] (Φ : (X₁ →L[ℝ] Y₁) →L[ℝ] (X₂ →L[ℝ] Y₂))
    {f : Vec 2 → X₁ →L[ℝ] Y₁} {n : WithTop ℕ∞} (h : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => Φ (f x)) :=
  Φ.contDiff.comp h

/-- The coefficient bounds of `x ↦ (A x ⊗ id)` from those of `A`. -/
def tensorBound (m : ℕ) (BA : ℕ → ℝ) : ℕ → ℝ := fun l => 2 ^ l * ((2 ^ m * 2) * BA l)

/-- The constant of the pointwise tensor flux of order-`m` words. -/
def tensorConst (m Kc : ℕ) (BA : ℕ → ℝ) : ℝ := mulConst (tensorBound m BA) Kc

/-- The pointwise operator adjoint of a coefficient `C`: `ψ ↦ (C y)^* (ψ y)`, of order zero. -/
def TorusAdj.adjointCoeffOp {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [CompleteSpace Y] (C : Vec 2 → X →L[ℝ] Y) (R Kc : ℕ) (hCR : ContDiff ℝ (R : ℕ) C)
    (hCK : ContDiff ℝ (Kc : ℕ) C) (hp : AVenhance.IsZ2Periodic C) (B : ℕ → ℝ)
    (hB : ∀ l ≤ Kc, ∀ x, ‖coefficientDerivativeArray C l x‖ ≤ B l) :
    TorusAdj (fun (ψ : Vec 2 → Y) (x : Vec 2) => ContinuousLinearMap.adjoint (C x) (ψ x))
      0 R Kc (mulConst B Kc) :=
  TorusAdj.mulOp (M := fun x => ContinuousLinearMap.adjoint (C x)) (N := C) R Kc
    (contDiff_clm_comp (adjointCLM X Y) hCR) (fun n x => by
      change ContinuousLinearMap.adjoint (C (x + AVenhance.latticeShift n)) = _
      rw [hp n x])
    hCK hp (fun x v w => (ContinuousLinearMap.adjoint_inner_right (C x) v w).symm) B hB

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] in
theorem inner_tensorPrimal {m : ℕ}
    (B : PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (φ : PiLp 2 (fun _ : DerivativeWord2 m => E)) (ψ : PiLp 2 (fun _ : Fin 2 => E)) :
    inner ℝ (tensorPrimal B φ) ψ = inner ℝ φ (AVRegularity.tensorFluxAdjoint B ψ) := by
  simp only [PiLp.inner_apply, tensorPrimal, tensorFluxAdjoint_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp)

/-- The pointwise tensor flux `ψ ↦ tensorFluxAdjoint (A y) (ψ y)`, of order zero. -/
def TorusAdj.tensorFlux {m : ℕ}
    (A : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (R Kc : ℕ) (hAR : ContDiff ℝ (R : ℕ) A) (hAK : ContDiff ℝ (Kc : ℕ) A)
    (hp : AVenhance.IsZ2Periodic A) (BA : ℕ → ℝ)
    (hBA : ∀ l ≤ Kc, ∀ x, ‖coefficientDerivativeArray A l x‖ ≤ BA l) :
    TorusAdj (fun (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (y : Vec 2) =>
      AVRegularity.tensorFluxAdjoint (A y) (ψ y)) 0 R Kc (tensorConst m Kc BA) :=
  TorusAdj.mulOp (M := fun x => tensorFluxAdjointMap E m (A x))
    (N := fun x => tensorPrimalMap E m (A x)) R Kc
    (contDiff_clm_comp (tensorFluxAdjointMap E m) hAR) (fun n x => by
      change tensorFluxAdjointMap E m (A (x + AVenhance.latticeShift n)) = _
      rw [hp n x])
    (contDiff_clm_comp (tensorPrimalMap E m) hAK) (fun n x => by
      change tensorPrimalMap E m (A (x + AVenhance.latticeShift n)) = _
      rw [hp n x])
    (fun x v w => inner_tensorPrimal (A x) v w) (tensorBound m BA) (by
      intro l hl x
      refine (norm_array_clm_comp_le (tensorPrimalMap E m) A l
        (hAK.of_le (by exact_mod_cast hl)) x).trans ?_
      unfold tensorBound
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul norm_tensorPrimalMap_le (hBA l hl x)
        (ContinuousLinearMap.opNorm_nonneg _) (by positivity))

/-- The constant of the diagonal flux adjoint. -/
def diagConst (D Kc : ℕ) (BA : ℕ → ℕ → ℝ) : ℝ :=
  ∑ d : Finset.Icc 2 D, ((2 ^ (d.1 - 1) * (Kc.factorial : ℝ)) * tensorConst (d.1 - 1) Kc (BA d.1))

/-- The diagonal flux adjoint `diagonalFluxAdjoint D AD s` at a fixed time: order `D - 1`.
The coefficients are `C^Q` with `R + D ≤ Q` and `Kc ≤ Q`; `BA d l` bounds the `l`-th derivative
array of `AD d s`. -/
def TorusAdj.diagFlux (D : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (R Kc Q : ℕ) (hQR : R + D ≤ Q) (hQK : Kc ≤ Q)
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s)) (hp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (BA : ℕ → ℕ → ℝ)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l) :
    TorusAdj (AVRegularity.diagonalFluxAdjoint (E := E) D AD s) (D - 1) R Kc
      (diagConst D Kc BA) :=
  (TorusAdj.sum (Finset.univ : Finset (Finset.Icc 2 D)) (fun d =>
    ((TorusAdj.wordAdj (E := E) (d.1 - 1) R Kc).comp
      (TorusAdj.tensorFlux (E := E) (AD d s) (R + (d.1 - 1)) Kc
        ((hA d).of_le (by have := Finset.mem_Icc.mp d.2; exact_mod_cast (by omega)))
        ((hA d).of_le (by exact_mod_cast hQK)) (hp d) (BA d.1) (hBA d)) le_rfl le_rfl).liftOrder
      (by have := Finset.mem_Icc.mp d.2; omega : d.1 - 1 + 0 ≤ D - 1))).ofOp
    (by funext ψ x; rfl)

/-- The constant of the edge flux adjoint (one source and target component). -/
def edgeConst (D H Kc : ℕ) (BE : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
    ((2 ^ (d.1 - 1) * (Kc.factorial : ℝ)) * mulConst (BE r d.1) Kc)

/-- The `(v,u)` block of the edge flux adjoint at a fixed time, as an operator on a single flux
field `ψ` valued in `ℝ² ⊗ X`, with values in `Y`: order `D - 1`. -/
def TorusAdj.edgeFluxBlock {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [CompleteSpace Y] [FiniteDimensional ℝ Y] (D H : ℕ)
    (C : ℕ → ∀ d : Finset.Icc 2 D, Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => Y)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => X)))
    (R Kc Q : ℕ) (hQR : R + D ≤ Q) (hQK : Kc ≤ Q)
    (hC : ∀ r d, ContDiff ℝ (Q : ℕ) (C r d)) (hp : ∀ r d, AVenhance.IsZ2Periodic (C r d))
    (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (C r d) l x‖ ≤ BE r d.1 l) :
    TorusAdj (fun (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => X)) (x : Vec 2) =>
      ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
        AVRegularity.wordAdjoint (d.1 - 1)
          (fun y => ContinuousLinearMap.adjoint (C r d y) (ψ y)) x) (D - 1) R Kc
      (edgeConst D H Kc BE) :=
  TorusAdj.sumMem (Finset.Icc 1 H) fun r _ =>
    (TorusAdj.sum (Finset.univ : Finset (Finset.Icc 2 D)) (fun d =>
      ((TorusAdj.wordAdj (E := Y) (d.1 - 1) R Kc).comp
        (TorusAdj.adjointCoeffOp (C r d) (R + (d.1 - 1)) Kc
          ((hC r d).of_le (by have := Finset.mem_Icc.mp d.2; exact_mod_cast (by omega)))
          ((hC r d).of_le (by exact_mod_cast hQK)) (hp r d) (BE r d.1) (hBE r d))
        le_rfl le_rfl).liftOrder
        (by have := Finset.mem_Icc.mp d.2; omega : d.1 - 1 + 0 ≤ D - 1)))
end

/-! The commutator flux adjoint `𝒥_H^*` at a fixed time, as a `TorusAdj` of order one.

`𝒥_H^* ψ = ∑_j ∂_j (∑_k 𝔑_{kj} ψ_k)` with `𝔑 = D𝐛 H + H D𝐛ᵀ` linear in `D𝐛`. The entries
`𝔑_{kj}` are bounded linear functionals of `D𝐛 : Vec 2 →L Vec 2` with norm `≤ 2 M`
(`M ≥ ∑ |H_{ij}|`), so that the coefficient and its pointwise adjoint are bounded linear images
of `D𝐛` of norm `≤ 4 M`. Derivative arrays of `D𝐛` are bounded by the iterated derivatives of
`𝐛` (`Coeff.lean`). -/

section
/-- The entry `𝔑_{kj}` as a function of the Jacobian `T = D𝐛`. -/
def centry (Hc : Matrix (Fin 2) (Fin 2) ℝ) (k j : Fin 2) (T : Vec 2 →L[ℝ] Vec 2) : ℝ :=
  ∑ K : Fin 2, (T (basisVec K) k * Hc K j + Hc k K * T (basisVec K) j)

theorem centry_add (Hc : Matrix (Fin 2) (Fin 2) ℝ) (k j : Fin 2) (T T' : Vec 2 →L[ℝ] Vec 2) :
    centry Hc k j (T + T') = centry Hc k j T + centry Hc k j T' := by
  simp only [centry, add_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun K _ => by ring

theorem centry_smul (Hc : Matrix (Fin 2) (Fin 2) ℝ) (k j : Fin 2) (c : ℝ) (T : Vec 2 →L[ℝ] Vec 2) :
    centry Hc k j (c • T) = c * centry Hc k j T := by
  simp only [centry, smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun K _ => by ring

theorem abs_centry_le (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M) (k j : Fin 2)
    (T : Vec 2 →L[ℝ] Vec 2) : |centry Hc k j T| ≤ 2 * M * ‖T‖ := by
  have hT : ∀ K i, |T (basisVec K) i| ≤ ‖T‖ := fun K i => by
    calc |T (basisVec K) i| = ‖T (basisVec K) i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖T (basisVec K)‖ := norm_le_pi_norm _ _
      _ ≤ ‖T‖ * ‖basisVec K‖ := T.le_opNorm _
      _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left (norm_basisVec_le_one K) (norm_nonneg _)
      _ = ‖T‖ := mul_one _
  have h1 : ∑ K : Fin 2, |Hc K j| ≤ M := by
    refine le_trans ?_ hM
    exact Finset.sum_le_sum fun i _ => Finset.single_le_sum (f := fun j' => |Hc i j'|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ K : Fin 2, |Hc k K| ≤ M := by
    refine le_trans ?_ hM
    exact Finset.single_le_sum (f := fun i => ∑ j' : Fin 2, |Hc i j'|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k)
  have hterm : ∀ K : Fin 2, |T (basisVec K) k * Hc K j + Hc k K * T (basisVec K) j| ≤
      ‖T‖ * |Hc K j| + ‖T‖ * |Hc k K| := fun K => by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hT K k) (abs_nonneg _)
    · rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hT K j) (abs_nonneg _)
  calc |centry Hc k j T| ≤ ∑ K : Fin 2, |T (basisVec K) k * Hc K j + Hc k K * T (basisVec K) j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ K : Fin 2, (‖T‖ * |Hc K j| + ‖T‖ * |Hc k K|) := Finset.sum_le_sum fun K _ => hterm K
    _ = ‖T‖ * ∑ K : Fin 2, |Hc K j| + ‖T‖ * ∑ K : Fin 2, |Hc k K| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ ‖T‖ * M + ‖T‖ * M := add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    _ = 2 * M * ‖T‖ := by ring

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The pointwise adjoint coefficient `v ↦ (𝔑_{kj} v)_k`. -/
def commPrimalVec (Hc : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) (T : Vec 2 →L[ℝ] Vec 2) (v : E) :
    PiLp 2 (fun _ : Fin 2 => E) :=
  WithLp.toLp 2 fun k => centry Hc k j T • v

/-- The coefficient `w ↦ ∑_k 𝔑_{kj} w_k`. -/
def commFluxVec (Hc : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) (T : Vec 2 →L[ℝ] Vec 2)
    (w : PiLp 2 (fun _ : Fin 2 => E)) : E :=
  ∑ k : Fin 2, centry Hc k j T • w k

theorem norm_commPrimalVec_le (Hc : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) (T : Vec 2 →L[ℝ] Vec 2)
    (v : E) : ‖commPrimalVec Hc j T v‖ ≤ 4 * covBound Hc * ‖T‖ * ‖v‖ := by
  refine (norm_piLp_le_sum _).trans ?_
  calc ∑ k : Fin 2, ‖commPrimalVec Hc j T v k‖ ≤ ∑ _k : Fin 2, 2 * covBound Hc * ‖T‖ * ‖v‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        change ‖centry Hc k j T • v‖ ≤ _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (abs_centry_le Hc le_rfl k j T) (norm_nonneg _)
    _ = 4 * covBound Hc * ‖T‖ * ‖v‖ := by simp [Finset.sum_const]; ring

theorem norm_commFluxVec_le (Hc : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) (T : Vec 2 →L[ℝ] Vec 2)
    (w : PiLp 2 (fun _ : Fin 2 => E)) : ‖commFluxVec Hc j T w‖ ≤ 4 * covBound Hc * ‖T‖ * ‖w‖ := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k : Fin 2, ‖centry Hc k j T • w k‖ ≤ ∑ _k : Fin 2, 2 * covBound Hc * ‖T‖ * ‖w‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (abs_centry_le Hc le_rfl k j T) (PiLp.norm_apply_le w k) (norm_nonneg _)
          (by have := abs_nonneg (centry Hc k j T); have := abs_centry_le Hc le_rfl k j T; linarith)
    _ = 4 * covBound Hc * ‖T‖ * ‖w‖ := by simp [Finset.sum_const]; ring

/-- `v ↦ (𝔑_{kj} v)_k` as a bounded linear map. -/
def commPrimalCLM (Hc : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) (T : Vec 2 →L[ℝ] Vec 2) :
    E →L[ℝ] PiLp 2 (fun _ : Fin 2 => E) :=
  LinearMap.mkContinuous
    { toFun := commPrimalVec Hc j T
      map_add' := fun v v' => by ext k; simp [commPrimalVec, smul_add]
      map_smul' := fun c v => by ext k; simp [commPrimalVec, smul_comm c] }
    (4 * covBound Hc * ‖T‖) (fun v => norm_commPrimalVec_le Hc j T v)

/-- `w ↦ ∑_k 𝔑_{kj} w_k` as a bounded linear map. -/
def commFluxCLM (Hc : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) (T : Vec 2 →L[ℝ] Vec 2) :
    PiLp 2 (fun _ : Fin 2 => E) →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := commFluxVec Hc j T
      map_add' := fun w w' => by simp [commFluxVec, smul_add, Finset.sum_add_distrib]
      map_smul' := fun c w => by simp [commFluxVec, smul_comm c] }
    (4 * covBound Hc * ‖T‖) (fun w => norm_commFluxVec_le Hc j T w)

/-- `T ↦ (v ↦ (𝔑_{kj}(T) v)_k)` as a bounded linear map. -/
def commPrimalMap (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) :
    (Vec 2 →L[ℝ] Vec 2) →L[ℝ] (E →L[ℝ] PiLp 2 (fun _ : Fin 2 => E)) :=
  LinearMap.mkContinuous
    { toFun := commPrimalCLM Hc j
      map_add' := fun T T' => by
        ext v k; simp [commPrimalCLM, commPrimalVec, centry_add, add_smul]
      map_smul' := fun c T => by
        ext v k; simp [commPrimalCLM, commPrimalVec, centry_smul, mul_smul] }
    (4 * covBound Hc) (fun T => by
      refine ContinuousLinearMap.opNorm_le_bound _ (by
        have := covBound_nonneg Hc; positivity) fun v => ?_
      exact (norm_commPrimalVec_le Hc j T v))

/-- `T ↦ (w ↦ ∑_k 𝔑_{kj}(T) w_k)` as a bounded linear map. -/
def commFluxMap (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) :
    (Vec 2 →L[ℝ] Vec 2) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => E) →L[ℝ] E) :=
  LinearMap.mkContinuous
    { toFun := commFluxCLM Hc j
      map_add' := fun T T' => by
        ext w; simp [commFluxCLM, commFluxVec, centry_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c T => by
        ext w; simp [commFluxCLM, commFluxVec, centry_smul, mul_smul] }
    (4 * covBound Hc) (fun T => by
      refine ContinuousLinearMap.opNorm_le_bound _ (by
        have := covBound_nonneg Hc; positivity) fun w => ?_
      exact (norm_commFluxVec_le Hc j T w))

theorem norm_commPrimalMap_le (Hc : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) :
    ‖commPrimalMap E Hc j‖ ≤ 4 * covBound Hc :=
  LinearMap.mkContinuous_norm_le _ (by have := covBound_nonneg Hc; positivity) _

omit [NormedSpace ℝ E] in
theorem inner_commPrimalVec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) (T : Vec 2 →L[ℝ] Vec 2) (v : E)
    (w : PiLp 2 (fun _ : Fin 2 => E)) :
    inner ℝ (commPrimalVec Hc j T v) w = inner ℝ v (commFluxVec Hc j T w) := by
  simp only [commPrimalVec, commFluxVec, PiLp.inner_apply, inner_sum, real_inner_smul_left,
    real_inner_smul_right]

end Linear

theorem isZ2Periodic_clm_comp {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (Φ : X →L[ℝ] Z) {f : Vec 2 → X}
    (hf : AVenhance.IsZ2Periodic f) : AVenhance.IsZ2Periodic (fun x => Φ (f x)) := fun n x => by
  change Φ (f (x + AVenhance.latticeShift n)) = _
  rw [hf n x]

section Op

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The derivative-array bounds of the pointwise adjoint coefficient of `𝒥_H^*`. -/
def commBound (M : ℝ) (Bb : ℕ → ℝ) : ℕ → ℝ := fun l => 2 ^ l * (4 * M * (2 ^ l * Bb l))

/-- The constant of the commutator flux adjoint. -/
def commConst (M : ℝ) (Kc : ℕ) (Bb : ℕ → ℝ) : ℝ := 2 * mulConst (commBound M Bb) Kc

/-- The commutator flux adjoint `𝒥_H^*` at the time `s`: order one. The drift `b s` is `C^Q`
with `R + 2 ≤ Q` and `Kc + 1 ≤ Q`, periodic, with `‖D^{l+1}(b s)(x)‖ ≤ Bb l` for `l ≤ Kc`;
`M ≥ ∑ |H_{ij}|`. -/
def TorusAdj.commutator (b : ℝ → Vec 2 → Vec 2) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ}
    (hM : covBound Hc ≤ M) (s : ℝ) (R Kc Q : ℕ) (hQR : R + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l) :
    TorusAdj (AVRegularity.commutatorAdjoint (E := E) b Hc s) 1 R Kc (commConst M Kc Bb) := by
  have hD : ∀ n : ℕ, n + 1 ≤ Q → ContDiff ℝ (n : ℕ) (fderiv ℝ (b s)) := fun n hn =>
    hb.fderiv_right (m := n) (by exact_mod_cast hn)
  have hDp : AVenhance.IsZ2Periodic (fderiv ℝ (b s)) :=
    fderiv_isZ2Periodic (hb.differentiable (by
      have : (1 : ℕ) ≤ Q := by omega
      exact_mod_cast (by omega : Q ≠ 0))) hp
  refine ((TorusAdj.sum (Finset.univ : Finset (Fin 2)) (fun j =>
    ((TorusAdj.coordDeriv (E := E) j R Kc).comp
      (TorusAdj.mulOp (M := fun x => commFluxMap E Hc j (fderiv ℝ (b s) x))
        (N := fun x => commPrimalMap E Hc j (fderiv ℝ (b s) x)) (R + 1) Kc
        (contDiff_clm_comp (commFluxMap E Hc j) (hD (R + 1) (by omega))) (isZ2Periodic_clm_comp _ hDp)
        (contDiff_clm_comp (commPrimalMap E Hc j) (hD Kc hQK)) (isZ2Periodic_clm_comp _ hDp)
        (fun x v w => inner_commPrimalVec Hc j _ v w) (commBound M Bb) (by
          intro l hl x
          have hl' : l + 1 ≤ Q := by omega
          refine (norm_array_clm_comp_le (commPrimalMap E Hc j) (fderiv ℝ (b s)) l
            (hD l hl') x).trans ?_
          unfold commBound
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul ((norm_commPrimalMap_le Hc j).trans
            (mul_le_mul_of_nonneg_left hM (by norm_num))) ?_ (norm_nonneg _) ?_
          · refine (norm_array_le_iteratedFDeriv _ l (hD l hl') x).trans ?_
            rw [norm_iteratedFDeriv_fderiv]
            exact mul_le_mul_of_nonneg_left (hBb l hl x) (by positivity)
          · linarith [covBound_nonneg Hc]))
      le_rfl le_rfl).ofOrder (Nat.add_zero 1))).mono le_rfl le_rfl (le_of_eq ?_)).ofOp ?_
  · simp [commConst]
  · funext ψ x
    refine Finset.sum_congr rfl fun j _ => ?_
    rfl

end Op
end

/-! The coarse response flux operator `ψ ↦ -(F_p^*(𝖰_p ψ))` as a `TorusAdj`, at a fixed time `s`,
of order `4p + D`.

With `M ≥ ∑ |H_{ij}|`, `cc` the commutator constant, `dg` the diagonal flux constant and
`κ = ∑_{l ≤ p} M^l / l!`, the constant is
`(∑_{l=1}^p (1/l!) ∑_{a<l} M^{l-1-a} cc M^a + κ dg) κ`. -/

section
/-- The commutator part of the constant of `F_p^*`. -/
def fluxConstA (M cc : ℝ) (p : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) *
    ∑ a ∈ Finset.range l, M ^ (l - 1 - a) * (cc * M ^ a)

/-- The constant of `F_p^*`. -/
def fluxConstF (M cc dg : ℝ) (p : ℕ) : ℝ := fluxConstA M cc p + covPolyConst M p * dg

/-- The constant of `ψ ↦ -(F_p^* 𝖰_p ψ)`. -/
def coarseFluxConst (M cc dg : ℝ) (p : ℕ) : ℝ := fluxConstF M cc dg p * covPolyConst M p

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- One term `𝒞^{l-1-a} 𝒥_H^* 𝒞^a` of `F_p^*`, as an operator of order `2p + D`. -/
def TorusAdj.coarseCommTerm (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (b : ℝ → Vec 2 → Vec 2) (s : ℝ) (R Kc Q p D l a : ℕ) (hal : a < l) (hlp : l ≤ p)
    (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l) :
    TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) =>
      (AVRegularity.covOperator Hc)^[l - 1 - a]
        (AVRegularity.commutatorAdjoint (E := E) b Hc s ((AVRegularity.covOperator Hc)^[a] ψ)))
      (2 * p + D) R Kc (M ^ (l - 1 - a) * (commConst M Kc Bb * M ^ a)) :=
  ((TorusAdj.covIter (E := E) Hc hM (l - 1 - a) R Kc).comp
    ((TorusAdj.commutator (E := E) b Hc hM s (R + 2 * (l - 1 - a)) Kc Q (by omega) hQK hb hbp Bb
        hBb).comp
      (TorusAdj.covIter (E := PiLp 2 (fun _ : Fin 2 => E)) Hc hM a (R + 2 * (l - 1 - a) + 1) Kc)
      le_rfl le_rfl) le_rfl le_rfl).liftOrder (by omega)

/-- The coarse response flux operator `ψ ↦ -(F_p(s)^* 𝖰_p ψ)`: order `4p + D`. The drift `b s`
and the diagonal-flux coefficients `AD d s` are `C^Q` periodic, with `R + 2p + D + 2 ≤ Q` and
`Kc + 1 ≤ Q`; `Bb l` bounds `‖D^{l+1}(b s)‖` and `BA d l` bounds the `l`-th derivative array
of `AD d s`, for `l ≤ Kc`. -/
def TorusAdj.coarseFlux (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (b : ℝ → Vec 2 → Vec 2) (D p : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (R Kc Q : ℕ) (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s)) (hAp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (BA : ℕ → ℕ → ℝ)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l) :
    TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) =>
      fun x => -(AVRegularity.coarseFluxAdjoint D b AD Hc p s
        (AVRegularity.covPolyQ Hc p ψ) x)) (4 * p + D) R Kc
      (coarseFluxConst M (commConst M Kc Bb) (diagConst D Kc BA) p) :=
  ((((((TorusAdj.sumMem (Finset.Icc 1 p) fun l hl =>
        (TorusAdj.sumMem (Finset.range l) fun a ha =>
          TorusAdj.coarseCommTerm (E := E) Hc hM b s R Kc Q p D l a (Finset.mem_range.mp ha)
            (Finset.mem_Icc.mp hl).2 hQR hQK hb hbp Bb hBb).smul ((l.factorial : ℝ)⁻¹)).mono
      le_rfl le_rfl (le_of_eq (by
        unfold fluxConstA
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]))).sub
    (((TorusAdj.covPolyP (E := E) Hc hM p R Kc).comp
      (TorusAdj.diagFlux (E := E) D AD s (R + 2 * p) Kc Q (by omega) (by omega) hA hAp BA hBA)
      le_rfl le_rfl).liftOrder (by omega : 2 * p + (D - 1) ≤ 2 * p + D))).ofOp
    (by
      funext ψ x
      simp [AVRegularity.coarseFluxAdjoint, Finset.sum_apply])).comp
    (TorusAdj.covPolyQ (E := PiLp 2 (fun _ : Fin 2 => E)) Hc hM p (R + (2 * p + D)) Kc)
    le_rfl le_rfl).neg.ofOrder (by omega : 2 * p + D + 2 * p = 4 * p + D)) |>.mono le_rfl le_rfl
    (le_of_eq rfl)

/-- The constant of `ψ ↦ 𝖯_p (F_E^*(𝖰_p ψ))_u` for one source component. -/
def edgeFluxPairConst (M : ℝ) (p : ℕ) (ec : ℝ) : ℝ := covPolyConst M p * (ec * covPolyConst M p)

/-- The `(v,u)` block of the edge flux operator `ψ ↦ 𝖯_p (F_E(s)^* 𝖰_p ψ)_u`, for a single source
component `ψ` valued in `ℝ² ⊗ h v`: order `4p + D`. The coefficients `CE r v u d s` are `C^Q`
periodic with `R + 2p + D ≤ Q` and `Kc ≤ Q`; `BE r d l` bounds their `l`-th derivative arrays. -/
def TorusAdj.edgeFluxPair {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M) (D H p : ℕ)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (v u : ι) (s : ℝ) (R Kc Q : ℕ) (hQR : R + 2 * p + D ≤ Q) (hQK : Kc ≤ Q)
    (hC : ∀ r d, ContDiff ℝ (Q : ℕ) (CE r v u d s))
    (hp : ∀ r d, AVenhance.IsZ2Periodic (CE r v u d s)) (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (CE r v u d s) l x‖ ≤ BE r d.1 l) :
    TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.covPolyP Hc p (fun x => ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
        AVRegularity.wordAdjoint (d.1 - 1)
          (fun y => ContinuousLinearMap.adjoint (CE r v u d s y)
            (AVRegularity.covPolyQ Hc p ψ y)) x)) (4 * p + D) R Kc
      (edgeFluxPairConst M p (edgeConst D H Kc BE)) :=
  ((TorusAdj.covPolyP (E := h u) Hc hM p R Kc).comp
    ((TorusAdj.edgeFluxBlock (X := h v) (Y := h u) D H (fun r d => CE r v u d s)
      (R + 2 * p) Kc Q (by omega) hQK hC hp BE hBE).comp
      (TorusAdj.covPolyQ (E := PiLp 2 (fun _ : Fin 2 => h v)) Hc hM p
        (R + 2 * p + (D - 1)) Kc) le_rfl le_rfl) le_rfl le_rfl).liftOrder
    (by omega : 2 * p + (D - 1 + 2 * p) ≤ 4 * p + D)
end

end AVRegularity.CycleComparison.Coarse
end
