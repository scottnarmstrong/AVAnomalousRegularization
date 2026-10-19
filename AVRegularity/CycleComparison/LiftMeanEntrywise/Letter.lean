-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.SecondCrossMean
import AVRegularity.CycleComparison.Lift.PositiveMeanCoefficientsAmbient
import AVRegularity.CycleComparison.Lift.SettingPairedCoefficientOriginalReserve
public import AVRegularity.CycleComparison.Lift.CellFieldAmbientBoxReserve
public import AVRegularity.CycleComparison.Lift.SettingLiftALeftTermsActionOfCoefficients
import AVRegularity.CycleComparison.Lift.SettingLiftAPolynomial
import AVRegularity.CycleComparison.Lift.SettingSourceLiftConvolutionAllDegrees
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.LiftMeanEntrywise

/-! Constant invertible changes of the component frame `∀ i, h i` commute with the
source-degree-zero lift recursion: the cross operators `ℬ_1`, `ℬ_2`, the cell mean and the
literal coefficient action are all equivariant under conjugation of the block coefficients by a
continuous linear equivalence (at source degree zero the operators are component independent).
No regularity is needed, since `fderiv` commutes with an equivalence. -/

section
section Frame
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem orderedDerivative_continuousLinearEquiv (S : E ≃L[ℝ] F) {m : ℕ}
    (α : DerivativeWord2 m) (g : Vec 2 → E) (Y : Vec 2) :
    orderedDerivative α (fun X => S (g X)) Y = S (orderedDerivative α g Y) := by
  have key : ∀ (l : List (Fin 2)) (g : Vec 2 → E),
      l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) (fun X => S (g X)) =
        fun Y => S (l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) g Y) := by
    intro l
    induction l with
    | nil => intro g; rfl
    | cons i l ih =>
      intro g
      simp only [List.foldl_cons]
      have hstep : (fun x => fderiv ℝ (fun X => S (g X)) x (basisVec i)) =
          fun x => S (fderiv ℝ g x (basisVec i)) := by
        funext x
        exact congrArg (fun A => A (basisVec i)) (S.comp_fderiv (f := g) (x := x))
      rw [hstep]
      exact ih (fun x => fderiv ℝ g x (basisVec i))
  exact congrFun (key (List.ofFn α) g) Y

theorem slowPartial_continuousLinearEquiv (S : E ≃L[ℝ] F) (i : Fin 2)
    (Φ : Vec 2 → Vec 2 → E) (X z : Vec 2) :
    slowPartial i (fun X' z' => S (Φ X' z')) X z = S (slowPartial i Φ X z) :=
  congrArg (fun A => A (basisVec i)) (S.comp_fderiv (f := fun X' => Φ X' z) (x := X))

theorem fastPartial_continuousLinearEquiv (S : E ≃L[ℝ] F) (i : Fin 2)
    (Φ : Vec 2 → Vec 2 → E) (X z : Vec 2) :
    fastPartial i (fun X' z' => S (Φ X' z')) X z = S (fastPartial i Φ X z) :=
  congrArg (fun A => A (basisVec i)) (S.comp_fderiv (f := fun z' => Φ X z') (x := z))

theorem cellB1_continuousLinearEquiv (S : E ≃L[ℝ] F) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (Φ : Vec 2 → Vec 2 → E) (X z : Vec 2) :
    cellB1 η G v t (fun X' z' => S (Φ X' z')) X z = S (cellB1 η G v t Φ X z) := by
  have hs (j : Fin 2) : slowPartial j (fun X' z' => S (Φ X' z')) =
      fun X' z' => S (slowPartial j Φ X' z') := by
    funext X' z'
    exact slowPartial_continuousLinearEquiv S j Φ X' z'
  have hf (i j : Fin 2) :
      (fun X' z' => G t X' i j • fastPartial j (fun X'' z'' => S (Φ X'' z'')) X' z') =
        fun X' z' => S (G t X' i j • fastPartial j Φ X' z') := by
    funext X' z'
    rw [fastPartial_continuousLinearEquiv S j Φ X' z', map_smul]
  have h1 (k : Fin 2) : slowPartial k (fun X' z' => S (Φ X' z')) X z =
      S (slowPartial k Φ X z) := slowPartial_continuousLinearEquiv S k Φ X z
  have h2 (i j : Fin 2) : fastPartial i (slowPartial j (fun X' z' => S (Φ X' z'))) X z =
      S (fastPartial i (slowPartial j Φ) X z) := by
    rw [hs j]
    exact fastPartial_continuousLinearEquiv S i (slowPartial j Φ) X z
  have h3 (i j : Fin 2) :
      slowPartial i (fun X' z' => G t X' i j •
        fastPartial j (fun X'' z'' => S (Φ X'' z'')) X' z') X z =
      S (slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z') X z) := by
    rw [hf i j]
    exact slowPartial_continuousLinearEquiv S i _ X z
  simp only [cellB1, h1, h2, h3, map_sub, map_sum, map_smul, map_add]

theorem cellB2_continuousLinearEquiv (S : E ≃L[ℝ] F) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ) (Φ : Vec 2 → Vec 2 → E) (X z : Vec 2) :
    cellB2 η G t (fun X' z' => S (Φ X' z')) X z = S (cellB2 η G t Φ X z) := by
  have hg (i j : Fin 2) :
      (fun X' z' => G t X' i j • slowPartial j (fun X'' z'' => S (Φ X'' z'')) X' z') =
        fun X' z' => S (G t X' i j • slowPartial j Φ X' z') := by
    funext X' z'
    rw [slowPartial_continuousLinearEquiv S j Φ X' z', map_smul]
  have h4 (i j : Fin 2) :
      slowPartial i (fun X' z' => G t X' i j •
        slowPartial j (fun X'' z'' => S (Φ X'' z'')) X' z') X z =
      S (slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z') X z) := by
    rw [hg i j]
    exact slowPartial_continuousLinearEquiv S i _ X z
  simp only [cellB2, h4, map_neg, map_smul, map_sum]

end Frame

section Blocks
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The operator on `∀ i, h i` with block entries `c v u : h u →L h v`. -/
def blockOperator (c : ∀ v u : ι, h u →L[ℝ] h v) : (∀ i, h i) →L[ℝ] (∀ i, h i) :=
  ContinuousLinearMap.pi fun v => ∑ u, (c v u).comp (ContinuousLinearMap.proj u)

omit [DecidableEq ι] in
theorem blockOperator_apply (c : ∀ v u : ι, h u →L[ℝ] h v) (ξ : ∀ i, h i) (v : ι) :
    blockOperator c ξ v = ∑ u, c v u (ξ u) := by
  simp [blockOperator]

/-- The block entries of `S⁻¹ ∘ c ∘ S`. -/
def conjugateEntry (S : (∀ i, h i) ≃L[ℝ] (∀ i, h i)) (c : ∀ v u : ι, h u →L[ℝ] h v)
    (v u : ι) : h u →L[ℝ] h v :=
  ((ContinuousLinearMap.proj v).comp
    (((S.symm : (∀ i, h i) →L[ℝ] (∀ i, h i)).comp (blockOperator c)).comp
      (S : (∀ i, h i) →L[ℝ] (∀ i, h i)))).comp (ContinuousLinearMap.single ℝ h u)

theorem conjugateEntry_sum (S : (∀ i, h i) ≃L[ℝ] (∀ i, h i))
    (c : ∀ v u : ι, h u →L[ℝ] h v) (v : ι) (y : ∀ i, h i) :
    ∑ u, conjugateEntry S c v u (y u) = S.symm (blockOperator c (S y)) v := by
  unfold conjugateEntry
  rw [ContinuousLinearMap.sum_comp_single]
  rfl

theorem blockOperator_conjugateEntry (S : (∀ i, h i) ≃L[ℝ] (∀ i, h i))
    (c : ∀ v u : ι, h u →L[ℝ] h v) :
    blockOperator (conjugateEntry S c) =
      (S.symm : (∀ i, h i) →L[ℝ] (∀ i, h i)).comp
        ((blockOperator c).comp (S : (∀ i, h i) →L[ℝ] (∀ i, h i))) := by
  apply ContinuousLinearMap.ext
  intro ξ
  funext v
  rw [blockOperator_apply, conjugateEntry_sum]
  rfl

/-- Conjugation of a lift coefficient array, entry by entry. -/
def conjugateCoeff (S : (∀ i, h i) ≃L[ℝ] (∀ i, h i)) (c : LiftCoeff ι h) : LiftCoeff ι h :=
  fun m α t X z => conjugateEntry S (c m α t X z)

/-- Conjugation of a whole lift sequence. -/
abbrev conjugateSequence (S : (∀ i, h i) ≃L[ℝ] (∀ i, h i)) (Cc : ℕ → ℕ → LiftCoeff ι h) :
    ℕ → ℕ → LiftCoeff ι h :=
  fun hh q => conjugateCoeff S (Cc hh q)

theorem liftApply_conjugateCoeff (S : (∀ i, h i) ≃L[ℝ] (∀ i, h i)) (n : ℕ) (c : LiftCoeff ι h)
    (a b : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (hab : ∀ Y, b t Y = S (a t Y)) (X z : Vec 2) :
    liftApply n (conjugateCoeff S c) a t X z = S.symm (liftApply n c b t X z) := by
  have hb : b t = fun Y => S (a t Y) := funext hab
  have hc : liftApply n c b t X z = ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m,
      blockOperator (c m α t X z) (S (orderedDerivative α (a t) X)) := by
    funext v
    simp only [liftApply, hb, Finset.sum_apply, blockOperator_apply,
      orderedDerivative_continuousLinearEquiv]
  rw [hc, map_sum]
  funext v
  simp only [liftApply, conjugateCoeff, conjugateEntry_sum, map_sum, Finset.sum_apply]

variable {D : ℕ}

omit [DecidableEq ι] in
theorem liftA_grade_zero (Q : LiftOperatorData ι h D) (C : ℕ → ℕ → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (n : ℕ) (t : ℝ) (X z : Vec 2) :
    liftA Q C f 0 n t X z = cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (C 0 (n - 1)) f t) X z +
      (if 2 ≤ n then cellB2 Q.η Q.G t (liftApply (n - 2) (C 0 (n - 2)) f t) X z else 0) := by
  show cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (C 0 (n - 1)) f t) X z +
      (if 2 ≤ n then cellB2 Q.η Q.G t (liftApply (n - 2) (C 0 (n - 2)) f t) X z else 0) -
      (if (0 : ℕ) = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
        sourceCoeff Q.edge Q.η j t (liftApply (n - j) (C (0 - 1) (n - j)) f t) X z) = _
  rw [ite_eq_left (rfl : (0 : ℕ) = 0), sub_zero]

theorem liftA_conjugate_zero (Q : LiftOperatorData ι h D) (S : (∀ i, h i) ≃L[ℝ] (∀ i, h i))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a b : ℝ → Vec 2 → ∀ i, h i)
    (hab : ∀ s Y, b s Y = S (a s Y)) (n : ℕ) (t : ℝ) (X z : Vec 2) :
    liftA Q (conjugateSequence S Cc) a 0 n t X z = S.symm (liftA Q Cc b 0 n t X z) := by
  have hL (q : ℕ) : liftApply q (conjugateSequence S Cc 0 q) a t =
      fun X' z' => S.symm (liftApply q (Cc 0 q) b t X' z') := by
    funext X' z'
    exact liftApply_conjugateCoeff S q (Cc 0 q) a b t (hab t) X' z'
  rw [liftA_grade_zero, liftA_grade_zero, hL, hL, cellB1_continuousLinearEquiv,
    cellB2_continuousLinearEquiv]
  split_ifs
  · rw [map_add]
  · rw [map_add, map_zero]

theorem liftMean_conjugate_zero (Q : LiftOperatorData ι h D) (S : (∀ i, h i) ≃L[ℝ] (∀ i, h i))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a b : ℝ → Vec 2 → ∀ i, h i)
    (hab : ∀ s Y, b s Y = S (a s Y)) (n : ℕ) (t : ℝ) (X : Vec 2) :
    liftMean Q (conjugateSequence S Cc) a 0 n t X = S.symm (liftMean Q Cc b 0 n t X) := by
  have he : (fun z => liftA Q (conjugateSequence S Cc) a 0 n t X z) =
      fun z => S.symm (liftA Q Cc b 0 n t X z) :=
    funext fun z => liftA_conjugate_zero Q S Cc a b hab n t X z
  change fieldCellMean (fun z => liftA Q (conjugateSequence S Cc) a 0 n t X z) =
    S.symm (fieldCellMean (fun z => liftA Q Cc b 0 n t X z))
  rw [he]
  exact S.symm.integral_comp_comm _

theorem liftCellSource_conjugate_zero (Q : LiftOperatorData ι h D)
    (S : (∀ i, h i) ≃L[ℝ] (∀ i, h i)) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a b : ℝ → Vec 2 → ∀ i, h i) (hab : ∀ s Y, b s Y = S (a s Y)) (n : ℕ) (t : ℝ)
    (X z : Vec 2) :
    liftCellSource Q (conjugateSequence S Cc) a 0 n t X z =
      S.symm (liftCellSource Q Cc b 0 n t X z) := by
  have hT (j : ℕ) : liftApply j (conjugateSequence S Cc 0 j)
      (liftMean Q (conjugateSequence S Cc) a 0 (n - j)) t X z =
      S.symm (liftApply j (Cc 0 j) (liftMean Q Cc b 0 (n - j)) t X z) :=
    liftApply_conjugateCoeff S j (Cc 0 j) _ _ t
      (fun Y => by rw [liftMean_conjugate_zero Q S Cc a b hab (n - j) t Y,
        ContinuousLinearEquiv.apply_symm_apply]) X z
  have hsum : (∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal 0,
      liftApply j (conjugateSequence S Cc p.1 j)
        (liftMean Q (conjugateSequence S Cc) a p.2 (n - j)) t X z) =
      S.symm (∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal 0,
        liftApply j (Cc p.1 j) (liftMean Q Cc b p.2 (n - j)) t X z) := by
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hT, map_sum]
  change -(liftA Q (conjugateSequence S Cc) a 0 n t X z -
      liftMean Q (conjugateSequence S Cc) a 0 n t X) +
      (∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal 0,
        liftApply j (conjugateSequence S Cc p.1 j)
          (liftMean Q (conjugateSequence S Cc) a p.2 (n - j)) t X z) =
    S.symm (-(liftA Q Cc b 0 n t X z - liftMean Q Cc b 0 n t X) +
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal 0,
        liftApply j (Cc p.1 j) (liftMean Q Cc b p.2 (n - j)) t X z)
  rw [hsum, liftA_conjugate_zero Q S Cc a b hab, liftMean_conjugate_zero Q S Cc a b hab,
    map_add, map_neg, map_sub]

end Blocks
end

/-! Slow translations `X ↦ X + T` commute with the lift recursion when the metric and the
source coefficients are `T`-invariant: every operator of the recursion (`ℬ_1`, `ℬ_2`,
`𝒮_j`, the source fluxes, the cell mean and the literal coefficient action) is pointwise in `X`
up to slow derivatives, and `∂_X` commutes with translations. -/

section
section Frame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem slowPartial_slowShift (i : Fin 2) (Φ : Vec 2 → Vec 2 → E) (T X z : Vec 2) :
    slowPartial i (fun X' z' => Φ (X' + T) z') X z = slowPartial i Φ (X + T) z :=
  congrArg (fun A => A (basisVec i))
    (fderiv_comp_add_right (𝕜 := ℝ) (f := fun X' => Φ X' z) (x := X) T)

theorem fastPartial_slowShift (i : Fin 2) (Φ : Vec 2 → Vec 2 → E) (T X z : Vec 2) :
    fastPartial i (fun X' z' => Φ (X' + T) z') X z = fastPartial i Φ (X + T) z := rfl

theorem orderedDerivative_slowShift {m : ℕ} (α : DerivativeWord2 m) (g : Vec 2 → E)
    (T Y : Vec 2) :
    orderedDerivative α (fun X => g (X + T)) Y = orderedDerivative α g (Y + T) := by
  have key : ∀ (l : List (Fin 2)) (g : Vec 2 → E),
      l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) (fun X => g (X + T)) =
        fun Y => l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) g (Y + T) := by
    intro l
    induction l with
    | nil => intro g; rfl
    | cons i l ih =>
      intro g
      simp only [List.foldl_cons]
      have hstep : (fun x => fderiv ℝ (fun X => g (X + T)) x (basisVec i)) =
          fun x => fderiv ℝ g (x + T) (basisVec i) := by
        funext x
        rw [fderiv_comp_add_right]
      rw [hstep]
      exact ih (fun x => fderiv ℝ g x (basisVec i))
  exact congrFun (key (List.ofFn α) g) Y

theorem dEps_slowShift (η ε : ℝ) (i : Fin 2) (Ψ : Vec 2 → Vec 2 → E) (T X z : Vec 2) :
    dEps η ε i (fun X' z' => Ψ (X' + T) z') X z = dEps η ε i Ψ (X + T) z := by
  simp only [dEps, fastPartial_slowShift, slowPartial_slowShift]

theorem dEpsWord_slowShift (η ε : ℝ) {m : ℕ} (α : DerivativeWord2 m)
    (Ψ : Vec 2 → Vec 2 → E) (T : Vec 2) :
    dEpsWord η ε α (fun X' z' => Ψ (X' + T) z') = fun X z => dEpsWord η ε α Ψ (X + T) z := by
  have key : ∀ (l : List (Fin 2)) (Ψ : Vec 2 → Vec 2 → E),
      l.foldl (fun Ψ' i => dEps η ε i Ψ') (fun X' z' => Ψ (X' + T) z') =
        fun X z => l.foldl (fun Ψ' i => dEps η ε i Ψ') Ψ (X + T) z := by
    intro l
    induction l with
    | nil => intro Ψ; rfl
    | cons i l ih =>
      intro Ψ
      simp only [List.foldl_cons]
      have hstep : dEps η ε i (fun X' z' => Ψ (X' + T) z') =
          fun X z => dEps η ε i Ψ (X + T) z := by
        funext X z
        exact dEps_slowShift η ε i Ψ T X z
      rw [hstep]
      exact ih (dEps η ε i Ψ)
  exact key (List.ofFn α) Ψ

theorem cellB1_slowShift (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (Φ : Vec 2 → Vec 2 → E) (T : Vec 2)
    (hG : ∀ X i j, G t (X + T) i j = G t X i j) (X z : Vec 2) :
    cellB1 η G v t (fun X' z' => Φ (X' + T) z') X z = cellB1 η G v t Φ (X + T) z := by
  have hs (j : Fin 2) : slowPartial j (fun X' z' => Φ (X' + T) z') =
      fun X' z' => slowPartial j Φ (X' + T) z' := by
    funext X' z'
    exact slowPartial_slowShift j Φ T X' z'
  have hg (i j : Fin 2) :
      (fun X' z' => G t X' i j • fastPartial j (fun X'' z'' => Φ (X'' + T) z'') X' z') =
        fun X' z' => (fun Y y => G t Y i j • fastPartial j Φ Y y) (X' + T) z' := by
    funext X' z'
    simp only [hG]
    rfl
  have h1 (k : Fin 2) : slowPartial k (fun X' z' => Φ (X' + T) z') X z =
      slowPartial k Φ (X + T) z := slowPartial_slowShift k Φ T X z
  have h2 (i j : Fin 2) : fastPartial i (slowPartial j (fun X' z' => Φ (X' + T) z')) X z =
      fastPartial i (slowPartial j Φ) (X + T) z := by
    rw [hs j]
    rfl
  have h3 (i j : Fin 2) :
      slowPartial i (fun X' z' => G t X' i j •
        fastPartial j (fun X'' z'' => Φ (X'' + T) z'') X' z') X z =
      slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z') (X + T) z := by
    rw [hg i j]
    exact slowPartial_slowShift i (fun Y y => G t Y i j • fastPartial j Φ Y y) T X z
  simp only [cellB1, h1, h2, h3, hG]

theorem cellB2_slowShift (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (Φ : Vec 2 → Vec 2 → E) (T : Vec 2) (hG : ∀ X i j, G t (X + T) i j = G t X i j)
    (X z : Vec 2) :
    cellB2 η G t (fun X' z' => Φ (X' + T) z') X z = cellB2 η G t Φ (X + T) z := by
  have hg (i j : Fin 2) :
      (fun X' z' => G t X' i j • slowPartial j (fun X'' z'' => Φ (X'' + T) z'') X' z') =
        fun X' z' => (fun Y y => G t Y i j • slowPartial j Φ Y y) (X' + T) z' := by
    funext X' z'
    simp only [slowPartial_slowShift, hG]
  have h4 (i j : Fin 2) :
      slowPartial i (fun X' z' => G t X' i j •
        slowPartial j (fun X'' z'' => Φ (X'' + T) z'') X' z') X z =
      slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z') (X + T) z := by
    rw [hg i j]
    exact slowPartial_slowShift i (fun Y y => G t Y i j • slowPartial j Φ Y y) T X z
  simp only [cellB2, h4]

end Frame

section Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The coefficient array read at the translated slow position `X + T`. -/
def slowShiftCoeff (T : Vec 2) (c : LiftCoeff ι h) : LiftCoeff ι h :=
  fun m α s Y y => c m α s (Y + T) y

/-- The lift sequence read at the translated slow position `X + T`. -/
abbrev slowShiftSequence (T : Vec 2) (Cc : ℕ → ℕ → LiftCoeff ι h) : ℕ → ℕ → LiftCoeff ι h :=
  fun hh q => slowShiftCoeff T (Cc hh q)

theorem sourceFlux_slowShift (edge : ConstituentEdges D h) (η ε t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (T : Vec 2)
    (hc : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (k : Fin 2) (X z : Vec 2) :
    sourceFlux edge η ε t (fun X' z' => Φ (X' + T) z') k X z =
      sourceFlux edge η ε t Φ k (X + T) z := by
  funext v
  simp only [sourceFlux, dEpsWord_slowShift]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  apply List.map_congr_left
  intro γ hγ
  apply Finset.sum_congr rfl
  intro α _
  rw [hc v u d γ hγ α X z]

theorem sourceOp_slowShift (edge : ConstituentEdges D h) (η ε t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (T : Vec 2)
    (hc : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (X z : Vec 2) :
    sourceOp edge η ε t (fun X' z' => Φ (X' + T) z') X z = sourceOp edge η ε t Φ (X + T) z := by
  have hf (k : Fin 2) : sourceFlux edge η ε t (fun X' z' => Φ (X' + T) z') k =
      fun X' z' => sourceFlux edge η ε t Φ k (X' + T) z' := by
    funext X' z'
    exact sourceFlux_slowShift edge η ε t Φ T hc k X' z'
  simp only [sourceOp, hf, dEps_slowShift]

theorem sourceCoeff_slowShift (edge : ConstituentEdges D h) (η : ℝ) (j : ℕ) (t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (T : Vec 2)
    (hc : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (X z : Vec 2) :
    sourceCoeff edge η j t (fun X' z' => Φ (X' + T) z') X z =
      sourceCoeff edge η j t Φ (X + T) z := by
  have he : (fun ε => sourceOp edge η ε t (fun X' z' => Φ (X' + T) z') X z) =
      fun ε => sourceOp edge η ε t Φ (X + T) z :=
    funext fun ε => sourceOp_slowShift edge η ε t Φ T hc X z
  simp only [sourceCoeff, he]

theorem sourceFluxCoeff_slowShift (edge : ConstituentEdges D h) (η : ℝ) (j : ℕ) (t : ℝ)
    (Φ : ℝ → Vec 2 → Vec 2 → ∀ i, h i) (T : Vec 2)
    (hc : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (k : Fin 2) (X z : Vec 2) :
    sourceFluxCoeff edge η j t (fun ε X' z' => Φ ε (X' + T) z') k X z =
      sourceFluxCoeff edge η j t Φ k (X + T) z := by
  have he : (fun ε => sourceFlux edge η ε t (fun X' z' => Φ ε (X' + T) z') k X z) =
      fun ε => sourceFlux edge η ε t (Φ ε) k (X + T) z :=
    funext fun ε => sourceFlux_slowShift edge η ε t (Φ ε) T hc k X z
  simp only [sourceFluxCoeff, he]

theorem liftApply_slowShift (n : ℕ) (c : LiftCoeff ι h) (a b : ℝ → Vec 2 → ∀ i, h i)
    (T : Vec 2) (t : ℝ) (hab : ∀ Y, b t Y = a t (Y + T)) (X z : Vec 2) :
    liftApply n (slowShiftCoeff T c) b t X z = liftApply n c a t (X + T) z := by
  have hb : b t = fun Y => a t (Y + T) := funext hab
  funext v
  simp only [liftApply, slowShiftCoeff, hb, orderedDerivative_slowShift]

theorem liftPolyField_slowShift (Cc : ℕ → ℕ → LiftCoeff ι h) (N : ℕ) (ε : ℝ) (hh : ℕ)
    (a b : ℝ → Vec 2 → ∀ i, h i) (T : Vec 2) (t : ℝ) (hab : ∀ Y, b t Y = a t (Y + T))
    (X z : Vec 2) :
    liftPolyField (slowShiftSequence T Cc) N ε hh b t X z =
      liftPolyField Cc N ε hh a t (X + T) z := by
  simp only [liftPolyField, liftApply_slowShift _ _ a b T t hab]

theorem liftA_slowShift (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a b : ℝ → Vec 2 → ∀ i, h i) (T : Vec 2) (hab : ∀ s Y, b s Y = a s (Y + T))
    (hG : ∀ t X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (hh n : ℕ) (t : ℝ) (X z : Vec 2) :
    liftA Q (slowShiftSequence T Cc) b hh n t X z = liftA Q Cc a hh n t (X + T) z := by
  have hL (q p : ℕ) : liftApply q (slowShiftCoeff T (Cc p q)) b t =
      fun X' z' => liftApply q (Cc p q) a t (X' + T) z' := by
    funext X' z'
    exact liftApply_slowShift q (Cc p q) a b T t (hab t) X' z'
  have hB1 (Φ : Vec 2 → Vec 2 → ∀ i, h i) (X' z' : Vec 2) :
      cellB1 Q.η Q.G Q.v t (fun Y y => Φ (Y + T) y) X' z' = cellB1 Q.η Q.G Q.v t Φ (X' + T) z' :=
    cellB1_slowShift Q.η Q.G Q.v t Φ T (hG t) X' z'
  have hB2 (Φ : Vec 2 → Vec 2 → ∀ i, h i) (X' z' : Vec 2) :
      cellB2 Q.η Q.G t (fun Y y => Φ (Y + T) y) X' z' = cellB2 Q.η Q.G t Φ (X' + T) z' :=
    cellB2_slowShift Q.η Q.G t Φ T (hG t) X' z'
  have hS (j : ℕ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (X' z' : Vec 2) :
      sourceCoeff Q.edge Q.η j t (fun Y y => Φ (Y + T) y) X' z' =
        sourceCoeff Q.edge Q.η j t Φ (X' + T) z' :=
    sourceCoeff_slowShift Q.edge Q.η j t Φ T
      (fun v u d γ hγ α X z => hc v u d γ hγ α t X z) X' z'
  simp only [liftA, hL, hB1, hB2, hS]

theorem liftMean_slowShift (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a b : ℝ → Vec 2 → ∀ i, h i) (T : Vec 2) (hab : ∀ s Y, b s Y = a s (Y + T))
    (hG : ∀ t X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (hh n : ℕ) (t : ℝ) (X : Vec 2) :
    liftMean Q (slowShiftSequence T Cc) b hh n t X = liftMean Q Cc a hh n t (X + T) := by
  have he : (fun z => liftA Q (slowShiftSequence T Cc) b hh n t X z) =
      fun z => liftA Q Cc a hh n t (X + T) z :=
    funext fun z => liftA_slowShift Q Cc a b T hab hG hc hh n t X z
  change fieldCellMean (fun z => liftA Q (slowShiftSequence T Cc) b hh n t X z) =
    fieldCellMean (fun z => liftA Q Cc a hh n t (X + T) z)
  rw [he]

theorem liftCellSource_slowShift (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a b : ℝ → Vec 2 → ∀ i, h i) (T : Vec 2) (hab : ∀ s Y, b s Y = a s (Y + T))
    (hG : ∀ t X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (hh n : ℕ) (t : ℝ) (X z : Vec 2) :
    liftCellSource Q (slowShiftSequence T Cc) b hh n t X z =
      liftCellSource Q Cc a hh n t (X + T) z := by
  have hT (j : ℕ) (p : ℕ × ℕ) : liftApply j (slowShiftSequence T Cc p.1 j)
      (liftMean Q (slowShiftSequence T Cc) b p.2 (n - j)) t X z =
      liftApply j (Cc p.1 j) (liftMean Q Cc a p.2 (n - j)) t (X + T) z :=
    liftApply_slowShift j (Cc p.1 j) _ _ T t
      (fun Y => liftMean_slowShift Q Cc a b T hab hG hc p.2 (n - j) t Y) X z
  change -(liftA Q (slowShiftSequence T Cc) b hh n t X z -
      liftMean Q (slowShiftSequence T Cc) b hh n t X) +
      (∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
        liftApply j (slowShiftSequence T Cc p.1 j)
          (liftMean Q (slowShiftSequence T Cc) b p.2 (n - j)) t X z) =
    -(liftA Q Cc a hh n t (X + T) z - liftMean Q Cc a hh n t (X + T)) +
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
        liftApply j (Cc p.1 j) (liftMean Q Cc a p.2 (n - j)) t (X + T) z
  rw [liftA_slowShift Q Cc a b T hab hG hc, liftMean_slowShift Q Cc a b T hab hG hc]
  simp only [hT]

end Lift
end

end AVRegularity.CycleComparison.LiftMeanEntrywise
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.LiftMeanEntrywise

/-! Time measurability of the covariant word coefficients and of the componentwise source-flux
coefficients, at their exact rectangular reserves (`j` slow and `|w| - j` fast derivatives). -/

section
section Covariant
variable {T E : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem covariantListCoefficient_parameter_measurable_reserve (η : ℝ) (w : List (Fin 2)) :
    ∀ (f : T → Vec 2 → Vec 2 → E), (∀ X z, Measurable (fun t => f t X z)) →
      ∀ m, m ≤ w.length → (∀ t, IsBoxSmooth m (w.length - m) (f t)) →
      ∀ X z, Measurable (fun t => covariantListCoefficients η w (f t) m X z) := by
  induction w using List.reverseRecOn with
  | nil =>
    intro f hm m _ _ X z
    simp only [covariantListCoefficients_nil]
    split_ifs
    · exact hm X z
    · exact measurable_const
  | append_singleton w k ih =>
    intro f hm m hmw hf X z
    have hlen : (w ++ [k]).length = w.length + 1 := by simp
    simp only [covariantListCoefficients_append_singleton, covariantCoefficientStep]
    apply Measurable.add
    · by_cases hmw' : m ≤ w.length
      · have hb (t : T) : IsBoxSmooth 0 1 (covariantListCoefficients η w (f t) m) :=
          covariantListCoefficient_box_reserve η w m 0 1 (f t) hmw'
            ((hf t).mono (by omega) (by omega))
        exact fastPartial_parameter_measurable _
          (ih f hm m hmw' (fun t => (hf t).mono le_rfl (by omega)))
          (fun t Y => ((hb t).1 Y).differentiable one_ne_zero) k X z
      · simp only [covariantListCoefficients_above_degree η w _ m (by omega)]
        exact measurable_const
    · split_ifs with hm0
      · exact measurable_const
      · have hb (t : T) : IsBoxSmooth 1 0 (covariantListCoefficients η w (f t) (m - 1)) :=
          covariantListCoefficient_box_reserve η w (m - 1) 1 0 (f t) (by omega)
            ((hf t).mono (by omega) (by omega))
        exact (slowPartial_parameter_measurable _
          (ih f hm (m - 1) (by omega) (fun t => (hf t).mono (by omega) (by omega)))
          (fun t y => (boxSmooth_slow_contDiff (hb t) y).differentiable one_ne_zero)
          k X z).const_smul (Real.sqrt η)

end Covariant

section Source
variable {ι T : Type*} [Fintype ι] [MeasurableSpace T] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, SecondCountableTopology (h i)] {D : ℕ}

theorem sourceFluxComponentCoefficient_parameter_measurable (edge : ConstituentEdges D h)
    (η : ℝ) (τ : T → ℝ) (Φ : T → Vec 2 → Vec 2 → ∀ i, h i) (j : ℕ)
    (hm : ∀ X z u, Measurable (fun t => Φ t X z u))
    (hf : ∀ t u, IsBoxSmooth j (D - 1 - j) (fun X z => Φ t X z u))
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z, Measurable (fun t => γ.coeff α (τ t) X z))
    (k : Fin 2) (v : ι) (X z : Vec 2) :
    Measurable (fun t => sourceFluxComponentCoefficient edge η (τ t) (Φ t) k j v X z) := by
  classical
  unfold sourceFluxComponentCoefficient
  apply Finset.measurable_sum
  intro u _
  apply Finset.measurable_sum
  intro d _
  have hc (γ : Constituent d.1 (h u) (h v)) (hγ : γ ∈ edge v u d) :
      Measurable (fun t => ∑ α : DerivativeWord2 (d.1 - 1),
        γ.coeff α (τ t) X z k • γ.map
          (covariantListCoefficients η (List.ofFn α) (fun Y y => Φ t Y y u) j X z)) := by
    apply Finset.measurable_sum
    intro α _
    have hw : Measurable (fun t =>
        covariantListCoefficients η (List.ofFn α) (fun Y y => Φ t Y y u) j X z) := by
      by_cases hj : j ≤ (List.ofFn α).length
      · refine covariantListCoefficient_parameter_measurable_reserve η (List.ofFn α)
          (fun t Y y => Φ t Y y u) (fun Y y => hm Y y u) j hj (fun t => ?_) X z
        have hd := (Finset.mem_Icc.mp d.2).2
        have hlen : (List.ofFn α).length = d.1 - 1 := List.length_ofFn
        exact (hf t u).mono le_rfl (by omega)
      · simp only [covariantListCoefficients_above_degree η (List.ofFn α) _ j (by omega)]
        exact measurable_const
    exact ((measurable_pi_apply k).comp (hΓ v u d γ hγ α X z)).smul
      (γ.map.continuous.measurable.comp hw)
  have hl := List.measurable_fun_sum
    ((edge v u d).map fun γ => fun t => ∑ α : DerivativeWord2 (d.1 - 1),
      γ.coeff α (τ t) X z k • γ.map
        (covariantListCoefficients η (List.ofFn α) (fun Y y => Φ t Y y u) j X z))
    (by intro f hf'; obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hf'; exact hc γ hγ)
  simpa only [List.map_map, Function.comp_def] using hl

end Source
end

/-! Source-degree-zero lifts are scalar: `C_n^{(0)} = T_n I`.
The source-degree-zero recursion commutes with every constant change of component frame, so by
uniqueness of the lift sequence each coefficient commutes with every invertible operator on
`∀ i, h i`, hence is a multiple of the identity. -/

section
section Center
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- An operator fixed by conjugation with every continuous linear automorphism commutes with
every operator. -/
theorem commute_of_conjugate_invariant (B : E →L[ℝ] E)
    (hB : ∀ S : E ≃L[ℝ] E, (S.symm : E →L[ℝ] E).comp (B.comp (S : E →L[ℝ] E)) = B)
    (g : E →L[ℝ] E) : g.comp B = B.comp g := by
  have hinj : Function.Injective (g + (‖g‖ + 1) • ContinuousLinearMap.id ℝ E) := by
    intro x y hxy
    have h0 : g (x - y) + (‖g‖ + 1) • (x - y) = 0 := by
      have hz : (g + (‖g‖ + 1) • ContinuousLinearMap.id ℝ E) (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      exact hz
    have hw : g (x - y) = -((‖g‖ + 1) • (x - y)) := eq_neg_of_add_eq_zero_left h0
    have hpos : 0 < ‖g‖ + 1 := by positivity
    have hn : (‖g‖ + 1) * ‖x - y‖ ≤ ‖g‖ * ‖x - y‖ := by
      have h1 : ‖g (x - y)‖ = (‖g‖ + 1) * ‖x - y‖ := by
        rw [hw, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
      rw [← h1]
      exact g.le_opNorm (x - y)
    have hz : ‖x - y‖ = 0 := by
      by_contra hne
      have hp : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      have := le_of_mul_le_mul_right hn hp
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  let T : E ≃ₗ[ℝ] E := LinearEquiv.ofInjectiveEndo
    (g + (‖g‖ + 1) • ContinuousLinearMap.id ℝ E).toLinearMap hinj
  let S : E ≃L[ℝ] E := T.toContinuousLinearEquiv
  have hS : ∀ x, S x = g x + (‖g‖ + 1) • x := fun x => rfl
  have h1 : ∀ x, B (S x) = S (B x) := by
    intro x
    have := congrArg (fun F : E →L[ℝ] E => S (F x)) (hB S)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using this
  apply ContinuousLinearMap.ext
  intro x
  have hx := h1 x
  rw [hS, hS, map_add, map_smul] at hx
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  exact (add_right_cancel hx).symm

/-- An operator fixed by conjugation with every continuous linear automorphism is scalar. -/
theorem exists_smul_id_of_conjugate_invariant (B : E →L[ℝ] E)
    (hB : ∀ S : E ≃L[ℝ] E, (S.symm : E →L[ℝ] E).comp (B.comp (S : E →L[ℝ] E)) = B) :
    ∃ s : ℝ, B = s • ContinuousLinearMap.id ℝ E := by
  have hc : (B : E →ₗ[ℝ] E) ∈ Set.center (Module.End ℝ E) := by
    rw [Semigroup.mem_center_iff]
    intro g
    have hg := commute_of_conjugate_invariant B hB (LinearMap.toContinuousLinearMap g)
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun F : E →L[ℝ] E => F x) hg
    simpa using hx
  obtain ⟨s, hsc, hs⟩ := Module.End.mem_center_iff.mp hc
  refine ⟨s, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  have hx : (B : E →ₗ[ℝ] E) x = Module.End.smulLeft s hsc x :=
    congrArg (fun F : Module.End ℝ E => F x) hs
  exact hx

end Center

section Blocks
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem blockOperator_entry (c : ∀ v u : ι, h u →L[ℝ] h v) (v u : ι) :
    c v u = (ContinuousLinearMap.proj v).comp
      ((blockOperator c).comp (ContinuousLinearMap.single ℝ h u)) := by
  apply ContinuousLinearMap.ext
  intro ξ
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, blockOperator_apply, Finset.sum_eq_single u]
  · simp
  · intro u' _ hne
    simp [hne]
  · intro hu
    exact absurd (Finset.mem_univ u) hu

omit [Fintype ι] in
theorem blockIdentityEntry_self (v : ι) :
    blockIdentityEntry h v v = ContinuousLinearMap.id ℝ (h v) := by
  apply ContinuousLinearMap.ext
  intro ξ
  rw [blockIdentityEntry_apply, Pi.single_eq_same, ContinuousLinearMap.id_apply]

theorem blockOperator_blockIdentity :
    blockOperator (fun v u : ι => blockIdentityEntry h v u) =
      ContinuousLinearMap.id ℝ (∀ i, h i) := by
  apply ContinuousLinearMap.ext
  intro ξ
  funext v
  simp [blockOperator_apply, blockIdentityEntry_apply]

omit [DecidableEq ι] in
theorem blockOperator_zero :
    blockOperator (fun (v u : ι) => (0 : h u →L[ℝ] h v)) = 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  funext v
  simp [blockOperator_apply]

theorem eq_conjugateEntry_of_zero (S : (∀ i, h i) ≃L[ℝ] (∀ i, h i))
    (c : ∀ v u : ι, h u →L[ℝ] h v) (hc : ∀ v u, c v u = 0) (v u : ι) :
    c v u = conjugateEntry S c v u := by
  have he : c = fun (v u : ι) => (0 : h u →L[ℝ] h v) := by
    funext v' u'
    exact hc v' u'
  subst he
  unfold conjugateEntry
  rw [blockOperator_zero]
  simp

theorem eq_conjugateEntry_of_identity (S : (∀ i, h i) ≃L[ℝ] (∀ i, h i))
    (c : ∀ v u : ι, h u →L[ℝ] h v) (hc : ∀ v u, c v u = blockIdentityEntry h v u)
    (v u : ι) : c v u = conjugateEntry S c v u := by
  have he : c = fun v u : ι => blockIdentityEntry h v u := by
    funext v' u'
    exact hc v' u'
  subst he
  apply ContinuousLinearMap.ext
  intro ξ
  change blockIdentityEntry h v u ξ =
    (S.symm : (∀ i, h i) →L[ℝ] (∀ i, h i))
      (blockOperator (fun v u : ι => blockIdentityEntry h v u)
        ((S : (∀ i, h i) →L[ℝ] (∀ i, h i)) (ContinuousLinearMap.single ℝ h u ξ))) v
  rw [blockOperator_blockIdentity, ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rfl

end Blocks

section Setting
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}

theorem liftSequence_gradeZero_degreeZero (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (α : DerivativeWord2 0) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v u : ι) :
    Cc 0 0 0 α t X z v u = blockIdentityEntry h v u := by
  apply ContinuousLinearMap.ext
  intro ξ
  have hC := liftApply_const_degree_zero Q sX sZ a b N H Cc hseq (Pi.single u ξ) 0
    (Nat.zero_le H) t ht
  rw [blockIdentityEntry_apply, ← liftApply_constant_single 0 (Cc 0 0) α t X z v u ξ, hC]
  simp

variable
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- Every source-degree-zero lift coefficient is invariant under conjugation by a constant
change of component frame. -/
theorem setting_gradeZero_conjugate_invariant (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (S : (∀ i, h i) ≃L[ℝ] (∀ i, h i)) (n : ℕ) :
    ∀ m (α : DerivativeWord2 m), ∀ t ∈ Set.Icc a b, ∀ X z v u,
      Cc 0 n m α t X z v u = conjugateEntry S (Cc 0 n m α t X z) v u := by
  induction n using Nat.strong_induction_on with
  | h n ihn =>
    intro m α t ht X z v u
    by_cases hnN : N < n
    · exact eq_conjugateEntry_of_zero S _
        (fun v' u' => hseq.2.2.1 0 (Nat.zero_le H) n hnN m α t X z v' u') v u
    · by_cases hn0 : n = 0
      · subst n
        cases m with
        | zero =>
          exact eq_conjugateEntry_of_identity S _
            (fun v' u' => liftSequence_gradeZero_degreeZero sX sZ Cc hseq α t ht X z v' u') v u
        | succ m =>
          exact eq_conjugateEntry_of_zero S _
            (fun v' u' => hseq.2.2.2.1 0 (Nat.zero_le H) 0 (m + 1) (Nat.succ_pos m)
              α t X z v' u') v u
      · by_cases hmn : n < m
        · exact eq_conjugateEntry_of_zero S _
            (fun v' u' => hseq.2.2.2.1 0 (Nat.zero_le H) n m hmn α t X z v' u') v u
        · have hperm : ∀ (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)),
              conjugateCoeff S (Cc 0 n) m (β ∘ σ) = conjugateCoeff S (Cc 0 n) m β := by
            intro β σ
            show (fun t X z => conjugateEntry S (Cc 0 n m (β ∘ σ) t X z)) =
              fun t X z => conjugateEntry S (Cc 0 n m β t X z)
            rw [hseq.2.2.2.2.1 0 (Nat.zero_le H) n m β σ]
          refine symmetric_lift_coefficient_eq_of_operator_eq n m (by omega) (Cc 0 n)
            (conjugateCoeff S (Cc 0 n)) (hseq.2.2.2.2.1 0 (Nat.zero_le H) n m) hperm
            t X z v u ?_ α
          intro a₀ ha₀
          have ha₁ : ContDiff ℝ (⊤ : ℕ∞) (fun Y => S (a₀ Y)) := S.contDiff.comp ha₀
          have hC := hseq.2.2.2.2.2.2 0 (Nat.zero_le H) n (by omega) (by omega) a₀ ha₀ X
          have hD : IsCellFieldInverse (fun r => Matrix.of (Q.G r X)) Q.v sZ a b (fun _ => 0)
              (fun r y => S.symm (liftCellSource Q Cc (fun _ Y => S (a₀ Y)) 0 n r X y))
              (fun r y => S.symm (liftApply n (Cc 0 n) (fun _ Y => S (a₀ Y)) r X y)) := by
            simpa only [map_zero, ContinuousLinearEquiv.coe_coe] using
              cellFieldInverse_postcomposition (S.symm : (∀ i, h i) →L[ℝ] (∀ i, h i)) _ _
                sZ hsZ a b _ _ _
                (hseq.2.2.2.2.2.2 0 (Nat.zero_le H) n (by omega) (by omega) _ ha₁ X)
          have hEq := setting_cellFieldInverse_unique P X sZ sZ (fun _ => 0)
            (fun r y => liftCellSource Q Cc (fun _ => a₀) 0 n r X y)
            (fun r y => S.symm (liftCellSource Q Cc (fun _ Y => S (a₀ Y)) 0 n r X y))
            (fun r y => liftApply n (Cc 0 n) (fun _ => a₀) r X y)
            (fun r y => S.symm (liftApply n (Cc 0 n) (fun _ Y => S (a₀ Y)) r X y)) hC hD
            (fun r hr => by
              funext y
              show liftCellSource Q Cc (fun _ => a₀) 0 n r X y =
                S.symm (liftCellSource Q Cc (fun _ Y => S (a₀ Y)) 0 n r X y)
              rw [liftCellSource_congr_predecessors Q Cc (conjugateSequence S Cc) (fun _ => a₀)
                0 n (by omega) r (fun p q hpq m' β Y y' w j => by
                  rcases hpq with hp | ⟨rfl, hq⟩
                  · exact absurd hp (Nat.not_lt_zero p)
                  · exact ihn q hq m' β r hr Y y' w j)]
              exact liftCellSource_conjugate_zero Q S Cc (fun _ => a₀) (fun _ Y => S (a₀ Y))
                (fun _ _ => rfl) n r X y)
          have h1 : liftApply n (Cc 0 n) (fun _ => a₀) t X z =
              S.symm (liftApply n (Cc 0 n) (fun _ Y => S (a₀ Y)) t X z) :=
            congrFun (hEq t ht) z
          rw [congrFun h1 v, liftApply_conjugateCoeff S n (Cc 0 n) (fun _ => a₀)
            (fun _ Y => S (a₀ Y)) t (fun _ => rfl) X z]

include P in
/-- Source-degree-zero lift coefficients are scalar multiples of the identity:
`C_n^{(0)} = T_n I`. -/
theorem setting_gradeZero_scalar (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (n m : ℕ) (α : DerivativeWord2 m) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    ∃ s : ℝ, ∀ v u, Cc 0 n m α t X z v u = s • blockIdentityEntry h v u := by
  obtain ⟨s, hs⟩ := exists_smul_id_of_conjugate_invariant (blockOperator (Cc 0 n m α t X z))
    (fun S => by
      rw [← blockOperator_conjugateEntry]
      congr 1
      funext v u
      exact (setting_gradeZero_conjugate_invariant P sX sZ hsZ Cc hseq S n m α t ht X z
        v u).symm)
  refine ⟨s, fun v u => ?_⟩
  rw [blockOperator_entry (Cc 0 n m α t X z) v u, hs]
  apply ContinuousLinearMap.ext
  intro ξ
  simp [blockIdentityEntry_apply]

end Setting
end

/-! A lift sequence read at translated slow positions `X + T` is again a lift sequence when the
metric and the source coefficients are `T`-invariant; by uniqueness of the lift sequence, every
lift coefficient is then `T`-invariant on the window. -/

section
section Box
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isBoxSmooth_slowShift {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E} (hf : IsBoxSmooth sX sZ f)
    (T : Vec 2) : IsBoxSmooth sX sZ (fun X z => f (X + T) z) := by
  refine ⟨fun X => hf.1 (X + T), fun b hb z => ?_, fun a b ha hb => ?_⟩
  · exact (hf.2.1 b hb z).comp (contDiff_id.add contDiff_const)
  · show Continuous (fun p : Vec 2 × Vec 2 =>
      iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b (f (X' + T)) p.2) p.1)
    have he : (fun p : Vec 2 × Vec 2 =>
        iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b (f (X' + T)) p.2) p.1) =
        fun p => iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b (f X') p.2) (p.1 + T) := by
      funext p
      exact iteratedFDeriv_comp_add_right (𝕜 := ℝ)
        (f := fun X' => iteratedFDeriv ℝ b (f X') p.2) a T p.1
    rw [he]
    exact (hf.2.2 a b ha hb).comp ((continuous_fst.add continuous_const).prodMk continuous_snd)

end Box

section Sequence
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  {D : ℕ}

theorem isLiftSequence_slowShift (Q : LiftOperatorData ι h D) (sX sZ : ℕ) (a b : ℝ)
    (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (T : Vec 2) (hG : ∀ t X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z) :
    IsLiftSequence Q sX sZ a b N H (slowShiftSequence T Cc) := by
  have hshift (a₀ : Vec 2 → ∀ i, h i) : ∀ s Y,
      (fun (_ : ℝ) => a₀) s Y = (fun (_ : ℝ) (Y' : Vec 2) => a₀ (Y' - T)) s (Y + T) := by
    intro s Y
    simp only [add_sub_cancel_right]
  have hsmooth (a₀ : Vec 2 → ∀ i, h i) (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀) :
      ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec 2 => a₀ (Y - T)) :=
    ha₀.comp (contDiff_id.sub contDiff_const)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a₀ ha₀ t ht X z
    rw [liftApply_slowShift 0 (Cc 0 0) (fun _ Y => a₀ (Y - T)) (fun _ => a₀) T t
      (hshift a₀ t) X z, hseq.1 _ (hsmooth a₀ ha₀) t ht (X + T) z]
    simp only [add_sub_cancel_right]
  · intro hh h₁ h₂ m α t X z v u
    exact hseq.2.1 hh h₁ h₂ m α t (X + T) z v u
  · intro hh hhh n hn m α t X z v u
    exact hseq.2.2.1 hh hhh n hn m α t (X + T) z v u
  · intro hh hhh n m hnm α t X z v u
    exact hseq.2.2.2.1 hh hhh n m hnm α t (X + T) z v u
  · intro hh hhh n m α σ
    funext t X z v u
    exact congrFun (congrFun (congrFun (congrFun (congrFun
      (hseq.2.2.2.2.1 hh hhh n m α σ) t) (X + T)) z) v) u
  · intro hh hhh n m α v u t ht
    exact ⟨isBoxSmooth_slowShift (hseq.2.2.2.2.2.1 hh hhh n m α v u t ht).1 T,
      fun X => (hseq.2.2.2.2.2.1 hh hhh n m α v u t ht).2 (X + T)⟩
  · intro hh hhh n hn hnN a₀ ha₀ X
    have hI := hseq.2.2.2.2.2.2 hh hhh n hn hnN _ (hsmooth a₀ ha₀) (X + T)
    have hGm : (fun t => Matrix.of (Q.G t (X + T))) = fun t => Matrix.of (Q.G t X) := by
      funext t
      congr 1
      funext i j
      exact hG t X i j
    have hsrc : (fun t z => liftCellSource Q Cc (fun _ Y => a₀ (Y - T)) hh n t (X + T) z) =
        fun t z => liftCellSource Q (slowShiftSequence T Cc) (fun _ => a₀) hh n t X z := by
      funext t z
      exact (liftCellSource_slowShift Q Cc (fun _ Y => a₀ (Y - T)) (fun _ => a₀) T
        (hshift a₀) hG hc hh n t X z).symm
    have hsol : (fun t z => liftApply n (Cc hh n) (fun _ Y => a₀ (Y - T)) t (X + T) z) =
        fun t z => liftApply n (slowShiftSequence T Cc hh n) (fun _ => a₀) t X z := by
      funext t z
      exact (liftApply_slowShift n (Cc hh n) (fun _ Y => a₀ (Y - T)) (fun _ => a₀) T t
        (hshift a₀ t) X z).symm
    rw [hGm, hsrc, hsol] at hI
    exact hI

end Sequence

section Setting
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- Every lift coefficient is invariant under a slow translation that leaves the metric and the
source coefficients invariant. -/
theorem setting_liftSequence_slowShift_invariant (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (T : Vec 2)
    (hG : ∀ t X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z) :
    ∀ hh, hh ≤ H → ∀ n m (α : DerivativeWord2 m) t, t ∈ Set.Icc a b → ∀ X z v u,
      Cc hh n m α t (X + T) z v u = Cc hh n m α t X z v u := by
  intro hh hhh n m α t ht X z v u
  exact (liftSequence_coefficients_unique P sX sZ sX sZ Cc (slowShiftSequence T Cc) hseq
    (isLiftSequence_slowShift Q sX sZ a b N H Cc hseq T hG hc) hh hhh n m α t ht X z v u).symm

end Setting
end

/-! The explicit divergence-form letters of the lift means `L_n^{(hh)}`: word symmetry, slow
regularity, the presentation of `liftMean`, and the pointwise entrywise path-product bound
`‖D_X^j b_{d,α}(t,X)_{vu}‖ ≤ C (A_phys^hh)_{vu} λ^{n-d+j}`. -/

section
section Letters
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

/-- The source-degree-zero mean letter: the truncated diagonal mean flux coefficients. -/
def diagonalMeanLetter (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (n : ℕ) :
    MeanCoeff ι h :=
  truncatedMeanCoefficient n (diagonalMeanFluxCoefficient Q Cc n)

/-- The positive-source-degree mean letter: the truncated positive mean flux coefficients. -/
def positiveMeanLetter (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n : ℕ) : MeanCoeff ι h :=
  truncatedMeanCoefficient n (positiveMeanFluxCoefficient Q Cc hh n)

/-- The explicit mean letter of grade `hh` and degree `n`. -/
def meanLetter (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) :
    MeanCoeff ι h :=
  if hh = 0 then diagonalMeanLetter Q Cc n else positiveMeanLetter Q Cc hh n

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem meanLetter_zero (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (n : ℕ) :
    meanLetter Q Cc 0 n = diagonalMeanLetter Q Cc n := by
  rw [meanLetter, ite_eq_left rfl]

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem meanLetter_of_ne_zero (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    {hh : ℕ} (h0 : hh ≠ 0) (n : ℕ) :
    meanLetter Q Cc hh n = positiveMeanLetter Q Cc hh n := by
  rw [meanLetter, ite_eq_right h0]

end Letters

/-- One word term is at most the sum over all words and flux directions. -/
theorem word_le_sum_pairs {m : ℕ} (f : DerivativeWord2 m → ℝ) (hf : ∀ α, 0 ≤ f α)
    (α : DerivativeWord2 m) (k₀ : Fin 2) :
    f α ≤ ∑ p : DerivativeWord2 m × Fin 2, f p.1 :=
  Finset.single_le_sum (f := fun p : DerivativeWord2 m × Fin 2 => f p.1)
    (fun p _ => hf p.1) (Finset.mem_univ (α, k₀))

section Setting
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- Symmetry, slow regularity, presentation and entrywise jets of the positive letter. -/
theorem setting_positiveMeanLetter_core (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D) :
    (∀ d (α : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))),
      positiveMeanLetter Q Cc hh n d (α ∘ σ) = positiveMeanLetter Q Cc hh n d α) ∧
    (∀ d α k₀ v u, ∀ t ∈ Set.Icc a b,
      ContDiff ℝ ((P₀ + 1 : ℕ) : ℕ∞) (fun X => positiveMeanLetter Q Cc hh n d α t X k₀ v u)) ∧
    (∀ f : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) f → ∀ t ∈ Set.Icc a b, ∀ X,
      liftMean Q Cc (fun _ => f) hh n t X =
        meanApply n (positiveMeanLetter Q Cc hh n) (fun _ => f) t X) ∧
    (∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
      ∀ j, j ≤ P₀ + 1 → ∀ t ∈ Set.Icc a b, ∀ X,
        ‖iteratedFDeriv ℝ j (fun X' => positiveMeanLetter Q Cc hh n d α t X' k₀ v u) X‖ ≤
          ambientMeanGradeConstant P₀ N k L D H CG Cw Cj *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u *
              lam ^ (n - d + j)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact truncatedMeanCoefficient_perm n (positiveMeanFluxCoefficient Q Cc hh n)
      (fun k₀ m α σ => setting_positive_mean_flux_coefficient_perm sX sZ Cc hseq hh hhh n
        k₀ m α σ)
  · intro d α k₀ v u t ht
    exact truncatedMeanCoefficient_contDiff n (P₀ + 1) (positiveMeanFluxCoefficient Q Cc hh n) t
      (fun k₀ m hm α v u => setting_positive_mean_flux_coefficient_contDiff_upto P sX sZ
        (by omega) Cc hseq P₀ hreserve hh hhpos hhh n hn hnR k₀ t ht m hm α 0 v u)
      d α k₀ v u
  · intro f hf t ht X
    change liftMean Q Cc (fun _ => f) hh n t X =
      meanApply n (truncatedMeanCoefficient n (positiveMeanFluxCoefficient Q Cc hh n))
        (fun _ => f) t X
    rw [truncatedMeanCoefficient_meanApply]
    exact setting_positive_mean_flux_meanApply P sX sZ hX hZ Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR f hf t ht X
  · intro d hd hdn α k₀ v u j hj t ht X
    have hfun : (fun X' => positiveMeanLetter Q Cc hh n d α t X' k₀ v u) =
        fun Y => positiveMeanFluxCoefficient Q Cc hh n k₀ (d - 1) α t Y 0 v u := by
      funext Y
      exact truncatedMeanCoefficient_eq n d hd hdn _ α t Y k₀ v u
    rw [hfun]
    have hb := setting_positive_mean_flux_coefficient_jet_upto P sX sZ (by omega) Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR k₀ t ht (d - 1) (by omega) α 0 X v u j hj
    have hδ : n - 1 - (d - 1) + j = n - d + j := by omega
    rw [hδ] at hb
    apply hb.trans
    have hM := finiteMatrixPower_nonneg _
      (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) hh v u
    have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hM) (pow_nonneg hlam _)
    have hw : ambientPositiveMeanFluxWordConstant P₀ N k L D H hh n (d - 1) j CG Cw Cj α ≤
        ambientPositiveMeanFluxConstant P₀ N k L D H hh n (d - 1) j CG Cw Cj := by
      unfold ambientPositiveMeanFluxConstant
      exact word_le_sum_pairs _
        (ambientPositiveMeanFluxWordConstant_nonneg P₀ N k L D H hh n (d - 1) j CG Cw Cj) α k₀
    exact hw.trans ((le_add_of_nonneg_right
      (ambientDiagonalMeanFluxConstant_nonneg P₀ N k L D H n (d - 1) j CG Cw Cj)).trans
      (ambientMeanGradeConstant_entry_le P₀ N k L D H CG Cw Cj hh n (d - 1) j hhh hnR
        (by omega) hj))

include P in
/-- Symmetry, slow regularity, presentation and entrywise jets of the source-degree-zero
letter. -/
theorem setting_diagonalMeanLetter_core (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D) :
    (∀ d (α : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))),
      diagonalMeanLetter Q Cc n d (α ∘ σ) = diagonalMeanLetter Q Cc n d α) ∧
    (∀ d α k₀ v u, ∀ t ∈ Set.Icc a b,
      ContDiff ℝ ((P₀ + 1 : ℕ) : ℕ∞) (fun X => diagonalMeanLetter Q Cc n d α t X k₀ v u)) ∧
    (∀ f : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) f → ∀ t ∈ Set.Icc a b, ∀ X,
      liftMean Q Cc (fun _ => f) 0 n t X =
        meanApply n (diagonalMeanLetter Q Cc n) (fun _ => f) t X) ∧
    (∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
      ∀ j, j ≤ P₀ + 1 → ∀ t ∈ Set.Icc a b, ∀ X,
        ‖iteratedFDeriv ℝ j (fun X' => diagonalMeanLetter Q Cc n d α t X' k₀ v u) X‖ ≤
          ambientMeanGradeConstant P₀ N k L D H CG Cw Cj *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) 0 v u *
              lam ^ (n - d + j)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact truncatedMeanCoefficient_perm n (diagonalMeanFluxCoefficient Q Cc n)
      (fun k₀ m α σ => setting_diagonal_mean_flux_coefficient_perm sX sZ Cc hseq n k₀ m α σ)
  · intro d α k₀ v u t ht
    exact truncatedMeanCoefficient_contDiff n (P₀ + 1) (diagonalMeanFluxCoefficient Q Cc n) t
      (fun k₀ m hm α v u => setting_diagonal_mean_flux_coefficient_contDiff_upto P sX sZ
        (by omega) Cc hseq P₀ hreserve n hn hnR k₀ t ht m hm α 0 v u)
      d α k₀ v u
  · intro f hf t ht X
    change liftMean Q Cc (fun _ => f) 0 n t X =
      meanApply n (truncatedMeanCoefficient n (diagonalMeanFluxCoefficient Q Cc n))
        (fun _ => f) t X
    rw [truncatedMeanCoefficient_meanApply]
    exact setting_diagonal_mean_flux_meanApply P sX sZ hX hZ Cc hseq
      P₀ hreserve n hn hnR f hf t ht X
  · intro d hd hdn α k₀ v u j hj t ht X
    have hfun : (fun X' => diagonalMeanLetter Q Cc n d α t X' k₀ v u) =
        fun Y => diagonalMeanFluxCoefficient Q Cc n k₀ (d - 1) α t Y 0 v u := by
      funext Y
      exact truncatedMeanCoefficient_eq n d hd hdn _ α t Y k₀ v u
    rw [hfun]
    have hb := setting_diagonal_mean_flux_coefficient_jet_upto P sX sZ (by omega) Cc hseq
      P₀ hreserve n hn hnR k₀ t ht (d - 1) (by omega) (by omega) α 0 X v u j hj
    have hδ : n - 1 - (d - 1) + j = n - d + j := by omega
    rw [hδ] at hb
    apply hb.trans
    have hM := finiteMatrixPower_nonneg _
      (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) 0 v u
    have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hM) (pow_nonneg hlam _)
    have hw : ambientDiagonalMeanFluxWordConstant P₀ N k L D H n j CG Cw Cj ≤
        ambientDiagonalMeanFluxConstant P₀ N k L D H n (d - 1) j CG Cw Cj := by
      unfold ambientDiagonalMeanFluxConstant
      exact word_le_sum_pairs (fun _ : DerivativeWord2 (d - 1) =>
          ambientDiagonalMeanFluxWordConstant P₀ N k L D H n j CG Cw Cj)
        (fun _ => ambientDiagonalMeanFluxWordConstant_nonneg P₀ N k L D H n j CG Cw Cj) α k₀
    exact hw.trans ((le_add_of_nonneg_left
      (ambientPositiveMeanFluxConstant_nonneg P₀ N k L D H 0 n (d - 1) j CG Cw Cj)).trans
      (ambientMeanGradeConstant_entry_le P₀ N k L D H CG Cw Cj 0 n (d - 1) j (Nat.zero_le H)
        hnR (by omega) hj))

end Setting
end

end AVRegularity.CycleComparison.LiftMeanEntrywise
end
