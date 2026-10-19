-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.SettingInverseZero
import AVRegularity.CycleComparison.CleanupChain
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
public import AVRegularity.CycleComparison.Lift.SourceZeroMean
public import AVRegularity.CycleComparison.Lift.SettingDimensionalScales
public import AVRegularity.Statements.Intermediate.CycleComparison.IsLiftSequence
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Grade and degree induction proves that positive lifts annihilate constants. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)


include P in
theorem liftSequence_constants_zero (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (c0 : ∀ i, h i) :
    ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → ∀ t ∈ Set.Icc a b,
      liftApply n (Cc hh n) (fun _ _ => c0) t = 0 := by
  intro hh
  induction hh using Nat.strong_induction_on with
  | h hh ih =>
    intro hhh n
    induction n using Nat.strong_induction_on with
    | h n ihn =>
      intro hn
      by_cases hcut : N < n
      · intro t ht
        exact congrFun (liftApply_above_cutoff Q sX sZ a b N H Cc hseq hh hhh n hcut (fun _ _ => c0)) t
      · have hnN : n ≤ N := by omega
        have hknown : ∀ q, q ≤ hh → ∀ d, 1 ≤ d → (q < hh ∨ d < n) →
            ∀ t ∈ Set.Icc a b, liftApply d (Cc q d) (fun _ _ => c0) t = 0 := by
          intro q hq d hd hqd
          by_cases hqlt : q < hh
          · exact ih q hqlt (hq.trans hhh) d hd
          · have hqe : q = hh := by omega
            subst q
            exact ihn d (by omega) hd
        have hg : ∀ t ∈ Set.Icc a b, ∀ X z,
            liftCellSource Q Cc (fun _ _ => c0) hh n t X z = 0 := by
          intro t ht X z
          exact congrFun (congrFun (liftCellSource_const_zero_lex Q sX sZ a b N H Cc hseq c0 hh n
            hhh hknown hn t ht) X) z
        have hc := liftConstant_zero_of_source_zero P sX sZ Cc hseq c0 hh n hhh hn hnN hg
        intro t ht
        funext X z
        exact hc t ht X z

include P in
theorem liftSequence_constant_means_zero (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (c0 : ∀ i, h i) :
    ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → ∀ t ∈ Set.Icc a b,
      liftMean Q Cc (fun _ _ => c0) hh n t = 0 := by
  intro hh hhh n hn t ht
  apply liftMean_zero_of_A_zero
  have hz := liftSequence_constants_zero P sX sZ Cc hseq c0
  apply liftA_const_zero_lex Q sX sZ a b N H Cc hseq c0 hh n hhh
    (fun q hq d hd _ => hz q (hq.trans hhh) d hd) hh n le_rfl hn (Or.inr le_rfl) t ht
end

/-! Constant inputs leave only the identity coefficient of the lift polynomial. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)



include P in
theorem liftPolyField_const (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (c0 : ∀ i, h i)
    (ε : ℝ) (hh : ℕ) (hhh : hh ≤ H) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    liftPolyField Cc N ε hh (fun _ _ => c0) t = fun _ _ => if hh = 0 then c0 else 0 := by
  have hz := liftSequence_constants_zero P sX sZ Cc hseq c0 hh hhh
  have hbase := liftApply_const_degree_zero Q sX sZ a b N H Cc hseq c0 hh hhh t ht
  funext X z
  unfold liftPolyField
  rw [Finset.sum_eq_single 0]
  · simpa only [pow_zero, one_smul] using congrFun (congrFun hbase X) z
  · intro n hn hn0
    have he := congrFun (congrFun (hz n (by omega) t ht) X) z
    simp only [he, Pi.zero_apply, smul_zero]
  · simp

include P in
theorem liftPolynomial_sourceFluxCoeff_const (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (c0 : ∀ i, h i)
    (hh : ℕ) (hhh : hh ≤ H) (j : ℕ) (t : ℝ) (ht : t ∈ Set.Icc a b) (q : Fin 2) :
    sourceFluxCoeff Q.edge Q.η j t
      (fun ε => liftPolyField Cc N ε hh (fun _ _ => c0) t) q = 0 := by
  have he : (fun ε => liftPolyField Cc N ε hh (fun _ _ => c0) t) =
      fun _ _ _ => if hh = 0 then c0 else 0 := by
    funext ε
    exact liftPolyField_const P sX sZ Cc hseq c0 ε hh hhh t ht
  rw [he]
  exact sourceFluxCoeff_const_eq_zero _ _ _ _ _ _
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Constant tests identify every zero-order left coefficient of a positive lift as zero. -/

section
section General
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_constant_single [DecidableEq ι] (n : ℕ) (c : LiftCoeff ι h)
    (α : DerivativeWord2 0) (t : ℝ) (X z : Vec 2) (v u : ι) (ξ : h u) :
    liftApply n c (fun _ _ => Pi.single u ξ) t X z v = c 0 α t X z v u ξ := by
  classical
  rw [liftApply_const]
  have ha : ∀ β : DerivativeWord2 0, β = α := fun _ => Subsingleton.elim _ _
  simp only [ha, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero, one_nsmul]
  rw [Finset.sum_eq_single u]
  · simp
  · intro j _ hju
    rw [Pi.single_eq_of_ne hju ξ, map_zero]
  · simp

end General

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftSequence_zero_order_coefficient_zero (sX sZ : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n)
    (α : DerivativeWord2 0) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v u : ι) :
    Cc hh n 0 α t X z v u = 0 := by
  classical
  apply ContinuousLinearMap.ext
  intro ξ
  have he := congrFun (congrFun (congrFun
    (liftSequence_constants_zero P sX sZ Cc hseq (Pi.single u ξ) hh hhh n hn t ht) X) z) v
  rw [liftApply_constant_single n (Cc hh n) α t X z v u ξ] at he
  exact he
end

/-! Constant single-component tests identify the actual identity row at degree zero. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequence_identity_coefficient (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (α : DerivativeWord2 0)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v u : ι) :
    Cc 0 0 0 α t X z v u =
      (ContinuousLinearMap.proj (R := ℝ) (φ := h) v).comp (ContinuousLinearMap.single ℝ h u) := by
  apply ContinuousLinearMap.ext
  intro ξ
  have he := congrFun (hseq.1 (fun _ => Pi.single u ξ) contDiff_const t ht X z) v
  rw [liftApply_constant_single 0 (Cc 0 0) α t X z v u ξ] at he
  exact he

theorem liftSequence_identity_coefficient_box_reserve (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (α : DerivativeWord2 0)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (p q : ℕ) :
    IsBoxSmooth p q (fun X z => Cc 0 0 0 α t X z v u) := by
  have he : (fun X z => Cc 0 0 0 α t X z v u) = fun (_ _ : Vec 2) =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := h) v).comp (ContinuousLinearMap.single ℝ h u) :=
    funext fun X => funext fun z => liftSequence_identity_coefficient Q sX sZ a b N H Cc hseq α t ht X z v u
  rw [he]
  exact isBoxSmooth_slow_field p q _ contDiff_const
end

/-! Zeroth-degree coefficient equality uses the initial identities even for different operator data. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequence_zero_degree_coefficients_cross_data_eq (Q Q' : LiftOperatorData ι h D)
    (sX sZ sX' sZ' : ℕ) (a b : ℝ) (N H : ℕ)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc)
    (hd : IsLiftSequence Q' sX' sZ' a b N H Dc)
    (hh : ℕ) (hhh : hh ≤ H) (m : ℕ) (α : DerivativeWord2 m)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v u : ι) :
    Cc hh 0 m α t X z v u = Dc hh 0 m α t X z v u := by
  classical
  cases m with
  | zero =>
    apply ContinuousLinearMap.ext
    intro ξ
    have hC := liftApply_const_degree_zero Q sX sZ a b N H Cc hc
      (Pi.single u ξ) hh hhh t ht
    have hD := liftApply_const_degree_zero Q' sX' sZ' a b N H Dc hd
      (Pi.single u ξ) hh hhh t ht
    have he := congrFun (congrFun (congrFun (hC.trans hD.symm) X) z) v
    rw [liftApply_constant_single 0 (Cc hh 0) α t X z v u ξ,
      liftApply_constant_single 0 (Dc hh 0) α t X z v u ξ] at he
    exact he
  | succ m =>
    rw [hc.2.2.2.1 hh hhh 0 (m + 1) (by omega),
      hd.2.2.2.1 hh hhh 0 (m + 1) (by omega)]
end

/-! The original zeroth-degree identities uniquely determine the actual supported coefficient maps. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequence_zero_degree_coefficients_unique (Q : LiftOperatorData ι h D)
    (sX sZ sX' sZ' : ℕ) (a b : ℝ) (N H : ℕ)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc)
    (hd : IsLiftSequence Q sX' sZ' a b N H Dc)
    (hh : ℕ) (hhh : hh ≤ H) (m : ℕ) (α : DerivativeWord2 m)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v u : ι) :
    Cc hh 0 m α t X z v u = Dc hh 0 m α t X z v u := by
  classical
  cases m with
  | zero =>
    apply ContinuousLinearMap.ext
    intro ξ
    have hC := liftApply_const_degree_zero Q sX sZ a b N H Cc hc
      (Pi.single u ξ) hh hhh t ht
    have hD := liftApply_const_degree_zero Q sX' sZ' a b N H Dc hd
      (Pi.single u ξ) hh hhh t ht
    have he := congrFun (congrFun (congrFun (hC.trans hD.symm) X) z) v
    rw [liftApply_constant_single 0 (Cc hh 0) α t X z v u ξ,
      liftApply_constant_single 0 (Dc hh 0) α t X z v u ξ] at he
    exact he
  | succ m =>
    rw [hc.2.2.2.1 hh hhh 0 (m + 1) (by omega),
      hd.2.2.2.1 hh hhh 0 (m + 1) (by omega)]
end

/-! Actual paired sequences have zero difference at degree zero and beyond the cutoff. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequence_paired_degree_zero_ambient_data (Q Qi : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (hab : a ≤ b) (N H : ℕ) (Cc Ci : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc)
    (hi : IsLiftSequence Qi sX sZ a b N H Ci) (hh : ℕ) (hhh : hh ≤ H)
    (par : Fin 2) (lam : ℝ) (p q : ℕ) :
    AmbientLiftCoefficientData par a b hab lam 0 p q
      (fun m α t X z v u => Cc hh 0 m α t X z v u - Ci hh 0 m α t X z v u)
      (fun _ _ => 0) := by
  apply (ambient_zero_coefficient_data par a b hab lam 0 p q).congr_on_window
  intro m _ α v u t ht X z
  have he := liftSequence_zero_degree_coefficients_cross_data_eq Q Qi sX sZ sX sZ a b N H
    Cc Ci hc hi hh hhh m α t ht X z v u
  simpa only [Pi.zero_apply] using sub_eq_zero.mpr he

theorem liftSequence_paired_cutoff_ambient_data (Q Qi : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (hab : a ≤ b) (N H : ℕ) (Cc Ci : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc)
    (hi : IsLiftSequence Qi sX sZ a b N H Ci) (hh : ℕ) (hhh : hh ≤ H)
    (n : ℕ) (hn : N < n) (par : Fin 2) (lam : ℝ) (p q : ℕ) :
    AmbientLiftCoefficientData par a b hab lam n p q
      (fun m α t X z v u => Cc hh n m α t X z v u - Ci hh n m α t X z v u)
      (fun _ _ => 0) := by
  apply (ambient_zero_coefficient_data par a b hab lam n p q).congr_on_window
  intro m _ α v u t _ X z
  rw [hc.2.2.1 hh hhh n hn m α t X z v u, hi.2.2.1 hh hhh n hn m α t X z v u]
  simp only [sub_self, Pi.zero_apply]
end

/-! The degree-zero lift is the identity on every current coarse field. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem liftApply_zero_degree (c : LiftCoeff ι h) (α : DerivativeWord2 0)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (X z : Vec 2) (v : ι) :
    liftApply 0 c f t X z v = ∑ u, c 0 α t X z v u (f t X u) := by
  simp only [liftApply]
  simp [orderedDerivative]
  apply Finset.sum_congr rfl
  intro u _
  congr 2
  exact Subsingleton.elim _ _

theorem liftSequence_zero_degree_action (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftApply 0 (Cc 0 0) f t X z = f t X := by
  funext v
  rw [liftApply_zero_degree (Cc 0 0) (fun i => Fin.elim0 i) f t X z v]
  simp_rw [liftSequence_identity_coefficient Q sX sZ a b N H Cc hseq _ t ht X z]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.single_apply]
  rw [Finset.sum_eq_single v]
  · simp
  · intro u _ huv
    exact Pi.single_eq_of_ne (Ne.symm huv) _
  · simp
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The actual identity and zero degrees supply the initial common-reserve induction states. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequence_identity_ambient_data (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (hab : a ≤ b) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (par : Fin 2) (lam : ℝ) (hlam : 0 ≤ lam)
    (p q : ℕ) : AmbientLiftCoefficientData par a b hab lam 0 p q (Cc 0 0)
      (fun v u => if v = u then 1 else 0) := by
  refine ⟨fun v u => by split_ifs <;> norm_num, ?_, ?_, ?_, ?_⟩
  · intro m hm α v u t ht
    have hm0 : m = 0 := by omega
    subst m
    exact liftSequence_identity_coefficient_box_reserve Q sX sZ a b N H Cc hseq α t ht v u p q
  · intro m hm α v u r hr s hs t ht X z
    have hm0 : m = 0 := by omega
    subst m
    let T := (ContinuousLinearMap.proj (R := ℝ) (φ := h) v).comp (ContinuousLinearMap.single ℝ h u)
    have he : (fun Y y => Cc 0 0 0 α t Y y v u) = fun (_ _ : Vec 2) => T :=
      funext fun Y => funext fun y => liftSequence_identity_coefficient Q sX sZ a b N H Cc hseq α t ht Y y v u
    have hej : (fun Y => iteratedFDeriv ℝ s (fun y => Cc 0 0 0 α t Y y v u) z) =
        fun Y => iteratedFDeriv ℝ s (fun _ : Vec 2 => T) z := by
      funext Y
      exact congrArg (fun f : Vec 2 → (h u →L[ℝ] h v) => iteratedFDeriv ℝ s f z)
        (congrFun he Y)
    rw [hej]
    simpa only [Nat.sub_self, Nat.zero_add] using
      norm_mixed_constant_graded_le r s T _ lam (by split_ifs <;> norm_num) hlam
        (identity_component_map_norm_le v u) X z
  · intro m hm α v u t ht X z s
    have hm0 : m = 0 := by omega
    subst m
    change Cc 0 0 0 α t X (z + s • basisVec par) v u = Cc 0 0 0 α t X z v u
    rw [liftSequence_identity_coefficient Q sX sZ a b N H Cc hseq α t ht X (z + s • basisVec par) v u,
      liftSequence_identity_coefficient Q sX sZ a b N H Cc hseq α t ht X z v u]
  · intro m hm α v u l X z
    have hm0 : m = 0 := by omega
    subst m
    have he : (fun t => l (Cc 0 0 0 α (Set.projIcc a b hab t) X z v u)) = fun (_ : ℝ) =>
        l ((ContinuousLinearMap.proj (R := ℝ) (φ := h) v).comp (ContinuousLinearMap.single ℝ h u)) := by
      funext t
      exact congrArg l (liftSequence_identity_coefficient Q sX sZ a b N H Cc hseq α _
        (Set.projIcc a b hab t).2 X z v u)
    rw [he]
    exact measurable_const

omit [DecidableEq ι] in
theorem liftSequence_positive_height_zero_ambient_data (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (hab : a ≤ b) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H)
    (par : Fin 2) (lam : ℝ) (p q : ℕ) :
    AmbientLiftCoefficientData par a b hab lam 0 p q (Cc hh 0) (fun _ _ => 0) := by
  have he : Cc hh 0 = 0 := by
    funext m α t X z v u
    exact hseq.2.1 hh hhpos hhh m α t X z v u
  rw [he]
  exact ambient_zero_coefficient_data par a b hab lam 0 p q

omit [DecidableEq ι] in
theorem liftSequence_truncated_ambient_data (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (hab : a ≤ b) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : N < n)
    (par : Fin 2) (lam : ℝ) (p q : ℕ) :
    AmbientLiftCoefficientData par a b hab lam n p q (Cc hh n) (fun _ _ => 0) := by
  have he : Cc hh n = 0 := by
    funext m α t X z v u
    exact hseq.2.2.1 hh hhh n hn m α t X z v u
  rw [he]
  exact ambient_zero_coefficient_data par a b hab lam n p q

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The graded degree-zero composition selects exactly the mean field of the current height. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequence_zero_degree_graded_action (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (f : ℕ → ℝ → Vec 2 → ∀ i, h i)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, liftApply 0 (Cc p.1 0) (f p.2) t X z) = f hh t X := by
  classical
  rw [Finset.sum_eq_single (0, hh)]
  · exact liftSequence_zero_degree_action Q sX sZ a b N H Cc hseq (f hh) t ht X z
  · intro p hp hne
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hpos : 1 ≤ p.1 := by
      by_contra hn
      have hq : p.1 = 0 := by omega
      have hr : p.2 = hh := by omega
      exact hne (Prod.ext hq hr)
    have he := congrFun (liftApply_positive_grade_zero_degree Q sX sZ a b N H Cc hseq
      p.1 hpos (by omega) (f p.2)) t
    exact congrFun (congrFun he X) z
  · intro hn
    exact (hn (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega))).elim
end

/-! Low-degree compositions have the mean term and precisely the positive-lift recurrence products. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftMeanComposition_low_degree (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 2 ≤ n) (hnN : n ≤ N)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftMeanCompositionCoefficient Q Cc N f hh n t X z = liftMean Q Cc f hh n t X +
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
        liftApply j (Cc p.1 j) (liftMean Q Cc f p.2 (n - j)) t X z := by
  classical
  have hs : (Finset.range (N + 1)).filter
      (fun r => r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D) = Finset.Icc 0 (n - 2) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have hi : Finset.Icc 0 (n - 2) = insert 0 (Finset.Icc 1 (n - 2)) := by
    ext r
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  unfold liftMeanCompositionCoefficient
  rw [← Finset.sum_filter, hs, hi, Finset.sum_insert (by simp)]
  simp only [Nat.sub_zero]
  rw [liftSequence_zero_degree_graded_action Q sX sZ a b N H Cc hseq hh hhh
    (fun q => liftMean Q Cc f q n) t ht X z]
end

end AVRegularity.CycleComparison.Lift
end
