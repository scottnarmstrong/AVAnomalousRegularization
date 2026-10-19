-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.LeftTermsFieldPostcomposition
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.LiftApplyFiniteVectorSynthesis
public import AVRegularity.CycleComparison.Residual.QuietMean.EpsPoly
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
public import AVRegularity.CycleComparison.Lift.SettingDimensionalScales
import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite indexed concatenation distributes the literal differential action. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem leftTermsApply_flatMap {ι : Type*} (l : List ι)
    (P : ι → List (LeftTerm E F)) (f : Vec 2 → E) (X z : Vec 2) :
    leftTermsApply (l.flatMap P) f X z = (l.map (fun i => leftTermsApply (P i) f X z)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.flatMap_cons, leftTermsApply_append, List.map_cons, List.sum_cons, ih]

theorem leftTermsApply_finset_flatMap {ι : Type*} (s : Finset ι)
    (P : ι → List (LeftTerm E F)) (f : Vec 2 → E) (X z : Vec 2) :
    leftTermsApply (s.toList.flatMap P) f X z = ∑ i ∈ s, leftTermsApply (P i) f X z := by
  rw [leftTermsApply_flatMap, Finset.sum_map_toList]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Mixed jet majorants sum over finite constituent families without a cardinality loss. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_jet_list_sum_le {α : Type*} (l : List α) (p q : ℕ)
    (f : α → Vec 2 → Vec 2 → E) (hf : ∀ a ∈ l, IsBoxSmooth p q (f a))
    (X z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (l.map fun a => f a Y y).sum) z) X‖ ≤
      (l.map fun a => ‖iteratedFDeriv ℝ p
        (fun Y => iteratedFDeriv ℝ q (f a Y) z) X‖).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_mixed_jet_add_le (hf a List.mem_cons_self)
      (isBoxSmooth_list_sum l p q f (fun b hb => hf b (List.mem_cons_of_mem a hb))) X z).trans
        (add_le_add le_rfl (ih (fun b hb => hf b (List.mem_cons_of_mem a hb))))

theorem norm_mixed_jet_finset_sum_le {α : Type*} (s : Finset α) (p q : ℕ)
    (f : α → Vec 2 → Vec 2 → E) (hf : ∀ a ∈ s, IsBoxSmooth p q (f a))
    (X z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => ∑ a ∈ s, f a Y y) z) X‖ ≤
      ∑ a ∈ s, ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (f a Y) z) X‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (norm_mixed_jet_add_le (hf a (Finset.mem_insert_self a s))
      (IsBoxSmooth.sum s (fun b hb => hf b (Finset.mem_insert_of_mem hb))) X z).trans
        (add_le_add le_rfl (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))))

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Genuine equality of continuous periodic representatives follows from equality of their cell classes. -/

variable {E : Type*} [NormedAddCommGroup E]

theorem periodicContinuous_eq_of_cell_ae (f g : Vec 2 → E)
    (hf : Continuous f) (hg : Continuous g)
    (hfp : AVenhance.IsZ2Periodic f) (hgp : AVenhance.IsZ2Periodic g)
    (he : f =ᵐ[volume.restrict AVenhance.unitCube] g) : f = g := by
  have hz : (fun x => f x - g x) =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
    filter_upwards [he] with x hx
    simp only [hx, sub_self, Pi.zero_apply]
  have hp : AVenhance.IsZ2Periodic (fun x => f x - g x) := by
    intro n x
    dsimp only
    rw [hfp n x, hgp n x]
  have h := periodicContinuous_zero_of_cell_ae _ (hf.sub hg) hp hz
  funext x
  have hx := congrFun h x
  exact sub_eq_zero.mp hx

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The source means used in the first recursion degree are genuine Bochner integrals. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceCoeff_zero_continuous (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (X : Vec 2)
    (hf : ContDiff ℝ (D : ℕ∞) (Φ X))
    (hc : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, ContDiff ℝ (D : ℕ∞) (γ.coeff α t X)) :
    Continuous (fun z => sourceCoeff edge η 0 t Φ X z) := by
  have hflux (q : Fin 2) : ContDiff ℝ 1 (sourceFlux edge η 0 t Φ q X) :=
    contDiff_pi.mpr (fun v => sourceFlux_zero_component_contDiff edge η t Φ X hf hc q v)
  simp only [sourceCoeff, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    iteratedDeriv_zero, sourceOp, dEps, mul_zero, zero_smul, add_zero, fastPartial]
  apply continuous_finsetSum
  intro q _
  exact ((hflux q).continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem sourceCoeff_one_independent_continuous (edge : ConstituentEdges D h) (η t : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (D : ℕ∞) f)
    (hfast : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X, ContDiff ℝ 1 (γ.coeff α t X))
    (hslow : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ 1 (fun X => γ.coeff α t X z)) (X : Vec 2) :
    Continuous (fun z => sourceCoeff edge η 1 t (fun X _ => f X) X z) := by
  rw [funext (sourceCoeff_one_independent edge η t f hf hfast hslow X)]
  apply continuous_finsetSum
  intro d _
  by_cases hd : d.1 = 2
  · simp only [ite_eq_left hd]
    apply continuous_finsetSum
    intro q _
    have hh := slowSourceFluxOrder_fast_contDiff edge η t f d q X
      (fun v u γ hγ α => hfast v u d γ hγ α X)
    exact (hh.continuous_fderiv (by norm_num)).clm_apply continuous_const
  · simp only [ite_eq_right hd]
    exact continuous_const
end

/-! Permutation averaging preserves the action on smooth real inputs. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem wordSymmetrize_action {m : ℕ} (c : DerivativeWord2 m → E →L[ℝ] F)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X : Vec 2) :
    (∑ α : DerivativeWord2 m, wordSymmetrize c α (orderedDerivative α f X)) =
      ∑ α : DerivativeWord2 m, c α (orderedDerivative α f X) := by
  have hp (σ : Equiv.Perm (Fin m)) :
      (∑ α : DerivativeWord2 m, c (α ∘ σ) (orderedDerivative α f X)) =
        ∑ α : DerivativeWord2 m, c α (orderedDerivative α f X) := by
    have he := Equiv.sum_comp (wordPermutationEquiv σ)
      (fun α : DerivativeWord2 m => c α (orderedDerivative α f X))
    simpa only [wordPermutationEquiv, Equiv.coe_fn_mk, orderedDerivative_comp_perm _ σ f hf]
      using he
  simp only [wordSymmetrize, smul_apply, sum_apply,
    ← Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [hp, Finset.sum_const, Finset.card_univ]
  have hcard : (Fintype.card (Equiv.Perm (Fin m)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
end

/-! Finite permutation averaging preserves rectangular coefficient regularity. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem wordSymmetrize_box {m : ℕ} (c : DerivativeWord2 m → Vec 2 → Vec 2 → E)
    (p q : ℕ) (hc : ∀ α, IsBoxSmooth p q (c α)) (α : DerivativeWord2 m) :
    IsBoxSmooth p q (fun X z => wordSymmetrize (fun β => c β X z) α) := by
  have hs := IsBoxSmooth.sum Finset.univ
    (fun (σ : Equiv.Perm (Fin m)) _ => hc (α ∘ σ))
  exact hs.clm_comp
    ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ • ContinuousLinearMap.id ℝ E)
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Adding a molecular metric adds only the diffusion part of the first cross operator. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellB1_metric_add (η : ℝ)
    (G J : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth 1 1 f)
    (hG : ∀ i j, IsBoxSmooth 1 0 (fun Y (_ : Vec 2) => G t Y i j))
    (hJ : ∀ i j, IsBoxSmooth 1 0 (fun Y (_ : Vec 2) => J t Y i j)) :
    cellB1 η (fun s Y i j => G s Y i j + J s Y i j) v t f =
      fun X z => cellB1 η G v t f X z + cellB1 η J (fun _ _ => 0) t f X z := by
  have he (i j : Fin 2) :
      slowPartial i (fun Y y => (G t Y i j + J t Y i j) • fastPartial j f Y y) =
      fun X z => slowPartial i (fun Y y => G t Y i j • fastPartial j f Y y) X z +
        slowPartial i (fun Y y => J t Y i j • fastPartial j f Y y) X z := by
    simp_rw [add_smul]
    exact slowPartial_add_box i _ _
      (isBoxSmooth_bilinear (hG i j) (hf.fastPartial j)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E))
      (isBoxSmooth_bilinear (hJ i j) (hf.fastPartial j)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E))
  have hterm (i j : Fin 2) (X z : Vec 2) :
      (G t X i j + J t X i j) • fastPartial i (slowPartial j f) X z +
        slowPartial i (fun Y y => (G t Y i j + J t Y i j) • fastPartial j f Y y) X z =
      (G t X i j • fastPartial i (slowPartial j f) X z +
        slowPartial i (fun Y y => G t Y i j • fastPartial j f Y y) X z) +
      (J t X i j • fastPartial i (slowPartial j f) X z +
        slowPartial i (fun Y y => J t Y i j • fastPartial j f Y y) X z) := by
    rw [congrFun (congrFun (he i j) X) z, add_smul]
    abel
  funext X z
  simp only [cellB1, Pi.zero_apply, mul_zero, zero_smul,
    Finset.sum_const_zero, zero_sub]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, smul_add]
  abel
end

/-! The second cross operator is linear in the molecular metric. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellB2_metric_add (η : ℝ)
    (G J : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth 2 0 f)
    (hG : ∀ i j, IsBoxSmooth 1 0 (fun Y (_ : Vec 2) => G t Y i j))
    (hJ : ∀ i j, IsBoxSmooth 1 0 (fun Y (_ : Vec 2) => J t Y i j)) :
    cellB2 η (fun s Y i j => G s Y i j + J s Y i j) t f =
      fun X z => cellB2 η G t f X z + cellB2 η J t f X z := by
  have he (i j : Fin 2) :
      slowPartial i (fun Y y => (G t Y i j + J t Y i j) • slowPartial j f Y y) =
      fun X z => slowPartial i (fun Y y => G t Y i j • slowPartial j f Y y) X z +
        slowPartial i (fun Y y => J t Y i j • slowPartial j f Y y) X z := by
    simp_rw [add_smul]
    exact slowPartial_add_box i _ _
      (isBoxSmooth_bilinear (hG i j) (hf.slowPartial j)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E))
      (isBoxSmooth_bilinear (hJ i j) (hf.slowPartial j)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E))
  funext X z
  simp only [cellB2, he, Finset.sum_add_distrib, smul_add, neg_add_rev]
  exact add_comm _ _
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The actual coordinate derivatives of a finite operator are finite left-term actions. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem leftTermsApply_fastPartial (l : List (LeftTerm E F)) (k : Fin 2)
    (hc : ∀ c ∈ l, IsBoxSmooth 0 1 c.coeff) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    fastPartial k (leftTermsApply l f) = leftTermsApply (l.map (fun c => c.fastDerivative k)) f := by
  induction l with
  | nil =>
    simp only [List.map_nil, leftTermsApply_nil]
    funext X z
    simp [fastPartial]
  | cons c l ih =>
    have hc' := hc c List.mem_cons_self
    have hl : ∀ d ∈ l, IsBoxSmooth 0 1 d.coeff := fun d hd => hc d (List.mem_cons_of_mem c hd)
    rw [leftTermsApply_cons, fastPartial_add_box k _ _ (c.apply_box 0 1 hc' f hf)
      (leftTermsApply_box l 0 1 hl f hf),
      ← c.fastDerivative_apply k hc'.1 f, ih hl, List.map_cons, leftTermsApply_cons]

theorem leftTermsApply_slowPartial (l : List (LeftTerm E F)) (k : Fin 2)
    (hc : ∀ c ∈ l, IsBoxSmooth 1 0 c.coeff) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    slowPartial k (leftTermsApply l f) = leftTermsApply (l.flatMap (fun c => c.slowDerivativeTerms k)) f := by
  induction l with
  | nil =>
    simp only [List.flatMap_nil, leftTermsApply_nil]
    funext X z
    simp [slowPartial]
  | cons c l ih =>
    have hc' := hc c List.mem_cons_self
    have hl : ∀ d ∈ l, IsBoxSmooth 1 0 d.coeff := fun d hd => hc d (List.mem_cons_of_mem c hd)
    rw [leftTermsApply_cons, slowPartial_add_box k _ _ (c.apply_box 1 0 hc' f hf)
      (leftTermsApply_box l 1 0 hl f hf),
      c.slowDerivative_apply k (boxSmooth_slow_contDiff hc') f hf, ih hl,
      List.flatMap_cons, leftTermsApply_append, leftTermsApply_slowDerivativeTerms]
end

/-! Constituent maps distribute over the finite differential action. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem leftTermsApply_map_postcompose (l : List (LeftTerm E F)) (T : F →L[ℝ] G)
    (f : Vec 2 → E) :
    leftTermsApply (l.map (fun c => c.postcompose T)) f =
      fun X z => T (leftTermsApply l f X z) := by
  funext X z
  induction l with
  | nil => simp [leftTermsApply]
  | cons c l ih =>
    simp only [List.map_cons, leftTermsApply_cons, LeftTerm.postcompose_apply, map_add, ih]

theorem leftTermsApply_map_fieldSmul (l : List (LeftTerm E F)) (a : Vec 2 → Vec 2 → ℝ)
    (f : Vec 2 → E) :
    leftTermsApply (l.map (fun c => c.fieldSmul a)) f =
      fun X z => a X z • leftTermsApply l f X z := by
  funext X z
  induction l with
  | nil => simp [leftTermsApply]
  | cons c l ih =>
    simp only [List.map_cons, leftTermsApply_cons, LeftTerm.fieldSmul_apply, smul_add, ih]
end

/-! The actual uncentered source adds the graded cross and source terms without a family-size loss. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftA_normalized_mixed_grading_of_terms (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n p q : ℕ) (t : ℝ) (v : ι) (A : Vec 2 →L[ℝ] ℝ) (lam C₁ C₂ : ℝ) (CS : ℕ → ℝ)
    (h₁ : IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ • cellB1 Q.η Q.G Q.v t
      (liftApply (n - 1) (Cc hh (n - 1)) f t) X z v))
    (hb₁ : ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => (Real.exp ((lam • A) Y))⁻¹ • cellB1 Q.η Q.G Q.v t
          (liftApply (n - 1) (Cc hh (n - 1)) f t) Y y v) z) X‖ ≤ C₁ * lam ^ (n + r))
    (h₂ : 2 ≤ n → IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ • cellB2 Q.η Q.G t
      (liftApply (n - 2) (Cc hh (n - 2)) f t) X z v))
    (hb₂ : 2 ≤ n → ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => (Real.exp ((lam • A) Y))⁻¹ • cellB2 Q.η Q.G t
          (liftApply (n - 2) (Cc hh (n - 2)) f t) Y y v) z) X‖ ≤ C₂ * lam ^ (n + r))
    (hS : hh ≠ 0 → ∀ j ≤ min D n,
      IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ • sourceCoeff Q.edge Q.η j t
        (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) X z v))
    (hbS : hh ≠ 0 → ∀ j ≤ min D n, ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => (Real.exp ((lam • A) Y))⁻¹ • sourceCoeff Q.edge Q.η j t
          (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) Y y v) z) X‖ ≤ CS j * lam ^ (n + r)) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ • liftA Q Cc f hh n t X z v) ∧
      ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
          (fun y => (Real.exp ((lam • A) Y))⁻¹ • liftA Q Cc f hh n t Y y v) z) X‖ ≤
            (C₁ + (if 2 ≤ n then C₂ else 0) +
              (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1), CS j)) * lam ^ (n + r) := by
  let F₁ := fun X z => (Real.exp ((lam • A) X))⁻¹ • cellB1 Q.η Q.G Q.v t
    (liftApply (n - 1) (Cc hh (n - 1)) f t) X z v
  let F₂ := fun X z => if 2 ≤ n then (Real.exp ((lam • A) X))⁻¹ • cellB2 Q.η Q.G t
    (liftApply (n - 2) (Cc hh (n - 2)) f t) X z v else 0
  let S := fun j X z => (Real.exp ((lam • A) X))⁻¹ • sourceCoeff Q.edge Q.η j t
    (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) X z v
  let FS := fun X z => if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1), S j X z
  have hf₂ : IsBoxSmooth p q F₂ := by
    dsimp only [F₂]
    split_ifs with hn
    · exact h₂ hn
    · exact IsBoxSmooth.zero
  have hb₂' r (hr : r ≤ p) s (hs : s ≤ q) X z :
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (F₂ Y) z) X‖ ≤
        (if 2 ≤ n then C₂ else 0) * lam ^ (n + r) := by
    dsimp only [F₂]
    split_ifs with hn
    · exact hb₂ hn r hr s hs X z
    · simp
  have hfs : IsBoxSmooth p q FS := by
    dsimp only [FS]
    split_ifs with hh0
    · exact IsBoxSmooth.zero
    · exact IsBoxSmooth.sum _ (fun j hj => hS hh0 j (by have he := Finset.mem_range.mp hj; omega))
  have hbs r (hr : r ≤ p) s (hs : s ≤ q) X z :
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (FS Y) z) X‖ ≤
        (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1), CS j) * lam ^ (n + r) := by
    dsimp only [FS]
    split_ifs with hh0
    · simp
    · apply (norm_mixed_jet_finset_sum_le _ r s S
        (fun j hj => (hS hh0 j (by have he := Finset.mem_range.mp hj; omega)).mono hr hs) X z).trans
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j hj => hbS hh0 j (by have he := Finset.mem_range.mp hj; omega)
        r hr s hs X z
  simp_rw [liftA_normalized_component_expansion]
  change IsBoxSmooth p q (fun X z => F₁ X z + F₂ X z - FS X z) ∧ _
  refine ⟨(h₁.add hf₂).sub hfs, ?_⟩
  intro r hr s hs X z
  have hfirst := (norm_mixed_jet_add_le (h₁.mono hr hs) (hf₂.mono hr hs) X z).trans
    (add_le_add (hb₁ r hr s hs X z) (hb₂' r hr s hs X z))
  have htotal := (norm_mixed_jet_sub_le ((h₁.add hf₂).mono hr hs) (hfs.mono hr hs) X z).trans
    (add_le_add hfirst (hbs r hr s hs X z))
  exact htotal.trans_eq (by ring)
end

/-! Joint regularity of a tested finite lift from its coefficient regularity. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_goodField_of_coefficients (D n : ℕ) (c : LiftCoeff ι h)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u,
      IsBoxSmooth D D (fun X z => c m α t X z v u))
    (hper : ∀ X, ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u,
      AVenhance.IsZ2Periodic (fun z => c m α t X z v u)) :
    GoodField D (liftApply n c (fun _ => f) t) := by
  have hbox := liftApply_box_reserve n D D c (fun _ => f) t
    (hf.of_le (by simp)) hc
  exact ⟨hbox.contDiff_uncurry le_rfl le_rfl,
    fun X => liftApply_periodic_of_coefficients n c (fun _ => f) t X (hper X)⟩
end

/-! The exact truncated tail combines uncentered and ordered composition jet budgets. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftTail_normalized_mixed_grading_of_terms (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (N hh n p q : ℕ) (t : ℝ) (v : ι) (A : Vec 2 →L[ℝ] ℝ) (lam C : ℝ)
    (hA : IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ •
      liftA Q Cc f hh n t X z v))
    (hbA : ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => (Real.exp ((lam • A) Y))⁻¹ • liftA Q Cc f hh n t Y y v) z) X‖ ≤
          C * lam ^ (n + r))
    (B : ℕ → ℕ × ℕ → ℝ)
    (hT : ∀ j ∈ Finset.range (N + 1),
      j ≤ n ∧ 2 ≤ n - j ∧ n - j ≤ N + D →
      ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
        IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ •
          liftApply j (Cc ab.1 j) (liftMean Q Cc f ab.2 (n - j)) t X z v))
    (hbT : ∀ j ∈ Finset.range (N + 1),
      j ≤ n ∧ 2 ≤ n - j ∧ n - j ≤ N + D →
      ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
          (fun y => (Real.exp ((lam • A) Y))⁻¹ •
            liftApply j (Cc ab.1 j) (liftMean Q Cc f ab.2 (n - j)) t Y y v) z) X‖ ≤
              B j ab * lam ^ (n + r)) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ •
      liftTailCoeff Q Cc N f hh n t X z v) ∧
      ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
          (fun y => (Real.exp ((lam • A) Y))⁻¹ • liftTailCoeff Q Cc N f hh n t Y y v) z) X‖ ≤
            (C + ∑ j ∈ Finset.range (N + 1),
              if j ≤ n ∧ 2 ≤ n - j ∧ n - j ≤ N + D then
                ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, B j ab else 0) *
                  lam ^ (n + r) := by
  let T := fun j (ab : ℕ × ℕ) X z => (Real.exp ((lam • A) X))⁻¹ •
    liftApply j (Cc ab.1 j) (liftMean Q Cc f ab.2 (n - j)) t X z v
  let S := fun j X z => if j ≤ n ∧ 2 ≤ n - j ∧ n - j ≤ N + D then
    ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, T j ab X z else 0
  have hS j (hj : j ∈ Finset.range (N + 1)) : IsBoxSmooth p q (S j) := by
    dsimp only [S]
    split_ifs with hg
    · exact IsBoxSmooth.sum _ (fun ab hab => hT j hj hg ab hab)
    · exact IsBoxSmooth.zero
  have hsum := IsBoxSmooth.sum (Finset.range (N + 1)) hS
  simp_rw [liftTail_normalized_component_expansion]
  refine ⟨hA.sub hsum, ?_⟩
  intro r hr s hs X z
  have hsb := norm_mixed_jet_finset_sum_le (Finset.range (N + 1)) r s S
    (fun j hj => (hS j hj).mono hr hs) X z
  have hb : ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => ∑ j ∈ Finset.range (N + 1), S j Y y) z) X‖ ≤
      (∑ j ∈ Finset.range (N + 1),
        if j ≤ n ∧ 2 ≤ n - j ∧ n - j ≤ N + D then
          ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, B j ab else 0) * lam ^ (n + r) := by
    apply hsb.trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    dsimp only [S]
    split_ifs with hg
    · apply (norm_mixed_jet_finset_sum_le _ r s (T j)
        (fun ab hab => (hT j hj hg ab hab).mono hr hs) X z).trans
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun ab hab => hbT j hj hg ab hab r hr s hs X z
    · simp
  exact (norm_mixed_jet_sub_le (hA.mono hr hs) (hsum.mono hr hs) X z).trans
    ((add_le_add (hbA r hr s hs X z) hb).trans_eq (by ring))
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set AVenhance.Infra.ODE
namespace AVRegularity.CycleComparison.Lift

/-! Summing the mode integral equations gives the pointwise time primitive of the actual profile. -/

theorem profileCellResponse_rhs_series_time_integral
    (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ) (a b κ M C₂ C₀ : ℝ)
    (hab : a ≤ b) (hκ : 0 < κ) (hM : 0 ≤ M) (hi : IntegrableOn g (Icc a b))
    (hg : ∀ s ∈ Icc a b, κ ≤ g s) (hgm : AEStronglyMeasurable g volume)
    (hgb : ∀ s, |g s| ≤ M) (hfm : Measurable (Function.uncurry f))
    (hC₂ : 0 ≤ C₂) (hC₀ : 0 ≤ C₀) (hf : ∀ s ∈ Icc a b, ContDiff ℝ 2 (f s))
    (hp : ∀ s ∈ Icc a b, Function.Periodic (f s) 1)
    (hj : ∀ s ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv 2 (f s) x‖ ≤ C₂)
    (hz : ∀ s ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1, ‖f s x‖ ≤ C₀)
    (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
    IntervalIntegrable (fun s => profileFourierSeries (fun n =>
      (-(‖profileFourierFrequency n‖ ^ 2) * g s) • profileModeResponse g f a s n +
        unitProfileFourierCoeff (f s) n) x) volume a t ∧
    profileCellResponse g f a t x = ∫ s in a..t, profileFourierSeries (fun n =>
      (-(‖profileFourierFrequency n‖ ^ 2) * g s) • profileModeResponse g f a s n +
        unitProfileFourierCoeff (f s) n) x := by
  let R := fun n s => (-(‖profileFourierFrequency n‖ ^ 2) * g s) •
    profileModeResponse g f a s n + unitProfileFourierCoeff (f s) n
  let T := fun n s => fourier n (x : AddCircle (1 : ℝ)) * R n s
  let W := profileJetMajorant (M * (C₂ / κ) + C₂) C₀
  have hW : Summable W := profileJetMajorant_summable _ _
  have hfm' : ∀ s ∈ uIcc a b, ∀ y ∈ Icc (0 : ℝ) 1, ‖f s y‖ ≤ C₀ := by
    simpa only [uIcc_of_le hab] using hz
  have hm (n : ℤ) : AEStronglyMeasurable (T n) (volume.restrict (Icc a b)) :=
    ((profileModeResponse_rhs_memLp_top g f a b hab M hM hgm hgb hfm C₀ hfm' n).aestronglyMeasurable).const_mul _
  have hb (n : ℤ) (s : ℝ) (hs : s ∈ Icc a b) : ‖T n s‖ ≤ W n := by
    simp only [T, norm_mul, fourier_apply, Circle.norm_coe, one_mul]
    exact profileModeResponse_uniform_rhs_bound g f a b κ M C₂ C₀ hκ hi hg
      (fun s _ => hgb s) hC₂ hC₀ hf hp hj hz n s hs
  have hLp := boundedTimeSeries_memLp (p := ⊤) T W hW a b hm hb
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hIb : IntegrableOn (fun s => ∑' n, T n s) (Icc a b) := hLp.integrable (by simp)
  have hInt : IntervalIntegrable (fun s => ∑' n, T n s) volume a t := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le ht.1] using hIb.mono_set hsub
  refine ⟨hInt, ?_⟩
  symm
  change (∫ s in a..t, ∑' n, T n s) = _
  rw [boundedTimeSeries_intervalIntegral_tsum T W hW a b hm hb a t ⟨le_rfl, hab⟩ ht ht.1]
  change (∑' n, ∫ s in a..t, T n s) = ∑' n, fourier n (x : AddCircle (1 : ℝ)) * profileModeResponse g f a t n
  apply tsum_congr
  intro n
  have hsol := (profileModeResponse_solves g f a b hab M hM hgm hgb hfm C₀ hfm' n).1 t ht
  have he : profileModeResponse g f a t n = ∫ s in a..t, R n s := by
    simpa only [linearRhs, smul_apply, ContinuousLinearMap.id_apply, zero_add] using hsol
  dsimp only [T]
  rw [intervalIntegral.integral_const_mul, he]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The common induction state gives clamped time measurability of applied slow and fast words. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n p q : ℕ}
  {c : LiftCoeff ι h} {M : ι → ι → ℝ}

theorem AmbientLiftCoefficientData.applied_measurable
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι)
    [FiniteDimensional ℝ (h v)] [MeasurableSpace (h v)] [BorelSpace (h v)]
    (ξ : h u) (X z : Vec 2) :
    Measurable (fun t => c m α (Set.projIcc a b hab t) X z v u ξ) := by
  apply measurable_of_all_real_duals
  intro l
  exact data.measurable m hm α v u
    (l.comp (ContinuousLinearMap.apply ℝ (h v) ξ)) X z

theorem AmbientLiftCoefficientData.applied_fast_word_measurable
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι)
    [FiniteDimensional ℝ (h v)] [MeasurableSpace (h v)] [BorelSpace (h v)]
    [SecondCountableTopology (h v)] (ξ : h u) (s : ℕ) (hs : s ≤ q)
    (β : DerivativeWord2 s) (X z : Vec 2) :
    Measurable (fun t => orderedDerivative β
      (fun y => c m α (Set.projIcc a b hab t) X y v u ξ) z) := by
  apply orderedDerivative_parameter_measurable _ q
    (fun y => data.applied_measurable m hm α v u ξ X y) _ s hs β z
  intro t
  exact ((data.box m hm α v u _ (Set.projIcc a b hab t).2).clm_comp
    (ContinuousLinearMap.apply ℝ (h v) ξ)).1 X

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Fast coordinate differentiation changes only left coefficients and spends one fast reserve. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def leftTermsFastPartial (k : Fin 2) (l : List (LeftTerm E F)) : List (LeftTerm E F) :=
  l.map (fun c => c.fastDerivative k)

theorem leftTermsFastPartial_order (k : Fin 2) (l : List (LeftTerm E F))
    (n : ℕ) (hl : ∀ c ∈ l, c.order ≤ n) (c : LeftTerm E F)
    (hc : c ∈ leftTermsFastPartial k l) : c.order ≤ n := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact hl d hd

theorem leftTermsFastPartial_box (k : Fin 2) (l : List (LeftTerm E F))
    (p q : ℕ) (hl : ∀ c ∈ l, IsBoxSmooth p (q + 1) c.coeff)
    (c : LeftTerm E F) (hc : c ∈ leftTermsFastPartial k l) : IsBoxSmooth p q c.coeff := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact d.fastDerivative_box p q (hl d hd) k

theorem leftTermsFastPartial_apply (k : Fin 2) (l : List (LeftTerm E F))
    (hl : ∀ c ∈ l, IsBoxSmooth 0 1 c.coeff)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    leftTermsApply (leftTermsFastPartial k l) f = fastPartial k (leftTermsApply l f) :=
  (leftTermsApply_fastPartial l k hl f hf).symm

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Actual ordered lift compositions preserve clamped time measurability. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n p q : ℕ}
  {c : LiftCoeff ι h} {M : ι → ι → ℝ}

theorem AmbientLiftCoefficientData.liftApply_clamped_measurable
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M)
    (g : ℝ → Vec 2 → ∀ i, h i)
    (hg : ∀ t ∈ Set.Icc a b, ContDiff ℝ (n : ℕ∞) (g t))
    (hgm : ∀ X, Measurable (fun t => g (Set.projIcc a b hab t) X))
    (v : ι) (X z : Vec 2) :
    Measurable (fun t => liftApply n c g (Set.projIcc a b hab t) X z v) := by
  unfold liftApply
  apply Finset.measurable_sum
  intro m hm
  have hmn : m ≤ n := by have hh := Finset.mem_range.mp hm; omega
  apply Finset.measurable_sum
  intro α _
  apply Finset.measurable_sum
  intro u _
  have hcm : Measurable (fun t => c m α (Set.projIcc a b hab t) X z v u) :=
    measurable_of_all_real_duals _ (fun l => data.measurable m hmn α v u l X z)
  have hword := orderedDerivative_parameter_measurable
    (fun t => g (Set.projIcc a b hab t)) n hgm
    (fun t => hg _ (Set.projIcc a b hab t).2) m hmn α X
  have heval : Continuous (fun pair : (h u →L[ℝ] h v) × h u => pair.1 pair.2) :=
    continuous_fst.clm_apply continuous_snd
  exact heval.measurable.comp (hcm.prodMk ((measurable_pi_apply u).comp hword))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The finite component terms reproduce exactly the lift action `liftApply`. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftComponentLeftTerms_apply (n : ℕ) (c : LiftCoeff ι h) (t : ℝ) (v : ι)
    (f : Vec 2 → ∀ i, h i) (X z : Vec 2) :
    leftTermsApply (liftComponentLeftTerms n c t v) f X z =
      liftApply n c (fun _ => f) t X z v := by
  classical
  unfold liftComponentLeftTerms
  rw [leftTermsApply_finset_flatMap]
  apply Finset.sum_congr rfl
  intro m hm
  rw [leftTermsApply_finset_flatMap]
  apply Finset.sum_congr rfl
  intro α hα
  simp only [leftTermsApply, List.map_map, Finset.sum_map_toList]
  rfl

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! The genuine finite-past Fourier response solves its classical scalar diffusion equation in time-integrated form. -/

theorem profileCellResponse_time_integral (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a b κ M : ℝ) (hab : a ≤ b) (hκ : 0 < κ) (hM : 0 ≤ M)
    (hi : IntegrableOn g (Icc a b)) (hg : ∀ s ∈ Icc a b, κ ≤ g s)
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ s, |g s| ≤ M)
    (hfm : Measurable (Function.uncurry f)) (C : ℕ → ℝ) (hC : ∀ j ≤ 2, 0 ≤ C j)
    (hf : ∀ s ∈ Icc a b, ContDiff ℝ 2 (f s))
    (hp : ∀ s ∈ Icc a b, Function.Periodic (f s) 1)
    (hj : ∀ j ≤ 2, ∀ s ∈ Icc a b, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (f s) y‖ ≤ C j) (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
    IntervalIntegrable (fun s => g s • iteratedDeriv 2 (profileCellResponse g f a s) x + f s x) volume a t ∧
    profileCellResponse g f a t x = ∫ s in a..t,
      g s • iteratedDeriv 2 (profileCellResponse g f a s) x + f s x := by
  have hz : ∀ s ∈ Icc a b, ∀ y ∈ Icc (0 : ℝ) 1, ‖f s y‖ ≤ C 0 := by
    simpa only [iteratedDeriv_zero] using hj 0 (by omega)
  obtain ⟨hInt, heq⟩ := profileCellResponse_rhs_series_time_integral g f a b κ M (C 2) (C 0)
    hab hκ hM hi hg hgm hgb hfm (hC 2 le_rfl) (hC 0 (by omega)) hf hp (hj 2 le_rfl) hz t ht x
  have he : ∀ s ∈ uIcc a t, profileFourierSeries (fun n =>
      (-(‖profileFourierFrequency n‖ ^ 2) * g s) • profileModeResponse g f a s n +
        unitProfileFourierCoeff (f s) n) x =
      g s • iteratedDeriv 2 (profileCellResponse g f a s) x + f s x := by
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc le_rfl (hs.2.trans ht.2)
    exact profileCellResponse_rhs_series_spatial_identity g f a s κ hs.1 hκ (hi.mono_set hsub)
      (fun r hr => hg r (hsub hr)) C hC (fun r hr => hf r (hsub hr))
      (fun r hr => hp r (hsub hr)) (fun j hj2 r hr => hj j hj2 r (hsub hr)) x
  refine ⟨hInt.congr (fun s hs => he s (uIoc_subset_uIcc hs)), ?_⟩
  rw [heq]
  exact intervalIntegral.integral_congr he

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite differential terms have symmetric coefficients on every smooth real input. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def leftTermsSymmetricCoefficient (l : List (LeftTerm E F)) (m : ℕ)
    (α : DerivativeWord2 m) : Vec 2 → Vec 2 → E →L[ℝ] F :=
  fun X z => wordSymmetrize (fun β => leftTermsCoefficient l m β X z) α

theorem leftTermsSymmetricCoefficient_perm (l : List (LeftTerm E F)) (m : ℕ)
    (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    leftTermsSymmetricCoefficient l m (α ∘ σ) = leftTermsSymmetricCoefficient l m α := by
  funext X z
  exact wordSymmetrize_comp_perm _ α σ

theorem leftTermsSymmetricCoefficient_box (l : List (LeftTerm E F)) (p q : ℕ)
    (hl : ∀ c ∈ l, IsBoxSmooth p q c.coeff) (m : ℕ) (α : DerivativeWord2 m) :
    IsBoxSmooth p q (leftTermsSymmetricCoefficient l m α) :=
  wordSymmetrize_box _ p q (fun β => leftTermsCoefficient_box l p q hl m β) α

theorem leftTermsSymmetricCoefficient_action (l : List (LeftTerm E F)) (n : ℕ)
    (hl : ∀ c ∈ l, c.order ≤ n) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X z : Vec 2) :
    (∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m,
      leftTermsSymmetricCoefficient l m α X z (orderedDerivative α f X)) =
        leftTermsApply l f X z := by
  simp only [leftTermsSymmetricCoefficient, wordSymmetrize_action _ f hf X]
  exact leftTermsCoefficient_action l n hl f X z
end

/-! Component left terms synthesize the literal block coefficient array. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def leftTermsBlockCoefficient (l : ∀ v, List (LeftTerm (∀ i, h i) (h v))) : LiftCoeff ι h :=
  fun m α _ X z v u => (leftTermsSymmetricCoefficient (l v) m α X z).comp
    (ContinuousLinearMap.single ℝ h u)

theorem leftTermsBlockCoefficient_perm (l : ∀ v, List (LeftTerm (∀ i, h i) (h v)))
    (m : ℕ) (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    leftTermsBlockCoefficient l m (α ∘ σ) = leftTermsBlockCoefficient l m α := by
  funext t X z v u
  simp only [leftTermsBlockCoefficient, leftTermsSymmetricCoefficient_perm]

theorem leftTermsBlockCoefficient_apply (l : ∀ v, List (LeftTerm (∀ i, h i) (h v)))
    (n : ℕ) (hl : ∀ v, ∀ c ∈ l v, c.order ≤ n)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (X z : Vec 2) (v : ι) :
    liftApply n (leftTermsBlockCoefficient l) (fun _ => f) t X z v =
      leftTermsApply (l v) f X z := by
  unfold liftApply leftTermsBlockCoefficient
  have he (m : ℕ) (α : DerivativeWord2 m) :
      (∑ u, ((leftTermsSymmetricCoefficient (l v) m α X z).comp
        (ContinuousLinearMap.single ℝ h u)) (orderedDerivative α f X u)) =
      leftTermsSymmetricCoefficient (l v) m α X z (orderedDerivative α f X) := by
    simp only [ContinuousLinearMap.comp_apply, ← map_sum]
    congr 1
    ext u
    simp
  simp only [he]
  exact leftTermsSymmetricCoefficient_action (l v) n (hl v) f hf X z
end

/-! Coefficient synthesis preserves the finite tested-order support of its literal terms. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem leftTermsCoefficient_zero_of_orders_ne (l : List (LeftTerm E F)) (m : ℕ)
    (hm : ∀ c ∈ l, c.order ≠ m) (α : DerivativeWord2 m) :
    leftTermsCoefficient l m α = fun _ _ => 0 := by
  funext X z
  unfold leftTermsCoefficient
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  rw [c.coeffAt_ne_order m α (hm c hc)]

theorem leftTermsSymmetricCoefficient_above_order (l : List (LeftTerm E F))
    (n : ℕ) (hl : ∀ c ∈ l, c.order ≤ n) (m : ℕ) (hm : n < m)
    (α : DerivativeWord2 m) :
    leftTermsSymmetricCoefficient l m α = fun _ _ => 0 := by
  have he (β : DerivativeWord2 m) : leftTermsCoefficient l m β = fun _ _ => 0 :=
    leftTermsCoefficient_zero_of_orders_ne l m (fun c hc => by have := hl c hc; omega) β
  funext X z
  simp only [leftTermsSymmetricCoefficient, wordSymmetrize, he, Finset.sum_const_zero, smul_zero]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Rectangular bilinear grading at a fixed slow point needs only local slow-jet majorants. -/

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_mixed_bilinear_graded_le_at_slow_point (p r s : ℕ) (lam A B : ℝ)
    (hlam : 0 ≤ lam) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (T : E →L[ℝ] F →L[ℝ] G) (hT : ‖T‖ ≤ 1) (X : Vec 2) :
    ∀ q (f : Vec 2 → Vec 2 → E) (g : Vec 2 → Vec 2 → F),
      IsBoxSmooth p q f → IsBoxSmooth p q g →
      (∀ a ≤ p, ∀ b ≤ q, ∀ z,
        ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ A * lam ^ (r + a)) →
      (∀ a ≤ p, ∀ b ≤ q, ∀ z,
        ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (g Y) z) X‖ ≤ B * lam ^ (s + a)) →
      ∀ z, ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
        (fun y => T (f Y y) (g Y y)) z) X‖ ≤
        (2 ^ (p + 2 * q) * A * B) * lam ^ (r + s + p) := by
  intro q
  induction q with
  | zero =>
    intro f g hf hg hbf hbg z
    have ha (a : ℕ) (ha : a ≤ p) := hbf a ha 0 le_rfl z
    have hb (a : ℕ) (ha : a ≤ p) := hbg a ha 0 le_rfl z
    simp only [norm_mixed_fast_zero_eq] at ha hb
    have h := norm_iteratedFDeriv_bilinear_uniform_graded_le p r s T hT
      (fun Y => f Y z) (fun Y => g Y z) (boxSmooth_slow_contDiff hf z)
      (boxSmooth_slow_contDiff hg z) X lam A B hlam hA hB ha hb
    simpa only [norm_mixed_fast_zero_eq,
      Nat.mul_zero, Nat.add_zero] using! h
  | succ q ih =>
    intro f g hf hg hbf hbg z
    have hf0 := hf.mono le_rfl (Nat.le_succ q)
    have hg0 := hg.mono le_rfl (Nat.le_succ q)
    have hbf0 := fun (a : ℕ) (ha : a ≤ p) (b : ℕ) (hb : b ≤ q) y => hbf a ha b (hb.trans (Nat.le_succ q)) y
    have hbg0 := fun (a : ℕ) (ha : a ≤ p) (b : ℕ) (hb : b ≤ q) y => hbg a ha b (hb.trans (Nat.le_succ q)) y
    have hbfk (k : Fin 2) : ∀ a ≤ p, ∀ b ≤ q, ∀ y,
        ‖iteratedFDeriv ℝ a (fun Z => iteratedFDeriv ℝ b (fastPartial k f Z) y) X‖ ≤
          A * lam ^ (r + a) := by
      intro a ha b hb y
      have h := norm_mixed_fast_direction_le (r := a) (q := b) (hf.mono ha (by omega)) (basisVec k) X y
      have h' : ‖iteratedFDeriv ℝ a (fun Z => iteratedFDeriv ℝ b (fastPartial k f Z) y) X‖ ≤
          ‖iteratedFDeriv ℝ a (fun Z => iteratedFDeriv ℝ (b + 1) (f Z) y) X‖ := by
        simpa only [fastPartial, norm_basisVec, one_mul] using! h
      exact h'.trans (hbf a ha (b + 1) (by omega) y)
    have hbgk (k : Fin 2) : ∀ a ≤ p, ∀ b ≤ q, ∀ y,
        ‖iteratedFDeriv ℝ a (fun Z => iteratedFDeriv ℝ b (fastPartial k g Z) y) X‖ ≤
          B * lam ^ (s + a) := by
      intro a ha b hb y
      have h := norm_mixed_fast_direction_le (r := a) (q := b) (hg.mono ha (by omega)) (basisVec k) X y
      have h' : ‖iteratedFDeriv ℝ a (fun Z => iteratedFDeriv ℝ b (fastPartial k g Z) y) X‖ ≤
          ‖iteratedFDeriv ℝ a (fun Z => iteratedFDeriv ℝ (b + 1) (g Z) y) X‖ := by
        simpa only [fastPartial, norm_basisVec, one_mul] using! h
      exact h'.trans (hbg a ha (b + 1) (by omega) y)
    apply (norm_mixed_fast_jet_le_sum_partials (isBoxSmooth_bilinear hf hg T) X z).trans
    calc
      _ ≤ ∑ _k : Fin 2, 2 * ((2 ^ (p + 2 * q) * A * B) * lam ^ (r + s + p)) := by
        apply Finset.sum_le_sum
        intro k _
        rw [fastPartial_bilinear_box hf hg T k]
        have h1 := isBoxSmooth_bilinear (hf.fastPartial k) hg0 T
        have h2 := isBoxSmooth_bilinear hf0 (hg.fastPartial k) T
        apply (norm_mixed_jet_add_le h1 h2 X z).trans
        have ha := ih (fastPartial k f) g (hf.fastPartial k) hg0 (hbfk k) hbg0 z
        have hb := ih f (fastPartial k g) hf0 (hg.fastPartial k) hbf0 (hbgk k) z
        have hab := add_le_add ha hb
        simpa only [two_mul] using! hab
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show p + 2 * (q + 1) = (p + 2 * q) + 2 by omega, pow_add]
        ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Summing genuine constituent bounds preserves the normalized source entry budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem norm_mixed_source_constituent_sum_le (edge : ConstituentEdges D h)
    (I : Set ℝ) (p q : ℕ) (lam K : ℝ) (C : ι → ℝ) (σ : ℕ) (v : ι)
    (T : ∀ u, ∀ d : Finset.Icc 2 D, Constituent d.val (h u) (h v) →
      DerivativeWord2 (d.val - 1) → Vec 2 → Vec 2 → h v)
    (hT : ∀ u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth p q (T u d γ α))
    (X z : Vec 2)
    (hb : ∀ u d, ∀ γ ∈ edge v u d, ∀ α,
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (T u d γ α Y) z) X‖ ≤
        K * (‖γ.map‖ * constituentUniformMixedBudget I p q lam (γ.coeff α)) * C u * lam ^ σ) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => ∑ u, ∑ d : Finset.Icc 2 D,
        ((edge v u d).map fun γ => ∑ α, T u d γ α Y y).sum) z) X‖ ≤
      ∑ u, K * sourceUniformMixedBudget edge I p q lam v u * C u * lam ^ σ := by
  have hγ (u : ι) (d : Finset.Icc 2 D) (γ : Constituent d.val (h u) (h v))
      (hm : γ ∈ edge v u d) : IsBoxSmooth p q (fun Y y => ∑ α, T u d γ α Y y) :=
    IsBoxSmooth.sum Finset.univ (fun α _ => hT u d γ hm α)
  have hd (u : ι) (d : Finset.Icc 2 D) :
      IsBoxSmooth p q (fun Y y => ((edge v u d).map fun γ => ∑ α, T u d γ α Y y).sum) :=
    isBoxSmooth_list_sum _ p q _ (fun γ hm => hγ u d γ hm)
  apply (norm_mixed_jet_finset_sum_le Finset.univ p q _
    (fun u _ => IsBoxSmooth.sum Finset.univ (fun d _ => hd u d)) X z).trans
  apply Finset.sum_le_sum
  intro u _
  apply (norm_mixed_jet_finset_sum_le Finset.univ p q _ (fun d _ => hd u d) X z).trans
  have he : K * sourceUniformMixedBudget edge I p q lam v u * C u * lam ^ σ =
      ∑ d : Finset.Icc 2 D, ((edge v u d).map fun γ => ∑ α,
        K * (‖γ.map‖ * constituentUniformMixedBudget I p q lam (γ.coeff α)) * C u * lam ^ σ).sum := by
    unfold sourceUniformMixedBudget
    have hl (l : List ℝ) (a : ℝ) : a * l.sum = (l.map fun x => a * x).sum := by
      induction l with
      | nil => simp
      | cons x l ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]
    calc
      _ = (K * C u * lam ^ σ) * ∑ d, ((edge v u d).map fun γ =>
          ‖γ.map‖ * ∑ α, constituentUniformMixedBudget I p q lam (γ.coeff α)).sum := by ring
      _ = _ := by
        simp only [Finset.mul_sum, hl, List.map_map, Function.comp_def]
        apply Finset.sum_congr rfl
        intro d _
        apply congrArg List.sum
        apply List.map_congr_left
        intro γ _
        apply Finset.sum_congr rfl
        intro α _
        ring
  rw [he]
  apply Finset.sum_le_sum
  intro d _
  apply (norm_mixed_jet_list_sum_le (edge v u d) p q _ (fun γ hm => hγ u d γ hm) X z).trans
  apply List.sum_le_sum
  intro γ hm
  exact (norm_mixed_jet_finset_sum_le Finset.univ p q _ (fun α _ => hT u d γ hm α) X z).trans
    (Finset.sum_le_sum fun α _ => hb u d γ hm α)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Multiplying by an exponential test uses a local exponential factor that later cancels exactly. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_exponential_smul_graded_le (p q δ : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (lam C : ℝ) (hlam : 0 ≤ lam) (hC : 0 ≤ C) (f : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth p q f) (X : Vec 2)
    (hb : ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (a b : ℕ) (ha : a ≤ p) (hbq : b ≤ q) (z : Vec 2) :
    ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
      (fun y => Real.exp ((lam • A) Y) • f Y y) z) X‖ ≤
      (Real.exp ((lam • A) X) * (2 ^ (p + 2 * q) * (max 1 ‖A‖) ^ p * C)) *
        lam ^ (δ + a) := by
  let e : Vec 2 → Vec 2 → ℝ := fun Y _ => Real.exp ((lam • A) Y)
  have he : IsBoxSmooth a b e := isBoxSmooth_slow_field a b _
    (Real.contDiff_exp.comp (lam • A).contDiff)
  have hej : ∀ r ≤ a, ∀ s ≤ b, ∀ y,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (e Y) y) X‖ ≤
        (Real.exp ((lam • A) X) * (max 1 ‖A‖) ^ p) * lam ^ (0 + r) := by
    intro r hr s _ y
    simpa only [Nat.zero_add] using
      norm_mixed_slow_exponential_le p A lam hlam r s (hr.trans ha) X y
  have hh := norm_mixed_bilinear_graded_le_at_slow_point a 0 δ lam
    (Real.exp ((lam • A) X) * (max 1 ‖A‖) ^ p) C hlam (by positivity) hC
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
    ContinuousLinearMap.opNorm_lsmul_le X b e f he (hf.mono ha hbq) hej
    (fun r hr s hs y => hb r (hr.trans ha) s (hs.trans hbq) y) z
  apply hh.trans
  simp only [Nat.zero_add]
  calc
    _ ≤ (2 ^ (p + 2 * q) * (Real.exp ((lam • A) X) * (max 1 ‖A‖) ^ p) * C) *
        lam ^ (δ + a) := by
      gcongr
      · norm_num
    _ = _ := by ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Block synthesis preserves the rectangular regularity of finite term coefficients. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem leftTermsBlockCoefficient_box
    (l : ∀ v, List (LeftTerm (∀ i, h i) (h v))) (p q : ℕ)
    (hl : ∀ v, ∀ c ∈ l v, IsBoxSmooth p q c.coeff)
    (m : ℕ) (α : DerivativeWord2 m) (t : ℝ) (v u : ι) :
    IsBoxSmooth p q (fun X z => leftTermsBlockCoefficient l m α t X z v u) :=
  (leftTermsSymmetricCoefficient_box (l v) p q (hl v) m α).clm_comp
    ((ContinuousLinearMap.compL ℝ (h u) (∀ i, h i) (h v)).flip
      (ContinuousLinearMap.single ℝ h u))

end AVRegularity.CycleComparison.Lift
end
