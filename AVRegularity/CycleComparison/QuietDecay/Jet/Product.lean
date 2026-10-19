-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.Jets.Lift
public import AVRegularity.CycleComparison.Residual.MixedTail.Energy
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

/-! Exact Leibniz identity for the ordered slow derivative of `X ↦ f X (ξ X)` with `f` operator
valued and `ξ` vector valued, indexed by the subsets (given as labellings `s : Fin m → Bool`) of
the positions of the word. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.QuietDecay

section DerivList

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The ordered derivative along a list of letters (first letter innermost). -/
def derivList (l : List (Fin 2)) (g : Vec 2 → V) : Vec 2 → V :=
  l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) g

theorem orderedDerivative_eq_derivList {m : ℕ} (α : DerivativeWord2 m) (g : Vec 2 → V) :
    orderedDerivative α g = derivList (List.ofFn α) g := rfl

@[simp] theorem derivList_nil (g : Vec 2 → V) : derivList [] g = g := rfl

theorem derivList_append_single (l : List (Fin 2)) (i : Fin 2) (g : Vec 2 → V) :
    derivList (l ++ [i]) g = fun x => fderiv ℝ (derivList l g) x (basisVec i) := by
  simp [derivList, List.foldl_append]

theorem contDiff_derivList (l : List (Fin 2)) : ∀ (g : Vec 2 → V) (r : ℕ),
    ContDiff ℝ ((l.length + r : ℕ) : ℕ∞) g → ContDiff ℝ (r : ℕ∞) (derivList l g) := by
  induction l with
  | nil => intro g r hg; simpa using hg
  | cons i l ih =>
    intro g r hg
    have h1 : ContDiff ℝ ((l.length + r : ℕ) : ℕ∞) (fun x => fderiv ℝ g x (basisVec i)) := by
      have hl : (i :: l).length + r = (l.length + r) + 1 := by simp; omega
      rw [hl] at hg
      exact (hg.fderiv_right (m := ((l.length + r : ℕ) : ℕ∞)) (by exact_mod_cast le_rfl)).clm_apply
        contDiff_const
    exact ih _ r h1

end DerivList

/-- Splitting of a word along a labelling: the letters labelled `true` and those labelled `false`,
in order. -/
def splitWord : (m : ℕ) → DerivativeWord2 m → (Fin m → Bool) → List (Fin 2) × List (Fin 2)
  | 0, _, _ => ([], [])
  | m + 1, w, s =>
    if s (Fin.last m) then
      ((splitWord m (fun i => w i.castSucc) (fun i => s i.castSucc)).1 ++ [w (Fin.last m)],
        (splitWord m (fun i => w i.castSucc) (fun i => s i.castSucc)).2)
    else
      ((splitWord m (fun i => w i.castSucc) (fun i => s i.castSucc)).1,
        (splitWord m (fun i => w i.castSucc) (fun i => s i.castSucc)).2 ++ [w (Fin.last m)])

theorem splitWord_length : ∀ (m : ℕ) (w : DerivativeWord2 m) (s : Fin m → Bool),
    (splitWord m w s).1.length + (splitWord m w s).2.length = m := by
  intro m
  induction m with
  | zero => intro w s; simp [splitWord]
  | succ m ih =>
    intro w s
    have := ih (fun i => w i.castSucc) (fun i => s i.castSucc)
    unfold splitWord
    split_ifs <;> simp <;> omega

section Leibniz

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Exact Leibniz identity for the ordered derivative of `X ↦ f X (ξ X)`: the sum over all
labellings `s` of the word of `(∂^{w|s} f)(∂^{w|sᶜ} ξ)`. -/
theorem orderedDerivative_clm_apply_eq : ∀ (m : ℕ) (w : DerivativeWord2 m)
    (f : Vec 2 → (E →L[ℝ] F)) (ξ : Vec 2 → E), ContDiff ℝ (m : ℕ∞) f → ContDiff ℝ (m : ℕ∞) ξ →
    orderedDerivative w (fun X => f X (ξ X)) = fun X => ∑ s : Fin m → Bool,
      derivList (splitWord m w s).1 f X (derivList (splitWord m w s).2 ξ X) := by
  intro m
  induction m with
  | zero =>
    intro w f ξ _ _
    rw [orderedDerivative_zero]
    funext X
    simp [splitWord]
  | succ m ih =>
    intro w f ξ hf hξ
    set w' : DerivativeWord2 m := fun i => w i.castSucc with hw'
    have hf' : ContDiff ℝ (m : ℕ∞) f := hf.of_le (by exact_mod_cast Nat.le_succ m)
    have hξ' : ContDiff ℝ (m : ℕ∞) ξ := hξ.of_le (by exact_mod_cast Nat.le_succ m)
    have hIH := ih w' f ξ hf' hξ'
    have hcd : ∀ (s' : Fin m → Bool), ContDiff ℝ (1 : ℕ∞) (derivList (splitWord m w' s').1 f) ∧
        ContDiff ℝ (1 : ℕ∞) (derivList (splitWord m w' s').2 ξ) := by
      intro s'
      have hl := splitWord_length m w' s'
      constructor
      · refine contDiff_derivList _ f 1 (hf.of_le ?_)
        exact_mod_cast (by omega : (splitWord m w' s').1.length + 1 ≤ m + 1)
      · refine contDiff_derivList _ ξ 1 (hξ.of_le ?_)
        exact_mod_cast (by omega : (splitWord m w' s').2.length + 1 ≤ m + 1)
    rw [orderedDerivative_succ]
    show (fun x => fderiv ℝ (orderedDerivative w' (fun X => f X (ξ X))) x (basisVec (w (Fin.last m)))) = _
    rw [hIH]
    funext x
    have hdiff : ∀ s' : Fin m → Bool, DifferentiableAt ℝ (fun X =>
        derivList (splitWord m w' s').1 f X (derivList (splitWord m w' s').2 ξ X)) x := by
      intro s'
      exact ((hcd s').1.differentiable (by norm_num) x).clm_apply
        ((hcd s').2.differentiable (by norm_num) x)
    rw [fderiv_fun_sum (fun s' _ => hdiff s')]
    simp only [sum_apply]
    rw [← (Fin.snocEquiv (fun _ : Fin (m + 1) => Bool)).sum_comp]
    rw [Fintype.sum_prod_type]
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Fintype.sum_bool]
    have hA : ∀ (l : List (Fin 2)), fderiv ℝ (derivList l f) x (basisVec (w (Fin.last m))) =
        derivList (l ++ [w (Fin.last m)]) f x := fun l => by rw [derivList_append_single]
    have hB : ∀ (l : List (Fin 2)), fderiv ℝ (derivList l ξ) x (basisVec (w (Fin.last m))) =
        derivList (l ++ [w (Fin.last m)]) ξ x := fun l => by rw [derivList_append_single]
    rw [fderiv_clm_apply ((hcd y).1.differentiable (by norm_num) x)
      ((hcd y).2.differentiable (by norm_num) x)]
    simp only [splitWord, Fin.snoc_last, Fin.snoc_castSucc, ite_true, Bool.false_eq_true, ite_false,
      add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      hA, hB]
    rw [add_comm]

/-- With a fast word: the fast derivatives fall on the operator-valued factor only. -/
theorem orderedDerivative_orderedDerivative_clm_apply_eq {sX sZ p q : ℕ}
    {c : Vec 2 → Vec 2 → (E →L[ℝ] F)} (hc : IsBoxSmooth sX sZ c) (hp : p ≤ sX) (hq : q ≤ sZ)
    {ξ : Vec 2 → E} (hξ : ContDiff ℝ (p : ℕ∞) ξ) (w : DerivativeWord2 p) (β : DerivativeWord2 q)
    (X z : Vec 2) :
    orderedDerivative w (fun X' => orderedDerivative β (fun z' => c X' z' (ξ X')) z) X =
      ∑ s : Fin p → Bool,
        derivList (splitWord p w s).1 (fun X' => orderedDerivative β (c X') z) X
          (derivList (splitWord p w s).2 ξ X) := by
  have hin : ∀ X', orderedDerivative β (fun z' => c X' z' (ξ X')) z =
      orderedDerivative β (c X') z (ξ X') := fun X' =>
    congrFun (orderedDerivative_clm_comp (ContinuousLinearMap.apply ℝ F (ξ X')) β
      ((hc.1 X').of_le (by exact_mod_cast hq))) z
  have hf : ContDiff ℝ (p : ℕ∞) (fun X' => orderedDerivative β (c X') z) := by
    have : (fun X' => orderedDerivative β (c X') z) = fun X' =>
        ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) (E →L[ℝ] F)
          (fun j => basisVec (β (Fin.rev j))) (iteratedFDeriv ℝ q (c X') z) := by
      funext X'
      rw [orderedDerivative_eq_iteratedFDeriv β ((hc.1 X').of_le (by exact_mod_cast hq))]
      rfl
    rw [this]
    have hcz : ContDiff ℝ (p : ℕ∞) (fun X' => iteratedFDeriv ℝ q (c X') z) :=
      (hc.2.1 q hq z).of_le (by exact_mod_cast hp)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) (E →L[ℝ] F)
      (fun j => basisVec (β (Fin.rev j)))).contDiff.comp hcz
  have e : (fun X' => orderedDerivative β (fun z' => c X' z' (ξ X')) z) =
      fun X' => orderedDerivative β (c X') z (ξ X') := funext hin
  rw [e]
  exact congrFun (orderedDerivative_clm_apply_eq p w _ ξ hf hξ) X

end Leibniz

section Sums

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Regularity making the word-of-word derivative additive. -/
def GoodWW (p q : ℕ) (β : DerivativeWord2 q) (z : Vec 2) (g : Vec 2 → Vec 2 → V) : Prop :=
  (∀ X', ContDiff ℝ (q : ℕ∞) (g X')) ∧
    ContDiff ℝ (p : ℕ∞) (fun X' => orderedDerivative β (g X') z)

theorem GoodWW.sum {p q : ℕ} {β : DerivativeWord2 q} {z : Vec 2} {κ : Type*} (s : Finset κ)
    {g : κ → Vec 2 → Vec 2 → V} (hg : ∀ k ∈ s, GoodWW p q β z (g k)) :
    GoodWW p q β z (fun X' z' => ∑ k ∈ s, g k X' z') := by
  refine ⟨fun X' => ContDiff.sum fun k hk => (hg k hk).1 X', ?_⟩
  have : (fun X' => orderedDerivative β (fun z' => ∑ k ∈ s, g k X' z') z) =
      fun X' => ∑ k ∈ s, orderedDerivative β (g k X') z := by
    funext X'
    exact congrFun (MixedTail.orderedDerivative_sum s β (fun k hk => (hg k hk).1 X')) z
  rw [this]
  exact ContDiff.sum fun k hk => (hg k hk).2

theorem orderedDerivative_orderedDerivative_sum {p q : ℕ} {β : DerivativeWord2 q} {z : Vec 2}
    {κ : Type*} (s : Finset κ) {g : κ → Vec 2 → Vec 2 → V} (hg : ∀ k ∈ s, GoodWW p q β z (g k))
    (w : DerivativeWord2 p) (X : Vec 2) :
    orderedDerivative w (fun X' => orderedDerivative β (fun z' => ∑ k ∈ s, g k X' z') z) X =
      ∑ k ∈ s, orderedDerivative w (fun X' => orderedDerivative β (g k X') z) X := by
  have h1 : (fun X' => orderedDerivative β (fun z' => ∑ k ∈ s, g k X' z') z) =
      fun X' => ∑ k ∈ s, orderedDerivative β (g k X') z := by
    funext X'
    exact congrFun (MixedTail.orderedDerivative_sum s β (fun k hk => (hg k hk).1 X')) z
  rw [h1]
  exact congrFun (MixedTail.orderedDerivative_sum s w (fun k hk => (hg k hk).2)) X

end Sums

section Lift

variable {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, NormedSpace ℝ (H i)]

/-- Vector form of the Leibniz bound for one component of a lift action: the cell `L²` norm of a
slow word derivative of a fast word derivative of `liftApply n c (fun _ => b) t X z v` is bounded
by the sum over `m`, `α`, `u` and the labellings `s` of the word of the `L²` norms of the
corresponding coefficient derivative applied to the fixed vector `∂^{w|sᶜ} ∂^α b (X) u`. -/
theorem eLpNorm_liftApply_word_le {p q n : ℕ} {sX sZ : ℕ} (hp : p ≤ sX) (hq : q ≤ sZ)
    (c : LiftCoeff ι H) (b : Vec 2 → ∀ i, H i) (t : ℝ) (v : ι)
    (hc : ∀ m α u, IsBoxSmooth sX sZ (fun X z => c m α t X z v u))
    (hb : ContDiff ℝ ((p + n : ℕ) : ℕ∞) b) (w : DerivativeWord2 p) (β : DerivativeWord2 q)
    (X : Vec 2) :
    eLpNorm (fun z => orderedDerivative w (fun X' => orderedDerivative β
        (fun z' => liftApply n c (fun _ => b) t X' z' v) z) X) 2
      (volume.restrict AVenhance.unitCube) ≤
    ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m, ∑ u : ι, ∑ s : Fin p → Bool,
      eLpNorm (fun z =>
        derivList (splitWord p w s).1
          (fun X' => orderedDerivative β (fun z' => c m α t X' z' v u) z) X
          (derivList (splitWord p w s).2 (fun X' => orderedDerivative α b X' u) X)) 2
        (volume.restrict AVenhance.unitCube) := by
  have hξ : ∀ m ∈ Finset.range (n + 1), ∀ (α : DerivativeWord2 m) (u : ι),
      ContDiff ℝ (p : ℕ∞) (fun X' => orderedDerivative α b X' u) := fun m hm α u =>
    contDiff_orderedDerivative_comp (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)) α hb u
  have hgood : ∀ m ∈ Finset.range (n + 1), ∀ (α : DerivativeWord2 m) (u : ι) (z : Vec 2),
      GoodWW p q β z (fun X' z' => c m α t X' z' v u (orderedDerivative α b X' u)) := by
    intro m hm α u z
    have hz : ∀ X', ContDiff ℝ (q : ℕ∞) (fun z' => c m α t X' z' v u (orderedDerivative α b X' u)) :=
      fun X' => (((hc m α u).1 X').of_le (by exact_mod_cast hq)).clm_apply contDiff_const
    refine ⟨hz, ?_⟩
    have e : (fun X' => orderedDerivative β
        (fun z' => c m α t X' z' v u (orderedDerivative α b X' u)) z) =
        fun X' => orderedDerivative β (fun z' => c m α t X' z' v u) z
          (orderedDerivative α b X' u) := by
      funext X'
      exact congrFun (orderedDerivative_clm_comp
        (ContinuousLinearMap.apply ℝ (H v) (orderedDerivative α b X' u)) β
        (((hc m α u).1 X').of_le (by exact_mod_cast hq))) z
    rw [e]
    have hf : ContDiff ℝ (p : ℕ∞) (fun X' => orderedDerivative β (fun z' => c m α t X' z' v u) z) := by
      have : (fun X' => orderedDerivative β (fun z' => c m α t X' z' v u) z) = fun X' =>
          ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) (H u →L[ℝ] H v)
            (fun j => basisVec (β (Fin.rev j))) (iteratedFDeriv ℝ q (c m α t X' · v u) z) := by
        funext X'
        rw [orderedDerivative_eq_iteratedFDeriv β
          (((hc m α u).1 X').of_le (by exact_mod_cast hq))]
        rfl
      rw [this]
      have hcz : ContDiff ℝ (p : ℕ∞) (fun X' => iteratedFDeriv ℝ q (c m α t X' · v u) z) :=
        ((hc m α u).2.1 q hq z).of_le (by exact_mod_cast hp)
      exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) (H u →L[ℝ] H v)
        (fun j => basisVec (β (Fin.rev j)))).contDiff.comp hcz
    exact hf.clm_apply (hξ m hm α u)
  have e : (fun z => orderedDerivative w (fun X' => orderedDerivative β
        (fun z' => liftApply n c (fun _ => b) t X' z' v) z) X) =
      ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m, ∑ u : ι, ∑ s : Fin p → Bool,
        fun z => derivList (splitWord p w s).1
          (fun X' => orderedDerivative β (fun z' => c m α t X' z' v u) z) X
          (derivList (splitWord p w s).2 (fun X' => orderedDerivative α b X' u) X) := by
    funext z
    have hsum : ∀ m ∈ Finset.range (n + 1), GoodWW p q β z (fun X' z' => ∑ α : DerivativeWord2 m,
        ∑ u : ι, c m α t X' z' v u (orderedDerivative α b X' u)) := fun m hm =>
      GoodWW.sum _ fun α _ => GoodWW.sum _ fun u _ => hgood m hm α u z
    have hall : GoodWW p q β z (fun X' z' => ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m,
        ∑ u : ι, c m α t X' z' v u (orderedDerivative α b X' u)) := GoodWW.sum _ hsum
    show orderedDerivative w (fun X' => orderedDerivative β (fun z' => ∑ m ∈ Finset.range (n + 1),
      ∑ α : DerivativeWord2 m, ∑ u : ι, c m α t X' z' v u (orderedDerivative α b X' u)) z) X = _
    rw [orderedDerivative_orderedDerivative_sum _ hsum w X, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [orderedDerivative_orderedDerivative_sum _ (fun α _ => GoodWW.sum _
      fun u _ => hgood m hm α u z) w X, Finset.sum_apply]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [orderedDerivative_orderedDerivative_sum _ (fun u _ => hgood m hm α u z) w X,
      Finset.sum_apply]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hcm : IsBoxSmooth sX sZ (fun X z => c m α t X z v u) := hc m α u
    rw [orderedDerivative_orderedDerivative_clm_apply_eq hcm hp hq (hξ m hm α u) w β X z]
    simp [Finset.sum_apply]
  rw [e]
  refine (eLpNorm_sum_le (by norm_num)).trans (Finset.sum_le_sum fun m _ => ?_)
  refine (eLpNorm_sum_le (by norm_num)).trans (Finset.sum_le_sum fun α _ => ?_)
  refine (eLpNorm_sum_le (by norm_num)).trans (Finset.sum_le_sum fun u _ => ?_)
  exact eLpNorm_sum_le (by norm_num)

end Lift

end AVRegularity.QuietDecay
