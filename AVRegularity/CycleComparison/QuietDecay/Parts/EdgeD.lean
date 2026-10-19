-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.QuietDecay.Lift.QuietMeanFrom
public import AVRegularity.CycleComparison.QuietDecay.Jet.Cell
public import AVRegularity.CycleComparison.QuietDecay.Meas.Words
import AVRegularity.CycleComparison.Residual.Jets.Lift
public import AVRegularity.CycleComparison.QuietDecay.Source.BoundBox
public import AVRegularity.CycleComparison.QuietDecay.Test.MonoLift

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! Calculus for the edge parts of the quiet source: slow and fast word derivatives commute for
box smooth fields, so the vector jets `vecJ` are bounded by the pointwise mixed jets `ptJet`; box
smoothness of `Pi`-valued fields from their components, of slow-only fields, and of the components
of a lift action. -/

section
section Comm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem edge_fastIter_slowPartial : ∀ (m : List (Fin 2)) {sX sZ : ℕ} (F : Vec 2 → Vec 2 → E),
    IsBoxSmooth (sX + 1) (sZ + m.length) F → ∀ j : Fin 2,
      fastIter m (slowPartial j F) = slowPartial j (fastIter m F) := by
  intro m
  induction m with
  | nil => intro sX sZ F _ j; rfl
  | cons a m ih =>
    intro sX sZ F hF j
    have hF1 : IsBoxSmooth (sX + 1) ((sZ + m.length) + 1) F := hF
    show fastIter m (fastPartial a (slowPartial j F)) =
      slowPartial j (fastIter m (fastPartial a F))
    have e : fastPartial a (slowPartial j F) = slowPartial j (fastPartial a F) :=
      funext fun X => funext fun z => IsBoxSmooth.fastPartial_slowPartial
        (hF1.mono le_rfl le_rfl : IsBoxSmooth (sX + 1) ((sZ + m.length) + 1) F) a j X z
    rw [e]
    exact ih (fastPartial a F) (hF1.fastPartial a) j

theorem edge_fastIter_slowIter : ∀ (l : List (Fin 2)) {sX sZ : ℕ} (m : List (Fin 2))
    (F : Vec 2 → Vec 2 → E), IsBoxSmooth (sX + l.length) (sZ + m.length) F →
      fastIter m (slowIter l F) = slowIter l (fastIter m F) := by
  intro l
  induction l with
  | nil => intro sX sZ m F _; rfl
  | cons j l ih =>
    intro sX sZ m F hF
    have hF1 : IsBoxSmooth ((sX + l.length) + 1) (sZ + m.length) F := hF
    show fastIter m (slowIter l (slowPartial j F)) = slowIter l (slowPartial j (fastIter m F))
    rw [ih m (slowPartial j F) (hF1.slowPartial j),
      edge_fastIter_slowPartial m F (sX := sX + l.length) hF1 j]

/-- Fast word derivative of a slow word derivative equals the slow word derivative of the fast word
derivative, for box smooth fields. -/
theorem edge_orderedDerivative_comm {sX sZ : ℕ} {F : Vec 2 → Vec 2 → E} (hF : IsBoxSmooth sX sZ F)
    (l m : List (Fin 2)) (hl : l.length ≤ sX) (hm : m.length ≤ sZ) (X z : Vec 2) :
    fastDerivs m (slowDerivs l F X) z =
      orderedDerivative (m := l.length) l.get
        (fun X' => orderedDerivative (m := m.length) m.get (F X') z) X := by
  have hF' : IsBoxSmooth ((sX - l.length) + l.length) ((sZ - m.length) + m.length) F := by
    rwa [Nat.sub_add_cancel hl, Nat.sub_add_cancel hm]
  have key := edge_fastIter_slowIter l (sX := sX - l.length) (sZ := sZ - m.length) m F hF'
  have e1 : (fun X' => orderedDerivative (m := m.length) m.get (F X') z) =
      fun X' => fastIter m F X' z := funext fun X' => by
    rw [orderedDerivative_eq_wordList, List.ofFn_get, wordList_fastIter]
  rw [e1, orderedDerivative_eq_wordList, List.ofFn_get, wordList_slowIter, ← key]
  exact (wordList_fastIter m (slowIter l F) X z)

/-- The vector jet is bounded by the pointwise mixed jet. -/
theorem edge_vecJ_le_ptJet {sX sZ : ℕ} {F : Vec 2 → Vec 2 → E} (hF : IsBoxSmooth sX sZ F)
    (l m : List (Fin 2)) (hl : l.length ≤ sX) (hm : m.length ≤ sZ) (X : Vec 2) :
    vecJ F X l m ≤ ptJet F X l.length m.length := by
  unfold vecJ
  have e : (fun z => fastDerivs m (slowDerivs l F X) z) = fun z => orderedDerivative
      (m := l.length) l.get (fun X' => orderedDerivative (m := m.length) m.get (F X') z) X :=
    funext (edge_orderedDerivative_comm hF l m hl hm X)
  rw [e]
  exact eLpNorm_orderedDerivative_le_ptJet hF hl hm l.get m.get X

end Comm

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem edge_isBoxSmooth_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {sX sZ : ℕ}
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : ∀ i, IsBoxSmooth sX sZ (fun X z => Φ X z i)) :
    IsBoxSmooth sX sZ Φ := by
  have e : Φ = fun X z => ∑ i, ContinuousLinearMap.single ℝ h i (Φ X z i) := by
    funext X z
    simp only [ContinuousLinearMap.single_apply]
    exact (Finset.univ_sum_single (Φ X z)).symm
  rw [e]
  exact IsBoxSmooth.sum _ fun i _ => (hΦ i).map_clm (ContinuousLinearMap.single ℝ h i)

theorem edge_isBoxSmooth_slowOnly {sX sZ : ℕ} {g : Vec 2 → E} (hg : ContDiff ℝ (sX : ℕ∞) g) :
    IsBoxSmooth sX sZ (fun X _ => g X) := by
  refine ⟨fun X => contDiff_const, fun b hb z => ?_, fun a b ha hb => ?_⟩
  · rcases Nat.eq_zero_or_pos b with rfl | hb0
    · have : (fun X => iteratedFDeriv ℝ 0 (fun _ : Vec 2 => g X) z) =
          fun X => (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm (g X) := by
        funext X; rw [iteratedFDeriv_zero_eq_comp]; rfl
      rw [this]
      exact (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm.contDiff.comp hg
    · have : (fun X => iteratedFDeriv ℝ b (fun _ : Vec 2 => g X) z) = fun _ => 0 := by
        funext X; rw [iteratedFDeriv_const_of_ne hb0.ne']; rfl
      rw [this]; exact contDiff_const
  · rcases Nat.eq_zero_or_pos b with rfl | hb0
    · have : (fun p : Vec 2 × Vec 2 =>
          iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ 0 (fun _ : Vec 2 => g X') p.2) p.1) =
          fun p => iteratedFDeriv ℝ a (fun X' => (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm
            (g X')) p.1 := by
        funext p
        congr 1
      rw [this]
      have h2 : ContDiff ℝ (a : ℕ∞) (fun X' => (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm
          (g X')) :=
        ((continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm.contDiff.comp
          (hg.of_le (by exact_mod_cast ha)))
      exact (h2.continuous_iteratedFDeriv (by exact_mod_cast le_rfl)).comp continuous_fst
    · have : (fun p : Vec 2 × Vec 2 =>
          iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b (fun _ : Vec 2 => g X') p.2) p.1) =
          fun _ => 0 := by
        funext p
        have : (fun X' => iteratedFDeriv ℝ b (fun _ : Vec 2 => g X') p.2) = fun _ => 0 := by
          funext X'; rw [iteratedFDeriv_const_of_ne hb0.ne']; rfl
        rw [this, iteratedFDeriv_fun_zero]; rfl
      rw [this]; exact continuous_const

theorem edge_isBoxSmooth_list_sum {κ : Type*} (l : List κ) {sX sZ : ℕ}
    {f : κ → Vec 2 → Vec 2 → E} (h : ∀ i ∈ l, IsBoxSmooth sX sZ (f i)) :
    IsBoxSmooth sX sZ (fun X z => (l.map fun i => f i X z).sum) := by
  induction l with
  | nil => simpa using (IsBoxSmooth.zero (sX := sX) (sZ := sZ) (E := E))
  | cons a l ih =>
    have := (h a List.mem_cons_self).add (ih fun i hi => h i (List.mem_cons_of_mem _ hi))
    simpa using this

end Smooth

section Lift

variable {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, NormedSpace ℝ (H i)]

/-- Box smoothness of one component of a lift action. -/
theorem edge_isBoxSmooth_liftApply {sX sZ : ℕ} (c : LiftCoeff ι H) (N : ℕ) (B : Vec 2 → ∀ i, H i)
    (t : ℝ) (v : ι) (hc : ∀ m α u, IsBoxSmooth sX sZ (fun X z => c m α t X z v u))
    (hB : ContDiff ℝ ((sX + N : ℕ) : ℕ∞) B) :
    IsBoxSmooth sX sZ (fun X z => liftApply N c (fun _ => B) t X z v) := by
  have hξ : ∀ m ∈ Finset.range (N + 1), ∀ (α : DerivativeWord2 m) (u : ι),
      ContDiff ℝ (sX : ℕ∞) (fun X' => orderedDerivative α B X' u) := fun m hm α u =>
    contDiff_orderedDerivative_comp (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)) α hB u
  have hterm : ∀ m ∈ Finset.range (N + 1), ∀ (α : DerivativeWord2 m) (u : ι),
      IsBoxSmooth sX sZ (fun X z => c m α t X z v u (orderedDerivative α B X u)) :=
    fun m hm α u => (hc m α u).apply_slow (hξ m hm α u)
  show IsBoxSmooth sX sZ (fun X z => ∑ m ∈ Finset.range (N + 1), ∑ α : DerivativeWord2 m, ∑ u : ι,
    c m α t X z v u (orderedDerivative α B X u))
  exact IsBoxSmooth.sum _ fun m hm => IsBoxSmooth.sum _ fun α _ =>
    IsBoxSmooth.sum _ fun u _ => hterm m hm α u

end Lift
end

/-! Auxiliary calculus for the metric parts `ℬ₁`, `ℬ₂` of the quiet source: word derivatives as
lists, commutation of the fast and slow word derivatives of a box smooth field (so the cell jets
`vecJ` are word derivatives of the `orderedDerivative` form), continuous linear maps through
`cellB1`/`cellB2`, box smoothness of their outputs, and the pointwise jets of fast independent
fields. -/

section
section Deriv

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem metric_derivList_eq_orderedDerivative (l : List (Fin 2)) (g : Vec 2 → V) :
    derivList l g = orderedDerivative (m := l.length) l.get g := by
  rw [orderedDerivative_eq_derivList, List.ofFn_get]

theorem metric_derivList_zero (l : List (Fin 2)) :
    derivList l (fun _ : Vec 2 => (0 : V)) = fun _ => 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    show derivList l (fun x => fderiv ℝ (fun _ : Vec 2 => (0 : V)) x (basisVec i)) = _
    simp only [fderiv_fun_const, Pi.zero_apply, zero_apply]
    exact ih

theorem metric_derivList_append (l₁ l₂ : List (Fin 2)) (g : Vec 2 → V) :
    derivList l₂ (derivList l₁ g) = derivList (l₁ ++ l₂) g := by
  simp [derivList, List.foldl_append]

theorem metric_derivList_clm {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W)
    (l : List (Fin 2)) {g : Vec 2 → V} (hg : ContDiff ℝ (l.length : ℕ∞) g) :
    derivList l (fun x => L (g x)) = fun x => L (derivList l g x) := by
  rw [metric_derivList_eq_orderedDerivative, metric_derivList_eq_orderedDerivative]
  exact orderedDerivative_clm_comp L _ hg

end Deriv

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem metric_slowDerivs_eq_slowL (l : List (Fin 2)) :
    ∀ (Ψ : Vec 2 → Vec 2 → E), slowDerivs l Ψ = FastJets.slowL l Ψ := by
  induction l with
  | nil => intro Ψ; rfl
  | cons i l ih => intro Ψ; rw [slowDerivs_cons, ih, FastJets.slowL_cons]

/-- Fast word of the slow word, as lists, equals slow word of fast word. -/
theorem metric_fastDerivs_slowDerivs_eq {Ψ : Vec 2 → Vec 2 → E} (l m : List (Fin 2))
    (hΨ : IsBoxSmooth l.length m.length Ψ) (X z : Vec 2) :
    fastDerivs m (slowDerivs l Ψ X) z = derivList l (fun X' => derivList m (Ψ X') z) X := by
  have h := MixedTail.fastL_slowL_comm l m hΨ
  have h2 := congrFun (congrFun h X) z
  rw [metric_slowDerivs_eq_slowL]
  exact h2

theorem metric_vecJ_eq {Ψ : Vec 2 → Vec 2 → E} (l m : List (Fin 2))
    (hΨ : IsBoxSmooth l.length m.length Ψ) (X : Vec 2) :
    vecJ Ψ X l m = eLpNorm (fun z => derivList l (fun X' => derivList m (Ψ X') z) X) 2
      (volume.restrict AVenhance.unitCube) := by
  unfold vecJ
  congr 1
  funext z
  exact metric_fastDerivs_slowDerivs_eq l m hΨ X z

theorem metric_vecJ_le_ptJet {Ψ : Vec 2 → Vec 2 → E} (l m : List (Fin 2))
    (hΨ : IsBoxSmooth l.length m.length Ψ) (X : Vec 2) :
    vecJ Ψ X l m ≤ ptJet Ψ X l.length m.length := by
  rw [metric_vecJ_eq l m hΨ]
  have := eLpNorm_orderedDerivative_le_ptJet hΨ le_rfl le_rfl l.get m.get X
  simpa [metric_derivList_eq_orderedDerivative] using this

end Bridge


section CellClm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem metric_slowPartial_clm (L : E →L[ℝ] F) {G : Vec 2 → Vec 2 → E} (i : Fin 2) (X z : Vec 2)
    (hG : DifferentiableAt ℝ (fun X' => G X' z) X) :
    slowPartial i (fun X' z' => L (G X' z')) X z = L (slowPartial i G X z) := by
  have := L.hasFDerivAt.comp X hG.hasFDerivAt
  simp only [slowPartial]
  have h2 : (fun X' => L (G X' z)) = L ∘ (fun X' => G X' z) := rfl
  rw [h2, this.fderiv]
  rfl

theorem metric_fastPartial_clm (L : E →L[ℝ] F) {G : Vec 2 → Vec 2 → E} (i : Fin 2) (X z : Vec 2)
    (hG : DifferentiableAt ℝ (G X) z) :
    fastPartial i (fun X' z' => L (G X' z')) X z = L (fastPartial i G X z) := by
  have := L.hasFDerivAt.comp z hG.hasFDerivAt
  simp only [fastPartial]
  have h2 : (fun z' => L (G X z')) = L ∘ G X := rfl
  rw [h2, this.fderiv]
  rfl

theorem metric_cellB2_clm (L : E →L[ℝ] F) {η : ℝ} {G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ} {t : ℝ}
    {Φ : Vec 2 → Vec 2 → E} (hΦ : ∀ z, ContDiff ℝ 2 (fun X => Φ X z))
    (hG : ∀ i j, Differentiable ℝ (fun X => G t X i j)) :
    cellB2 η G t (fun X z => L (Φ X z)) = fun X z => L (cellB2 η G t Φ X z) := by
  have hd1 : ∀ z, Differentiable ℝ (fun X => Φ X z) := fun z => (hΦ z).differentiable (by norm_num)
  have hd2 : ∀ j z, Differentiable ℝ (fun X => slowPartial j Φ X z) := by
    intro j z
    have : (fun X => slowPartial j Φ X z) = fun X => ContinuousLinearMap.apply ℝ E (basisVec j)
        (fderiv ℝ (fun X' => Φ X' z) X) := rfl
    rw [this]
    exact (ContinuousLinearMap.apply ℝ E (basisVec j)).differentiable.comp
      (((hΦ z).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))
  have h1 : ∀ j, slowPartial j (fun X z => L (Φ X z)) = fun X z => L (slowPartial j Φ X z) := by
    intro j; funext X z
    exact metric_slowPartial_clm L j X z ((hd1 z) X)
  funext X z
  simp only [cellB2, h1]
  have h2 : ∀ i j, slowPartial i (fun X' z' => G t X' i j • L (slowPartial j Φ X' z')) X z =
      L (slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z') X z) := by
    intro i j
    simp only [← map_smul]
    exact metric_slowPartial_clm L i X z (G := fun X' z' => G t X' i j • slowPartial j Φ X' z')
      (((hG i j) X).smul (hd2 j z X))
  simp only [h2, map_neg, map_smul, map_sum]

theorem metric_cellB1_clm (L : E →L[ℝ] F) {η : ℝ} {G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ}
    {v : ℝ → Vec 2 → Vec 2} {t : ℝ} {Φ : Vec 2 → Vec 2 → E} (hΦ : IsBoxSmooth 1 1 Φ)
    (hG : ∀ i j, Differentiable ℝ (fun X => G t X i j)) :
    cellB1 η G v t (fun X z => L (Φ X z)) = fun X z => L (cellB1 η G v t Φ X z) := by
  have hdX : ∀ z, Differentiable ℝ (fun X => Φ X z) := fun z =>
    (hΦ.contDiff_slow z).differentiable (by norm_num)
  have hdZ : ∀ X, Differentiable ℝ (Φ X) := fun X => (hΦ.1 X).differentiable (by norm_num)
  have hsZ : ∀ j X, Differentiable ℝ (slowPartial j Φ X) := fun j X =>
    ((hΦ.slowPartial j).1 X).differentiable (by norm_num)
  have hfX : ∀ j z, Differentiable ℝ (fun X => fastPartial j Φ X z) := fun j z =>
    ((hΦ.fastPartial j).contDiff_slow z).differentiable (by norm_num)
  have h1 : ∀ j, slowPartial j (fun X z => L (Φ X z)) = fun X z => L (slowPartial j Φ X z) := by
    intro j; funext X z
    exact metric_slowPartial_clm L j X z ((hdX z) X)
  have h2 : ∀ j, fastPartial j (fun X z => L (Φ X z)) = fun X z => L (fastPartial j Φ X z) := by
    intro j; funext X z
    exact metric_fastPartial_clm L j X z ((hdZ X) z)
  funext X z
  simp only [cellB1, h1, h2]
  have h3 : ∀ i j, fastPartial i (fun X' z' => L (slowPartial j Φ X' z')) X z =
      L (fastPartial i (slowPartial j Φ) X z) := fun i j =>
    metric_fastPartial_clm L i X z ((hsZ j X) z)
  have h4 : ∀ i j, slowPartial i (fun X' z' => G t X' i j • L (fastPartial j Φ X' z')) X z =
      L (slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z') X z) := by
    intro i j
    simp only [← map_smul]
    exact metric_slowPartial_clm L i X z (G := fun X' z' => G t X' i j • fastPartial j Φ X' z')
      (((hG i j) X).smul (hfX j z X))
  simp only [h3, h4, map_smul, map_add, map_sum, map_sub]

end CellClm

section CellSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem metric_isBoxSmooth_cellB1 {η : ℝ} {G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ}
    {v : ℝ → Vec 2 → Vec 2} {t : ℝ} {Φ : Vec 2 → Vec 2 → E} {p q : ℕ}
    (hΦ : IsBoxSmooth (p + 1) (q + 1) Φ) (hv : ∀ z, Real.sqrt η • v t z = 0)
    (hG : ∀ i j, ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun X => G t X i j)) :
    IsBoxSmooth p q (cellB1 η G v t Φ) := by
  rw [cellB1_eq_of_drift hv Φ]
  have hbox : ∀ i j : Fin 2, IsBoxSmooth p q (fun X z =>
      G t X i j • fastPartial i (slowPartial j Φ) X z
        + slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z') X z) := by
    intro i j
    have hΦs : IsBoxSmooth p (q + 1) (slowPartial j Φ) := hΦ.slowPartial j
    have hA : IsBoxSmooth p q (fun X z => G t X i j • fastPartial i (slowPartial j Φ) X z) :=
      (hΦs.fastPartial i).smul_slow ((hG i j).of_le (by exact_mod_cast Nat.le_succ p))
    have hΦf : IsBoxSmooth (p + 1) q (fastPartial j Φ) := hΦ.fastPartial j
    have hB : IsBoxSmooth p q (slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z')) :=
      (hΦf.smul_slow (hG i j)).slowPartial i
    exact hA.add hB
  have hrow : ∀ i : Fin 2, IsBoxSmooth p q (fun X z => ∑ j : Fin 2,
      (G t X i j • fastPartial i (slowPartial j Φ) X z
        + slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z') X z)) :=
    fun i => IsBoxSmooth.sum _ fun j _ => hbox i j
  have hS := IsBoxSmooth.sum (Finset.univ : Finset (Fin 2)) fun i _ => hrow i
  exact hS.clm_comp ((-Real.sqrt η) • ContinuousLinearMap.id ℝ E)

theorem metric_isBoxSmooth_cellB2 {η : ℝ} {G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ} {t : ℝ}
    {Φ : Vec 2 → Vec 2 → E} {p q : ℕ} (hΦ : IsBoxSmooth (p + 2) q Φ)
    (hG : ∀ i j, ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun X => G t X i j)) :
    IsBoxSmooth p q (cellB2 η G t Φ) := by
  rw [cellB2_eq]
  have hbox' : ∀ j : Fin 2, IsBoxSmooth (p + 1) q (slowPartial j Φ) := fun j => hΦ.slowPartial j
  have hbox : ∀ i j : Fin 2, IsBoxSmooth p q
      (slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z')) := fun i j =>
    (((hbox' j).smul_slow (hG i j))).slowPartial i
  have hrow : ∀ i : Fin 2, IsBoxSmooth p q (fun X z => ∑ j : Fin 2,
      slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z') X z) :=
    fun i => IsBoxSmooth.sum _ fun j _ => hbox i j
  have hS := IsBoxSmooth.sum (Finset.univ : Finset (Fin 2)) fun i _ => hrow i
  exact hS.clm_comp ((-η) • ContinuousLinearMap.id ℝ E)

end CellSmooth


section SlowOnly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem metric_volume_unitCube : volume (AVenhance.unitCube : Set (Vec 2)) = 1 := by
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp

theorem metric_isBoxSmooth_slowOnly {sX sZ : ℕ} {g : Vec 2 → E} (hg : ContDiff ℝ (sX : ℕ∞) g) :
    IsBoxSmooth sX sZ (fun X _ => g X) := by
  refine ⟨fun X => contDiff_const, fun b hb z => ?_, fun a b ha hb => ?_⟩
  · rcases Nat.eq_zero_or_pos b with rfl | hb0
    · have : (fun X => iteratedFDeriv ℝ 0 (fun _ : Vec 2 => g X) z) =
          fun X => (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm (g X) := by
        funext X; rw [iteratedFDeriv_zero_eq_comp]; rfl
      rw [this]
      exact (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm.contDiff.comp hg
    · have : (fun X => iteratedFDeriv ℝ b (fun _ : Vec 2 => g X) z) = fun _ => 0 := by
        funext X; rw [iteratedFDeriv_const_of_ne hb0.ne']; rfl
      rw [this]; exact contDiff_const
  · rcases Nat.eq_zero_or_pos b with rfl | hb0
    · have : (fun p : Vec 2 × Vec 2 =>
          iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ 0 (fun _ : Vec 2 => g X') p.2) p.1) =
          fun p => iteratedFDeriv ℝ a (fun X' => (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm
            (g X')) p.1 := by
        funext p
        congr 1
      rw [this]
      have h2 : ContDiff ℝ (a : ℕ∞) (fun X' => (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm
          (g X')) :=
        ((continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm.contDiff.comp
          (hg.of_le (by exact_mod_cast ha)))
      exact (h2.continuous_iteratedFDeriv (by exact_mod_cast le_rfl)).comp continuous_fst
    · have : (fun p : Vec 2 × Vec 2 =>
          iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b (fun _ : Vec 2 => g X') p.2) p.1) =
          fun _ => 0 := by
        funext p
        have : (fun X' => iteratedFDeriv ℝ b (fun _ : Vec 2 => g X') p.2) = fun _ => 0 := by
          funext X'; rw [iteratedFDeriv_const_of_ne hb0.ne']; rfl
        rw [this, iteratedFDeriv_fun_zero]; rfl
      rw [this]; exact continuous_const

/-- The pointwise jet of a fast-independent field is the norm of the slow jet. -/
theorem metric_ptJet_slowOnly (g : Vec 2 → E) (X : Vec 2) (r : ℕ) :
    ptJet (fun X _ => g X) X r 0 = ‖iteratedFDeriv ℝ r g X‖ₑ := by
  unfold ptJet
  have e : ∀ z : Vec 2, ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ 0
      (fun _ : Vec 2 => g X') z) X‖ = ‖iteratedFDeriv ℝ r g X‖ := by
    intro z
    have : (fun X' => iteratedFDeriv ℝ 0 (fun _ : Vec 2 => g X') z) =
        (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm ∘ g := by
      funext X'; rw [iteratedFDeriv_zero_eq_comp]; rfl
    rw [this]
    exact (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm.norm_iteratedFDeriv_comp_left g X r
  simp only [e]
  rw [eLpNorm_const _ (by norm_num) (by simp [metric_volume_unitCube])]
  simp [metric_volume_unitCube]

end SlowOnly
end

/-! The vector Leibniz bound for one component of a lift action, in terms of the block jets
`blkJ`: the mixed jet of the component is bounded by the fixed vectors (slow derivatives of the
input field) times the block jets of the coefficients. -/

section
section Smul
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem edge_slowDerivs_smul (r : ℝ) : ∀ (l : List (Fin 2)) (F : Vec 2 → Vec 2 → E),
    slowDerivs l (fun X z => r • F X z) = fun X z => r • slowDerivs l F X z := by
  intro l
  induction l with
  | nil => intro F; rfl
  | cons i l ih =>
    intro F
    rw [slowDerivs_cons, slowDerivs_cons]
    have : slowPartial i (fun X z => r • F X z) = fun X z => r • slowPartial i F X z := by
      funext X z
      unfold slowPartial
      rw [show (fun X' => r • F X' z) = r • (fun X' => F X' z) from rfl, fderiv_const_smul_field]
      rfl
    rw [this]
    exact ih _

theorem edge_fastDerivs_smul (r : ℝ) : ∀ (m : List (Fin 2)) (g : Vec 2 → E),
    fastDerivs m (fun z => r • g z) = fun z => r • fastDerivs m g z := by
  intro m
  induction m with
  | nil => intro g; rfl
  | cons i m ih =>
    intro g
    rw [fastDerivs_cons, fastDerivs_cons]
    have : (fun z => fderiv ℝ (fun z' => r • g z') z (basisVec i)) =
        fun z => r • fderiv ℝ g z (basisVec i) := by
      funext z
      rw [show (fun z' => r • g z') = r • g from rfl, fderiv_const_smul_field]
      rfl
    rw [this]
    exact ih _

theorem edge_vecJ_smul (r : ℝ) (F : Vec 2 → Vec 2 → E) (X : Vec 2) (l m : List (Fin 2)) :
    vecJ (fun X z => r • F X z) X l m = ‖r‖ₑ * vecJ F X l m := by
  unfold vecJ
  rw [edge_slowDerivs_smul, edge_fastDerivs_smul]
  exact eLpNorm_const_smul (μ := volume.restrict AVenhance.unitCube) (p := 2) r
    (fun z => fastDerivs m (slowDerivs l F X) z)

end Smul

section Comm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem edge_comm_lists {sX sZ : ℕ} {F : Vec 2 → Vec 2 → E} (hF : IsBoxSmooth sX sZ F)
    (l m : List (Fin 2)) (hl : l.length ≤ sX) (hm : m.length ≤ sZ) (X z : Vec 2) :
    fastDerivs m (slowDerivs l F X) z = derivList l (fun X' => derivList m (F X') z) X := by
  rw [edge_orderedDerivative_comm hF l m hl hm X z, orderedDerivative_eq_derivList,
    List.ofFn_get]
  congr 1
  funext X'
  rw [orderedDerivative_eq_derivList, List.ofFn_get]

end Comm

section Lift

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

omit [Fintype ι] in
/-- A term of the Leibniz expansion, applied to a fixed vector, as a vector jet. -/
theorem edge_term_eq {sX sZ q : ℕ} {u v : ι} {C : Vec 2 → Vec 2 → (h u →L[ℝ] h v)}
    (hC : IsBoxSmooth sX sZ C) (l1 : List (Fin 2)) (hl : l1.length ≤ sX) (β : DerivativeWord2 q)
    (hq : q ≤ sZ) (ξ : h u) (X z : Vec 2) :
    derivList l1 (fun X' => orderedDerivative β (fun z' => C X' z') z) X ξ =
      fastDerivs (List.ofFn β) (slowDerivs l1 (fun X z => C X z ξ) X) z := by
  set L : (h u →L[ℝ] h v) →L[ℝ] h v := ContinuousLinearMap.apply ℝ (h v) ξ with hL
  have hF : IsBoxSmooth sX sZ (fun X z => C X z ξ) := hC.map_clm L
  have hG : ContDiff ℝ (l1.length : ℕ∞) (fun X' => orderedDerivative β (C X') z) := by
    have : (fun X' => orderedDerivative β (C X') z) = fun X' =>
        ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) (h u →L[ℝ] h v)
          (fun j => basisVec (β (Fin.rev j))) (iteratedFDeriv ℝ q (C X') z) := by
      funext X'
      rw [orderedDerivative_eq_iteratedFDeriv β ((hC.1 X').of_le (by exact_mod_cast hq))]
      rfl
    rw [this]
    have hcz : ContDiff ℝ (l1.length : ℕ∞) (fun X' => iteratedFDeriv ℝ q (C X') z) :=
      (hC.2.1 q hq z).of_le (by exact_mod_cast hl)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) (h u →L[ℝ] h v)
      (fun j => basisVec (β (Fin.rev j)))).contDiff.comp hcz
  have e1 : (fun X' => orderedDerivative β (fun z' => C X' z' ξ) z) =
      fun X' => L (orderedDerivative β (C X') z) := funext fun X' =>
    congrFun (orderedDerivative_clm_comp L β ((hC.1 X').of_le (by exact_mod_cast hq))) z
  rw [edge_comm_lists hF l1 (List.ofFn β) hl (by simpa using hq) X z]
  have e2 : (fun X' => derivList (List.ofFn β) (fun z' => C X' z' ξ) z) =
      fun X' => L (orderedDerivative β (C X') z) := e1
  rw [e2]
  have := congrFun (fastDerivs_clm L l1 hG) X
  exact this.symm

omit [Fintype ι] in
/-- The scaling step: the vector jet of a coefficient block applied to any vector. -/
theorem edge_vecJ_apply_le (Cc : ℕ → ℕ → LiftCoeff ι h) (pp N : ℕ) (σ : ℝ) (v u : ι) (S F : ℕ)
    {m : ℕ} (hm : m ≤ N) (α : DerivativeWord2 m) (l mm : List (Fin 2)) (hl : l.length ≤ S)
    (hmm : mm.length ≤ F) (X : Vec 2) (ξ : h u) :
    vecJ (fun X z => Cc pp N m α σ X z v u ξ) X l mm ≤ ‖ξ‖ₑ * blkJ Cc pp N σ v u S F := by
  obtain ⟨η, hη, hξ⟩ : ∃ η : h u, ‖η‖ ≤ 1 ∧ ξ = ‖ξ‖ • η := by
    by_cases h0 : ξ = 0
    · exact ⟨0, by simp, by simp [h0]⟩
    · refine ⟨‖ξ‖⁻¹ • ξ, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
      · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_smul]
  have e : (fun X z => Cc pp N m α σ X z v u ξ) =
      fun X z => ‖ξ‖ • Cc pp N m α σ X z v u η := by
    funext X z
    conv_lhs => rw [hξ]
    rw [map_smul]
  rw [e, edge_vecJ_smul]
  exact mul_le_mul' (enorm_norm ξ).le (vecJ_le_blkJ Cc pp N σ v u S F hm α l mm hl hmm X η hη)

omit [Fintype ι] in
theorem edge_blkJ_mono (Cc : ℕ → ℕ → LiftCoeff ι h) (pp N : ℕ) (σ : ℝ) (v u : ι) {S S' F F' : ℕ}
    (hS : S ≤ S') (hF : F ≤ F') :
    blkJ Cc pp N σ v u S F ≤ blkJ Cc pp N σ v u S' F' := by
  unfold blkJ
  refine iSup_le fun m => iSup_le fun α => iSup_le fun l => iSup_le fun mm => iSup_le fun X =>
    iSup_le fun η => ?_
  exact vecJ_le_blkJ Cc pp N σ v u S' F' (Nat.lt_succ_iff.1 m.2) α l.1 mm.1 (l.2.trans hS)
    (mm.2.trans hF) X η.1 η.2

/-- **The vector Leibniz bound of a lift action in terms of block jets.** If the slow derivatives
of the input field `B` at `X` of total order at most `a + N` have norms at most `M u` in the
component `u`, then the pointwise mixed jet of orders `(a, b')` of the `v` component of the lift
action `liftApply N (Cc pp N) (fun _ => B) σ` is at most
`2 ^ (a + b') * ((N + 1) * 2 ^ N * 2 ^ a * ∑_u M u * blkJ Cc pp N σ v u a b')`. -/
theorem edge_ptJet_liftApply_le (Cc : ℕ → ℕ → LiftCoeff ι h) (pp N : ℕ) (σ : ℝ) (v : ι)
    {a b' sX sZ : ℕ} (ha : a ≤ sX) (hb' : b' ≤ sZ)
    (hc : ∀ m α u, IsBoxSmooth sX sZ (fun X z => Cc pp N m α σ X z v u)) (B : Vec 2 → ∀ i, h i)
    (hB : ContDiff ℝ ((a + N : ℕ) : ℕ∞) B) (X : Vec 2) (M : ι → ℝ≥0∞)
    (hM : ∀ m' ≤ N, ∀ α : DerivativeWord2 m', ∀ u, ∀ l2 : List (Fin 2), l2.length + m' ≤ a + N →
      ‖derivList l2 (fun X' => orderedDerivative α B X' u) X‖ₑ ≤ M u) :
    ptJet (fun X z => liftApply N (Cc pp N) (fun _ => B) σ X z v) X a b' ≤
      2 ^ (a + b') * (((N + 1 : ℕ) : ℝ≥0∞) * 2 ^ N * 2 ^ a *
        ∑ u : ι, M u * blkJ Cc pp N σ v u a b') := by
  set K : ι → ℝ≥0∞ := fun u => M u * blkJ Cc pp N σ v u a b' with hK
  have hc' : ∀ m α u, IsBoxSmooth a b' (fun X z => Cc pp N m α σ X z v u) := fun m α u =>
    (hc m α u).mono ha hb'
  have hΨ : IsBoxSmooth a b' (fun X z => liftApply N (Cc pp N) (fun _ => B) σ X z v) :=
    edge_isBoxSmooth_liftApply (Cc pp N) N B σ v hc' hB
  refine (ptJet_le_of_words_le hΨ le_rfl le_rfl X (S := ((N + 1 : ℕ) : ℝ≥0∞) * 2 ^ N * 2 ^ a *
    ∑ u : ι, K u) fun w β => ?_).trans (le_of_eq rfl)
  refine (eLpNorm_liftApply_word_le le_rfl le_rfl (Cc pp N) B σ v (fun m α u => hc' m α u) hB w
    β X).trans ?_
  -- bound every term
  have hterm : ∀ m ∈ Finset.range (N + 1), ∀ (α : DerivativeWord2 m) (u : ι) (s : Fin a → Bool),
      eLpNorm (fun z => derivList (splitWord a w s).1
          (fun X' => orderedDerivative β (fun z' => Cc pp N m α σ X' z' v u) z) X
          (derivList (splitWord a w s).2 (fun X' => orderedDerivative α B X' u) X)) 2
        (volume.restrict AVenhance.unitCube) ≤ K u := by
    intro m hm α u s
    have hmN : m ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    have hlen := splitWord_length a w s
    have hl1 : (splitWord a w s).1.length ≤ a := by omega
    have e : (fun z => derivList (splitWord a w s).1
          (fun X' => orderedDerivative β (fun z' => Cc pp N m α σ X' z' v u) z) X
          (derivList (splitWord a w s).2 (fun X' => orderedDerivative α B X' u) X)) =
        fun z => fastDerivs (List.ofFn β) (slowDerivs (splitWord a w s).1
          (fun Y z' => Cc pp N m α σ Y z' v u
            (derivList (splitWord a w s).2 (fun X' => orderedDerivative α B X' u) X)) X) z :=
      funext fun z => edge_term_eq (hc' m α u) _ (hl1.trans le_rfl) β le_rfl
        (derivList (splitWord a w s).2 (fun X' => orderedDerivative α B X' u) X) X z
    rw [e]
    show vecJ (fun Y z' => Cc pp N m α σ Y z' v u
      (derivList (splitWord a w s).2 (fun X' => orderedDerivative α B X' u) X)) X
        (splitWord a w s).1 (List.ofFn β) ≤ K u
    have h1 := edge_vecJ_apply_le Cc pp N σ v u a b' hmN α (splitWord a w s).1 (List.ofFn β) hl1
      (by simp) X (derivList (splitWord a w s).2 (fun X' => orderedDerivative α B X' u) X)
    refine h1.trans ?_
    exact mul_le_mul' (hM m hmN α u _ (by omega)) le_rfl
  refine (Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun u _ =>
    Finset.sum_le_sum fun s _ => hterm m hm α u s).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  refine (Finset.sum_le_sum fun m hm => mul_le_mul'
    (pow_right_mono₀ (by norm_num) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm))) le_rfl).trans
    (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  push_cast
  ring

end Lift
end

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal NNReal ContDiff
namespace AVRegularity.QuietDecay

/-! Box smoothness of the explicit source coefficient, the pointwise edge envelope `edgeEnv`, the
factorisation of the source majorant `srcBoundE` through it, and the fixed vectors produced by the
centred monomial test field. -/

section
section Smooth
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem edge_isBoxSmooth_srcTerm {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (η : ℝ) {k : Fin 2} {a : Vec 2 → ℝ} {p q : ℕ}
    (ha : ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) a) (L : E₁ →L[ℝ] E₂) {W : ℕ → Vec 2 → Vec 2 → E₁}
    (hW : ∀ i, IsBoxSmooth (p + 1) (q + 1) (W i)) (J : ℕ) :
    IsBoxSmooth p q (srcTerm η k a L W J) := by
  have hap : ContDiff ℝ (p : ℕ∞) a := ha.of_le (by exact_mod_cast Nat.le_succ p)
  have bf : ∀ i, IsBoxSmooth p q (fun X z => L (fastPartial k (W i) X z)) := fun i =>
    (isBoxSmooth_fast_piece_box hW L k i).mono (by omega) (by omega)
  have bp : ∀ i, IsBoxSmooth p q (fun X z => L (W i X z)) := fun i =>
    (isBoxSmooth_plain_piece_box hW L i).mono (by omega) (by omega)
  have bs : ∀ i, IsBoxSmooth p q (fun X z => L (slowPartial k (W i) X z)) := fun i =>
    (isBoxSmooth_slow_piece_box hW L k i).mono (by omega) (by omega)
  cases J with
  | zero => exact (bf 0).smul_slow hap
  | succ J =>
    exact ((bf (J + 1)).smul_slow hap).add
      ((((bp J).smul_slow (contDiff_slowDir ha k)).add ((bs J).smul_slow hap)).const_smul _)

theorem edge_isBoxSmooth_NS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (edge : ConstituentEdges D h) (v : ι) {sX sZ : ℕ}
    {T : ∀ (u : ι) (d : Finset.Icc 2 D), Constituent d.1 (h u) (h v) →
      DerivativeWord2 (d.1 - 1) → Vec 2 → Vec 2 → E}
    (hT : ∀ u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth sX sZ (T u d γ α)) :
    IsBoxSmooth sX sZ (NS edge v T) := by
  have : NS edge v T = fun X z => ∑ u ∈ Finset.univ, ∑ d ∈ Finset.univ,
      ((edge v u d).map fun γ => ∑ α ∈ Finset.univ, T u d γ α X z).sum := rfl
  rw [this]
  exact IsBoxSmooth.sum _ fun u _ => IsBoxSmooth.sum _ fun d _ =>
    edge_isBoxSmooth_list_sum _ fun γ hγ => IsBoxSmooth.sum _ fun α _ => hT u d γ hγ α

/-- The components of the explicit source coefficient are box smooth of orders `(p, q)`. -/
theorem edge_isBoxSmooth_srcCoef (edge : ConstituentEdges D h) (η t : ℝ)
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {sX sZ : ℕ} (hΦ : IsBoxSmooth sX sZ Φ) {p q : ℕ} (j : ℕ)
    (hX : p + D ≤ sX) (hZ : q + D ≤ sZ)
    (ha : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun Y => γ.coeff α t Y 0)) (v : ι) :
    IsBoxSmooth p q (fun X z => srcCoef edge η t Φ j X z v) := by
  have hfield : (fun X z => srcCoef edge η t Φ j X z v) = fun X z => ∑ k ∈ Finset.univ,
      NS edge v (fun u d γ α =>
        srcTerm η k (fun Y => γ.coeff α t Y 0 k) γ.map (srcW η u α Φ) j) X z := rfl
  rw [hfield]
  refine IsBoxSmooth.sum _ fun k _ => edge_isBoxSmooth_NS edge v fun u d γ hγ α => ?_
  have hd := Finset.mem_Icc.mp d.2
  have h1 : IsBoxSmooth sX sZ (fun X z => Φ X z u) :=
    hΦ.map_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) u)
  refine edge_isBoxSmooth_srcTerm η (contDiff_pi.mp (ha v u d γ hγ α) k) γ.map (fun i => ?_) j
  have := isBoxSmooth_seqWord_box η (List.ofFn α) h1 (by simp only [List.length_ofFn]; omega)
    (by simp only [List.length_ofFn]; omega) i
  exact (by simpa [srcW] using this : IsBoxSmooth (sX - min i (d.1 - 1)) (sZ - ((d.1 - 1) - i))
    (srcW η u α Φ i)).mono (by omega) (by omega)

/-- The source coefficient as a `Pi`-valued field is box smooth of orders `(p, q)`. -/
theorem edge_isBoxSmooth_sourceCoeff [DecidableEq ι] (edge : ConstituentEdges D h) (η t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {sX sZ : ℕ} (hΦ : IsBoxSmooth sX sZ Φ) {p q : ℕ} (j : ℕ)
    (hX : p + D ≤ sX) (hZ : q + D ≤ sZ) (hD : D ≤ sX) (hD' : D ≤ sZ)
    (ha : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun Y => γ.coeff α t Y z)) :
    IsBoxSmooth p q (sourceCoeff edge η j t Φ) := by
  have hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z) := fun v u d γ hγ α z =>
    (ha v u d γ hγ α z).of_le (by exact_mod_cast Nat.le_add_left 1 p)
  rw [sourceCoeff_eq_srcCoef_box edge η t hquiet hsm hΦ hD hD' j]
  exact edge_isBoxSmooth_pi fun v =>
    edge_isBoxSmooth_srcCoef edge η t hΦ j hX hZ (fun v u d γ hγ α => ha v u d γ hγ α 0) v

end Smooth

section Env
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The pointwise edge envelope: the edge `w → v`, order-`≤ r` slow jets at `X` of its flux
coefficients, with the norms of the component maps. -/
def edgeEnv (Q : LiftOperatorData ι h D) (σ : ℝ) (X : Vec 2) (v w : ι) (r : ℕ) : ℝ≥0∞ :=
  ∑ d : Finset.Icc 2 D, ((Q.edge v w d).map fun γ => ‖γ.map‖ₑ *
    ∑ α : DerivativeWord2 (d.1 - 1), ∑ i ∈ Finset.range (r + 1),
      ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α σ Y 0) X‖ₑ).sum

omit [Fintype ι] in
theorem edgeEnv_mono (Q : LiftOperatorData ι h D) (σ : ℝ) (X : Vec 2) (v w : ι) {r r' : ℕ}
    (hr : r ≤ r') : edgeEnv Q σ X v w r ≤ edgeEnv Q σ X v w r' := by
  unfold edgeEnv
  refine Finset.sum_le_sum fun d _ => List.sum_le_sum fun γ _ => ?_
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun α _ => ?_)
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))

/-- The source majorant factors through the edge envelope. -/
theorem edge_srcBoundE_eq (Q : LiftOperatorData ι h D) (σ : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i)
    (p q j : ℕ) (X : Vec 2) (v : ι) :
    srcBoundE Q.edge σ Φ p q j X v = ∑ u : ι, edgeEnv Q σ X v u (p + 1) *
      ∑ a ∈ Finset.range (p + j + 1), ∑ b ∈ Finset.range (q + D + 1),
        srcPtJet (fun X z => Φ X z u) X a b := by
  simp only [srcBoundE, edgeEnv, Finset.sum_mul, List.sum_map_mul_right]

end Env

section Fixed
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem edge_contDiff_testField (X : Vec 2) (β : List (Fin 2)) (u : ι) (x : h u) (k : ℕ∞) :
    ContDiff ℝ k (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) :=
  ((contDiff_monoF X (k : WithTop ℕ∞) β).smul contDiff_const)

theorem derivList_append' (l l' : List (Fin 2)) {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (g : Vec 2 → V) : derivList l' (derivList l g) = derivList (l ++ l') g := by
  simp [derivList, List.foldl_append]

omit [DecidableEq ι] in
/-- The fixed vector produced by the centred monomial test field. -/
theorem edge_fixedVec_eq (X : Vec 2) (β : List (Fin 2)) (w : ∀ i, h i) {m' : ℕ}
    (α : DerivativeWord2 m') (l2 : List (Fin 2)) (u : ι) :
    derivList l2 (fun X' => orderedDerivative α (fun Y => monoF X β Y • w) X' u) X =
      derivList (List.ofFn α ++ l2) (monoF X β) X • w u := by
  have h1 : (fun X' => orderedDerivative α (fun Y => monoF X β Y • w) X' u) =
      fun X' => derivList (List.ofFn α) (monoF X β) X' • w u := by
    funext X'
    rw [orderedDerivative_eq_derivList, derivList_smul_const w _ _ (contDiff_monoF X ∞ β)]
    rfl
  rw [h1, derivList_smul_const (w u) l2 _
    (contDiff_derivList_infty _ _ (contDiff_monoF X ∞ β)), derivList_append']

end Fixed
end

/-! **The source term built from the lower lift action (the "D" part of the quiet source).** For the
centred test field `b = monoF X β • Pi.single u x`, the vector mixed jets of
`𝒮_j (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => b) σ)` at the slow point `X` are bounded by
the pointwise edge envelope times the block jets of the lower coefficient blocks, a left product. -/

section
section D
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The mixed jet of one component of the lift action on the test field, by the block jets. -/
theorem edge_D_ptJet_le (Cc : ℕ → ℕ → LiftCoeff ι h) (pp N : ℕ) (σ : ℝ) (X : Vec 2)
    (β : List (Fin 2)) (u : ι) (x : h u) (hx : ‖x‖ ≤ 1) (w : ι) {a b' sX sZ : ℕ} (ha : a ≤ sX)
    (hb' : b' ≤ sZ) (hc : ∀ m α u', IsBoxSmooth sX sZ (fun X z => Cc pp N m α σ X z w u')) :
    ptJet (fun X' z => liftApply N (Cc pp N)
        (fun _ Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) σ X' z w) X a b' ≤
      2 ^ (a + b') * (((N + 1 : ℕ) : ℝ≥0∞) * 2 ^ N * 2 ^ a *
        ((β.length.factorial : ℝ≥0∞) * blkJ Cc pp N σ w u a b')) := by
  have key := edge_ptJet_liftApply_le Cc pp N σ w ha hb' hc
    (fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) (edge_contDiff_testField X β u x _) X
    (fun u' => if u' = u then (β.length.factorial : ℝ≥0∞) else 0) (by
      intro m' _ α u' l2 _
      rw [edge_fixedVec_eq]
      by_cases hu : u' = u
      · subst hu
        simp only [ite_true]
        rw [Pi.single_eq_same]
        have h1 := derivList_monoF_abs_le X X (by simp) (List.ofFn α ++ l2) β
        have h2 : ‖derivList (List.ofFn α ++ l2) (monoF X β) X • x‖ ≤
            (β.length.factorial : ℝ) := by
          rw [norm_smul, Real.norm_eq_abs]
          calc _ ≤ (β.length.factorial : ℝ) * 1 :=
                mul_le_mul h1 hx (norm_nonneg _) (by positivity)
            _ = _ := mul_one _
        have := enorm_le_ofReal_of_norm_le h2
        rwa [ENNReal.ofReal_natCast] at this
      · simp only [hu, ite_false]
        rw [Pi.single_eq_of_ne hu]
        simp)
  have hsum : ∑ u' : ι, (if u' = u then (β.length.factorial : ℝ≥0∞) else 0) *
      blkJ Cc pp N σ w u' a b' = (β.length.factorial : ℝ≥0∞) * blkJ Cc pp N σ w u a b' := by
    rw [Finset.sum_eq_single u]
    · simp
    · intro u' _ hu'
      simp [hu']
    · intro hu; exact absurd (Finset.mem_univ u) hu
  rwa [hsum] at key

/-- The explicit constant of `edge_D_bound`. -/
def edgeCD (D p q n j : ℕ) (β : List (Fin 2)) : ℕ :=
  6 * 2 ^ (p + D) * ((p + j + 1) * (q + D + 1)) * (2 ^ (p + j + (q + D)) *
    ((n - j + 1) * 2 ^ (n - j) * 2 ^ (p + j) * β.length.factorial))

/-- **The `D` part of the quiet source.** `S_D = p + j`, `F_D = q + D`, and the constant is
`edgeCD D p q n j β` (a left product: the edge acts on the lower lift action). -/
theorem edge_D_bound (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (σ : ℝ)
    (hη : Q.η ≤ 1)
    (hquiet : ∀ v w d, ∀ γ ∈ Q.edge v w d, ∀ α X z z', γ.coeff α σ X z = γ.coeff α σ X z')
    {p q n j hh : ℕ} (hjD : j ≤ D)
    (hedge : ∀ v w d, ∀ γ ∈ Q.edge v w d, ∀ α z,
      ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun Y => γ.coeff α σ Y z))
    (hc : ∀ m α w u', IsBoxSmooth (p + D) (q + D)
      (fun X z => Cc (hh - 1) (n - j) m α σ X z w u'))
    (X : Vec 2) (β : List (Fin 2)) (u : ι) (x : h u) (hx : ‖x‖ ≤ 1)
    {l m : List (Fin 2)} (hl : l.length ≤ p) (hm : m.length ≤ q) (v : ι) :
    vecJ (fun X' z => sourceCoeff Q.edge Q.η j σ (liftApply (n - j) (Cc (hh - 1) (n - j))
        (fun _ Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) σ) X' z v) X l m ≤
      ENNReal.ofReal (edgeCD D p q n j β : ℝ) * ∑ w : ι, edgeEnv Q σ X v w (p + 1) *
        blkJ Cc (hh - 1) (n - j) σ w u (p + j) (q + D) := by
  set N := n - j with hN
  set b : Vec 2 → ∀ i, h i := fun Y => monoF X β Y • (Pi.single u x : ∀ i, h i) with hb
  set Φ := liftApply N (Cc (hh - 1) N) (fun _ => b) σ with hΦ
  set p0 := l.length with hp0
  set q0 := m.length with hq0
  have hΦbox : IsBoxSmooth (p + D) (q + D) Φ :=
    edge_isBoxSmooth_pi fun w => edge_isBoxSmooth_liftApply (Cc (hh - 1) N) N b σ w
      (fun m α u' => hc m α w u') (edge_contDiff_testField X β u x _)
  have hedge0 : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α z,
      ContDiff ℝ ((p0 + 1 : ℕ) : ℕ∞) (fun X => γ.coeff α σ X z) := fun v u d γ hγ α z =>
    (hedge v u d γ hγ α z).of_le (by exact_mod_cast (by omega : p0 + 1 ≤ p + 1))
  have hTbox : IsBoxSmooth p0 q0 (fun X' z => sourceCoeff Q.edge Q.η j σ Φ X' z v) :=
    (edge_isBoxSmooth_sourceCoeff Q.edge Q.η σ hquiet hΦbox j (by omega) (by omega) (by omega)
      (by omega) hedge0).map_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
  have h1 := edge_vecJ_le_ptJet hTbox l m le_rfl le_rfl X
  have hsq : Real.sqrt Q.η ≤ 1 := (Real.sqrt_le_sqrt hη).trans_eq Real.sqrt_one
  have h2 := srcPtJet_sourceCoeff_le_box Q.edge Q.η σ hsq hquiet hΦbox p0 q0 j (by omega)
    (by omega) hedge0 X v
  rw [edge_srcBoundE_eq] at h2
  have h12 := h1.trans h2
  set T0 : ℕ := 2 ^ (p + j + (q + D)) * ((N + 1) * 2 ^ N * 2 ^ (p + j) * β.length.factorial)
    with hT0
  have hterm : ∀ w : ι, ∀ a ∈ Finset.range (p0 + j + 1), ∀ b' ∈ Finset.range (q0 + D + 1),
      srcPtJet (fun X z => Φ X z w) X a b' ≤
        (T0 : ℝ≥0∞) * blkJ Cc (hh - 1) N σ w u (p + j) (q + D) := by
    intro w a ha b' hb'
    have ha' := Finset.mem_range.1 ha
    have hb'' := Finset.mem_range.1 hb'
    have e := edge_D_ptJet_le Cc (hh - 1) N σ X β u x hx w (a := a) (b' := b') (sX := p + D)
      (sZ := q + D) (by omega) (by omega) (fun m α u' => hc m α w u')
    have hb1 : blkJ Cc (hh - 1) N σ w u a b' ≤ blkJ Cc (hh - 1) N σ w u (p + j) (q + D) :=
      edge_blkJ_mono _ _ _ _ _ _ (by omega) (by omega)
    have hp1 : (2 : ℝ≥0∞) ^ (a + b') ≤ 2 ^ (p + j + (q + D)) :=
      pow_right_mono₀ one_le_two (by omega)
    have hp2 : (2 : ℝ≥0∞) ^ a ≤ 2 ^ (p + j) := pow_right_mono₀ one_le_two (by omega)
    calc srcPtJet (fun X z => Φ X z w) X a b' = ptJet (fun X' z => liftApply N (Cc (hh - 1) N)
          (fun _ Y => monoF X β Y • (Pi.single u x : ∀ i, h i)) σ X' z w) X a b' := rfl
      _ ≤ _ := e
      _ ≤ 2 ^ (p + j + (q + D)) * (((N + 1 : ℕ) : ℝ≥0∞) * 2 ^ N * 2 ^ (p + j) *
            ((β.length.factorial : ℝ≥0∞) * blkJ Cc (hh - 1) N σ w u (p + j) (q + D))) :=
          mul_le_mul' hp1 (mul_le_mul' (mul_le_mul' le_rfl hp2) (mul_le_mul' le_rfl hb1))
      _ = (T0 : ℝ≥0∞) * blkJ Cc (hh - 1) N σ w u (p + j) (q + D) := by
          simp only [hT0]; push_cast; ring
  have hB : ∀ w : ι, ∑ a ∈ Finset.range (p0 + j + 1), ∑ b' ∈ Finset.range (q0 + D + 1),
      srcPtJet (fun X z => Φ X z w) X a b' ≤
        (((p + j + 1) * (q + D + 1) : ℕ) : ℝ≥0∞) *
          ((T0 : ℝ≥0∞) * blkJ Cc (hh - 1) N σ w u (p + j) (q + D)) := by
    intro w
    calc _ ≤ ∑ a ∈ Finset.range (p0 + j + 1), ∑ b' ∈ Finset.range (q0 + D + 1),
          (T0 : ℝ≥0∞) * blkJ Cc (hh - 1) N σ w u (p + j) (q + D) :=
          Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b' hb' => hterm w a ha b' hb'
      _ = (((p0 + j + 1) * (q0 + D + 1) : ℕ) : ℝ≥0∞) *
          ((T0 : ℝ≥0∞) * blkJ Cc (hh - 1) N σ w u (p + j) (q + D)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
      _ ≤ _ := mul_le_mul' (by exact_mod_cast Nat.mul_le_mul (by omega) (by omega)) le_rfl
  calc _ ≤ _ := h12
    _ ≤ (((6 * 2 ^ (p + D) : ℕ)) : ℝ≥0∞) * ∑ w : ι, edgeEnv Q σ X v w (p + 1) *
          ((((p + j + 1) * (q + D + 1) : ℕ) : ℝ≥0∞) *
            ((T0 : ℝ≥0∞) * blkJ Cc (hh - 1) N σ w u (p + j) (q + D))) :=
        mul_le_mul' (by exact_mod_cast Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right (by norm_num)
          (by omega)))
          (Finset.sum_le_sum fun w _ => mul_le_mul' (edgeEnv_mono Q σ X v w (by omega)) (hB w))
    _ = _ := by
        rw [ENNReal.ofReal_natCast, edgeCD, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        simp only [hT0, hN]; push_cast; ring

end D
end

end AVRegularity.QuietDecay
end
