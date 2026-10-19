-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.SourceLocalCrossCongruence

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

/-! Smooth edge extensions preserve the literal source on every slow open germ. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def SlowOpenEdgeEq (U : Set (Vec 2)) (t : ℝ) (edge edge' : ConstituentEdges D h) : Prop :=
  ∀ v u d, List.Forall₂ (fun γ γ' => γ.map = γ'.map ∧
    ∀ α X, X ∈ U → ∀ z, γ.coeff α t X z = γ'.coeff α t X z) (edge v u d) (edge' v u d)

theorem sourceFlux_slow_open_congr {U : Set (Vec 2)} (hU : IsOpen U)
    {f g : Vec 2 → Vec 2 → ∀ i, h i} (he : SlowOpenFieldEq U f g)
    {edge edge' : ConstituentEdges D h} (η ε t : ℝ)
    (hΓ : SlowOpenEdgeEq U t edge edge') (k : Fin 2) :
    SlowOpenFieldEq U (sourceFlux edge η ε t f k) (sourceFlux edge' η ε t g k) := by
  intro X hX z
  funext v
  unfold sourceFlux
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro d _
  have hterms : ∀ {l l' : List (Constituent d.val (h u) (h v))},
      List.Forall₂ (fun γ γ' => γ.map = γ'.map ∧
        ∀ α X, X ∈ U → ∀ z, γ.coeff α t X z = γ'.coeff α t X z) l l' →
      (l.map (fun γ => ∑ α : DerivativeWord2 (d.val - 1), γ.coeff α t X z k •
        γ.map (dEpsWord η ε α f X z u))).sum =
      (l'.map (fun γ => ∑ α : DerivativeWord2 (d.val - 1), γ.coeff α t X z k •
        γ.map (dEpsWord η ε α g X z u))).sum := by
    intro l l' hh
    induction hh with
    | nil => rfl
    | @cons γ γ' l l' hγ _ ih =>
        simp only [List.map_cons, List.sum_cons]
        apply congrArg₂ (fun a b : h v => a + b) _ ih
        apply Finset.sum_congr rfl
        intro α _
        rw [hγ.1, hγ.2 α X hX z, he.dEpsWord hU η ε α X hX z]
  exact hterms (hΓ v u d)

theorem sourceCoeff_slow_open_congr {U : Set (Vec 2)} (hU : IsOpen U)
    {f g : Vec 2 → Vec 2 → ∀ i, h i} (he : SlowOpenFieldEq U f g)
    {edge edge' : ConstituentEdges D h} (η t : ℝ)
    (hΓ : SlowOpenEdgeEq U t edge edge') (j : ℕ) :
    SlowOpenFieldEq U (sourceCoeff edge η j t f) (sourceCoeff edge' η j t g) := by
  intro X hX z
  have hs : (fun ε => sourceOp edge η ε t f X z) =
      fun ε => sourceOp edge' η ε t g X z := by
    funext ε
    unfold sourceOp
    apply Finset.sum_congr rfl
    intro k _
    exact ((sourceFlux_slow_open_congr hU he η ε t hΓ k).dEps hU η ε k) X hX z
  unfold sourceCoeff
  rw [hs]
end

/-! Literal left-coefficient application depends only on the coefficient values and the slow germ of its input. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem SlowOpenFieldEq.orderedDerivative {U : Set (Vec 2)} (hU : IsOpen U)
    {f g : Vec 2 → Vec 2 → E} (he : SlowOpenFieldEq U f g)
    {n : ℕ} (α : DerivativeWord2 n) :
    SlowOpenFieldEq U
      (fun X z => AVRegularity.orderedDerivative α (fun Y => f Y z) X)
      (fun X z => AVRegularity.orderedDerivative α (fun Y => g Y z) X) := by
  have main : ∀ w : List (Fin 2), ∀ {f g : Vec 2 → Vec 2 → E},
      SlowOpenFieldEq U f g → SlowOpenFieldEq U
        (fun X z => w.foldl (fun F i => fun Y => fderiv ℝ F Y (basisVec i))
          (fun Y => f Y z) X)
        (fun X z => w.foldl (fun F i => fun Y => fderiv ℝ F Y (basisVec i))
          (fun Y => g Y z) X) := by
    intro w
    induction w with
    | nil => intro f g hh; exact hh
    | cons i w ih =>
        intro f g hh
        exact ih (hh.slowPartial hU i)
  exact main (List.ofFn α) he

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_slow_open_congr {U : Set (Vec 2)} (hU : IsOpen U)
    (n : ℕ) (t : ℝ) (c c' : LiftCoeff ι h)
    (f g : ℝ → Vec 2 → ∀ i, h i)
    (hc : ∀ m ≤ n, ∀ α X, X ∈ U → ∀ z v u, c m α t X z v u = c' m α t X z v u)
    (hf : ∀ X ∈ U, f t X = g t X) :
    SlowOpenFieldEq U (liftApply n c f t) (liftApply n c' g t) := by
  have he : SlowOpenFieldEq U (fun X (_ : Vec 2) => f t X)
      (fun X (_ : Vec 2) => g t X) := fun X hX _ => hf X hX
  intro X hX z
  funext v
  unfold liftApply
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro u _
  rw [hc m (by have := Finset.mem_range.mp hm; omega) α X hX z v u]
  have hd := he.orderedDerivative hU α X hX z
  change orderedDerivative α (f t) X = orderedDerivative α (g t) X at hd
  exact congrArg (c' m α t X z v u) (congrFun hd u)
end

end AVRegularity.EntryWeakProofs
end

section
open Homogenization Set
namespace AVRegularity.EntryWeakProofs

/-! Cell averaging preserves equality on a slow open carrier without using values outside it. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem SlowOpenFieldEq.fieldCellMean {U : Set (Vec 2)}
    {f g : Vec 2 → Vec 2 → E} (he : SlowOpenFieldEq U f g) :
    SlowOpenFieldEq U (fun X (_ : Vec 2) => AVRegularity.fieldCellMean (f X))
      (fun X (_ : Vec 2) => AVRegularity.fieldCellMean (g X)) := by
  intro X hX _
  exact congrArg AVRegularity.fieldCellMean (funext (he X hX))

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! Finite uniform budgets for the positive spatial jets of weak charts. -/

def weakBaseChartJetBudget (K : ℕ) : ℝ :=
  1 + ∑ n ∈ Finset.range (K + 1), (2 : ℝ) ^ n * (2 * n.factorial * (2 ^ 14 : ℝ) ^ (n - 1))

theorem weakBaseChartJetBudget_ge_one (K : ℕ) : 1 ≤ weakBaseChartJetBudget K := by
  unfold weakBaseChartJetBudget
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun n _ => by positivity))

theorem weakBaseChartJetBudget_bounds_order (K n : ℕ) (hn : n ≤ K) :
    (2 : ℝ) ^ n * (2 * n.factorial * (2 ^ 14 : ℝ) ^ (n - 1)) ≤ weakBaseChartJetBudget K := by
  have h := Finset.single_le_sum
    (s := Finset.range (K + 1))
    (f := fun n => (2 : ℝ) ^ n * (2 * n.factorial * (2 ^ 14 : ℝ) ^ (n - 1)))
    (fun n _ => by positivity) (Finset.mem_range.mpr (by omega : n < K + 1))
  exact h.trans (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))

def weakChartJetBudget (K : ℕ) : ℕ → ℝ
  | 0 => weakBaseChartJetBudget K
  | n + 1 => positiveJetCompositionBudget K
      (positiveJetCompositionBudget K
        (max (weakChartJetBudget K n) (1 + (2 * Real.pi) ^ (K + 1))))

theorem weakChartJetBudget_ge_one (K n : ℕ) : 1 ≤ weakChartJetBudget K n := by
  induction n with
  | zero => exact weakBaseChartJetBudget_ge_one K
  | succ n ih =>
    exact positiveJetCompositionBudget_ge_one K _
      (positiveJetCompositionBudget_ge_one K _ (ih.trans (le_max_left _ _)))

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

/-! Local edge comparisons compose without changing the constituent maps or coefficient germs. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem SlowOpenEdgeEq.symm {U : Set (Vec 2)} {t : ℝ}
    {edge other : ConstituentEdges D h} (he : SlowOpenEdgeEq U t edge other) :
    SlowOpenEdgeEq U t other edge := by
  intro v u d
  apply List.Forall₂.flip
  exact (he v u d).imp fun _ _ hh =>
    ⟨hh.1.symm, fun α X hX z => (hh.2 α X hX z).symm⟩

theorem SlowOpenEdgeEq.trans {U : Set (Vec 2)} {t : ℝ}
    {edge middle other : ConstituentEdges D h}
    (he : SlowOpenEdgeEq U t edge middle) (hf : SlowOpenEdgeEq U t middle other) :
    SlowOpenEdgeEq U t edge other := by
  intro v u d
  let R := fun a b : Constituent d.val (h u) (h v) => a.map = b.map ∧
    ∀ α X, X ∈ U → ∀ z, a.coeff α t X z = b.coeff α t X z
  have hcomp : ∀ {l l' l''}, List.Forall₂ R l l' → List.Forall₂ R l' l'' →
      List.Forall₂ R l l'' := by
    intro l l' l'' hh hk
    induction hh generalizing l'' with
    | nil =>
        cases hk
        exact List.Forall₂.nil
    | cons hab _ ih =>
        cases hk with
        | cons hbc htail =>
            exact List.Forall₂.cons
              ⟨hab.1.trans hbc.1, fun α X hX z => (hab.2 α X hX z).trans (hbc.2 α X hX z)⟩
              (ih htail)
  exact hcomp (he v u d) (hf v u d)

theorem SlowOpenEdgeEq.mono {U V : Set (Vec 2)} {t : ℝ}
    {edge other : ConstituentEdges D h} (he : SlowOpenEdgeEq U t edge other)
    (hVU : V ⊆ U) : SlowOpenEdgeEq V t edge other := by
  intro v u d
  exact (he v u d).imp fun _ _ hh =>
    ⟨hh.1, fun α X hX z => hh.2 α X (hVU hX) z⟩

end AVRegularity.EntryWeakProofs
end

section
open Homogenization Set
namespace AVRegularity.EntryWeakProofs

/-! Both cross operators depend only on the metric germ on their open slow carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellB1_metric_slow_open_congr {U : Set (Vec 2)} (hU : IsOpen U)
    (η : ℝ) (G G' : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (hG : ∀ X ∈ U, G t X = G' t X)
    (f : Vec 2 → Vec 2 → E) :
    SlowOpenFieldEq U (cellB1 η G v t f) (cellB1 η G' v t f) := by
  intro X hX z
  unfold cellB1
  apply congrArg₂ (fun a b : E => a - Real.sqrt η • b) rfl
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hG X hX]
  have he : SlowOpenFieldEq U
      (fun Y y => G t Y i j • fastPartial j f Y y)
      (fun Y y => G' t Y i j • fastPartial j f Y y) := by
    intro Y hY y
    dsimp only
    rw [hG Y hY]
  rw [he.slowPartial hU i X hX z]

theorem cellB2_metric_slow_open_congr {U : Set (Vec 2)} (hU : IsOpen U)
    (η : ℝ) (G G' : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (t : ℝ) (hG : ∀ X ∈ U, G t X = G' t X) (f : Vec 2 → Vec 2 → E) :
    SlowOpenFieldEq U (cellB2 η G t f) (cellB2 η G' t f) := by
  intro X hX z
  unfold cellB2
  apply congrArg (fun a : E => -(η • a))
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : SlowOpenFieldEq U
      (fun Y y => G t Y i j • slowPartial j f Y y)
      (fun Y y => G' t Y i j • slowPartial j f Y y) := by
    intro Y hY y
    dsimp only
    rw [hG Y hY]
  exact he.slowPartial hU i X hX z

end AVRegularity.EntryWeakProofs
end
