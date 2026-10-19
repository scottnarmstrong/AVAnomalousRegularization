-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.BoundPointwise
public import AVRegularity.CycleComparison.Residual.ChainProject
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.FastJets

/-! Fibrewise `L²_y` jets of two-scale fields with a fixed fast word `δ` applied first: the
analogues of `scalJet` and `vecJet` (which are the case `δ = []`). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Word-summed fibrewise `L²_y` mixed jet of order `m` (slow words `β`) of the fast derivative
`∂_z^δ g`, at the slow point `X`. -/
def scalJetF (g : Vec 2 → Vec 2 → E) (m : ℕ) {b : ℕ} (δ : DerivativeWord2 b) (X : Vec 2) : ℝ≥0∞ :=
  ∑ β : DerivativeWord2 m, ∫⁻ y in AVenhance.unitCube,
    ‖orderedDerivative β (fun X' => orderedDerivative δ (g X') y) X‖ₑ ^ 2

/-- The vector-field version of `scalJetF`. -/
def vecJetF (W : Vec 2 → Vec 2 → Fin 2 → E) (m : ℕ) {b : ℕ} (δ : DerivativeWord2 b)
    (X : Vec 2) : ℝ≥0∞ :=
  ∑ β : DerivativeWord2 m, ∫⁻ y in AVenhance.unitCube, ∑ k : Fin 2,
    ‖orderedDerivative β (fun X' => orderedDerivative δ (fun y' => W X' y' k) y) X‖ₑ ^ 2

end AVRegularity.FastJets
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.FastJets

/-! Slow and fast derivative words of a two-scale field, with words given as lists: the list `l`
is applied letter by letter, first letter innermost (as `orderedDerivative`). The mixed field
`mixL γ δ W` applies the fast word `δ` first and then the slow word `γ`; box smoothness and the
interchange of one fast derivative with a slow word (and conversely) follow from
`IsBoxSmooth.fastPartial_slowPartial`. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative word `l` (a list of coordinate directions) of `g`. -/
def odL (l : List (Fin 2)) (g : Vec 2 → E) : Vec 2 → E :=
  l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) g

theorem orderedDerivative_eq_odL {m : ℕ} (β : DerivativeWord2 m) (g : Vec 2 → E) :
    orderedDerivative β g = odL (List.ofFn β) g := rfl

@[simp] theorem odL_nil (g : Vec 2 → E) : odL [] g = g := rfl

theorem odL_append_singleton (l : List (Fin 2)) (i : Fin 2) (g : Vec 2 → E) :
    odL (l ++ [i]) g = fun x => fderiv ℝ (odL l g) x (basisVec i) := by
  simp [odL, List.foldl_append]

/-- The slow word `γ` applied at fixed fast point. -/
def slowL (γ : List (Fin 2)) (F : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  fun X z => odL γ (fun X' => F X' z) X

/-- The fast word `δ` applied at fixed slow point. -/
def fastL (δ : List (Fin 2)) (F : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  fun X z => odL δ (F X) z

/-- The mixed derivative: fast word first, then slow word. -/
def mixL (γ δ : List (Fin 2)) (F : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  slowL γ (fastL δ F)

@[simp] theorem slowL_nil (F : Vec 2 → Vec 2 → E) : slowL [] F = F := rfl
@[simp] theorem fastL_nil (F : Vec 2 → Vec 2 → E) : fastL [] F = F := rfl

theorem slowL_cons (k : Fin 2) (γ : List (Fin 2)) (F : Vec 2 → Vec 2 → E) :
    slowL (k :: γ) F = slowL γ (slowPartial k F) := rfl

theorem fastL_cons (k : Fin 2) (δ : List (Fin 2)) (F : Vec 2 → Vec 2 → E) :
    fastL (k :: δ) F = fastL δ (fastPartial k F) := rfl

theorem slowL_append_singleton (γ : List (Fin 2)) (i : Fin 2) (F : Vec 2 → Vec 2 → E) :
    slowL (γ ++ [i]) F = slowPartial i (slowL γ F) := by
  funext X z
  simp only [slowL, odL_append_singleton, slowPartial]

theorem fastL_append_singleton (δ : List (Fin 2)) (i : Fin 2) (F : Vec 2 → Vec 2 → E) :
    fastL (δ ++ [i]) F = fastPartial i (fastL δ F) := by
  funext X z
  simp only [fastL, odL_append_singleton, fastPartial]

theorem isBoxSmooth_slowL {sX sZ : ℕ} :
    ∀ (γ : List (Fin 2)) {F : Vec 2 → Vec 2 → E}, IsBoxSmooth (sX + γ.length) sZ F →
      IsBoxSmooth sX sZ (slowL γ F) := by
  intro γ
  induction γ with
  | nil => intro F hF; exact hF
  | cons k γ ih =>
    intro F hF
    rw [slowL_cons]
    exact ih (hF.slowPartial (sX := sX + γ.length) k |> fun h => by simpa using h)

theorem isBoxSmooth_fastL {sX sZ : ℕ} :
    ∀ (δ : List (Fin 2)) {F : Vec 2 → Vec 2 → E}, IsBoxSmooth sX (sZ + δ.length) F →
      IsBoxSmooth sX sZ (fastL δ F) := by
  intro δ
  induction δ with
  | nil => intro F hF; exact hF
  | cons k δ ih =>
    intro F hF
    rw [fastL_cons]
    exact ih (hF.fastPartial (sZ := sZ + δ.length) k |> fun h => by simpa using h)

/-- A fast derivative commutes with a slow word. -/
theorem fastPartial_slowL (i : Fin 2) :
    ∀ (γ : List (Fin 2)) {F : Vec 2 → Vec 2 → E}, IsBoxSmooth γ.length 1 F →
      fastPartial i (slowL γ F) = slowL γ (fastPartial i F) := by
  intro γ
  induction γ with
  | nil => intro F _; rfl
  | cons k γ ih =>
    intro F hF
    have hG : IsBoxSmooth γ.length 1 (slowPartial k F) := by
      have := hF.slowPartial (sX := γ.length) (sZ := 1) k
      exact this
    rw [slowL_cons, ih hG, slowL_cons]
    congr 1
    funext X z
    have h11 : IsBoxSmooth (0 + 1) (0 + 1) F := hF.mono (by simp) le_rfl
    exact IsBoxSmooth.fastPartial_slowPartial h11 i k X z

/-- A slow derivative commutes with a fast word. -/
theorem slowPartial_fastL (k : Fin 2) :
    ∀ (δ : List (Fin 2)) {F : Vec 2 → Vec 2 → E}, IsBoxSmooth 1 δ.length F →
      slowPartial k (fastL δ F) = fastL δ (slowPartial k F) := by
  intro δ
  induction δ with
  | nil => intro F _; rfl
  | cons i δ ih =>
    intro F hF
    have hG : IsBoxSmooth 1 δ.length (fastPartial i F) := by
      have := hF.fastPartial (sX := 1) (sZ := δ.length) i
      exact this
    rw [fastL_cons, ih hG, fastL_cons]
    congr 1
    funext X z
    have h11 : IsBoxSmooth (0 + 1) (0 + 1) F := hF.mono le_rfl (by simp)
    exact (IsBoxSmooth.fastPartial_slowPartial h11 i k X z).symm
end

/-! Word derivatives of a diagonal sample `x ↦ W(ρ⁻¹x, e⁻¹x)`: the Leibniz expansion
`∂^l[W_diag] = ∑_σ ρ^{-|γ_σ|} e^{-|δ_σ|} (∂_X^{γ_σ} ∂_z^{δ_σ} W)_diag`, where `σ` runs over the
`2^{|l|}` ways of sending each letter of `l` to the slow or the fast factor (`splitTerms`), `γ_σ`
(resp. `δ_σ`) being the subword sent to the slow (resp. fast) factor. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One letter is sent either to the slow or to the fast factor. -/
def splitStep (i : Fin 2) (p : List (Fin 2) × List (Fin 2)) :
    List (List (Fin 2) × List (Fin 2)) :=
  [(p.1 ++ [i], p.2), (p.1, p.2 ++ [i])]

/-- The `2^{|l|}` splits (slow subword, fast subword) of the word `l`. -/
def splitTerms (l : List (Fin 2)) : List (List (Fin 2) × List (Fin 2)) :=
  l.foldl (fun acc i => acc.flatMap (splitStep i)) [([], [])]

@[simp] theorem splitTerms_nil : splitTerms [] = [([], [])] := rfl

theorem splitTerms_append_singleton (l : List (Fin 2)) (i : Fin 2) :
    splitTerms (l ++ [i]) = (splitTerms l).flatMap (splitStep i) := by
  simp [splitTerms, List.foldl_append]

theorem splitTerms_length_sum (l : List (Fin 2)) :
    ∀ p ∈ splitTerms l, p.1.length + p.2.length = l.length := by
  induction l using List.reverseRecOn with
  | nil => intro p hp; simp at hp; subst hp; simp
  | append_singleton l i ih =>
    intro p hp
    rw [splitTerms_append_singleton, List.mem_flatMap] at hp
    obtain ⟨q, hq, hpq⟩ := hp
    have := ih q hq
    simp only [splitStep, List.mem_cons, List.not_mem_nil, or_false] at hpq
    rcases hpq with rfl | rfl <;> simp <;> omega

theorem length_flatMap_const {α β : Type*} (g : α → List β) (n : ℕ) (h : ∀ a, (g a).length = n) :
    ∀ L : List α, (L.flatMap g).length = n * L.length := by
  intro L
  induction L with
  | nil => simp
  | cons a L ih => rw [List.flatMap_cons, List.length_append, h, ih]; simp [Nat.mul_succ]; ring

theorem splitTerms_card (l : List (Fin 2)) : (splitTerms l).length = 2 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l i ih =>
    rw [splitTerms_append_singleton, length_flatMap_const _ 2 (fun a => rfl), ih]
    simp [pow_succ, mul_comm]

theorem isBoxSmooth_mixL {sX sZ : ℕ} (γ δ : List (Fin 2)) {W : Vec 2 → Vec 2 → E}
    (hW : IsBoxSmooth (sX + γ.length) (sZ + δ.length) W) : IsBoxSmooth sX sZ (mixL γ δ W) :=
  isBoxSmooth_slowL γ (isBoxSmooth_fastL (sX := sX + γ.length) (sZ := sZ) δ hW)

/-- The weight `ρ^{-|γ|} e^{-|δ|}` of a split term. -/
def termCoef (ρ e : ℝ) (p : List (Fin 2) × List (Fin 2)) : ℝ :=
  (ρ⁻¹) ^ p.1.length * (e⁻¹) ^ p.2.length

/-- A split term of the diagonal sample. -/
def diagTerm (W : Vec 2 → Vec 2 → E) (ρ e : ℝ) (p : List (Fin 2) × List (Fin 2)) (x : Vec 2) : E :=
  termCoef ρ e p • mixL p.1 p.2 W (ρ⁻¹ • x) (e⁻¹ • x)

theorem mixL_isBoxSmooth_of_le {sX sZ : ℕ} {W : Vec 2 → Vec 2 → E} (hW : IsBoxSmooth sX sZ W)
    (γ δ : List (Fin 2)) (ha : γ.length ≤ sX) (hb : δ.length ≤ sZ) :
    IsBoxSmooth (sX - γ.length) (sZ - δ.length) (mixL γ δ W) :=
  isBoxSmooth_mixL γ δ (hW.mono (by omega) (by omega))

theorem differentiableAt_diagTerm {sX sZ : ℕ} {W : Vec 2 → Vec 2 → E} (hW : IsBoxSmooth sX sZ W)
    (ρ e : ℝ) (p : List (Fin 2) × List (Fin 2)) (hp : p.1.length + p.2.length < min sX sZ)
    (x : Vec 2) : DifferentiableAt ℝ (diagTerm W ρ e p) x := by
  have hT := mixL_isBoxSmooth_of_le hW p.1 p.2 (by omega) (by omega)
  have hg : DifferentiableAt ℝ (fun x' : Vec 2 => (ρ⁻¹ • x', e⁻¹ • x')) x := by fun_prop
  have hd : DifferentiableAt ℝ (fun x' => mixL p.1 p.2 W (ρ⁻¹ • x') (e⁻¹ • x')) x :=
    DifferentiableAt.comp (g := Function.uncurry (mixL p.1 p.2 W)) x
      (hT.hasFDerivAt_uncurry (by omega) (by omega) (ρ⁻¹ • x, e⁻¹ • x)).differentiableAt hg
  exact hd.const_smul _

theorem fderiv_diagTerm {sX sZ : ℕ} {W : Vec 2 → Vec 2 → E} (hW : IsBoxSmooth sX sZ W)
    (ρ e : ℝ) (p : List (Fin 2) × List (Fin 2)) (hp : p.1.length + p.2.length < min sX sZ)
    (x : Vec 2) (i : Fin 2) :
    fderiv ℝ (diagTerm W ρ e p) x (basisVec i) =
      termCoef ρ e p • (ρ⁻¹ • mixL (p.1 ++ [i]) p.2 W (ρ⁻¹ • x) (e⁻¹ • x) +
        e⁻¹ • mixL p.1 (p.2 ++ [i]) W (ρ⁻¹ • x) (e⁻¹ • x)) := by
  have hT := mixL_isBoxSmooth_of_le hW p.1 p.2 (by omega) (by omega)
  have hd : DifferentiableAt ℝ (fun x' => mixL p.1 p.2 W (ρ⁻¹ • x') (e⁻¹ • x')) x := by
    have hg : DifferentiableAt ℝ (fun x' : Vec 2 => (ρ⁻¹ • x', e⁻¹ • x')) x := by fun_prop
    exact DifferentiableAt.comp (g := Function.uncurry (mixL p.1 p.2 W)) x
      (hT.hasFDerivAt_uncurry (by omega) (by omega) (ρ⁻¹ • x, e⁻¹ • x)).differentiableAt hg
  have h1 : fderiv ℝ (diagTerm W ρ e p) x (basisVec i) =
      termCoef ρ e p • fderiv ℝ (fun x' => mixL p.1 p.2 W (ρ⁻¹ • x') (e⁻¹ • x')) x (basisVec i) := by
    show fderiv ℝ (fun x' => termCoef ρ e p • mixL p.1 p.2 W (ρ⁻¹ • x') (e⁻¹ • x')) x
      (basisVec i) = _
    rw [fderiv_fun_const_smul hd]
    rfl
  rw [h1, hT.fderiv_diag (by omega) (by omega) ρ e x (basisVec i)]
  have hF : IsBoxSmooth p.1.length 1 (fastL p.2 W) :=
    isBoxSmooth_fastL (sX := p.1.length) (sZ := 1) p.2 (hW.mono (by omega) (by omega))
  have hslow : fderiv ℝ (fun X => mixL p.1 p.2 W X (e⁻¹ • x)) (ρ⁻¹ • x) (basisVec i) =
      mixL (p.1 ++ [i]) p.2 W (ρ⁻¹ • x) (e⁻¹ • x) := by
    simp only [mixL, slowL_append_singleton]
    rfl
  have hfast : fderiv ℝ (mixL p.1 p.2 W (ρ⁻¹ • x)) (e⁻¹ • x) (basisVec i) =
      mixL p.1 (p.2 ++ [i]) W (ρ⁻¹ • x) (e⁻¹ • x) := by
    have := congrFun (congrFun (fastPartial_slowL i p.1 hF) (ρ⁻¹ • x)) (e⁻¹ • x)
    simp only [mixL, fastL_append_singleton]
    exact this
  rw [hslow, hfast]

theorem hasFDerivAt_list_sum_map {ι : Type*} (L : List ι) (f : ι → Vec 2 → E) (x : Vec 2)
    (hf : ∀ p ∈ L, DifferentiableAt ℝ (f p) x) :
    DifferentiableAt ℝ (fun x' => (L.map fun p => f p x').sum) x ∧
      fderiv ℝ (fun x' => (L.map fun p => f p x').sum) x =
        (L.map fun p => fderiv ℝ (f p) x).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨ih1, ih2⟩ := ih fun p hp => hf p (List.mem_cons_of_mem _ hp)
    have ha := hf a List.mem_cons_self
    refine ⟨?_, ?_⟩
    · exact ha.add ih1
    · simp only [List.map_cons, List.sum_cons]
      rw [fderiv_fun_add ha ih1, ih2]

theorem list_sum_clm_apply {ι : Type*} (L : List ι) (F : ι → Vec 2 →L[ℝ] E) (v : Vec 2) :
    (L.map F).sum v = (L.map fun p => F p v).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem list_sum_flatMap {ι κ M : Type*} [AddCommMonoid M] (L : List ι) (g : ι → List κ)
    (h : κ → M) :
    ((L.flatMap g).map h).sum = (L.map fun p => ((g p).map h).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

/-- **Leibniz expansion** of a word derivative of the diagonal sample. -/
theorem odL_diag_eq {sX sZ : ℕ} {W : Vec 2 → Vec 2 → E} (hW : IsBoxSmooth sX sZ W) (ρ e : ℝ) :
    ∀ l : List (Fin 2), l.length ≤ min sX sZ →
      odL l (fun x => W (ρ⁻¹ • x) (e⁻¹ • x)) =
        fun x => ((splitTerms l).map fun p => diagTerm W ρ e p x).sum := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro _
    funext x
    simp [splitTerms, diagTerm, termCoef, mixL]
  | append_singleton l i ih =>
    intro hl
    have hl' : l.length < min sX sZ := by simpa using hl
    rw [odL_append_singleton, ih hl'.le]
    funext x
    have hdiff : ∀ p ∈ splitTerms l, DifferentiableAt ℝ (diagTerm W ρ e p) x := fun p hp =>
      differentiableAt_diagTerm hW ρ e p (by have := splitTerms_length_sum l p hp; omega) x
    obtain ⟨-, hfd⟩ := hasFDerivAt_list_sum_map (splitTerms l) (diagTerm W ρ e) x hdiff
    rw [hfd, list_sum_clm_apply, splitTerms_append_singleton, list_sum_flatMap]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    rw [fderiv_diagTerm hW ρ e p (by have := splitTerms_length_sum l p hp; omega) x i]
    simp [splitStep, diagTerm, termCoef, smul_add, smul_smul, pow_succ]
    congr 1 <;> congr 1 <;> ring

theorem list_sum_map_fin {M ι : Type*} [AddCommMonoid M] (L : List ι) (f : ι → M) :
    (L.map f).sum = ∑ k : Fin L.length, f (L.get k) := by
  conv_lhs => rw [← List.ofFn_get L, List.map_ofFn, List.sum_ofFn]
  rfl

theorem rs_weight_le {rs e ρ : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ) (a b : ℕ) :
    rs ^ (a + b) * ((ρ⁻¹) ^ a * (e⁻¹) ^ b) ≤ 1 := by
  have he : 0 < e := hrs.trans_le hrse
  have hρ : 0 < ρ := he.trans_le heρ
  have h1 : rs * ρ⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hρ]; exact hrse.trans heρ
  have h2 : rs * e⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one he]; exact hrse
  calc rs ^ (a + b) * ((ρ⁻¹) ^ a * (e⁻¹) ^ b) = (rs * ρ⁻¹) ^ a * (rs * e⁻¹) ^ b := by
        rw [pow_add, mul_pow, mul_pow]; ring
    _ ≤ 1 := by
        have h3 : (rs * ρ⁻¹) ^ a ≤ 1 := pow_le_one₀ (by positivity) h1
        have h4 : (rs * e⁻¹) ^ b ≤ 1 := pow_le_one₀ (by positivity) h2
        calc (rs * ρ⁻¹) ^ a * (rs * e⁻¹) ^ b ≤ 1 * 1 := by gcongr
          _ = 1 := one_mul 1

/-- The weighted word derivative of the diagonal sample is dominated by the mixed derivatives. -/
theorem enorm_rs_odL_diag_le {sX sZ : ℕ} {W : Vec 2 → Vec 2 → E} (hW : IsBoxSmooth sX sZ W)
    {ρ e rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ) (l : List (Fin 2))
    (hl : l.length ≤ min sX sZ) (x : Vec 2) :
    ‖rs ^ l.length • odL l (fun x => W (ρ⁻¹ • x) (e⁻¹ • x)) x‖ₑ ≤
      ((splitTerms l).map fun p => ‖mixL p.1 p.2 W (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ).sum := by
  rw [odL_diag_eq hW ρ e l hl]
  beta_reduce
  rw [list_sum_map_fin, list_sum_map_fin, Finset.smul_sum]
  refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hp := splitTerms_length_sum l ((splitTerms l).get k) (List.get_mem _ _)
  simp only [diagTerm, smul_smul, enorm_smul]
  have hw : ‖rs ^ l.length * termCoef ρ e ((splitTerms l).get k)‖ₑ ≤ 1 := by
    rw [← hp]
    have := rs_weight_le hrs hrse heρ ((splitTerms l).get k).1.length ((splitTerms l).get k).2.length
    have h0 : 0 ≤ rs ^ (((splitTerms l).get k).1.length + ((splitTerms l).get k).2.length) *
        termCoef ρ e ((splitTerms l).get k) := by
      have he : 0 < e := hrs.trans_le hrse
      have hρ : 0 < ρ := he.trans_le heρ
      unfold termCoef; positivity
    rw [Real.enorm_eq_ofReal h0]
    exact ENNReal.ofReal_le_one.2 this
  calc ‖rs ^ l.length * termCoef ρ e ((splitTerms l).get k)‖ₑ * ‖mixL ((splitTerms l).get k).1
        ((splitTerms l).get k).2 W (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ
      ≤ 1 * _ := by gcongr
    _ = _ := one_mul _

open scoped ENNReal in
/-- Squared form: `‖rs^j ∂^l[W_diag]‖² ≤ 2^j ∑_σ ‖(∂_X^{γ_σ} ∂_z^{δ_σ} W)_diag‖²`. -/
theorem enorm_sq_rs_odL_diag_le {sX sZ : ℕ} {W : Vec 2 → Vec 2 → E}
    (hW : IsBoxSmooth sX sZ W) {ρ e rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ)
    (l : List (Fin 2)) (hl : l.length ≤ min sX sZ) (x : Vec 2) :
    ‖rs ^ l.length • odL l (fun x => W (ρ⁻¹ • x) (e⁻¹ • x)) x‖ₑ ^ 2 ≤
      2 ^ l.length * ((splitTerms l).map fun p =>
        ‖mixL p.1 p.2 W (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ ^ 2).sum := by
  have h1 := enorm_rs_odL_diag_le hW hrs hrse heρ l hl x
  rw [list_sum_map_fin] at h1 ⊢
  calc _ ≤ (∑ k : Fin (splitTerms l).length,
        ‖mixL ((splitTerms l).get k).1 ((splitTerms l).get k).2 W (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ) ^ 2 := by
        gcongr
    _ ≤ _ := by
        refine (ennreal_sq_sum_le_card_mul_sum_sq _ _).trans ?_
        simp [splitTerms_card]
end

end AVRegularity.FastJets
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.FastJets

/-! Regrouping the split terms of a word by the lengths `(a, b)` of the slow and fast subwords and
by the subwords themselves, at the price of the multiplicity bound `2^{|l|}`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The lists of length `n` (images of the derivative words of length `n`). -/
def wordsFin (n : ℕ) : Finset (List (Fin 2)) :=
  (Finset.univ : Finset (DerivativeWord2 n)).image List.ofFn

theorem mem_wordsFin_self (l : List (Fin 2)) : l ∈ wordsFin l.length :=
  Finset.mem_image.2 ⟨l.get, Finset.mem_univ _, List.ofFn_get l⟩

theorem sum_wordsFin {M : Type*} [AddCommMonoid M] (n : ℕ) (f : List (Fin 2) → M) :
    ∑ l ∈ wordsFin n, f l = ∑ γ : DerivativeWord2 n, f (List.ofFn γ) :=
  Finset.sum_image fun _ _ _ _ h => List.ofFn_injective h

theorem length_of_mem_wordsFin {n : ℕ} {l : List (Fin 2)} (h : l ∈ wordsFin n) : l.length = n := by
  obtain ⟨γ, -, rfl⟩ := Finset.mem_image.1 h
  simp

/-- Regrouping of the split terms: each pair of subwords occurs at most `2^{|l|}` times. -/
theorem sum_splitTerms_le (H : List (Fin 2) × List (Fin 2) → ℝ≥0∞) (l : List (Fin 2)) :
    ((splitTerms l).map H).sum ≤ 2 ^ l.length *
      ∑ ab ∈ Finset.antidiagonal l.length, ∑ γ : DerivativeWord2 ab.1, ∑ δ : DerivativeWord2 ab.2,
        H (List.ofFn γ, List.ofFn δ) := by
  classical
  set P : Finset (List (Fin 2) × List (Fin 2)) :=
    (Finset.antidiagonal l.length).biUnion (fun ab => wordsFin ab.1 ×ˢ wordsFin ab.2) with hP
  have hmem : ∀ q ∈ splitTerms l, q ∈ P := by
    intro q hq
    simp only [hP, Finset.mem_biUnion, Finset.mem_antidiagonal, Finset.mem_product]
    exact ⟨(q.1.length, q.2.length), splitTerms_length_sum l q hq, mem_wordsFin_self _,
      mem_wordsFin_self _⟩
  have hdisj : (↑(Finset.antidiagonal l.length) : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun ab => wordsFin ab.1 ×ˢ wordsFin ab.2) := by
    intro ab _ ab' _ hne
    refine Finset.disjoint_left.2 fun q hq hq' => hne ?_
    simp only [Finset.mem_product] at hq hq'
    have h1 := length_of_mem_wordsFin hq.1
    have h2 := length_of_mem_wordsFin hq.2
    have h1' := length_of_mem_wordsFin hq'.1
    have h2' := length_of_mem_wordsFin hq'.2
    exact Prod.ext (h1.symm.trans h1') (h2.symm.trans h2')
  have hPsum : ∑ q ∈ P, H q = ∑ ab ∈ Finset.antidiagonal l.length, ∑ γ : DerivativeWord2 ab.1,
      ∑ δ : DerivativeWord2 ab.2, H (List.ofFn γ, List.ofFn δ) := by
    rw [hP, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [Finset.sum_product, sum_wordsFin]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [sum_wordsFin]
  rw [← hPsum]
  have hle : ∀ q ∈ splitTerms l, H q ≤ ∑ q' ∈ P, H q' := fun q hq =>
    Finset.single_le_sum (f := H) (fun _ _ => bot_le) (hmem q hq)
  calc ((splitTerms l).map H).sum ≤ ((splitTerms l).map fun _ => ∑ q' ∈ P, H q').sum :=
        List.sum_le_sum fun q hq => hle q hq
    _ = 2 ^ l.length * ∑ q' ∈ P, H q' := by
        rw [List.map_const', List.sum_replicate, splitTerms_card, nsmul_eq_mul]
        norm_num

/-- The weighted word derivative of a diagonal sample, squared, in terms of the mixed derivatives
`∂_X^γ ∂_z^δ W` (words `γ, δ` with `|γ| + |δ| = j`), with the factor `4^j`. -/
theorem enorm_sq_rs_odL_diag_le_words {sX sZ : ℕ} {W : Vec 2 → Vec 2 → E}
    (hW : IsBoxSmooth sX sZ W) {ρ e rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ)
    (l : List (Fin 2)) (hl : l.length ≤ min sX sZ) (x : Vec 2) :
    ‖rs ^ l.length • odL l (fun x => W (ρ⁻¹ • x) (e⁻¹ • x)) x‖ₑ ^ 2 ≤
      4 ^ l.length * ∑ ab ∈ Finset.antidiagonal l.length, ∑ γ : DerivativeWord2 ab.1,
        ∑ δ : DerivativeWord2 ab.2,
          ‖mixL (List.ofFn γ) (List.ofFn δ) W (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ ^ 2 := by
  refine (enorm_sq_rs_odL_diag_le hW hrs hrse heρ l hl x).trans ?_
  have := sum_splitTerms_le (fun p => ‖mixL p.1 p.2 W (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ ^ 2) l
  refine (mul_le_mul_right this (2 ^ l.length)).trans (le_of_eq ?_)
  rw [← mul_assoc, ← mul_pow]
  norm_num

end AVRegularity.FastJets
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.FastJets

/-! Sampling of the mixed derivatives `∂_X^γ ∂_z^δ W` of a box smooth field (the analogue of
`diag_scal_sq_le` for the field `U = ∂_X^γ ∂_z^δ W`), and the resulting bound for the weighted
word derivative of a diagonal sample in terms of the fibrewise mixed jets `scalJetF`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isZ2Periodic_fderiv_apply {g : Vec 2 → E} (hg : AVenhance.IsZ2Periodic g) (v : Vec 2) :
    AVenhance.IsZ2Periodic (fun x => fderiv ℝ g x v) := fun n x => by
  have e : (fun y => g (y + AVenhance.latticeShift n)) = g := funext (hg n)
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := x) (AVenhance.latticeShift n)
  rw [e] at h
  show fderiv ℝ g (x + AVenhance.latticeShift n) v = fderiv ℝ g x v
  rw [← h]

theorem isZ2Periodic_odL (l : List (Fin 2)) :
    ∀ {g : Vec 2 → E}, AVenhance.IsZ2Periodic g → AVenhance.IsZ2Periodic (odL l g) := by
  induction l with
  | nil => intro g hg; exact hg
  | cons i l ih => intro g hg; exact ih (isZ2Periodic_fderiv_apply hg _)

theorem isZ2Periodic_mixL {W : Vec 2 → Vec 2 → E} (hW : ∀ X, AVenhance.IsZ2Periodic (W X))
    (γ δ : List (Fin 2)) (X : Vec 2) : AVenhance.IsZ2Periodic (mixL γ δ W X) := by
  intro n z
  have hG : ∀ X', fastL δ W X' (z + AVenhance.latticeShift n) = fastL δ W X' z := fun X' =>
    isZ2Periodic_odL δ (hW X') n z
  simp only [mixL, slowL]
  have : (fun X' => fastL δ W X' (z + AVenhance.latticeShift n)) = fun X' => fastL δ W X' z :=
    funext hG
  rw [this]

theorem odL_append (l₁ l₂ : List (Fin 2)) (g : Vec 2 → E) :
    odL (l₁ ++ l₂) g = odL l₂ (odL l₁ g) := by
  simp [odL, List.foldl_append]

/-- The jets of the mixed derivative fields, summed over the slow words `γ`, are the jets of
the fast derivative `∂_z^δ W`. -/
theorem sum_scalJet_mixL (W : Vec 2 → Vec 2 → E) (a m : ℕ) {b : ℕ} (δ : DerivativeWord2 b)
    (X : Vec 2) :
    ∑ γ : DerivativeWord2 a, scalJet (mixL (List.ofFn γ) (List.ofFn δ) W) m X =
      scalJetF W (a + m) δ X := by
  unfold scalJet scalJetF
  have hpt : ∀ (γ : DerivativeWord2 a) (β : DerivativeWord2 m) (y : Vec 2),
      orderedDerivative β (fun X' => mixL (List.ofFn γ) (List.ofFn δ) W X' y) X =
        orderedDerivative (Fin.append γ β : DerivativeWord2 (a + m))
          (fun X' => orderedDerivative δ (W X') y) X := by
    intro γ β y
    rw [orderedDerivative_eq_odL, orderedDerivative_eq_odL, List.ofFn_fin_append, odL_append]
    rfl
  simp_rw [hpt]
  rw [← Fintype.sum_prod_type']
  exact (Fin.appendEquiv a m).sum_comp
    (fun w : DerivativeWord2 (a + m) => ∫⁻ y in AVenhance.unitCube,
      ‖orderedDerivative w (fun X' => orderedDerivative δ (W X') y) X‖ₑ ^ 2)

theorem isSlowSmooth_mixL {a b : ℕ} {W : Vec 2 → Vec 2 → E} (hW : IsBoxSmooth (2 + a) b W)
    (γ : DerivativeWord2 a) (δ : DerivativeWord2 b) :
    IsSlowSmooth 2 (mixL (List.ofFn γ) (List.ofFn δ) W) := by
  have h : IsBoxSmooth 2 0 (mixL (List.ofFn γ) (List.ofFn δ) W) :=
    isBoxSmooth_mixL (sX := 2) (sZ := 0) _ _ (by simpa using hW)
  exact h.isSlowSmooth

theorem diag_mixL_sq_le {a b : ℕ} {W : Vec 2 → Vec 2 → E} (hW : IsBoxSmooth (2 + a) b W)
    (hper : ∀ X, AVenhance.IsZ2Periodic (W X)) (γ : DerivativeWord2 a) (δ : DerivativeWord2 b)
    {ρ e : ℝ} (hρ : 0 < ρ) (he : 0 < e) (heρ : e ≤ ρ) (M : ℕ) (hM : e⁻¹ = (M : ℝ)) :
    ∫⁻ x in AVenhance.unitCube,
        ‖mixL (List.ofFn γ) (List.ofFn δ) W (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ ^ 2 ≤
      ENNReal.ofReal (4 * ρ ^ 2) * ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ,
        scalJet (mixL (List.ofFn γ) (List.ofFn δ) W) m X :=
  diag_scal_sq_le _ (isSlowSmooth_mixL hW γ δ) (isZ2Periodic_mixL hper _ _) hρ he heρ M hM

/-- **Word derivatives of a diagonal sample, in `L²`.** For `0 < rs ≤ e ≤ ρ`, `e⁻¹ ∈ ℕ`, a
box smooth `ℤ²`-periodic `W` and a word `β` of length `j`, the cell integral of
`‖rs^j ∂^β[W(ρ⁻¹x, e⁻¹x)]‖²` is bounded by the fibrewise mixed jets `scalJetF W (a + m) δ` of `W`
(`a + b = j`, `|δ| = b`, `m < 3`). -/
theorem lintegral_rs_odL_diag_sq_le {j : ℕ} (β : DerivativeWord2 j) {W : Vec 2 → Vec 2 → E}
    (hW : IsBoxSmooth (j + 2) j W) (hper : ∀ X, AVenhance.IsZ2Periodic (W X))
    {ρ e rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ) (M : ℕ) (hM : e⁻¹ = (M : ℝ)) :
    ∫⁻ x in AVenhance.unitCube,
        ‖rs ^ j • orderedDerivative β (fun x' => W (ρ⁻¹ • x') (e⁻¹ • x')) x‖ₑ ^ 2 ≤
      4 ^ j * ENNReal.ofReal (4 * ρ ^ 2) * ∑ ab ∈ Finset.antidiagonal j,
        ∑ δ : DerivativeWord2 ab.2, ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ,
          scalJetF W (ab.1 + m) δ X := by
  have he : 0 < e := hrs.trans_le hrse
  have hρ : 0 < ρ := he.trans_le heρ
  have hpt : ∀ x : Vec 2,
      ‖rs ^ j • orderedDerivative β (fun x' => W (ρ⁻¹ • x') (e⁻¹ • x')) x‖ₑ ^ 2 ≤
        4 ^ j * ∑ ab ∈ Finset.antidiagonal j, ∑ γ : DerivativeWord2 ab.1,
          ∑ δ : DerivativeWord2 ab.2,
            ‖mixL (List.ofFn γ) (List.ofFn δ) W (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ ^ 2 := by
    intro x
    have h := enorm_sq_rs_odL_diag_le_words (hW.mono (sX' := j) (sZ' := j) (by omega) le_rfl) hrs hrse heρ
      (List.ofFn β) (by simp) x
    simp only [List.length_ofFn] at h
    exact h
  have hmeas : ∀ (ab : ℕ × ℕ) (hab : ab ∈ Finset.antidiagonal j) (γ : DerivativeWord2 ab.1)
      (δ : DerivativeWord2 ab.2), Measurable fun x : Vec 2 =>
        ‖mixL (List.ofFn γ) (List.ofFn δ) W (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ ^ 2 := by
    intro ab hab γ δ
    have hab' := Finset.mem_antidiagonal.1 hab
    have hW' : IsBoxSmooth (2 + ab.1) ab.2 W := hW.mono (by omega) (by omega)
    have hc : Continuous fun x : Vec 2 => mixL (List.ofFn γ) (List.ofFn δ) W (ρ⁻¹ • x) (e⁻¹ • x) :=
      (isSlowSmooth_mixL hW' γ δ).continuous_uncurry.comp
        ((continuous_const_smul _).prodMk (continuous_const_smul _))
    exact hc.enorm.measurable.pow_const 2
  calc _ ≤ ∫⁻ x in AVenhance.unitCube, 4 ^ j * ∑ ab ∈ Finset.antidiagonal j,
        ∑ γ : DerivativeWord2 ab.1, ∑ δ : DerivativeWord2 ab.2,
          ‖mixL (List.ofFn γ) (List.ofFn δ) W (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ ^ 2 := lintegral_mono hpt
    _ = 4 ^ j * ∑ ab ∈ Finset.antidiagonal j, ∑ γ : DerivativeWord2 ab.1,
          ∑ δ : DerivativeWord2 ab.2, ∫⁻ x in AVenhance.unitCube,
            ‖mixL (List.ofFn γ) (List.ofFn δ) W (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ (by simp [ENNReal.pow_eq_top_iff])]
        congr 1
        rw [lintegral_finsetSum _ (fun ab hab => Finset.measurable_sum _ fun γ _ =>
          Finset.measurable_sum _ fun δ _ => hmeas ab hab γ δ)]
        refine Finset.sum_congr rfl fun ab hab => ?_
        rw [lintegral_finsetSum _ (fun γ _ => Finset.measurable_sum _ fun δ _ => hmeas ab hab γ δ)]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [lintegral_finsetSum _ (fun δ _ => hmeas ab hab γ δ)]
    _ ≤ 4 ^ j * ∑ ab ∈ Finset.antidiagonal j, ∑ δ : DerivativeWord2 ab.2,
          (ENNReal.ofReal (4 * ρ ^ 2) * ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ,
            scalJetF W (ab.1 + m) δ X) := by
        gcongr with ab hab
        have hab' := Finset.mem_antidiagonal.1 hab
        have hW' : IsBoxSmooth (2 + ab.1) ab.2 W := hW.mono (by omega) (by omega)
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun δ _ => ?_
        calc ∑ γ : DerivativeWord2 ab.1, ∫⁻ x in AVenhance.unitCube,
              ‖mixL (List.ofFn γ) (List.ofFn δ) W (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ ^ 2
            ≤ ∑ γ : DerivativeWord2 ab.1, ENNReal.ofReal (4 * ρ ^ 2) *
                ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ,
                  scalJet (mixL (List.ofFn γ) (List.ofFn δ) W) m X :=
              Finset.sum_le_sum fun γ _ => diag_mixL_sq_le hW' hper γ δ hρ he heρ M hM
          _ = ENNReal.ofReal (4 * ρ ^ 2) * ∑ m ∈ Finset.range 3, ∑ γ : DerivativeWord2 ab.1,
                ∫⁻ X in slowCell ρ, scalJet (mixL (List.ofFn γ) (List.ofFn δ) W) m X := by
              rw [← Finset.mul_sum, Finset.sum_comm]
          _ ≤ _ := by
              gcongr with m _
              refine (sum_lintegral_le_lintegral_sum (μ := volume.restrict (slowCell ρ))
                (Finset.univ : Finset (DerivativeWord2 ab.1))
                (fun γ X => scalJet (mixL (List.ofFn γ) (List.ofFn δ) W) m X)).trans (le_of_eq ?_)
              congr 1
              funext X
              exact sum_scalJet_mixL W ab.1 m δ X
    _ = _ := by
        rw [mul_assoc]
        congr 1
        simp only [Finset.mul_sum]

end AVRegularity.FastJets
end
