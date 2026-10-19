-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.QuietDecay.Source.Rep
import AVRegularity.CycleComparison.Residual.QuietMean.EpsPoly

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.QuietDecay

/-! The nested sum over `u`, the order `d`, the constituents `γ ∈ edge v u d` and the words `α` that
defines the source flux, as an operation `NS` on families of fields, with its differentiability,
`D_ε`, and exchange with sums in an auxiliary index. -/

section
section NS
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `∑_u ∑_d ∑_{γ ∈ edge v u d} ∑_α T u d γ α`. -/
def NS (edge : ConstituentEdges D h) (v : ι)
    (T : ∀ (u : ι) (d : Finset.Icc 2 D), Constituent d.1 (h u) (h v) →
      DerivativeWord2 (d.1 - 1) → Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  fun X z => ∑ u : ι, ∑ d : Finset.Icc 2 D,
    ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1), T u d γ α X z).sum

theorem NS.diffF (edge : ConstituentEdges D h) (v : ι)
    {T : ∀ (u : ι) (d : Finset.Icc 2 D), Constituent d.1 (h u) (h v) →
      DerivativeWord2 (d.1 - 1) → Vec 2 → Vec 2 → E}
    (hT : ∀ u d, ∀ γ ∈ edge v u d, ∀ α, DiffF (T u d γ α)) : DiffF (NS edge v T) := by
  have : NS edge v T = fun X z => ∑ u ∈ Finset.univ, ∑ d ∈ Finset.univ,
      ((edge v u d).map fun γ => ∑ α ∈ Finset.univ, T u d γ α X z).sum := rfl
  rw [this]
  refine DiffF.sum _ fun u _ => DiffF.sum _ fun d _ => DiffF.list_sum _ fun γ hγ =>
    DiffF.sum _ fun α _ => hT u d γ hγ α

theorem NS.dEps (edge : ConstituentEdges D h) (v : ι)
    {T : ∀ (u : ι) (d : Finset.Icc 2 D), Constituent d.1 (h u) (h v) →
      DerivativeWord2 (d.1 - 1) → Vec 2 → Vec 2 → E}
    (hT : ∀ u d, ∀ γ ∈ edge v u d, ∀ α, DiffF (T u d γ α)) (η ε : ℝ) (k : Fin 2) (X z : Vec 2) :
    dEps η ε k (NS edge v T) X z =
      NS edge v (fun u d γ α => dEps η ε k (T u d γ α)) X z := by
  have e : NS edge v T = fun X z => ∑ u ∈ Finset.univ, ∑ d ∈ Finset.univ,
      ((edge v u d).map fun γ => ∑ α ∈ Finset.univ, T u d γ α X z).sum := rfl
  have hα : ∀ u d, ∀ γ ∈ edge v u d, DiffF (fun X z => ∑ α : DerivativeWord2 (d.1 - 1),
      T u d γ α X z) := fun u d γ hγ => DiffF.sum _ fun α _ => hT u d γ hγ α
  have hl : ∀ u d, DiffF (fun X z => ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
      T u d γ α X z).sum) := fun u d => DiffF.list_sum _ (hα u d)
  have hd : ∀ u, DiffF (fun X z => ∑ d : Finset.Icc 2 D,
      ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1), T u d γ α X z).sum) :=
    fun u => DiffF.sum _ fun d _ => hl u d
  rw [e, dEps_finset_sum _ (fun u _ => hd u)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [dEps_finset_sum _ (fun d _ => hl u d)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [dEps_list_sum _ (hα u d)]
  congr 1
  refine List.map_congr_left fun γ hγ => ?_
  rw [dEps_finset_sum _ (fun α _ => hT u d γ hγ α)]

theorem list_sum_map_smul_sum {κ ι' : Type*} (l : List κ) (s : Finset ι') (c : ι' → ℝ)
    (f : κ → ι' → E) :
    (l.map fun x => ∑ i ∈ s, c i • f x i).sum = ∑ i ∈ s, c i • (l.map fun x => f x i).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib, smul_add]

theorem NS.sum_smul {κ : Type*} (edge : ConstituentEdges D h) (v : ι) (s : Finset κ) (c : κ → ℝ)
    (F : κ → ∀ (u : ι) (d : Finset.Icc 2 D), Constituent d.1 (h u) (h v) →
      DerivativeWord2 (d.1 - 1) → Vec 2 → Vec 2 → E) (X z : Vec 2) :
    NS edge v (fun u d γ α X z => ∑ i ∈ s, c i • F i u d γ α X z) X z =
      ∑ i ∈ s, c i • NS edge v (F i) X z := by
  simp only [NS, Finset.smul_sum]
  have : ∀ (u : ι) (d : Finset.Icc 2 D), ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
      ∑ i ∈ s, c i • F i u d γ α X z).sum =
      ∑ i ∈ s, c i • ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
        F i u d γ α X z).sum := by
    intro u d
    have e : ∀ γ : Constituent d.1 (h u) (h v), ∑ α : DerivativeWord2 (d.1 - 1),
        ∑ i ∈ s, c i • F i u d γ α X z =
        ∑ i ∈ s, c i • ∑ α : DerivativeWord2 (d.1 - 1), F i u d γ α X z := fun γ => by
      rw [Finset.sum_comm]; simp only [Finset.smul_sum]
    simp only [e]
    exact list_sum_map_smul_sum _ _ _ _
  simp only [this]
  calc _ = ∑ u : ι, ∑ i ∈ s, ∑ d : Finset.Icc 2 D, c i • ((edge v u d).map fun γ =>
        ∑ α : DerivativeWord2 (d.1 - 1), F i u d γ α X z).sum :=
        Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

end NS
end

/-! Regularity, continuity of the mixed jets and the mixed-jet triangle inequality for the nested
sum `NS`. -/

section
section NSJet
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem NS.regBox (edge : ConstituentEdges D h) (v : ι) {sX sZ : ℕ}
    {T : ∀ (u : ι) (d : Finset.Icc 2 D), Constituent d.1 (h u) (h v) →
      DerivativeWord2 (d.1 - 1) → Vec 2 → Vec 2 → E}
    (hT : ∀ u d, ∀ γ ∈ edge v u d, ∀ α, RegBox sX sZ (T u d γ α)) :
    RegBox sX sZ (NS edge v T) := by
  have : NS edge v T = fun X z => ∑ u ∈ Finset.univ, ∑ d ∈ Finset.univ,
      ((edge v u d).map fun γ => ∑ α ∈ Finset.univ, T u d γ α X z).sum := rfl
  rw [this]
  exact RegBox.sum _ fun u _ => RegBox.sum _ fun d _ => RegBox.list_sum _ fun γ hγ =>
    RegBox.sum _ fun α _ => hT u d γ hγ α

theorem NS.jcont (edge : ConstituentEdges D h) (v : ι) {sX sZ : ℕ}
    {T : ∀ (u : ι) (d : Finset.Icc 2 D), Constituent d.1 (h u) (h v) →
      DerivativeWord2 (d.1 - 1) → Vec 2 → Vec 2 → E}
    (hT : ∀ u d, ∀ γ ∈ edge v u d, ∀ α, RegBox sX sZ (T u d γ α)) {p q : ℕ} (hp : p ≤ sX)
    (hq : q ≤ sZ) {X : Vec 2} (hc : ∀ u d, ∀ γ ∈ edge v u d, ∀ α, JCont (T u d γ α) X p q) :
    JCont (NS edge v T) X p q := by
  have : NS edge v T = fun X z => ∑ u ∈ Finset.univ, ∑ d ∈ Finset.univ,
      ((edge v u d).map fun γ => ∑ α ∈ Finset.univ, T u d γ α X z).sum := rfl
  rw [this]
  have hα : ∀ u d, ∀ γ ∈ edge v u d, RegBox sX sZ (fun X z => ∑ α : DerivativeWord2 (d.1 - 1),
      T u d γ α X z) := fun u d γ hγ => RegBox.sum _ fun α _ => hT u d γ hγ α
  have hl : ∀ u d, RegBox sX sZ (fun X z => ((edge v u d).map fun γ =>
      ∑ α : DerivativeWord2 (d.1 - 1), T u d γ α X z).sum) := fun u d =>
    RegBox.list_sum _ (hα u d)
  refine JCont.sum _ (fun u _ => RegBox.sum _ fun d _ => hl u d) hp hq fun u _ => ?_
  refine JCont.sum _ (fun d _ => hl u d) hp hq fun d _ => ?_
  refine JCont.list_sum _ (hα u d) hp hq fun γ hγ => ?_
  exact JCont.sum _ (fun α _ => hT u d γ hγ α) hp hq fun α _ => hc u d γ hγ α

theorem NS.srcJp_le (edge : ConstituentEdges D h) (v : ι) {sX sZ : ℕ}
    {T : ∀ (u : ι) (d : Finset.Icc 2 D), Constituent d.1 (h u) (h v) →
      DerivativeWord2 (d.1 - 1) → Vec 2 → Vec 2 → E}
    (hT : ∀ u d, ∀ γ ∈ edge v u d, ∀ α, RegBox sX sZ (T u d γ α)) {p q : ℕ} (hp : p ≤ sX)
    (hq : q ≤ sZ) (X z : Vec 2) :
    srcJp (NS edge v T) X p q z ≤ ∑ u : ι, ∑ d : Finset.Icc 2 D,
      ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1), srcJp (T u d γ α) X p q z).sum := by
  have : NS edge v T = fun X z => ∑ u ∈ Finset.univ, ∑ d ∈ Finset.univ,
      ((edge v u d).map fun γ => ∑ α ∈ Finset.univ, T u d γ α X z).sum := rfl
  rw [this]
  have hα : ∀ u d, ∀ γ ∈ edge v u d, RegBox sX sZ (fun X z => ∑ α : DerivativeWord2 (d.1 - 1),
      T u d γ α X z) := fun u d γ hγ => RegBox.sum _ fun α _ => hT u d γ hγ α
  have hl : ∀ u d, RegBox sX sZ (fun X z => ((edge v u d).map fun γ =>
      ∑ α : DerivativeWord2 (d.1 - 1), T u d γ α X z).sum) := fun u d =>
    RegBox.list_sum _ (hα u d)
  refine (srcJp_sum _ (fun u _ => RegBox.sum _ fun d _ => hl u d) hp hq X z).trans ?_
  refine Finset.sum_le_sum fun u _ => ?_
  refine (srcJp_sum _ (fun d _ => hl u d) hp hq X z).trans ?_
  refine Finset.sum_le_sum fun d _ => ?_
  refine (srcJp_list_sum _ (hα u d) hp hq X z).trans ?_
  refine List.sum_le_sum fun γ hγ => ?_
  exact srcJp_sum (Finset.univ : Finset (DerivativeWord2 (d.1 - 1)))
    (fun α _ => hT u d γ hγ α) hp hq X z

end NSJet
end

/-! **Explicit representation of the source coefficients at a quiet time.** For a box-smooth `Φ`
and fast independent edge coefficients, the source coefficient `𝒮_j Φ` is the explicit finite sum
`srcCoef` over `k`, `u`, `d`, `γ ∈ edge v u d` and the words `α` of the terms
`srcTerm η k a L W j`, with `a = (γ.coeff α t · 0) k`, `L = γ.map` and `W` the `ε`-coefficients
`srcW` of the word derivative of the `u`-component of `Φ`. -/

section
section Repr
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The explicit source coefficient `∑_k ∑_u ∑_d ∑_{γ ∈ edge v u d} ∑_α srcTerm_j`. -/
def srcCoef (edge : ConstituentEdges D h) (η t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (j : ℕ) :
    Vec 2 → Vec 2 → ∀ i, h i :=
  fun X z v => ∑ k : Fin 2, NS edge v (fun u _d γ α =>
    srcTerm η k (fun Y => γ.coeff α t Y 0 k) γ.map (srcW η u α Φ) j) X z

/-- The term of the source flux, at the parameter `ε`. -/
def srcFluxTerm {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
    [NormedSpace ℝ E₂] (ε : ℝ) (a : Vec 2 → ℝ) (L : E₁ →L[ℝ] E₂) (n : ℕ)
    (W : ℕ → Vec 2 → Vec 2 → E₁) : Vec 2 → Vec 2 → E₂ :=
  fun X z => a X • L (∑ i ∈ Finset.range (n + 1), ε ^ i • W i X z)

theorem NS.congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (edge : ConstituentEdges D h)
    (v : ι) {T T' : ∀ (u : ι) (d : Finset.Icc 2 D), Constituent d.1 (h u) (h v) →
      DerivativeWord2 (d.1 - 1) → Vec 2 → Vec 2 → E} (X z : Vec 2)
    (hT : ∀ u d, ∀ γ ∈ edge v u d, ∀ α, T u d γ α X z = T' u d γ α X z) :
    NS edge v T X z = NS edge v T' X z := by
  simp only [NS]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun d _ => ?_
  congr 1
  refine List.map_congr_left fun γ hγ => ?_
  exact Finset.sum_congr rfl fun α _ => hT u d γ hγ α

theorem sourceFlux_apply (edge : ConstituentEdges D h) (η t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {s : ℕ} (hΦ : IsBoxSmooth s s Φ) (hDs : D ≤ s) (ε : ℝ)
    (k : Fin 2) (X z : Vec 2) (v : ι) :
    sourceFlux edge η ε t Φ k X z v = NS edge v (fun u d γ α =>
      srcFluxTerm ε (fun Y => γ.coeff α t Y 0 k) γ.map (d.1 - 1) (srcW η u α Φ)) X z := by
  simp only [sourceFlux, NS, srcFluxTerm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun d _ => ?_
  have hd := Finset.mem_Icc.mp d.2
  congr 1
  refine List.map_congr_left fun γ hγ => ?_
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [hquiet v u d γ hγ α X z 0, dEpsWord_apply_eq η ε α hΦ (by omega) u X z]

omit [Fintype ι] in
theorem diffF_srcFluxTerm {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (ε : ℝ)
    {a : Vec 2 → ℝ} (ha : Differentiable ℝ a) {u : ι} (L : h u →L[ℝ] E₂) (n : ℕ)
    {W : ℕ → Vec 2 → Vec 2 → h u} (hW : ∀ i, DiffF (W i)) :
    DiffF (srcFluxTerm ε a L n W) :=
  ((DiffF.sum _ fun i _ => (hW i).const_smul (ε ^ i)).clm L).mulX ha

omit [Fintype ι] in
theorem differentiable_coeff (edge : ConstituentEdges D h) (t : ℝ)
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    {v u : ι} {d : Finset.Icc 2 D} {γ : Constituent d.1 (h u) (h v)} (hγ : γ ∈ edge v u d)
    (α : DerivativeWord2 (d.1 - 1)) (k : Fin 2) :
    Differentiable ℝ (fun Y => γ.coeff α t Y 0 k) :=
  ((contDiff_pi.mp (hsm v u d γ hγ α 0)) k).differentiable one_ne_zero

theorem diffF_flux (edge : ConstituentEdges D h) (η t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {s : ℕ} (hΦ : IsBoxSmooth s s Φ) (hDs : D ≤ s) (ε : ℝ)
    (k : Fin 2) : DiffF (sourceFlux edge η ε t Φ k) := by
  have hc : ∀ w, DiffF (fun X z => sourceFlux edge η ε t Φ k X z w) := by
    intro w
    have e : (fun X z => sourceFlux edge η ε t Φ k X z w) = NS edge w (fun u d γ α =>
        srcFluxTerm ε (fun Y => γ.coeff α t Y 0 k) γ.map (d.1 - 1) (srcW η u α Φ)) :=
      funext fun X => funext fun z => sourceFlux_apply edge η t hquiet hΦ hDs ε k X z w
    rw [e]
    refine NS.diffF edge w fun u d γ hγ α => diffF_srcFluxTerm ε
      (differentiable_coeff edge t hsm hγ α k) _ _ fun i => ?_
    have hd := Finset.mem_Icc.mp d.2
    exact diffF_srcW η u α hΦ (by omega) i
  exact ⟨fun X => differentiable_pi.mpr fun w => (hc w).1 X,
    fun z => differentiable_pi.mpr fun w => (hc w).2 z⟩

/-- The source operator is a polynomial in `ε`, with the explicit coefficients `srcCoef`. -/
theorem sourceOp_apply (edge : ConstituentEdges D h) (η t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {s : ℕ} (hΦ : IsBoxSmooth s s Φ) (hDs : D ≤ s) (ε : ℝ)
    (X z : Vec 2) (v : ι) :
    sourceOp edge η ε t Φ X z v =
      ∑ i ∈ Finset.range (D + 2), ε ^ i • srcCoef edge η t Φ i X z v := by
  have hT : ∀ k : Fin 2, ∀ u d, ∀ γ ∈ edge v u d, ∀ α, DiffF (srcFluxTerm ε
      (fun Y => γ.coeff α t Y 0 k) γ.map (d.1 - 1) (srcW η u α Φ)) := fun k u d γ hγ α =>
    diffF_srcFluxTerm ε (differentiable_coeff edge t hsm hγ α k) _ _ fun i => by
      have hd := Finset.mem_Icc.mp d.2
      exact diffF_srcW η u α hΦ (by omega) i
  have h1 : ∀ k : Fin 2, dEps η ε k (sourceFlux edge η ε t Φ k) X z v =
      NS edge v (fun u d γ α X z => ∑ i ∈ Finset.range (D + 2), ε ^ i • srcTerm η k
        (fun Y => γ.coeff α t Y 0 k) γ.map (srcW η u α Φ) i X z) X z := by
    intro k
    have e1 := dEps_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
      (diffF_flux edge η t hquiet hsm hΦ hDs ε k) η ε k X z
    have e2 : (fun X' z' => (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
        (sourceFlux edge η ε t Φ k X' z')) = NS edge v (fun u d γ α =>
        srcFluxTerm ε (fun Y => γ.coeff α t Y 0 k) γ.map (d.1 - 1) (srcW η u α Φ)) :=
      funext fun X' => funext fun z' => sourceFlux_apply edge η t hquiet hΦ hDs ε k X' z' v
    rw [e2, NS.dEps edge v (hT k)] at e1
    simp only [ContinuousLinearMap.proj_apply] at e1
    rw [← e1]
    refine NS.congr edge v X z fun u d γ hγ α => ?_
    have hd := Finset.mem_Icc.mp d.2
    have := dEps_term_poly η ε k (differentiable_coeff edge t hsm hγ α k) γ.map (d.1 - 1)
      (W := srcW η u α Φ) (fun i => diffF_srcW η u α hΦ (by omega) i)
      (fun i hi => srcW_eq_zero η u α Φ hi) (N := D + 2) (by omega)
    exact congrFun (congrFun this X) z
  have h2 : sourceOp edge η ε t Φ X z v = ∑ k : Fin 2, dEps η ε k (sourceFlux edge η ε t Φ k) X z v := by
    simp only [sourceOp, Finset.sum_apply]
  rw [h2]
  simp only [h1, NS.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [srcCoef, Finset.smul_sum]

/-- The explicit coefficient vanishes beyond the order `D`. -/
theorem srcCoef_eq_zero (edge : ConstituentEdges D h) (η t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i)
    {j : ℕ} (hj : D < j) : srcCoef edge η t Φ j = fun _ _ => 0 := by
  funext X z v
  simp only [srcCoef, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [NS]
  refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun d _ => ?_
  have hd := Finset.mem_Icc.mp d.2
  have : ∀ (γ : Constituent d.1 (h u) (h v)) (α : DerivativeWord2 (d.1 - 1)),
      srcTerm η k (fun Y => γ.coeff α t Y 0 k) γ.map (srcW η u α Φ) j X z = 0 := fun γ α => by
    have := srcTerm_eq_zero η k (fun Y => γ.coeff α t Y 0 k) γ.map
      (W := srcW η u α Φ) (n := d.1 - 1) (fun i hi => srcW_eq_zero η u α Φ hi) (j := j)
      (by omega)
    exact congrFun (congrFun this X) z
  simp [this]

/-- **Explicit representation of the source coefficients** at a time where every edge coefficient
is fast independent: `𝒮_j Φ = srcCoef j`. -/
theorem sourceCoeff_eq_srcCoef (edge : ConstituentEdges D h) (η t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {s : ℕ} (hΦ : IsBoxSmooth s s Φ) (hDs : D ≤ s) (j : ℕ) :
    sourceCoeff edge η j t Φ = srcCoef edge η t Φ j := by
  funext X z
  have hf : (fun ε : ℝ => sourceOp edge η ε t Φ X z) =
      fun ε => ∑ i ∈ Finset.range (D + 1 + 1), ε ^ i • srcCoef edge η t Φ i X z := by
    funext ε
    funext v
    rw [sourceOp_apply edge η t hquiet hsm hΦ hDs ε X z v]
    simp [Finset.sum_apply]
  simp only [sourceCoeff, hf, iteratedDeriv_epsPoly]
  by_cases hj : j ≤ D + 1
  · simp [hj, Nat.factorial_ne_zero]
  · have := srcCoef_eq_zero edge η t Φ (j := j) (by omega)
    simp [hj, congrFun (congrFun this X) z]

end Repr
end

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization
open scoped ENNReal NNReal
namespace AVRegularity.QuietDecay

/-! Regularity, continuity and mixed-jet bounds of one term `srcTerm η k a L W J` of the source
coefficient in terms of the mixed jets of the `ε`-coefficients `W`. -/

section TermBound
variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂]

theorem srcJp_mulX_le {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E₂} (hf : RegBox sX sZ f) {a : Vec 2 → ℝ}
    {p q : ℕ} (ha : ContDiff ℝ (p : ℕ∞) a) (hp : p ≤ sX) (hq : q ≤ sZ) (X z : Vec 2) {M : ℝ}
    (hM : ∀ i ≤ p, srcJp f X (p - i) q z ≤ M) :
    srcJp (fun X z => a X • f X z) X p q z ≤
      2 ^ p * M * ∑ i ∈ Finset.range (p + 1), ‖iteratedFDeriv ℝ i a X‖ := by
  refine (srcJp_mulX hf ha hp hq X z).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ p := by simpa [Nat.lt_succ_iff] using hi
  have hc : (p.choose i : ℝ) ≤ 2 ^ p := by exact_mod_cast Nat.choose_le_two_pow p i
  have h1 : (p.choose i : ℝ) * ‖iteratedFDeriv ℝ i a X‖ * srcJp f X (p - i) q z ≤
      2 ^ p * ‖iteratedFDeriv ℝ i a X‖ * M :=
    mul_le_mul (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) (hM i hi')
      (srcJp_nonneg _ _ _ _ _) (by positivity)
  calc _ ≤ _ := h1
    _ = _ := by ring

section Pieces
variable {W : ℕ → Vec 2 → Vec 2 → E₁} {r : ℕ} (hW : ∀ i, IsBoxSmooth (r + 1) (r + 1) (W i))
include hW

variable {k : Fin 2} {a : Vec 2 → ℝ} {p q m : ℕ} (L : E₁ →L[ℝ] E₂) (X z : Vec 2) (J₀ : ℕ)
  {β : ℕ → ℕ → ℝ} (hpq : p + q ≤ r)
  (hJ : ∀ i p' q', p' + q' ≤ p + q + 1 →
    srcJp (W i) X p' q' z ≤ 2 ^ m * β (p' + i) (q' + m - i))
  {Bs : ℝ} (hBs : ∀ a' b', a' ≤ p + J₀ → b' ≤ q + m + 1 → β a' b' ≤ Bs)
include hpq hJ hBs

end Pieces

end TermBound

end AVRegularity.QuietDecay
end
