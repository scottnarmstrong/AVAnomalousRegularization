-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.QuietMean.EpsPoly
public import AVRegularity.Proofs.Results.Construction.LiftPathDecomposition.ChainWalk
import AVRegularity.Proofs.Results.Construction.LiftPathDecomposition.Mean
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
public import AVRegularity.Definitions.Construction.DiagLetter
import Mathlib.Combinatorics.SimpleGraph.Basic

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.PathDecomp

/-! Linearity of the two-scale operators on smooth fields.

For finitely many jointly smooth fields `Φ i` with values in `P` and continuous linear maps
`L i : P → E`, the partial derivatives, `D_ε`, `D_ε^α`, `ℬ₁`, `ℬ₂`, the cell mean, the ordered slow
derivatives and the `ε`-derivatives of `∑ i, L i (Φ i)` are the corresponding sums of the images.
For non-differentiable fields these identities can fail (the `fderiv` junk value), so every lemma
carries the joint regularity it needs (`GoodField r`). -/

section
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {κ : Type*}

theorem goodField_clm_sum {r : ℕ} (s : Finset κ) (L : κ → P →L[ℝ] E)
    {Φ : κ → Vec 2 → Vec 2 → P} (hΦ : ∀ i ∈ s, GoodField r (Φ i)) :
    GoodField r (fun X z => ∑ i ∈ s, L i (Φ i X z)) :=
  GoodField.sum s fun i hi => (hΦ i hi).clm (L i)

theorem slowPartial_clm_sum (s : Finset κ) (L : κ → P →L[ℝ] E) {Φ : κ → Vec 2 → Vec 2 → P}
    (hΦ : ∀ i ∈ s, GoodField 1 (Φ i)) (k : Fin 2) (X z : Vec 2) :
    slowPartial k (fun X z => ∑ i ∈ s, L i (Φ i X z)) X z =
      ∑ i ∈ s, L i (slowPartial k (Φ i) X z) := by
  have hdd : ∀ i ∈ s, DifferentiableAt ℝ (fun X' => Φ i X' z) X := fun i hi =>
    (((hΦ i hi).1.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero) X
  have hd : ∀ i ∈ s, DifferentiableAt ℝ (fun X' => L i (Φ i X' z)) X := fun i hi =>
    (L i).differentiableAt.comp X (hdd i hi)
  simp only [slowPartial]
  rw [fderiv_fun_sum hd]
  simp only [sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [fderiv_fun_comp X (L i).differentiableAt (hdd i hi), (L i).fderiv]
  rfl

theorem fastPartial_clm_sum (s : Finset κ) (L : κ → P →L[ℝ] E) {Φ : κ → Vec 2 → Vec 2 → P}
    (hΦ : ∀ i ∈ s, GoodField 1 (Φ i)) (k : Fin 2) (X z : Vec 2) :
    fastPartial k (fun X z => ∑ i ∈ s, L i (Φ i X z)) X z =
      ∑ i ∈ s, L i (fastPartial k (Φ i) X z) := by
  have hdd : ∀ i ∈ s, DifferentiableAt ℝ (Φ i X) z := fun i hi =>
    ((hΦ i hi).contDiff_slice X).differentiable one_ne_zero z
  have hd : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => L i (Φ i X z')) z := fun i hi =>
    (L i).differentiableAt.comp z (hdd i hi)
  simp only [fastPartial]
  rw [fderiv_fun_sum hd]
  simp only [sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [fderiv_fun_comp z (L i).differentiableAt (hdd i hi), (L i).fderiv]
  rfl

theorem dEps_clm_sum (s : Finset κ) (L : κ → P →L[ℝ] E) {Φ : κ → Vec 2 → Vec 2 → P}
    (hΦ : ∀ i ∈ s, GoodField 1 (Φ i)) (η ε : ℝ) (k : Fin 2) :
    dEps η ε k (fun X z => ∑ i ∈ s, L i (Φ i X z)) =
      fun X z => ∑ i ∈ s, L i (dEps η ε k (Φ i) X z) := by
  funext X z
  simp only [dEps]
  rw [fastPartial_clm_sum s L hΦ, slowPartial_clm_sum s L hΦ, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, map_smul]

theorem goodField_dEps {r : ℕ} {Φ : Vec 2 → Vec 2 → P} (hΦ : GoodField (r + 1) Φ) (η ε : ℝ)
    (k : Fin 2) : GoodField r (dEps η ε k Φ) := by
  have := (hΦ.fastPartial k).add ((hΦ.slowPartial k).smul (Real.sqrt η * ε))
  exact this

theorem foldl_dEps_clm_sum (s : Finset κ) (L : κ → P →L[ℝ] E) (η ε : ℝ) :
    ∀ (l : List (Fin 2)) {Φ : κ → Vec 2 → Vec 2 → P}, (∀ i ∈ s, GoodField l.length (Φ i)) →
      l.foldl (fun Ψ k => dEps η ε k Ψ) (fun X z => ∑ i ∈ s, L i (Φ i X z)) =
        fun X z => ∑ i ∈ s, L i (l.foldl (fun Ψ k => dEps η ε k Ψ) (Φ i) X z)
  | [], _, _ => rfl
  | k :: l, Φ, hΦ => by
      simp only [List.foldl_cons]
      have h1 : ∀ i ∈ s, GoodField 1 (Φ i) := fun i hi =>
        (hΦ i hi).mono (by simp)
      rw [dEps_clm_sum s L h1 η ε k]
      exact foldl_dEps_clm_sum s L η ε l (Φ := fun i => dEps η ε k (Φ i)) fun i hi =>
        goodField_dEps ((hΦ i hi).mono (by simp)) η ε k

theorem dEpsWord_clm_sum (s : Finset κ) (L : κ → P →L[ℝ] E) {m : ℕ} (α : DerivativeWord2 m)
    {Φ : κ → Vec 2 → Vec 2 → P} (hΦ : ∀ i ∈ s, GoodField m (Φ i)) (η ε : ℝ) :
    dEpsWord η ε α (fun X z => ∑ i ∈ s, L i (Φ i X z)) =
      fun X z => ∑ i ∈ s, L i (dEpsWord η ε α (Φ i) X z) :=
  foldl_dEps_clm_sum s L η ε (List.ofFn α) (by simpa using hΦ)

/-- `ℬ₁` is linear on fields of class `C²` when the metric is `C¹` in the slow variable. -/
theorem cellB1_clm_sum (s : Finset κ) (L : κ → P →L[ℝ] E) {Φ : κ → Vec 2 → Vec 2 → P}
    (hΦ : ∀ i ∈ s, GoodField 2 (Φ i)) (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (hG : ∀ a b, ContDiff ℝ (1 : ℕ∞) (fun X => G t X a b))
    (X z : Vec 2) :
    cellB1 η G v t (fun X z => ∑ i ∈ s, L i (Φ i X z)) X z =
      ∑ i ∈ s, L i (cellB1 η G v t (Φ i) X z) := by
  have h1 : ∀ i ∈ s, GoodField 1 (Φ i) := fun i hi => (hΦ i hi).mono (by norm_num)
  have hs : ∀ j, ∀ i ∈ s, GoodField 1 (slowPartial j (Φ i)) := fun j i hi =>
    (hΦ i hi).slowPartial j
  have hf : ∀ j, ∀ i ∈ s, GoodField 1 (fastPartial j (Φ i)) := fun j i hi =>
    (hΦ i hi).fastPartial j
  have hGf : ∀ a b, ∀ i ∈ s, GoodField 1 (fun X' z' => G t X' a b • fastPartial b (Φ i) X' z') :=
    fun a b i hi => (hf b i hi).mulX (hG a b)
  have eS : ∀ j, slowPartial j (fun X z => ∑ i ∈ s, L i (Φ i X z)) =
      fun X z => ∑ i ∈ s, L i (slowPartial j (Φ i) X z) := fun j =>
    funext fun X => funext fun z => slowPartial_clm_sum s L h1 j X z
  have eF : ∀ j, fastPartial j (fun X z => ∑ i ∈ s, L i (Φ i X z)) =
      fun X z => ∑ i ∈ s, L i (fastPartial j (Φ i) X z) := fun j =>
    funext fun X => funext fun z => fastPartial_clm_sum s L h1 j X z
  have eG : ∀ a b, (fun X' z' => G t X' a b • fastPartial b
      (fun X z => ∑ i ∈ s, L i (Φ i X z)) X' z') =
      fun X' z' => ∑ i ∈ s, L i (G t X' a b • fastPartial b (Φ i) X' z') := by
    intro a b
    funext X' z'
    rw [eF b, Finset.smul_sum]
    simp only [map_smul]
  simp only [cellB1, eS, eG]
  simp only [fastPartial_clm_sum s L (hs _), slowPartial_clm_sum s L (hGf _ _)]
  simp only [map_sub, map_sum, map_smul, map_add, Finset.smul_sum, smul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  congr 1
  · conv_rhs => rw [Finset.sum_comm]
  · congr 1
    · conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
    · conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]

/-- `ℬ₂` is linear on fields of class `C²` when the metric is `C¹` in the slow variable. -/
theorem cellB2_clm_sum (s : Finset κ) (L : κ → P →L[ℝ] E) {Φ : κ → Vec 2 → Vec 2 → P}
    (hΦ : ∀ i ∈ s, GoodField 2 (Φ i)) (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (hG : ∀ a b, ContDiff ℝ (1 : ℕ∞) (fun X => G t X a b)) (X z : Vec 2) :
    cellB2 η G t (fun X z => ∑ i ∈ s, L i (Φ i X z)) X z =
      ∑ i ∈ s, L i (cellB2 η G t (Φ i) X z) := by
  have h1 : ∀ i ∈ s, GoodField 1 (Φ i) := fun i hi => (hΦ i hi).mono (by norm_num)
  have hGs : ∀ a b, ∀ i ∈ s, GoodField 1 (fun X' z' => G t X' a b • slowPartial b (Φ i) X' z') :=
    fun a b i hi => ((hΦ i hi).slowPartial b).mulX (hG a b)
  have eG : ∀ a b, (fun X' z' => G t X' a b • slowPartial b
      (fun X z => ∑ i ∈ s, L i (Φ i X z)) X' z') =
      fun X' z' => ∑ i ∈ s, L i (G t X' a b • slowPartial b (Φ i) X' z') := by
    intro a b
    funext X' z'
    rw [slowPartial_clm_sum s L h1 b X' z', Finset.smul_sum]
    simp only [map_smul]
  simp only [cellB2, eG, slowPartial_clm_sum s L (hGs _ _)]
  simp only [map_neg, map_smul, map_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

theorem fieldCellMean_clm_sum [CompleteSpace P] [CompleteSpace E] (s : Finset κ)
    (L : κ → P →L[ℝ] E) {Φ : κ → Vec 2 → P} (hΦ : ∀ i ∈ s, Continuous (Φ i)) :
    fieldCellMean (fun z => ∑ i ∈ s, L i (Φ i z)) = ∑ i ∈ s, L i (fieldCellMean (Φ i)) := by
  rw [fieldCellMean_sum (f := fun i z => L i (Φ i z)) s fun i hi => (L i).continuous.comp (hΦ i hi)]
  exact Finset.sum_congr rfl fun i hi => fieldCellMean_clm (L i) (hΦ i hi)

theorem foldl_fderiv_clm_sum (s : Finset κ) (L : κ → P →L[ℝ] E) :
    ∀ (l : List (Fin 2)) {β : κ → Vec 2 → P}, (∀ i ∈ s, ContDiff ℝ (l.length : ℕ∞) (β i)) →
      l.foldl (fun g' j => fun x => fderiv ℝ g' x (basisVec j)) (fun Y => ∑ i ∈ s, L i (β i Y)) =
        fun Y => ∑ i ∈ s, L i (l.foldl (fun g' j => fun x => fderiv ℝ g' x (basisVec j)) (β i) Y)
  | [], _, _ => rfl
  | j :: l, β, hβ => by
      simp only [List.foldl_cons]
      have hd : ∀ i ∈ s, Differentiable ℝ (β i) := fun i hi =>
        (hβ i hi).differentiable (by simp)
      have e : (fun x => fderiv ℝ (fun Y => ∑ i ∈ s, L i (β i Y)) x (basisVec j)) =
          fun Y => ∑ i ∈ s, L i (fderiv ℝ (β i) Y (basisVec j)) := by
        funext x
        rw [fderiv_fun_sum (A := fun i Y => L i (β i Y)) fun i hi =>
          ((L i).differentiableAt.comp x (hd i hi x) : DifferentiableAt ℝ (fun Y => L i (β i Y)) x)]
        simp only [sum_apply]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [fderiv_fun_comp x (L i).differentiableAt (hd i hi x), (L i).fderiv]
        rfl
      rw [e]
      exact foldl_fderiv_clm_sum s L l (β := fun i Y => fderiv ℝ (β i) Y (basisVec j))
        fun i hi => ((hβ i hi).fderiv_right (m := (l.length : ℕ∞))
          (by simp [List.length_cons])).clm_apply contDiff_const

theorem orderedDerivative_clm_sum (s : Finset κ) (L : κ → P →L[ℝ] E) {m : ℕ}
    (α : DerivativeWord2 m) {β : κ → Vec 2 → P} (hβ : ∀ i ∈ s, ContDiff ℝ (m : ℕ∞) (β i)) :
    orderedDerivative α (fun Y => ∑ i ∈ s, L i (β i Y)) =
      fun Y => ∑ i ∈ s, L i (orderedDerivative α (β i) Y) :=
  foldl_fderiv_clm_sum s L (List.ofFn α) (by simpa using hβ)

theorem iteratedDeriv_clm_sum (s : Finset κ) (L : κ → P →L[ℝ] E) {j : ℕ} {F : κ → ℝ → P}
    (hF : ∀ i ∈ s, ContDiff ℝ (j : ℕ∞) (F i)) (x : ℝ) :
    iteratedDeriv j (fun ε => ∑ i ∈ s, L i (F i ε)) x =
      ∑ i ∈ s, L i (iteratedDeriv j (F i) x) := by
  rw [iteratedDeriv_fun_sum (f := fun i ε => L i (F i ε)) fun i hi =>
    (((L i).contDiff.comp (hF i hi)).contDiffAt : ContDiffAt ℝ (j : ℕ∞) (fun ε => L i (F i ε)) x)]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  rw [show (fun ε => L i (F i ε)) = (L i) ∘ F i from rfl,
    (L i).iteratedFDeriv_comp_left (hF i hi).contDiffAt le_rfl]
  rfl
end

/-! Explicit scalar formulas along a walk.

For a context (cell data `η, G, v`, maximal order `D`, scalar test field `g₀`, scalar arrays `T`
indexed by step data, time `t`) and step data `cd : Fin g → StepDat`:
* `valF k g cd`: the degree-`k` value `∑ T g cd k m α · ∂^α g₀`;
* `fluxS k g cd ε κ`: the source flux of the last step applied to the value of the prefix;
* `opS`: its `D_ε`-divergence; `formA, formM, formCL, formS`: the scalar cell operator
  `A_n`, its cell mean, the `C_j L_{n-j}` terms and the cell source.
These are the per-walk scalar factors of the corresponding quantities of a path-candidate array. -/

section
/-- The context of the explicit formulas. -/
structure Ctx where
  /-- The cell contrast. -/
  η : ℝ
  /-- The metric. -/
  G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ
  /-- The drift. -/
  v : ℝ → Vec 2 → Vec 2
  /-- The maximal order. -/
  D : ℕ
  /-- The scalar test field. -/
  g₀ : Vec 2 → ℝ
  /-- The scalar arrays, indexed by step data. -/
  T : (g : ℕ) → (Fin g → StepDat) → SArr
  /-- The time. -/
  t : ℝ

namespace Ctx

variable (C : Ctx)

/-- The default step data. -/
def dflt : StepDat := (0, fun _ _ _ _ _ => 0)

/-- The degree-`k` value along step data `cd`. -/
def valF (k g : ℕ) (cd : Fin g → StepDat) : Vec 2 → Vec 2 → ℝ :=
  fun X z => ∑ m ∈ Finset.range (k + 1), ∑ α : DerivativeWord2 m,
    C.T g cd k m α C.t X z * orderedDerivative α C.g₀ X

/-- The source flux of the last step applied to the degree-`k` value of the prefix. -/
def fluxS (k g : ℕ) (cd : Fin (g + 1) → StepDat) (ε : ℝ) (κ : Fin 2) : Vec 2 → Vec 2 → ℝ :=
  fun X z => ∑ d : Finset.Icc 2 C.D,
    if d.1 ≤ (cd (Fin.last g)).1 then
      ∑ α : DerivativeWord2 (d.1 - 1),
        (cd (Fin.last g)).2 d.1 α C.t X z κ * dEpsWord C.η ε α (C.valF k g (Fin.init cd)) X z
    else 0

/-- The `D_ε`-divergence of `fluxS`. -/
def opS (k g : ℕ) (cd : Fin (g + 1) → StepDat) (ε : ℝ) : Vec 2 → Vec 2 → ℝ :=
  fun X z => ∑ κ : Fin 2, dEps C.η ε κ (C.fluxS k g cd ε κ) X z

/-- The scalar cell operator `A_n` along step data. -/
def formA (n : ℕ) : (g : ℕ) → (Fin g → StepDat) → Vec 2 → Vec 2 → ℝ
  | 0, cd => fun X z => cellB1 C.η C.G C.v C.t (C.valF (n - 1) 0 cd) X z +
      (if 2 ≤ n then cellB2 C.η C.G C.t (C.valF (n - 2) 0 cd) X z else 0)
  | g + 1, cd => fun X z => cellB1 C.η C.G C.v C.t (C.valF (n - 1) (g + 1) cd) X z +
      (if 2 ≤ n then cellB2 C.η C.G C.t (C.valF (n - 2) (g + 1) cd) X z else 0) -
      ∑ j ∈ Finset.range (min C.D n + 1), ((j.factorial : ℝ)⁻¹) •
        iteratedDeriv j (fun ε => C.opS (n - j) g cd ε X z) 0

/-- The cell mean of `formA`. -/
def formM (n g : ℕ) (cd : Fin g → StepDat) : Vec 2 → ℝ :=
  fun X => fieldCellMean (C.formA n g cd X)

/-- The left part of length `p` of step data of length `g` (default beyond `g`). -/
def leftDat {g : ℕ} (cd : Fin g → StepDat) (p : ℕ) : Fin p → StepDat :=
  fun i => if h : i.val < g then cd ⟨i.val, h⟩ else dflt

/-- The right part, from position `p₂`, of length `p₁`. -/
def rightDat {g : ℕ} (cd : Fin g → StepDat) (p₂ p₁ : ℕ) : Fin p₁ → StepDat :=
  fun i => if h : p₂ + i.val < g then cd ⟨p₂ + i.val, h⟩ else dflt

/-- The `C_j^{(p₁)} L_{n-j}^{(p₂)}` term along step data of length `g`. -/
def formCL (n j p₁ p₂ g : ℕ) (cd : Fin g → StepDat) : Vec 2 → Vec 2 → ℝ :=
  fun X z => ∑ m ∈ Finset.range (j + 1), ∑ α : DerivativeWord2 m,
    C.T p₁ (rightDat cd p₂ p₁) j m α C.t X z *
      orderedDerivative α (C.formM (n - j) p₂ (leftDat cd p₂)) X

/-- The scalar cell source along step data. -/
def formS (n g : ℕ) (cd : Fin g → StepDat) : Vec 2 → Vec 2 → ℝ :=
  fun X z => -(C.formA n g cd X z - C.formM n g cd X) +
    ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal g, C.formCL n j p.1 p.2 g cd X z

end Ctx
end

end AVRegularity.Providers.PathDecomp
end
end
end

section
/-! Regularity of the explicit formulas: the values are good fields, the source flux is a
polynomial in `ε` with good coefficients, `formA` is a good field and `formM` is smooth. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- The product of two good fields. -/
theorem GoodField.mul {r : ℕ} {a b : Vec 2 → Vec 2 → ℝ} (ha : GoodField r a) (hb : GoodField r b) :
    GoodField r (fun X z => a X z * b X z) :=
  ⟨ha.1.mul hb.1, fun X n x => by simp [ha.2 X n x, hb.2 X n x]⟩

theorem GoodField.congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℕ}
    {Φ Ψ : Vec 2 → Vec 2 → E} (hΦ : GoodField r Φ) (h : ∀ X z, Φ X z = Ψ X z) :
    GoodField r Ψ := by
  have : Φ = Ψ := funext fun X => funext fun z => h X z
  exact this ▸ hΦ

theorem GoodField.sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℕ}
    {Φ Ψ : Vec 2 → Vec 2 → E} (hΦ : GoodField r Φ) (hΨ : GoodField r Ψ) :
    GoodField r (fun X z => Φ X z - Ψ X z) :=
  (hΦ.add hΨ.neg).congr fun X z => by simp [sub_eq_add_neg]

/-- Multiplication of an `ε`-polynomial by a good scalar field. -/
theorem EpsPoly.mulGood {q r : ℕ} {a : Vec 2 → Vec 2 → ℝ} (ha : GoodField r a)
    {Ψ : ℝ → Vec 2 → Vec 2 → ℝ} (h : EpsPoly False q r Ψ) :
    EpsPoly False q r (fun ε X z => a X z * Ψ ε X z) := by
  obtain ⟨P, hP, hz, he⟩ := h
  refine ⟨fun i X z => a X z * P i X z, fun i => ⟨ha.mul (hP i).1, fun h => h.elim⟩,
    fun i hi X z => by simp [hz i hi], fun ε X z => ?_⟩
  show a X z * Ψ ε X z = _
  rw [he, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_eq_mul]; ring

end AVRegularity

namespace AVRegularity.Providers.PathDecomp

/-- `ε`-polynomials are smooth in `ε`. -/
theorem EpsPoly.contDiff_eps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : Prop}
    {q r : ℕ} {Ψ : ℝ → Vec 2 → Vec 2 → E} (h : EpsPoly c q r Ψ) (X z : Vec 2) (n : ℕ∞) :
    ContDiff ℝ n (fun ε => Ψ ε X z) := by
  obtain ⟨P, -, -, he⟩ := h
  have : (fun ε => Ψ ε X z) = fun ε => ∑ i ∈ Finset.range (q + 1), ε ^ i • P i X z :=
    funext fun ε => he ε X z
  rw [this]
  exact ContDiff.sum fun i _ => (contDiff_id.pow i).smul contDiff_const

/-- The coefficient fields of a step datum are good at time `t`. -/
def GoodDat (r : ℕ) (t : ℝ) (sd : StepDat) : Prop :=
  ∀ d α κ, GoodField r (fun X z => sd.2 d α t X z κ)

namespace Ctx

variable (C : Ctx)

/-- The arrays `T` are good at the context time. -/
def GoodT (r : ℕ) : Prop :=
  ∀ g (cd : Fin g → StepDat) k m (α : DerivativeWord2 m),
    GoodField r (fun X z => C.T g cd k m α C.t X z)

theorem goodField_valF {r : ℕ} (hT : C.GoodT r) (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀) (k g : ℕ)
    (cd : Fin g → StepDat) : GoodField r (C.valF k g cd) := by
  refine GoodField.sum _ fun m _ => GoodField.sum _ fun α _ => ?_
  have hd : ContDiff ℝ (r : ℕ∞) (orderedDerivative α C.g₀) :=
    (orderedDerivative_contDiff α hg₀).of_le (by exact_mod_cast le_top)
  have := (hT g cd k m α).mulX hd
  refine ⟨?_, ?_⟩
  · have e : Function.uncurry (fun X z => C.T g cd k m α C.t X z * orderedDerivative α C.g₀ X) =
        Function.uncurry (fun X z => orderedDerivative α C.g₀ X • C.T g cd k m α C.t X z) := by
      funext p; simp [smul_eq_mul, mul_comm]
    rw [e]; exact this.1
  · intro X n x
    simp [(hT g cd k m α).2 X n x]

theorem epsPoly_fluxS {r : ℕ} (hT : C.GoodT (r + 1 + C.D)) (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀)
    (k g : ℕ) (cd : Fin (g + 1) → StepDat) (hcd : GoodDat (r + 1 + C.D) C.t (cd (Fin.last g)))
    (κ : Fin 2) : EpsPoly False C.D (r + 1) (fun ε => C.fluxS k g cd ε κ) := by
  unfold fluxS
  refine EpsPoly.sum _ fun d _ => ?_
  by_cases hd : d.1 ≤ (cd (Fin.last g)).1
  · simp only [hd, ite_true]
    refine EpsPoly.sum _ fun α _ => ?_
    have hdm : d.1 - 1 ≤ C.D := by have := (Finset.mem_Icc.mp d.2).2; omega
    have hv : CoefField False (r + 1 + (d.1 - 1)) (C.valF k g (Fin.init cd)) :=
      ⟨(C.goodField_valF hT hg₀ k g _).mono (by omega), fun h => h.elim⟩
    have hw := (EpsPoly.dEpsWord C.η α (EpsPoly.const hv)).mono_deg (q' := C.D) (by omega)
    exact (hw.mulGood ((hcd d.1 α κ).mono (by omega)))
  · simp only [hd, ite_false]
    exact EpsPoly.zero

theorem epsPoly_opS {r : ℕ} (hT : C.GoodT (r + 1 + C.D)) (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀)
    (k g : ℕ) (cd : Fin (g + 1) → StepDat) (hcd : GoodDat (r + 1 + C.D) C.t (cd (Fin.last g))) :
    EpsPoly False (C.D + 1) r (fun ε => C.opS k g cd ε) := by
  unfold opS
  exact EpsPoly.sum _ fun κ _ => (C.epsPoly_fluxS hT hg₀ k g cd hcd κ).dEps C.η κ

/-- The `ε`-Taylor coefficients of `opS` are good fields. -/
theorem goodField_iteratedDeriv_opS {r : ℕ} (hT : C.GoodT (r + 1 + C.D))
    (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀) (k g : ℕ) (cd : Fin (g + 1) → StepDat)
    (hcd : GoodDat (r + 1 + C.D) C.t (cd (Fin.last g))) (j : ℕ) :
    GoodField r (fun X z => iteratedDeriv j (fun ε => C.opS k g cd ε X z) 0) := by
  obtain ⟨P, hP, hz, he⟩ := C.epsPoly_opS hT hg₀ k g cd hcd
  have e : ∀ X z, iteratedDeriv j (fun ε => C.opS k g cd ε X z) 0 =
      if j ≤ C.D + 1 then (j.factorial : ℝ) • P j X z else 0 := by
    intro X z
    have : (fun ε => C.opS k g cd ε X z) = fun ε => ∑ i ∈ Finset.range (C.D + 1 + 1), ε ^ i • P i X z :=
      funext fun ε => he ε X z
    rw [this, iteratedDeriv_epsPoly]
  have e' : (fun X z => iteratedDeriv j (fun ε => C.opS k g cd ε X z) 0) =
      fun X z => if j ≤ C.D + 1 then (j.factorial : ℝ) • P j X z else 0 := by
    funext X z; exact e X z
  rw [e']
  by_cases hj : j ≤ C.D + 1
  · simp only [hj, ite_true]; exact (hP j).1.smul _
  · simp only [hj, ite_false]; exact GoodField.zero

/-- The context regularity of the metric and drift. -/
def GoodGv (r : ℕ) : Prop :=
  (∀ a b, ContDiff ℝ (r : ℕ∞) (fun X => C.G C.t X a b)) ∧
    ∀ κ, GoodField r (fun (_ z : Vec 2) => C.v C.t z κ)

theorem goodField_cellB1 {r : ℕ} (hGv : C.GoodGv (r + 2)) {Φ : Vec 2 → Vec 2 → ℝ}
    (hΦ : GoodField (r + 2) Φ) : GoodField r (cellB1 C.η C.G C.v C.t Φ) := by
  have hs : ∀ j, GoodField (r + 1) (slowPartial j Φ) := fun j => hΦ.slowPartial j
  have hf : ∀ j, GoodField (r + 1) (fastPartial j Φ) := fun j => hΦ.fastPartial j
  refine GoodField.sub ?_ ?_
  · refine GoodField.sum _ fun κ _ => ?_
    have h1 : GoodField r (fun X z => Real.sqrt C.η * C.v C.t z κ) :=
      ((hGv.2 κ).mono (by omega)).smul (Real.sqrt C.η) |>.congr fun _ _ => by simp [smul_eq_mul]
    exact (h1.mul ((hs κ).mono (by omega))).congr fun _ _ => by simp [smul_eq_mul]
  · refine GoodField.smul _ (GoodField.sum _ fun a _ => GoodField.sum _ fun b _ => ?_)
    refine GoodField.add ?_ ?_
    · exact (((hs b).fastPartial a).mulX ((hGv.1 a b).of_le (by exact_mod_cast (by omega)))).congr
        fun _ _ => rfl
    · exact (((hf b).mulX ((hGv.1 a b).of_le (by exact_mod_cast (by omega)))).slowPartial a)

theorem goodField_cellB2 {r : ℕ} (hGv : C.GoodGv (r + 2)) {Φ : Vec 2 → Vec 2 → ℝ}
    (hΦ : GoodField (r + 2) Φ) : GoodField r (cellB2 C.η C.G C.t Φ) := by
  refine GoodField.neg (GoodField.smul _ (GoodField.sum _ fun a _ => GoodField.sum _ fun b _ => ?_))
  exact ((hΦ.slowPartial b).mulX ((hGv.1 a b).of_le (by exact_mod_cast (by omega)))).slowPartial a

theorem goodField_formA {r : ℕ} (hD : 2 ≤ C.D) (hT : C.GoodT (r + 1 + C.D))
    (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀) (hGv : C.GoodGv (r + 2)) (n : ℕ) :
    ∀ (g : ℕ) (cd : Fin g → StepDat), (∀ i, GoodDat (r + 1 + C.D) C.t (cd i)) →
      GoodField r (C.formA n g cd)
  | 0, cd, _ => by
      have hv : ∀ k, GoodField (r + 2) (C.valF k 0 cd) := fun k =>
        (C.goodField_valF hT hg₀ k 0 cd).mono (by omega)
      refine (C.goodField_cellB1 hGv (hv _)).add ?_
      by_cases h2 : 2 ≤ n
      · simpa [h2] using C.goodField_cellB2 hGv (hv (n - 2))
      · simpa [h2] using (GoodField.zero (r := r) (E := ℝ))
  | g + 1, cd, hcd => by
      have hv : ∀ k, GoodField (r + 2) (C.valF k (g + 1) cd) := fun k =>
        (C.goodField_valF hT hg₀ k (g + 1) cd).mono (by omega)
      refine GoodField.sub ((C.goodField_cellB1 hGv (hv _)).add ?_) ?_
      · by_cases h2 : 2 ≤ n
        · simpa [h2] using C.goodField_cellB2 hGv (hv (n - 2))
        · simpa [h2] using (GoodField.zero (r := r) (E := ℝ))
      · exact GoodField.sum _ fun j _ =>
          (C.goodField_iteratedDeriv_opS hT hg₀ (n - j) g cd (hcd _) j).smul _

theorem contDiff_formM {r : ℕ} (hD : 2 ≤ C.D) (hT : C.GoodT (r + 1 + C.D))
    (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀) (hGv : C.GoodGv (r + 2)) (n g : ℕ)
    (cd : Fin g → StepDat) (hcd : ∀ i, GoodDat (r + 1 + C.D) C.t (cd i)) :
    ContDiff ℝ (r : ℕ∞) (C.formM n g cd) :=
  contDiff_fieldCellMean (C.goodField_formA hD hT hg₀ hGv n g cd hcd).1

end Ctx

end AVRegularity.Providers.PathDecomp
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.PathDecomp

/-! The value of a path-candidate array on a single-component test field.

For the test field `a = Pi.single w (g₀ • e)`, the value of the path-candidate array of grade `g`
and degree `k` is the sum, over the walks `q` of length `g` from `w`, of the scalar value along
the step data of `q` times the composite map of `q` applied to `e`. -/

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {hs : ι → Type} [∀ i, NormedAddCommGroup (hs i)]
  [∀ i, NormedSpace ℝ (hs i)]

/-- The walks of length `g` from `w`, with their targets. -/
abbrev WalkFrom (F : FamData ι hs) (g : ℕ) (w : ι) : Type := Σ v : ι, F.Walk g w v

/-- The vector of a walk: `Pi.single (target) (composite map e)`. -/
def walkVec (F : FamData ι hs) {g : ℕ} {w : ι} (e : hs w) (p : WalkFrom F g w) : ∀ i, hs i :=
  Pi.single p.1 (F.compMap p.2 e)

/-- A sum over walks from `w` of scalars times walk vectors, read at a component. -/
theorem sum_walkVec_apply (F : FamData ι hs) {g : ℕ} {w : ι} (e : hs w)
    (c : WalkFrom F g w → ℝ) (v : ι) :
    (∑ p : WalkFrom F g w, c p • walkVec F e p) v = ∑ q : F.Walk g w v, c ⟨v, q⟩ • F.compMap q e := by
  rw [Finset.sum_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single v]
  · refine Finset.sum_congr rfl fun q _ => ?_
    simp [walkVec]
  · intro b _ hb
    refine Finset.sum_eq_zero fun q _ => ?_
    simp [walkVec, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ v) h

/-- Ordered derivatives of a single-component test field. -/
theorem orderedDerivative_single {w : ι} (e : hs w) {g₀ : Vec 2 → ℝ}
    (hg₀ : ContDiff ℝ (⊤ : ℕ∞) g₀) {m : ℕ} (α : DerivativeWord2 m) :
    orderedDerivative α (fun Y => (Pi.single w (g₀ Y • e) : ∀ i, hs i)) =
      fun Y => Pi.single w (orderedDerivative α g₀ Y • e) := by
  let L : Unit → ℝ →L[ℝ] (∀ i, hs i) := fun _ =>
    (ContinuousLinearMap.id ℝ ℝ).smulRight (Pi.single w e : ∀ i, hs i)
  have h := orderedDerivative_clm_sum (Finset.univ : Finset Unit) L α (β := fun _ => g₀)
    (fun _ _ => hg₀.of_le (by exact_mod_cast le_top))
  have e1 : (fun Y => (Pi.single w (g₀ Y • e) : ∀ i, hs i)) =
      fun Y => ∑ i ∈ (Finset.univ : Finset Unit), L i (g₀ Y) := by
    funext Y; simp [L, Pi.single_smul]
  rw [e1, h]
  funext Y; simp [L, Pi.single_smul]

/-- **Value of a path-candidate array.** -/
theorem liftApply_cand (F : FamData ι hs) (C : Ctx) (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀)
    {w : ι} (e : hs w) (k g : ℕ) (X z : Vec 2) :
    liftApply k (cand F C.T g k) (fun _ Y => Pi.single w (C.g₀ Y • e)) C.t X z =
      ∑ p : WalkFrom F g w, C.valF k g (F.walkDat p.2) X z • walkVec F e p := by
  funext v
  rw [sum_walkVec_apply]
  simp only [liftApply, orderedDerivative_single e hg₀]
  have hcol : ∀ m (α : DerivativeWord2 m), ∑ u : ι, cand F C.T g k m α C.t X z v u
      ((Pi.single w (orderedDerivative α C.g₀ X • e) : ∀ i, hs i) u) =
      ∑ q : F.Walk g w v, (C.T g (F.walkDat q) k m α C.t X z * orderedDerivative α C.g₀ X) •
        F.compMap q e := by
    intro m α
    rw [Finset.sum_eq_single w]
    · simp only [Pi.single_eq_same, cand, sum_apply, smul_apply, map_smul]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_smul, mul_comm]
    · intro u _ hu; simp [hu]
    · intro h; exact absurd (Finset.mem_univ w) h
  simp only [hcol, Ctx.valF, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]
end

/-! The cell operator `A_n` of a path-candidate array on a single-component test field: the sum
over the walks `q` of the scalar `formA` along the step data of `q` times the walk vector. The
source flux of the family splits each walk at its last step (`HasFamFlux`). -/

section
theorem EpsPoly.goodField_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : Prop}
    {q r : ℕ} {Ψ : ℝ → Vec 2 → Vec 2 → E} (h : EpsPoly c q r Ψ) (ε : ℝ) : GoodField r (Ψ ε) := by
  obtain ⟨P, hP, -, he⟩ := h
  exact (GoodField.sum _ fun i _ => (hP i).1.smul (ε ^ i)).congr fun X z => (he ε X z).symm

theorem ite_sum_zero {M : Type*} [AddCommMonoid M] {κ : Type*} (p : Prop) [Decidable p]
    (s : Finset κ) (f : κ → M) :
    (if p then ∑ i ∈ s, f i else 0) = ∑ i ∈ s, if p then f i else 0 := by
  split_ifs <;> simp

variable {ι : Type} [Fintype ι] [DecidableEq ι] {hs : ι → Type} [∀ i, NormedAddCommGroup (hs i)]
  [∀ i, NormedSpace ℝ (hs i)]

/-- The value field of a path-candidate array. -/
def valField (F : FamData ι hs) (C : Ctx) {w : ι} (e : hs w) (k g : ℕ) :
    Vec 2 → Vec 2 → ∀ i, hs i :=
  fun X z => ∑ p : WalkFrom F g w, C.valF k g (F.walkDat p.2) X z • walkVec F e p

/-- The walk vectors as continuous linear maps `ℝ → ∏ hs`. -/
def walkL (F : FamData ι hs) {g : ℕ} {w : ι} (e : hs w) (p : WalkFrom F g w) :
    ℝ →L[ℝ] ∀ i, hs i :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (walkVec F e p)

omit [Fintype ι] in
theorem walkL_apply (F : FamData ι hs) {g : ℕ} {w : ι} (e : hs w) (p : WalkFrom F g w) (c : ℝ) :
    walkL F e p c = c • walkVec F e p := rfl

/-- **Source flux of a value field.** -/
theorem sourceFlux_valField {Dm : ℕ} (F : FamData ι hs) (Q : LiftOperatorData ι hs Dm)
    (hQ : HasFamFlux Q F) (C : Ctx) (hDm : C.D = Dm) {r : ℕ} (hT : C.GoodT (r + Dm))
    (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀) {w : ι} (e : hs w) (k g : ℕ) (ε : ℝ) (κ : Fin 2) :
    sourceFlux Q.edge C.η ε C.t (valField F C e k g) κ =
      fun X z => ∑ p : WalkFrom F (g + 1) w, C.fluxS k g (F.walkDat p.2) ε κ X z • walkVec F e p := by
  subst hDm
  funext X z
  funext v
  rw [hQ, sum_walkVec_apply]
  -- the word derivatives of the value field, read at a component
  have hdw : ∀ (d : Finset.Icc 2 C.D) (α : DerivativeWord2 (d.1 - 1)) (u : ι),
      dEpsWord C.η ε α (valField F C e k g) X z u =
        ∑ q' : F.Walk g w u, dEpsWord C.η ε α (C.valF k g (F.walkDat q')) X z • F.compMap q' e := by
    intro d α u
    have hgood : ∀ p ∈ (Finset.univ : Finset (WalkFrom F g w)),
        GoodField (d.1 - 1) (C.valF k g (F.walkDat p.2)) := fun p _ =>
      (C.goodField_valF hT hg₀ k g _).mono (by have := (Finset.mem_Icc.mp d.2).2; omega)
    have h := dEpsWord_clm_sum Finset.univ (walkL F e) α hgood C.η ε
    simp only [walkL_apply] at h
    rw [show valField F C e k g = fun X z => ∑ p : WalkFrom F g w,
        C.valF k g (F.walkDat p.2) X z • walkVec F e p from rfl, h]
    exact sum_walkVec_apply F e _ u
  simp only [hdw, map_sum, map_smul, Finset.smul_sum, smul_smul]
  show _ = ∑ q : (Σ u : ι, F.Walk g w u × F.Γ v u),
    C.fluxS k g (F.walkDat (g := g + 1) q) ε κ X z • F.compMap (g := g + 1) q e
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Fintype.sum_prod_type]
  simp only [FamData.walkDat, FamData.compMap, ContinuousLinearMap.comp_apply]
  simp only [Ctx.fluxS, Fin.snoc_last, Fin.init_snoc, Finset.sum_smul, ite_smul, zero_smul,
    Finset.sum_smul]
  simp only [ite_sum_zero]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => arg 2; ext γ; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext γ; arg 2; ext d; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]

omit [Fintype ι] [DecidableEq ι] in
/-- The step data of a walk inherits the regularity of the identities. -/
theorem goodDat_walkDat (F : FamData ι hs) {R : ℕ} {t : ℝ}
    (hdat : ∀ v u (γ : F.Γ v u), GoodDat R t (F.dat v u γ)) :
    ∀ {g : ℕ} {w v : ι} (q : F.Walk g w v) (i : Fin g), GoodDat R t (F.walkDat q i)
  | 0, _, _, _, i => Fin.elim0 i
  | _ + 1, _, v, ⟨u, q, γ⟩, i => by
      simp only [FamData.walkDat]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hdat v u γ
      · simpa using goodDat_walkDat F hdat q j

/-- **The cell operator of a path-candidate array.** -/
theorem liftA_cand {Dm : ℕ} (F : FamData ι hs) (Q : LiftOperatorData ι hs Dm)
    (hQ : HasFamFlux Q F) (C : Ctx) (hη : C.η = Q.η) (hG : C.G = Q.G) (hv : C.v = Q.v)
    (hDm : C.D = Dm) (hD2 : 2 ≤ Dm) {r : ℕ} (hT : C.GoodT (r + 1 + Dm))
    (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀) (hGv : C.GoodGv (r + 2))
    (hdat : ∀ v u (γ : F.Γ v u), GoodDat (r + 1 + Dm) C.t (F.dat v u γ)) {w : ι} (e : hs w)
    (g n : ℕ) (X z : Vec 2) :
    liftA Q (cand F C.T) (fun _ Y => Pi.single w (C.g₀ Y • e)) g n C.t X z =
      ∑ p : WalkFrom F g w, C.formA n g (F.walkDat p.2) X z • walkVec F e p := by
  have hval : ∀ k g', liftApply k (cand F C.T g' k) (fun _ Y => Pi.single w (C.g₀ Y • e)) C.t =
      valField F C e k g' := fun k g' => funext fun X => funext fun z => liftApply_cand F C hg₀ e k g' X z
  have hgood2 : ∀ k g', ∀ p ∈ (Finset.univ : Finset (WalkFrom F g' w)),
      GoodField 2 (C.valF k g' (F.walkDat p.2)) := fun k g' p _ =>
    (C.goodField_valF hT hg₀ k g' _).mono (by omega)
  have hG1 : ∀ a b, ContDiff ℝ (1 : ℕ∞) (fun X => Q.G C.t X a b) := fun a b => by
    rw [← hG]; exact (hGv.1 a b).of_le (by exact_mod_cast (by omega))
  have hB1 : ∀ k g', cellB1 Q.η Q.G Q.v C.t (valField F C e k g') X z =
      ∑ p : WalkFrom F g' w, cellB1 C.η C.G C.v C.t (C.valF k g' (F.walkDat p.2)) X z •
        walkVec F e p := by
    intro k g'
    have h := cellB1_clm_sum Finset.univ (walkL F e) (hgood2 k g') Q.η Q.G Q.v C.t hG1 X z
    simp only [walkL_apply] at h
    rw [← hη, ← hG, ← hv] at h ⊢
    exact h
  have hB2 : ∀ k g', cellB2 Q.η Q.G C.t (valField F C e k g') X z =
      ∑ p : WalkFrom F g' w, cellB2 C.η C.G C.t (C.valF k g' (F.walkDat p.2)) X z •
        walkVec F e p := by
    intro k g'
    have h := cellB2_clm_sum Finset.univ (walkL F e) (hgood2 k g') Q.η Q.G C.t hG1 X z
    simp only [walkL_apply] at h
    rw [← hη, ← hG] at h ⊢
    exact h
  cases g with
  | zero =>
      by_cases h2 : 2 ≤ n
      · simp only [liftA, hval, hB1, hB2, Ctx.formA, ↓reduceIte, sub_zero, h2, add_smul,
          Finset.sum_add_distrib]
      · simp only [liftA, hval, hB1, Ctx.formA, ↓reduceIte, sub_zero, h2, add_zero]
  | succ g' =>
      -- the source part
      have hsrc : ∀ j, sourceCoeff Q.edge Q.η j C.t (valField F C e (n - j) g') X z =
          ∑ p : WalkFrom F (g' + 1) w, (((j.factorial : ℝ)⁻¹) •
            iteratedDeriv j (fun ε => C.opS (n - j) g' (F.walkDat p.2) ε X z) 0) • walkVec F e p := by
        intro j
        have hflux := sourceFlux_valField F Q hQ C hDm (r := r + 1) hT hg₀ e (n - j) g'
        have hgood1 : ∀ (ε : ℝ) (κ : Fin 2), ∀ p ∈ (Finset.univ : Finset (WalkFrom F (g' + 1) w)),
            GoodField 1 (C.fluxS (n - j) g' (F.walkDat p.2) ε κ) := fun ε κ p _ =>
          (EpsPoly.goodField_at (C.epsPoly_fluxS (r := r) (by rw [hDm]; exact hT) hg₀ (n - j) g'
            (F.walkDat p.2) (by rw [hDm]; exact goodDat_walkDat F hdat p.2 _) κ) ε).mono (by omega)
        have hop : ∀ ε, sourceOp Q.edge Q.η ε C.t (valField F C e (n - j) g') X z =
            ∑ p : WalkFrom F (g' + 1) w, C.opS (n - j) g' (F.walkDat p.2) ε X z • walkVec F e p := by
          intro ε
          simp only [sourceOp]
          rw [← hη]
          simp only [hflux]
          have hd : ∀ κ, dEps C.η ε κ (fun X z => ∑ p : WalkFrom F (g' + 1) w,
              C.fluxS (n - j) g' (F.walkDat p.2) ε κ X z • walkVec F e p) X z =
              ∑ p : WalkFrom F (g' + 1) w,
                dEps C.η ε κ (C.fluxS (n - j) g' (F.walkDat p.2) ε κ) X z • walkVec F e p := by
            intro κ
            have h := dEps_clm_sum Finset.univ (walkL F e) (hgood1 ε κ) C.η ε κ
            simp only [walkL_apply] at h
            exact congrFun (congrFun h X) z
          simp only [hd, Ctx.opS, Finset.sum_smul]
          rw [Finset.sum_comm]
        simp only [sourceCoeff, hop]
        have hcd : ∀ p ∈ (Finset.univ : Finset (WalkFrom F (g' + 1) w)),
            ContDiff ℝ (j : ℕ∞) (fun ε => C.opS (n - j) g' (F.walkDat p.2) ε X z) := fun p _ =>
          EpsPoly.contDiff_eps (C.epsPoly_opS (r := r) (by rw [hDm]; exact hT) hg₀ (n - j) g'
            (F.walkDat p.2) (by rw [hDm]; exact goodDat_walkDat F hdat p.2 _)) X z _
        have h := iteratedDeriv_clm_sum Finset.univ (walkL F e) hcd 0
        simp only [walkL_apply] at h
        rw [h, Finset.smul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [smul_smul, smul_eq_mul]
      simp only [liftA, Nat.add_sub_cancel, hval, hB1, hB2, hsrc,
        show (g' + 1 = 0) = False from propext ⟨fun h => by omega, fun h => h.elim⟩, ite_false,
        Ctx.formA, hDm]
      rw [Finset.sum_comm (s := Finset.range (min Dm n + 1))]
      by_cases h2 : 2 ≤ n
      · simp only [h2, ite_true, sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_smul]
      · simp only [h2, ite_false, add_zero, sub_smul, Finset.sum_sub_distrib, Finset.sum_smul]
end

/-! The cell mean and the cell source of a path-candidate array on a single-component test field.

The `C_j^{(p₁)} L_{n-j}^{(p₂)}` terms compose a walk of length `p₂` (the mean) with a walk of length
`p₁` (the lift): their sum over composable pairs is the sum over walks of length `p₂ + p₁`, split at
`p₂` (`sum_walk_append`, `compMap_append`). -/

section
theorem Ctx.leftDat_append {p₂ p₁ : ℕ} (a : Fin p₂ → StepDat) (b : Fin p₁ → StepDat) :
    Ctx.leftDat (Fin.append a b) p₂ = a := by
  funext i
  simp only [Ctx.leftDat, show i.val < p₂ + p₁ by omega, dite_true]
  exact Fin.append_left a b i

theorem Ctx.rightDat_append {p₂ p₁ : ℕ} (a : Fin p₂ → StepDat) (b : Fin p₁ → StepDat) :
    Ctx.rightDat (Fin.append a b) p₂ p₁ = b := by
  funext i
  simp only [Ctx.rightDat, show p₂ + i.val < p₂ + p₁ by omega, dite_true]
  exact Fin.append_right a b i

variable {ι : Type} [Fintype ι] [DecidableEq ι] {hs : ι → Type} [∀ i, NormedAddCommGroup (hs i)]
  [∀ i, NormedSpace ℝ (hs i)]

/-- Summation over walks of equal lengths. -/
theorem sum_walkFrom_cast (F : FamData ι hs) {w : ι} (e : hs w) {a b : ℕ} (h : a = b)
    (Φ : (len : ℕ) → (Fin len → StepDat) → ℝ) :
    ∑ q : WalkFrom F a w, Φ a (F.walkDat q.2) • walkVec F e q =
      ∑ q : WalkFrom F b w, Φ b (F.walkDat q.2) • walkVec F e q := by
  subst h; rfl

variable [∀ i, FiniteDimensional ℝ (hs i)]

/-- **The cell mean of a path-candidate array.** -/
theorem liftMean_cand {Dm : ℕ} (F : FamData ι hs) (Q : LiftOperatorData ι hs Dm)
    (hQ : HasFamFlux Q F) (C : Ctx) (hη : C.η = Q.η) (hG : C.G = Q.G) (hv : C.v = Q.v)
    (hDm : C.D = Dm) (hD2 : 2 ≤ Dm) {r : ℕ} (hT : C.GoodT (r + 1 + Dm))
    (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀) (hGv : C.GoodGv (r + 2))
    (hdat : ∀ v u (γ : F.Γ v u), GoodDat (r + 1 + Dm) C.t (F.dat v u γ)) {w : ι} (e : hs w)
    (g n : ℕ) (X : Vec 2) :
    liftMean Q (cand F C.T) (fun _ Y => Pi.single w (C.g₀ Y • e)) g n C.t X =
      ∑ p : WalkFrom F g w, C.formM n g (F.walkDat p.2) X • walkVec F e p := by
  simp only [liftMean, liftA_cand F Q hQ C hη hG hv hDm hD2 hT hg₀ hGv hdat e g n X]
  have hc : ∀ p ∈ (Finset.univ : Finset (WalkFrom F g w)),
      Continuous (C.formA n g (F.walkDat p.2) X) := fun p _ =>
    (C.goodField_formA (r := r) (by rw [hDm]; exact hD2) (by rw [hDm]; exact hT) hg₀ hGv n g _
      (by rw [hDm]; exact goodDat_walkDat F hdat p.2)).continuous_slice X
  have h := fieldCellMean_clm_sum Finset.univ (walkL F e) hc
  simp only [walkL_apply] at h
  exact h

/-- **A `C_j L` term of a path-candidate array.** -/
theorem liftApply_liftMean_cand {Dm : ℕ} (F : FamData ι hs) (Q : LiftOperatorData ι hs Dm)
    (hQ : HasFamFlux Q F) (C : Ctx) (hη : C.η = Q.η) (hG : C.G = Q.G) (hv : C.v = Q.v)
    (hDm : C.D = Dm) (hD2 : 2 ≤ Dm) {r : ℕ} (hT : C.GoodT (r + 1 + Dm))
    (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀) (hGv : C.GoodGv (r + 2))
    (hdat : ∀ v u (γ : F.Γ v u), GoodDat (r + 1 + Dm) C.t (F.dat v u γ)) {w : ι} (e : hs w)
    (n j p₁ p₂ : ℕ) (hj : j ≤ r) (X z : Vec 2) :
    liftApply j (cand F C.T p₁ j)
        (liftMean Q (cand F C.T) (fun _ Y => Pi.single w (C.g₀ Y • e)) p₂ (n - j)) C.t X z =
      ∑ q : WalkFrom F (p₂ + p₁) w, C.formCL n j p₁ p₂ (p₂ + p₁) (F.walkDat q.2) X z •
        walkVec F e q := by
  have hM : liftMean Q (cand F C.T) (fun _ Y => Pi.single w (C.g₀ Y • e)) p₂ (n - j) C.t =
      fun X => ∑ p : WalkFrom F p₂ w, C.formM (n - j) p₂ (F.walkDat p.2) X • walkVec F e p :=
    funext fun X => liftMean_cand F Q hQ C hη hG hv hDm hD2 hT hg₀ hGv hdat e p₂ (n - j) X
  have hsm : ∀ p ∈ (Finset.univ : Finset (WalkFrom F p₂ w)), ∀ m ≤ j,
      ContDiff ℝ (m : ℕ∞) (C.formM (n - j) p₂ (F.walkDat p.2)) := fun p _ m hm =>
    (C.contDiff_formM (r := r) (by rw [hDm]; exact hD2) (by rw [hDm]; exact hT) hg₀ hGv (n - j) p₂ _
      (by rw [hDm]; exact goodDat_walkDat F hdat p.2)).of_le (by exact_mod_cast (by omega))
  have hod : ∀ m ≤ j, ∀ (α : DerivativeWord2 m) (u : ι),
      orderedDerivative α (liftMean Q (cand F C.T) (fun _ Y => Pi.single w (C.g₀ Y • e)) p₂ (n - j)
        C.t) X u = ∑ q₂ : F.Walk p₂ w u,
          orderedDerivative α (C.formM (n - j) p₂ (F.walkDat q₂)) X • F.compMap q₂ e := by
    intro m hm α u
    rw [hM]
    have h := orderedDerivative_clm_sum Finset.univ (walkL F e) α (fun p hp => hsm p hp m hm)
    simp only [walkL_apply] at h
    rw [h]
    exact sum_walkVec_apply F e _ u
  funext v
  rw [sum_walkVec_apply]
  simp only [liftApply]
  rw [Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl
    fun u _ => by rw [hod m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) α u]]
  simp only [cand, sum_apply, smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  -- the right side, split at `p₂`
  rw [F.sum_walk_append p₂ p₁ w v]
  simp only [F.walkDat_append, Ctx.formCL, Ctx.leftDat_append, Ctx.rightDat_append,
    F.compMap_append, ContinuousLinearMap.comp_apply, Finset.sum_smul]
  -- reorder: (m, α, u, q₁, q₂) ↦ (u, q₂, q₁, m, α)
  conv_lhs => arg 2; ext m; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  conv_lhs => arg 2; ext α; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q₂ _ => ?_
  conv_lhs => arg 2; ext m; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q₁ _ => ?_
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun α _ => ?_
  rw [mul_comm]

/-- **The cell source of a path-candidate array.** -/
theorem liftCellSource_cand {Dm : ℕ} (F : FamData ι hs) (Q : LiftOperatorData ι hs Dm)
    (hQ : HasFamFlux Q F) (C : Ctx) (hη : C.η = Q.η) (hG : C.G = Q.G) (hv : C.v = Q.v)
    (hDm : C.D = Dm) (hD2 : 2 ≤ Dm) {r : ℕ} (hT : C.GoodT (r + 1 + Dm))
    (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀) (hGv : C.GoodGv (r + 2))
    (hdat : ∀ v u (γ : F.Γ v u), GoodDat (r + 1 + Dm) C.t (F.dat v u γ)) {w : ι} (e : hs w)
    (g n : ℕ) (hn : n ≤ r) (X z : Vec 2) :
    liftCellSource Q (cand F C.T) (fun _ Y => Pi.single w (C.g₀ Y • e)) g n C.t X z =
      ∑ p : WalkFrom F g w, C.formS n g (F.walkDat p.2) X z • walkVec F e p := by
  have hCL : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ pp ∈ Finset.HasAntidiagonal.antidiagonal g,
      liftApply j (cand F C.T pp.1 j)
        (liftMean Q (cand F C.T) (fun _ Y => Pi.single w (C.g₀ Y • e)) pp.2 (n - j)) C.t X z =
      ∑ q : WalkFrom F g w, C.formCL n j pp.1 pp.2 g (F.walkDat q.2) X z • walkVec F e q := by
    intro j hj pp hpp
    have hj' : j ≤ r := by have := (Finset.mem_Icc.mp hj).2; omega
    rw [liftApply_liftMean_cand F Q hQ C hη hG hv hDm hD2 hT hg₀ hGv hdat e n j pp.1 pp.2 hj' X z]
    have hlen : pp.2 + pp.1 = g := by
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hpp; omega
    exact sum_walkFrom_cast F e hlen (fun len cd => C.formCL n j pp.1 pp.2 len cd X z)
  simp only [liftCellSource, liftA_cand F Q hQ C hη hG hv hDm hD2 hT hg₀ hGv hdat e g n X z,
    liftMean_cand F Q hQ C hη hG hv hDm hD2 hT hg₀ hGv hdat e g n X]
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun pp hpp => hCL j hj pp hpp]
  simp only [Ctx.formS, add_smul, neg_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.sum_sub_distrib, Finset.sum_smul]
  congr 1
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
end

/-! Chain families at their last vertex.

For a scalar chain coefficient sequence and the test field `Pi.single 0 g₀`, the value at the
last vertex is the scalar value of its `(last ← 0)` entries. The cell source of the path-candidate
array of the chain family of `cd` at the last vertex is `formS cd` (the chain has one walk from `0`
to `last`, with step data `cd` and identity composite map). -/

/-- The value of a scalar chain sequence at the last vertex on `Pi.single 0 g₀`. -/
theorem chain_liftApply_last {g : ℕ} (Cs : LiftCoeff (Fin (g + 1)) (fun _ => ℝ)) {g₀ : Vec 2 → ℝ}
    (hg₀ : ContDiff ℝ (⊤ : ℕ∞) g₀) (k : ℕ) (t : ℝ) (X z : Vec 2) :
    liftApply k Cs (fun _ Y => Pi.single (0 : Fin (g + 1)) (g₀ Y)) t X z (Fin.last g) =
      ∑ m ∈ Finset.range (k + 1), ∑ α : DerivativeWord2 m,
        Cs m α t X z (Fin.last g) 0 1 * orderedDerivative α g₀ X := by
  have e1 : (fun Y => (Pi.single (0 : Fin (g + 1)) (g₀ Y) : Fin (g + 1) → ℝ)) =
      fun Y => Pi.single (0 : Fin (g + 1)) (g₀ Y • (1 : ℝ)) := by
    funext Y; simp
  simp only [liftApply, e1, orderedDerivative_single (hs := fun _ : Fin (g + 1) => ℝ) (1 : ℝ) hg₀]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_eq_single (0 : Fin (g + 1))]
  · simp only [Pi.single_eq_same, smul_eq_mul, mul_one]
    rw [show orderedDerivative α g₀ X = orderedDerivative α g₀ X • (1 : ℝ) by simp, map_smul,
      smul_eq_mul, mul_comm]
    simp
  · intro u _ hu; simp [hu]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The candidate cell source of a chain family at the last vertex. -/
theorem chain_liftCellSource_last {Dm L : ℕ} (cd : Fin L → StepDat)
    (Q : LiftOperatorData (Fin (L + 1)) (fun _ => ℝ) Dm) (hQ : HasFamFlux Q (chainFam cd)) (C : Ctx)
    (hη : C.η = Q.η) (hG : C.G = Q.G) (hv : C.v = Q.v) (hDm : C.D = Dm) (hD2 : 2 ≤ Dm) {r : ℕ}
    (hT : C.GoodT (r + 1 + Dm)) (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀) (hGv : C.GoodGv (r + 2))
    (hcd : ∀ i, GoodDat (r + 1 + Dm) C.t (cd i)) (n : ℕ) (hn : n ≤ r) (X z : Vec 2) :
    liftCellSource Q (cand (chainFam cd) C.T) (fun _ Y => Pi.single (0 : Fin (L + 1)) (C.g₀ Y))
      L n C.t X z (Fin.last L) = C.formS n L cd X z := by
  have hdat : ∀ v u (γ : (chainFam cd).Γ v u), GoodDat (r + 1 + Dm) C.t ((chainFam cd).dat v u γ) :=
    fun v u γ => hcd _
  have e1 : (fun (_ : ℝ) Y => (Pi.single (0 : Fin (L + 1)) (C.g₀ Y) : Fin (L + 1) → ℝ)) =
      fun _ Y => Pi.single (0 : Fin (L + 1)) (C.g₀ Y • (1 : ℝ)) := by
    funext _ Y; simp
  rw [e1, liftCellSource_cand (chainFam cd) Q hQ C hη hG hv hDm hD2 hT hg₀ hGv hdat (1 : ℝ) L n hn X z,
    sum_walkVec_apply, chain_sum_walk]
  have hlast : (Fin.last L).val = (0 : Fin (L + 1)).val + L := by simp
  rw [dite_eq_left_of_eq_true (eq_true hlast), chain_compMap, chain_walkDat]
  simp only [ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
  congr 1
  funext j
  congr 1
  ext
  simp

/-! The slow flux `liftFluxX` of a path-candidate array on a single-component test field: the sum
over the walks of the scalar `formX` along their step data times the walk vectors; for a chain
family at its last vertex, `formX` of its data. -/

section
namespace Ctx

variable (C : Ctx)

/-- The source part of the slow flux along step data. -/
def fluxPartX (n : ℕ) (κ : Fin 2) : (g : ℕ) → (Fin g → StepDat) → Vec 2 → Vec 2 → ℝ
  | 0, _ => fun _ _ => 0
  | g + 1, cd => fun X z => ∑ j ∈ Finset.Icc 1 (min C.D n),
      (Real.sqrt C.η * ((j - 1).factorial : ℝ)⁻¹) *
        iteratedDeriv (j - 1) (fun ε => C.fluxS (n - j) g cd ε κ X z) 0

/-- The scalar slow flux along step data. -/
def formX (n g : ℕ) (cd : Fin g → StepDat) (κ : Fin 2) : Vec 2 → Vec 2 → ℝ :=
  fun X z => ((Real.sqrt C.η * C.v C.t z κ) * C.valF (n - 1) g cd X z
      - Real.sqrt C.η * ∑ j : Fin 2, C.G C.t X κ j * fastPartial j (C.valF (n - 1) g cd) X z)
    + (if 2 ≤ n then -(C.η * ∑ j : Fin 2, C.G C.t X κ j * slowPartial j (C.valF (n - 2) g cd) X z)
      else 0)
    - C.fluxPartX n κ g cd X z

theorem goodField_iteratedDeriv_fluxS {r : ℕ} (hT : C.GoodT (r + 1 + C.D))
    (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀) (k g : ℕ) (cd : Fin (g + 1) → StepDat)
    (hcd : GoodDat (r + 1 + C.D) C.t (cd (Fin.last g))) (κ : Fin 2) (j : ℕ) :
    GoodField (r + 1) (fun X z => iteratedDeriv j (fun ε => C.fluxS k g cd ε κ X z) 0) := by
  obtain ⟨P, hP, hz, he⟩ := C.epsPoly_fluxS hT hg₀ k g cd hcd κ
  have e' : (fun X z => iteratedDeriv j (fun ε => C.fluxS k g cd ε κ X z) 0) =
      fun X z => if j ≤ C.D then (j.factorial : ℝ) • P j X z else 0 := by
    funext X z
    have : (fun ε => C.fluxS k g cd ε κ X z) =
        fun ε => ∑ i ∈ Finset.range (C.D + 1), ε ^ i • P i X z := funext fun ε => he ε X z
    rw [this, iteratedDeriv_epsPoly]
  rw [e']
  by_cases hj : j ≤ C.D
  · simp only [hj, ite_true]; exact (hP j).1.smul _
  · simp only [hj, ite_false]; exact GoodField.zero

theorem goodField_formX {r : ℕ} (hT : C.GoodT (r + 1 + C.D)) (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀)
    (hGv : C.GoodGv (r + 2)) (n g : ℕ) (cd : Fin g → StepDat)
    (hcd : ∀ i, GoodDat (r + 1 + C.D) C.t (cd i)) (κ : Fin 2) : GoodField r (C.formX n g cd κ) := by
  have hv : ∀ k, GoodField (r + 1) (C.valF k g cd) := fun k =>
    (C.goodField_valF hT hg₀ k g cd).mono (by omega)
  have hG : ∀ a b, ContDiff ℝ (r : ℕ∞) (fun X => C.G C.t X a b) := fun a b =>
    (hGv.1 a b).of_le (by exact_mod_cast (by omega))
  refine GoodField.sub (GoodField.add (GoodField.sub ?_ ?_) ?_) ?_
  · have h1 : GoodField r (fun (_ z : Vec 2) => Real.sqrt C.η * C.v C.t z κ) :=
      (((hGv.2 κ).mono (by omega)).smul (Real.sqrt C.η)).congr fun _ _ => by simp [smul_eq_mul]
    exact h1.mul ((hv _).mono (by omega))
  · refine (GoodField.sum (Finset.univ : Finset (Fin 2))
      (Φ := fun j X z => C.G C.t X κ j * fastPartial j (C.valF (n - 1) g cd) X z)
      fun j _ => ?_).smul (Real.sqrt C.η) |>.congr fun X z => by simp [smul_eq_mul]
    exact (((hv (n - 1)).fastPartial j).mulX (hG κ j)).congr fun _ _ => by simp [smul_eq_mul]
  · by_cases h2 : 2 ≤ n
    · simp only [h2, ite_true]
      refine ((GoodField.sum (Finset.univ : Finset (Fin 2))
        (Φ := fun j X z => C.G C.t X κ j * slowPartial j (C.valF (n - 2) g cd) X z)
        fun j _ => ?_).smul C.η).neg.congr fun X z => by simp [smul_eq_mul]
      exact (((hv (n - 2)).slowPartial j).mulX (hG κ j)).congr fun _ _ => by simp [smul_eq_mul]
    · simp only [h2, ite_false]; exact GoodField.zero
  · cases g with
    | zero => exact GoodField.zero
    | succ g' =>
        refine GoodField.sum _ fun j _ => ?_
        have hj := C.goodField_iteratedDeriv_fluxS (r := r) hT hg₀ (n - j) g' cd (hcd _) κ (j - 1)
        exact ((hj.mono (by omega)).smul (Real.sqrt C.η * ((j - 1).factorial : ℝ)⁻¹)).congr
          fun X z => by simp [smul_eq_mul]

end Ctx

variable {ι : Type} [Fintype ι] [DecidableEq ι] {hs : ι → Type} [∀ i, NormedAddCommGroup (hs i)]
  [∀ i, NormedSpace ℝ (hs i)]

/-- **The slow flux of a path-candidate array.** -/
theorem liftFluxX_cand {Dm : ℕ} (F : FamData ι hs) (Q : LiftOperatorData ι hs Dm)
    (hQ : HasFamFlux Q F) (C : Ctx) (hη : C.η = Q.η) (hG : C.G = Q.G) (hv : C.v = Q.v)
    (hDm : C.D = Dm) {r : ℕ} (hT : C.GoodT (r + 1 + Dm))
    (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀)
    (hdat : ∀ v u (γ : F.Γ v u), GoodDat (r + 1 + Dm) C.t (F.dat v u γ)) {w : ι} (e : hs w)
    (g n : ℕ) (X z : Vec 2) (κ : Fin 2) :
    liftFluxX Q (cand F C.T) (fun _ Y => Pi.single w (C.g₀ Y • e)) g n C.t X z κ =
      ∑ p : WalkFrom F g w, C.formX n g (F.walkDat p.2) κ X z • walkVec F e p := by
  have hval : ∀ k g', liftApply k (cand F C.T g' k) (fun _ Y => Pi.single w (C.g₀ Y • e)) C.t =
      valField F C e k g' := fun k g' =>
    funext fun X => funext fun z => liftApply_cand F C hg₀ e k g' X z
  have hgood1 : ∀ k g', ∀ p ∈ (Finset.univ : Finset (WalkFrom F g' w)),
      GoodField 1 (C.valF k g' (F.walkDat p.2)) := fun k g' p _ =>
    (C.goodField_valF hT hg₀ k g' _).mono (by omega)
  have hF : ∀ k g' j, fastPartial j (valField F C e k g') X z =
      ∑ p : WalkFrom F g' w, fastPartial j (C.valF k g' (F.walkDat p.2)) X z • walkVec F e p := by
    intro k g' j
    have h := fastPartial_clm_sum Finset.univ (walkL F e) (hgood1 k g') j X z
    simp only [walkL_apply] at h
    exact h
  have hS : ∀ k g' j, slowPartial j (valField F C e k g') X z =
      ∑ p : WalkFrom F g' w, slowPartial j (C.valF k g' (F.walkDat p.2)) X z • walkVec F e p := by
    intro k g' j
    have h := slowPartial_clm_sum Finset.univ (walkL F e) (hgood1 k g') j X z
    simp only [walkL_apply] at h
    exact h
  have hV : ∀ k g', valField F C e k g' X z =
      ∑ p : WalkFrom F g' w, C.valF k g' (F.walkDat p.2) X z • walkVec F e p := fun _ _ => rfl
  have hmain : ((Real.sqrt C.η * C.v C.t z κ) • valField F C e (n - 1) g X z
      - Real.sqrt C.η • ∑ j : Fin 2, C.G C.t X κ j • fastPartial j (valField F C e (n - 1) g) X z)
      + (if 2 ≤ n then -(C.η • ∑ j : Fin 2,
          C.G C.t X κ j • slowPartial j (valField F C e (n - 2) g) X z) else 0) =
      ∑ p : WalkFrom F g w, (((Real.sqrt C.η * C.v C.t z κ) * C.valF (n - 1) g (F.walkDat p.2) X z
        - Real.sqrt C.η * ∑ j : Fin 2,
          C.G C.t X κ j * fastPartial j (C.valF (n - 1) g (F.walkDat p.2)) X z)
        + (if 2 ≤ n then -(C.η * ∑ j : Fin 2,
          C.G C.t X κ j * slowPartial j (C.valF (n - 2) g (F.walkDat p.2)) X z) else 0)) •
          walkVec F e p := by
    simp only [hV, hF, hS, Finset.smul_sum, smul_smul]
    by_cases h2 : 2 ≤ n
    · simp only [h2, ite_true, add_smul, sub_smul, neg_smul, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_smul, Finset.mul_sum]
      congr 1
      · congr 1
        rw [Finset.sum_comm]
      · congr 1
        rw [Finset.sum_comm]
    · simp only [h2, ite_false, add_zero, sub_smul, Finset.sum_sub_distrib, Finset.sum_smul,
        Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
  simp only [liftFluxX, hval]
  rw [← hη, ← hG, ← hv, hmain]
  cases g with
  | zero =>
      simp only [↓reduceIte, sub_zero, Ctx.formX, Ctx.fluxPartX]
  | succ g' =>
      have hflux := sourceFlux_valField F Q hQ C hDm (r := r + 1) hT hg₀ e
      have hcd : ∀ (j : ℕ) (p : WalkFrom F (g' + 1) w), ContDiff ℝ ((j - 1 : ℕ) : ℕ∞)
          (fun ε => C.fluxS (n - j) g' (F.walkDat p.2) ε κ X z) := fun j p =>
        EpsPoly.contDiff_eps (C.epsPoly_fluxS (r := r) (by rw [hDm]; exact hT) hg₀ (n - j) g' (F.walkDat p.2)
          (by rw [hDm]; exact goodDat_walkDat F hdat p.2 _) κ) X z _
      have hsrc : ∀ j, iteratedDeriv (j - 1) (fun ε : ℝ =>
          sourceFlux Q.edge C.η ε C.t (valField F C e (n - j) g') κ X z) 0 =
          ∑ p : WalkFrom F (g' + 1) w,
            iteratedDeriv (j - 1) (fun ε => C.fluxS (n - j) g' (F.walkDat p.2) ε κ X z) 0 •
              walkVec F e p := by
        intro j
        simp only [hflux]
        have h := iteratedDeriv_clm_sum Finset.univ (walkL F e) (fun p _ => hcd j p) 0
        simp only [walkL_apply] at h
        exact h
      rw [show min Dm n = min C.D n by rw [hDm]]
      simp only [Nat.add_sub_cancel, show (g' + 1 = 0) = False from
        propext ⟨fun h => by omega, fun h => h.elim⟩, ite_false, hsrc, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [Ctx.formX, Ctx.fluxPartX, sub_smul, Finset.sum_sub_distrib, Finset.sum_smul]

/-- The candidate slow flux of a chain family at the last vertex. -/
theorem chain_liftFluxX_last {Dm L : ℕ} (cd : Fin L → StepDat)
    (Q : LiftOperatorData (Fin (L + 1)) (fun _ => ℝ) Dm) (hQ : HasFamFlux Q (chainFam cd)) (C : Ctx)
    (hη : C.η = Q.η) (hG : C.G = Q.G) (hv : C.v = Q.v) (hDm : C.D = Dm) {r : ℕ}
    (hT : C.GoodT (r + 1 + Dm)) (hg₀ : ContDiff ℝ (⊤ : ℕ∞) C.g₀)
    (hcd : ∀ i, GoodDat (r + 1 + Dm) C.t (cd i)) (n : ℕ) (X z : Vec 2) (κ : Fin 2) :
    liftFluxX Q (cand (chainFam cd) C.T) (fun _ Y => Pi.single (0 : Fin (L + 1)) (C.g₀ Y))
      L n C.t X z κ (Fin.last L) = C.formX n L cd κ X z := by
  have hdat : ∀ v u (γ : (chainFam cd).Γ v u), GoodDat (r + 1 + Dm) C.t ((chainFam cd).dat v u γ) :=
    fun v u γ => hcd _
  have e1 : (fun (_ : ℝ) Y => (Pi.single (0 : Fin (L + 1)) (C.g₀ Y) : Fin (L + 1) → ℝ)) =
      fun _ Y => Pi.single (0 : Fin (L + 1)) (C.g₀ Y • (1 : ℝ)) := by
    funext _ Y; simp
  rw [e1, liftFluxX_cand (chainFam cd) Q hQ C hη hG hv hDm hT hg₀ hdat (1 : ℝ) L n X z κ,
    sum_walkVec_apply, chain_sum_walk]
  have hlast : (Fin.last L).val = (0 : Fin (L + 1)).val + L := by simp
  rw [dite_eq_left_of_eq_true (eq_true hlast), chain_compMap, chain_walkDat]
  simp only [ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
  congr 1
  funext j
  congr 1
  ext
  simp
end

end AVRegularity.Providers.PathDecomp
end
end
end
