-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.CoeffArr.Mean
import Mathlib.Algebra.Order.Archimedean.Real.Hom

@[expose] public noncomputable section

section
open Homogenization AVRegularity
namespace AVRegularity.Providers.GenSem

/-! **Denotability of scalar functions of `(X, z)`.**

`RepEnv` fixes `D, bw, j₀`, a level `i`, a slot `p`, a base chain `A`, a scale `ρ`, a time `t`, a
seed registry `𝒮` and an open set `U` of slow points. A scalar function `φ(X, z)` is *represented*
by the cell expression `e` (`RepEnv.CellRep`) when `e` is scheduled, from the seed, and denotes some
`f` with `φ X z = f t (A.recenter (ρ • X)) z` for `X ∈ U`. Closure under the constructors:

* sums, products, constants, geometric letters, the drift;
* fast derivative: `dInternal` represents `fastPartial (transverseIndex p)` (no scaling, the
  derivative of `Denotes.dInternal` is the plain `fderiv` along `basisVec`); a function invariant
  along `basisVec j` has `fastPartial j φ = 0`;
* slow derivative: `ρ * dSlowCell j` represents `slowPartial j φ` (by `recenter_recenter`,
  `dSlowCell` computes `ρ⁻¹ * slowPartial j φ`);
* family functions via `famCell`, the cell mean via `mean`. -/

/-- The data of a representation problem. -/
structure RepEnv where
  /-- The construction. -/
  D : OCData
  /-- The carrier width. -/
  bw : ℝ
  /-- The starting level. -/
  j₀ : ℕ
  /-- The level. -/
  i : ℕ
  /-- The slot. -/
  p : ℤ
  /-- The base chain. -/
  A : RealChain
  /-- The scale. -/
  ρ : ℝ
  /-- The time. -/
  t : ℝ
  /-- The seed registry. -/
  𝒮 : SeedExports
  /-- The open set of slow points on which the representation holds. -/
  U : Set (Vec 2)

namespace RepEnv

variable (E : RepEnv)

/-- The chain at the slow point `X`: `A.recenter (ρ • X)`. -/
def ch (X : Vec 2) : RealChain := E.A.recenter E.D (E.ρ • X)

/-- `φ` is represented by the cell expression `e`. -/
def CellRep (φ : Vec 2 → Vec 2 → ℝ) (e : Gen .cell E.i E.p) : Prop :=
  Gen.IsScheduled E.D e ∧ Gen.FromSeed E.𝒮 e ∧ ∃ f : GenSort.Sem .cell,
    Gen.Denotes E.D E.bw E.j₀ e f ∧ ∀ X ∈ E.U, ∀ z, φ X z = f E.t (E.ch X) z

/-- The family function `ψ(X)` is represented by the family expression `e`. -/
def FamRep (ψ : Vec 2 → ℝ) (e : Gen .fam E.i E.p) : Prop :=
  Gen.IsScheduled E.D e ∧ Gen.FromSeed E.𝒮 e ∧ ∃ f : GenSort.Sem .fam,
    Gen.Denotes E.D E.bw E.j₀ e f ∧ ∀ X ∈ E.U, ψ X = f E.t (E.ch X)

/-- `φ` is represented by some cell expression. -/
def IsCellRep (φ : Vec 2 → Vec 2 → ℝ) : Prop := ∃ e, E.CellRep φ e

variable {E}

theorem CellRep.congr {φ ψ : Vec 2 → Vec 2 → ℝ} {e : Gen .cell E.i E.p} (h : E.CellRep φ e)
    (hφψ : ∀ X ∈ E.U, ∀ z, ψ X z = φ X z) : E.CellRep ψ e := by
  obtain ⟨hs, hf, f, hd, hv⟩ := h
  exact ⟨hs, hf, f, hd, fun X hX z => (hφψ X hX z).trans (hv X hX z)⟩

theorem CellRep.add {φ ψ : Vec 2 → Vec 2 → ℝ} {a b : Gen .cell E.i E.p} (ha : E.CellRep φ a)
    (hb : E.CellRep ψ b) : E.CellRep (fun X z => φ X z + ψ X z) (Gen.add a b) := by
  obtain ⟨sa, fa, f, hf, hφ⟩ := ha
  obtain ⟨sb, fb, g, hg, hψ⟩ := hb
  exact ⟨.add sa sb, .add fa fb, GenSort.add .cell f g, .add hf hg,
    fun X hX z => by
      show φ X z + ψ X z = f E.t (E.ch X) z + g E.t (E.ch X) z
      rw [hφ X hX z, hψ X hX z]⟩

theorem CellRep.mul {φ ψ : Vec 2 → Vec 2 → ℝ} {a b : Gen .cell E.i E.p} (ha : E.CellRep φ a)
    (hb : E.CellRep ψ b) : E.CellRep (fun X z => φ X z * ψ X z) (Gen.mul a b) := by
  obtain ⟨sa, fa, f, hf, hφ⟩ := ha
  obtain ⟨sb, fb, g, hg, hψ⟩ := hb
  exact ⟨.mul sa sb, .mul fa fb, GenSort.mul .cell f g, .mul hf hg,
    fun X hX z => by
      show φ X z * ψ X z = f E.t (E.ch X) z * g E.t (E.ch X) z
      rw [hφ X hX z, hψ X hX z]⟩

/-- Constants: `(K1)` time letter. -/
theorem cellRep_const (c : ℝ) :
    E.CellRep (fun _ _ => c) (Gen.time (s := .cell) (i := E.i) (p := E.p) (.const c)) :=
  ⟨.timeConst c, .time _, GenSort.ofTime .cell (TimeLetter.eval E.D (.const c)),
    .time _, fun _ _ _ => rfl⟩

theorem isCellRep_const (c : ℝ) : E.IsCellRep (fun _ _ => c) := ⟨_, cellRep_const c⟩

theorem IsCellRep.add {φ ψ : Vec 2 → Vec 2 → ℝ} (ha : E.IsCellRep φ) (hb : E.IsCellRep ψ) :
    E.IsCellRep (fun X z => φ X z + ψ X z) := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  exact ⟨_, ha.add hb⟩

theorem IsCellRep.mul {φ ψ : Vec 2 → Vec 2 → ℝ} (ha : E.IsCellRep φ) (hb : E.IsCellRep ψ) :
    E.IsCellRep (fun X z => φ X z * ψ X z) := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  exact ⟨_, ha.mul hb⟩

theorem IsCellRep.congr {φ ψ : Vec 2 → Vec 2 → ℝ} (h : E.IsCellRep φ)
    (hφψ : ∀ X ∈ E.U, ∀ z, ψ X z = φ X z) : E.IsCellRep ψ := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha.congr hφψ⟩

/-- Finite sums of represented functions are represented. -/
theorem IsCellRep.sum {ι : Type*} (s : Finset ι) {φ : ι → Vec 2 → Vec 2 → ℝ}
    (h : ∀ k ∈ s, E.IsCellRep (φ k)) : E.IsCellRep (fun X z => ∑ k ∈ s, φ k X z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCellRep_const (E := E) 0
  | insert a s ha ih =>
    have h1 := (h a (Finset.mem_insert_self a s)).add
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
    exact h1.congr fun X _ z => by simp [Finset.sum_insert ha]

/-! ### Geometric letters and the drift -/

/-! ### Fast derivatives -/

/-- `fastPartial` along the transverse index is represented by `dInternal` (a plain `fderiv` along
`basisVec`, no scaling). -/
theorem CellRep.dInternal {φ : Vec 2 → Vec 2 → ℝ} {e : Gen .cell E.i E.p} (h : E.CellRep φ e) :
    E.CellRep (fastPartial (transverseIndex E.p) φ) (Gen.dInternal e) := by
  obtain ⟨hs, hf, f, hd, hv⟩ := h
  refine ⟨.dInternal hs, .dInternal hf, _, .dInternal hd, fun X hX z => ?_⟩
  have : (fun z' => φ X z') = f E.t (E.ch X) := funext (hv X hX)
  simp only [fastPartial, this]

/-- A function invariant along `basisVec j` has vanishing `j`-th fast partial. -/
theorem fastPartial_eq_zero_of_invariant {φ : Vec 2 → Vec 2 → ℝ} (j : Fin 2) (X : Vec 2)
    (hinv : ∀ z (s : ℝ), φ X (z + s • basisVec j) = φ X z) (z : Vec 2) :
    fastPartial j φ X z = 0 := by
  unfold fastPartial
  by_cases hd : DifferentiableAt ℝ (fun z' => φ X z') z
  · have hl : HasDerivAt (fun s : ℝ => z + s • basisVec j) (basisVec j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (basisVec j)).const_add z
    have h1 : HasDerivAt (fun s : ℝ => φ X (z + s • basisVec j))
        (fderiv ℝ (fun z' => φ X z') z (basisVec j)) 0 := by
      exact HasFDerivAt.comp_hasDerivAt_of_eq (l := fun z' => φ X z') (x := (0 : ℝ))
        hd.hasFDerivAt hl (by simp)
    have h2 : HasDerivAt (fun s : ℝ => φ X (z + s • basisVec j)) 0 0 := by
      have : (fun s : ℝ => φ X (z + s • basisVec j)) = fun _ => φ X z := funext fun s => hinv z s
      rw [this]; exact hasDerivAt_const _ _
    exact h1.unique h2
  · simp [fderiv_zero_of_not_differentiableAt hd]

/-! ### Slow derivatives -/

/-- The chain of the recentered slow point: `(ch X).recenter h = A.recenter (ρ • X + h)`. -/
theorem ch_recenter (hζ : IsFastProfile E.D.ζ) (X h : Vec 2) :
    (E.ch X).recenter E.D h = E.A.recenter E.D (E.ρ • X + h) :=
  recenter_recenter E.D hζ E.A _ _

/-- The semantic slow derivative at `ch X` is `ρ⁻¹` times `slowPartial j φ`. -/
theorem fderiv_recenter_eq (hζ : IsFastProfile E.D.ζ) (hρ : E.ρ ≠ 0) (hU : IsOpen E.U)
    {φ : Vec 2 → Vec 2 → ℝ} (f : GenSort.Sem .cell) (hv : ∀ X ∈ E.U, ∀ z, φ X z = f E.t (E.ch X) z)
    (hd : ∀ X ∈ E.U, ∀ z, DifferentiableAt ℝ (fun X' => φ X' z) X) (j : Fin 2) {X : Vec 2}
    (hX : X ∈ E.U) (z : Vec 2) :
    fderiv ℝ (fun h : Vec 2 => f E.t ((E.ch X).recenter E.D h) z) 0 (basisVec j) =
      E.ρ⁻¹ * AVRegularity.slowPartial j φ X z := by
  set T : Vec 2 → Vec 2 := fun h => X + E.ρ⁻¹ • h with hT
  have hTc : Continuous T := by fun_prop
  have hT0 : T 0 = X := by simp [hT]
  have hev : (fun h : Vec 2 => f E.t ((E.ch X).recenter E.D h) z) =ᶠ[nhds 0]
      fun h => (fun X' => φ X' z) (T h) := by
    have hnb : T ⁻¹' E.U ∈ nhds (0 : Vec 2) :=
      (hU.preimage hTc).mem_nhds (by simpa [Set.mem_preimage, hT0] using hX)
    filter_upwards [hnb] with h hh
    have hh' : T h ∈ E.U := hh
    rw [hv (T h) hh' z, ch_recenter hζ]
    simp only [RepEnv.ch, hT, smul_add, smul_inv_smul₀ hρ]
  rw [hev.fderiv_eq]
  have hTd : HasFDerivAt T (E.ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)) 0 :=
    ((hasFDerivAt_id (0 : Vec 2)).const_smul E.ρ⁻¹).const_add X
  have hφd : HasFDerivAt (fun X' => φ X' z) (fderiv ℝ (fun X' => φ X' z) X) (T 0) := by
    rw [hT0]; exact (hd X hX z).hasFDerivAt
  change fderiv ℝ ((fun X' => φ X' z) ∘ T) 0 (basisVec j) = _
  rw [(hφd.comp 0 hTd).fderiv]
  simp [AVRegularity.slowPartial]

/-- `slowPartial j φ` is represented by `ρ * dSlowCell j e`. Hypotheses: `IsFastProfile D.ζ`,
`ρ ≠ 0`, `U` open, and `φ(·, z)` differentiable on `U`. -/
theorem CellRep.slowPartial (hζ : IsFastProfile E.D.ζ) (hρ : E.ρ ≠ 0) (hU : IsOpen E.U)
    {φ : Vec 2 → Vec 2 → ℝ} {e : Gen .cell E.i E.p} (h : E.CellRep φ e)
    (hd : ∀ X ∈ E.U, ∀ z, DifferentiableAt ℝ (fun X' => φ X' z) X) (j : Fin 2) :
    E.CellRep (AVRegularity.slowPartial j φ)
      (Gen.mul (Gen.time (s := .cell) (i := E.i) (p := E.p) (.const E.ρ)) (Gen.dSlowCell j e)) := by
  obtain ⟨hs, hf, f, hdn, hv⟩ := h
  refine ⟨.mul (.timeConst _) (.dSlowCell j hs), .mul (.time _) (.dSlowCell j hf),
    GenSort.mul .cell (GenSort.ofTime .cell (TimeLetter.eval E.D (.const E.ρ))) _,
    .mul (.time _) (.dSlowCell j hdn), fun X hX z => ?_⟩
  show AVRegularity.slowPartial j φ X z = E.ρ * fderiv ℝ (fun h : Vec 2 =>
    f E.t ((E.ch X).recenter E.D h) z) 0 (basisVec j)
  rw [fderiv_recenter_eq hζ hρ hU f hv hd j hX z, ← mul_assoc, mul_inv_cancel₀ hρ, one_mul]

/-! ### Family functions and the mean -/

/-- A family function is a cell function through `famCell`. -/
theorem FamRep.famCell {ψ : Vec 2 → ℝ} {e : Gen .fam E.i E.p} (h : E.FamRep ψ e) :
    E.CellRep (fun X _ => ψ X) (Gen.famCell e) := by
  obtain ⟨hs, hf, f, hd, hv⟩ := h
  exact ⟨.famCell hs, .famCell hf, _, .famCell hd, fun X hX _ => hv X hX⟩

/-- The cell mean `X ↦ fieldCellMean (φ X)` is represented by `mean`. -/
theorem CellRep.mean {φ : Vec 2 → Vec 2 → ℝ} {e : Gen .cell E.i E.p} (h : E.CellRep φ e) :
    E.FamRep (fun X => fieldCellMean (φ X)) (Gen.mean e) := by
  obtain ⟨hs, hf, f, hd, hv⟩ := h
  refine ⟨.mean hs, .mean hf, _, .mean hd, fun X hX => ?_⟩
  have : φ X = f E.t (E.ch X) := funext (hv X hX)
  simp only [fieldCellMean, this]
  rfl

/-- The cell mean as a (z-independent) cell function. -/
theorem CellRep.meanCell {φ : Vec 2 → Vec 2 → ℝ} {e : Gen .cell E.i E.p} (h : E.CellRep φ e) :
    E.CellRep (fun X _ => fieldCellMean (φ X)) (Gen.famCell (Gen.mean e)) :=
  h.mean.famCell

end RepEnv

end AVRegularity.Providers.GenSem
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **Denotability closure of coefficient arrays.**

An array `A` is represented when every entry `A m α` (all orders `m`) is represented by a cell
expression. An array supported up to order `K` is represented (entries above `K` are `0`,
represented by the constant `0`). Closure under `slowArr`, `fastArr` (transverse or invariant
direction), `mulArr`, `meanArr`, `iterSlow` and `compArr` (with `B` independent of `z`). -/

namespace RepEnv

variable {E : RepEnv}

/-- The array does not depend on the fast variable. -/
def ArrZConst (A : CArr) : Prop := ∀ m α X z z', A m α X z = A m α X z'

theorem arrZConst_slowArr {A : CArr} (hA : ArrZConst A) (j : Fin 2) : ArrZConst (slowArr j A) := by
  intro m β X z z'
  have h1 : (fun X' => A m β X' z) = fun X' => A m β X' z' := funext fun X' => hA m β X' z z'
  cases m with
  | zero => simp [slowArr, slowExtra, AVRegularity.slowPartial, h1]
  | succ m =>
    simp only [slowArr, slowExtra, AVRegularity.slowPartial, h1]
    split_ifs
    · rw [hA m]
    · rfl

theorem arrZConst_iterSlow : ∀ {n : ℕ} (α : DerivativeWord2 n) {B : CArr}, ArrZConst B →
    ArrZConst (iterSlow n α B)
  | 0, _, _, h => h
  | _ + 1, α, _, h => arrZConst_iterSlow (fun i => α i.succ) (arrZConst_slowArr h (α 0))

end RepEnv

end AVRegularity.Providers.GenSem
end
