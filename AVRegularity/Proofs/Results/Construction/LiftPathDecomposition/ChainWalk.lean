-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.LiftCoeff
public import AVRegularity.Statements.Intermediate.CycleComparison.LiftOperatorData
public import AVRegularity.Statements.Intermediate.CycleComparison.SourceFlux

@[expose] public section
noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.PathDecomp

/-! Walks of a branching family.

A branching family on an index type `ι` with spaces `hs` has, for every ordered pair `(v, u)`, a
finite type `Γ v u` of constituent identities `u → v`, each with a constant map `hs u → hs v` and
step data (maximal order and reparametrised flux field). A walk of length `g` from `w` to `v` is
defined recursively by its last step, so that the last-step decomposition is definitional; its
composite map composes the maps of its steps (first step first), and its step data is the list of
the data of its steps. Walks split uniquely at every intermediate length. -/

section
/-- The data of one step: maximal current order and the reparametrised flux field. -/
abbrev StepDat : Type :=
  ℕ × ((d : ℕ) → DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec 2 → Vec 2)

/-- A branching family with constituent identities `Γ v u` (`u → v`). -/
structure FamData (ι : Type) (hs : ι → Type) [∀ i, NormedAddCommGroup (hs i)]
    [∀ i, NormedSpace ℝ (hs i)] where
  /-- The identities of the edge `u → v`. -/
  Γ : ι → ι → Type
  /-- Finitely many identities per edge. -/
  fΓ : ∀ v u, Fintype (Γ v u)
  /-- The constant map of an identity. -/
  map : ∀ v u, Γ v u → hs u →L[ℝ] hs v
  /-- The step data of an identity. -/
  dat : ∀ v u, Γ v u → StepDat

variable {ι : Type} {hs : ι → Type} [∀ i, NormedAddCommGroup (hs i)]
  [∀ i, NormedSpace ℝ (hs i)]

attribute [instance] FamData.fΓ

namespace FamData

variable (F : FamData ι hs)

/-- Walks of length `g` from `w` to `v`, by their last step. -/
def Walk : ℕ → ι → ι → Type
  | 0, w, v => PLift (w = v)
  | g + 1, w, v => Σ u : ι, Walk g w u × F.Γ v u

section Fin
variable [Fintype ι] [DecidableEq ι]

instance instFintypeWalk : ∀ g w v, Fintype (F.Walk g w v)
  | 0, w, v => inferInstanceAs (Fintype (PLift (w = v)))
  | g + 1, w, v => by
      letI : ∀ u, Fintype (F.Walk g w u) := fun u => instFintypeWalk g w u
      exact inferInstanceAs (Fintype (Σ u : ι, F.Walk g w u × F.Γ v u))

end Fin

/-- The composite map of a walk (first step first). -/
def compMap : ∀ {g : ℕ} {w v : ι}, F.Walk g w v → hs w →L[ℝ] hs v
  | 0, w, _, ⟨h⟩ => h ▸ ContinuousLinearMap.id ℝ (hs w)
  | _ + 1, _, v, ⟨u, q, γ⟩ => (F.map v u γ).comp (compMap q)

/-- The step data of a walk (first step first). -/
def walkDat : ∀ {g : ℕ} {w v : ι}, F.Walk g w v → Fin g → StepDat
  | 0, _, _, _ => Fin.elim0
  | _ + 1, _, v, ⟨u, q, γ⟩ => Fin.snoc (walkDat q) (F.dat v u γ)

/-- Concatenation of walks. -/
def append : ∀ {p₂ p₁ : ℕ} {w u v : ι}, F.Walk p₂ w u → F.Walk p₁ u v → F.Walk (p₂ + p₁) w v
  | _, 0, _, _, _, q₂, ⟨h⟩ => h ▸ q₂
  | _, _ + 1, _, _, _, q₂, ⟨u', q₁, γ⟩ => ⟨u', append q₂ q₁, γ⟩

/-- Splitting a walk at length `p₂`. -/
def split : ∀ {p₂ p₁ : ℕ} {w v : ι}, F.Walk (p₂ + p₁) w v → Σ u : ι, F.Walk p₂ w u × F.Walk p₁ u v
  | _, 0, _, v, q => ⟨v, q, ⟨rfl⟩⟩
  | _, _ + 1, _, _, ⟨u', q, γ⟩ =>
      let s := split q
      ⟨s.1, s.2.1, ⟨u', s.2.2, γ⟩⟩

theorem split_append : ∀ {p₂ p₁ : ℕ} {w u v : ι} (q₂ : F.Walk p₂ w u) (q₁ : F.Walk p₁ u v),
    F.split (F.append q₂ q₁) = ⟨u, q₂, q₁⟩
  | _, 0, _, _, _, q₂, ⟨h⟩ => by subst h; rfl
  | _, _ + 1, _, _, v, q₂, ⟨u', q₁, γ⟩ => by
      simp only [append, split]
      rw [split_append q₂ q₁]

theorem append_split : ∀ {p₂ p₁ : ℕ} {w v : ι} (q : F.Walk (p₂ + p₁) w v),
    F.append (F.split q).2.1 (F.split q).2.2 = q
  | _, 0, _, _, q => rfl
  | _, _ + 1, _, v, ⟨u', q, γ⟩ => by
      simp only [split, append]
      rw [append_split q]

/-- Walks of length `p₂ + p₁` are pairs of composable walks. -/
def splitEquiv (p₂ p₁ : ℕ) (w v : ι) :
    F.Walk (p₂ + p₁) w v ≃ Σ u : ι, F.Walk p₂ w u × F.Walk p₁ u v where
  toFun := F.split
  invFun s := F.append s.2.1 s.2.2
  left_inv q := F.append_split q
  right_inv s := by
    obtain ⟨u, q₂, q₁⟩ := s
    exact F.split_append q₂ q₁

/-- Summation over walks of length `p₂ + p₁` as a double summation. -/
theorem sum_walk_append [Fintype ι] [DecidableEq ι] {M : Type*} [AddCommMonoid M] (p₂ p₁ : ℕ) (w v : ι)
    (Φ : F.Walk (p₂ + p₁) w v → M) :
    ∑ q, Φ q = ∑ u, ∑ q₂ : F.Walk p₂ w u, ∑ q₁ : F.Walk p₁ u v, Φ (F.append q₂ q₁) := by
  rw [← (F.splitEquiv p₂ p₁ w v).symm.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

theorem compMap_append : ∀ {p₂ p₁ : ℕ} {w u v : ι} (q₂ : F.Walk p₂ w u) (q₁ : F.Walk p₁ u v),
    F.compMap (F.append q₂ q₁) = (F.compMap q₁).comp (F.compMap q₂)
  | _, 0, _, _, _, q₂, ⟨h⟩ => by subst h; rfl
  | _, _ + 1, _, _, v, q₂, ⟨u', q₁, γ⟩ => by
      simp only [append, compMap]
      rw [compMap_append q₂ q₁, ContinuousLinearMap.comp_assoc]

theorem walkDat_append : ∀ {p₂ p₁ : ℕ} {w u v : ι} (q₂ : F.Walk p₂ w u) (q₁ : F.Walk p₁ u v),
    F.walkDat (F.append q₂ q₁) = Fin.append (F.walkDat q₂) (F.walkDat q₁)
  | _, 0, _, _, _, q₂, ⟨h⟩ => by
      subst h
      funext i
      simp [append, walkDat, Fin.append_right_nil]
  | _, _ + 1, _, _, v, q₂, ⟨u', q₁, γ⟩ => by
      simp only [append, walkDat]
      rw [walkDat_append q₂ q₁, Fin.append_snoc]

end FamData
end

/-! Chain families, path-candidate coefficient arrays and flux representations.

* `chainFam cd`: the scalar family on `Fin (L+1)` with one identity `i → i+1` carrying the step
  data `cd i` (the path family of a walk with step data `cd`).
* `cand F T g n`: the path-candidate array of grade `g` and degree `n` of a family `F`: the sum,
  over the walks `q : w → v` of length `g`, of the scalar array `T g (walkDat q) n` times the
  composite map of `q`.
* `topArr C g`: the `(last ← 0)` entries of a scalar chain array.
* `HasFamFlux Q F`: the source flux of `Q` is the sum over the identities of `F`. -/

section
/-- Scalar arrays indexed by degree: `n ↦ (m, α, t, X, z) ↦ ℝ`. -/
abbrev SArr : Type := ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec 2 → ℝ

/-- The chain family of step data `cd`. -/
def chainFam {L : ℕ} (cd : Fin L → StepDat) : FamData (Fin (L + 1)) (fun _ => ℝ) where
  Γ w i := PLift (w.val = i.val + 1)
  fΓ _ _ := inferInstance
  map _ _ _ := ContinuousLinearMap.id ℝ ℝ
  dat w i γ := cd ⟨i.val, by have := γ.down; have := w.isLt; omega⟩

variable {ι : Type} [Fintype ι] [DecidableEq ι] {hs : ι → Type} [∀ i, NormedAddCommGroup (hs i)]
  [∀ i, NormedSpace ℝ (hs i)]

/-- The path-candidate coefficient array of grade `g`, degree `n`. -/
def cand (F : FamData ι hs) (T : (g : ℕ) → (Fin g → StepDat) → SArr) (g n : ℕ) :
    LiftCoeff ι hs :=
  fun m α t X z v w => ∑ q : F.Walk g w v, T g (F.walkDat q) n m α t X z • F.compMap q

/-- The `(last ← 0)` entries of a scalar chain coefficient sequence. -/
def topArr {g : ℕ} (C : ℕ → ℕ → LiftCoeff (Fin (g + 1)) (fun _ => ℝ)) : SArr :=
  fun n m α t X z => C g n m α t X z (Fin.last g) 0 1

/-- The source flux of `Q` is the sum over the identities of `F`. -/
def HasFamFlux {Dm : ℕ} (Q : LiftOperatorData ι hs Dm) (F : FamData ι hs) : Prop :=
  ∀ (η ε t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, hs i) (k : Fin 2) (X z : Vec 2) (v : ι),
    sourceFlux Q.edge η ε t Φ k X z v =
      ∑ u : ι, ∑ d : Finset.Icc 2 Dm, ∑ γ : F.Γ v u,
        if d.1 ≤ (F.dat v u γ).1 then
          ∑ α : DerivativeWord2 (d.1 - 1),
            ((F.dat v u γ).2 d.1 α t X z k) • F.map v u γ (dEpsWord η ε α Φ X z u)
        else 0
end

/-! Walks of chain families and sub-walks.

In the chain family of step data `cd : Fin L → StepDat`, a walk of length `g` from `i` ends at
`i + g`, is unique, has identity composite map and the shifted step data
`j ↦ cd (i + j)`. Every window of the step data of a walk of a branching family is the step data
of a walk. -/

section
variable {L : ℕ} (cd : Fin L → StepDat)

theorem chain_walk_target : ∀ {g : ℕ} {i w : Fin (L + 1)}, (chainFam cd).Walk g i w →
    w.val = i.val + g := by
  intro g
  induction g with
  | zero => intro i w q; obtain ⟨h⟩ := q; subst h; simp
  | succ g ih =>
      intro i w q
      obtain ⟨u, q, γ⟩ := q
      have h1 := ih q
      have h2 := γ.down
      omega

theorem chain_walk_subsingleton (g : ℕ) (i w : Fin (L + 1)) :
    Subsingleton ((chainFam cd).Walk g i w) := by
  induction g generalizing w with
  | zero => exact ⟨fun a b => by obtain ⟨a⟩ := a; obtain ⟨b⟩ := b; rfl⟩
  | succ g ih =>
      refine ⟨fun a b => ?_⟩
      obtain ⟨u, q, γ⟩ := a
      obtain ⟨u', q', γ'⟩ := b
      have h1 := chain_walk_target cd q
      have h1' := chain_walk_target cd q'
      have h2 := γ.down
      have h2' := γ'.down
      have hu : u = u' := Fin.ext (by omega)
      subst hu
      have := ih (w := u)
      have hγ : γ = γ' := Subsingleton.elim (α := PLift (w.val = u.val + 1)) γ γ'
      rw [Subsingleton.elim q q', hγ]

/-- The walk of length `g` from `i` to `w = i + g`. -/
def chainWalk : ∀ (g : ℕ) (i w : Fin (L + 1)), w.val = i.val + g → (chainFam cd).Walk g i w
  | 0, i, w, h => ⟨Fin.ext (by omega)⟩
  | g + 1, i, w, h =>
      ⟨⟨w.val - 1, by have := w.isLt; omega⟩,
        chainWalk g i ⟨w.val - 1, by have := w.isLt; omega⟩ (by simp; omega),
        ⟨by simp; omega⟩⟩

theorem chain_walkDat {g : ℕ} {i w : Fin (L + 1)} (q : (chainFam cd).Walk g i w) :
    (chainFam cd).walkDat q = fun j => cd ⟨i.val + j.val, by
      have := chain_walk_target cd q; have := w.isLt; omega⟩ := by
  induction g generalizing w with
  | zero => obtain ⟨h⟩ := q; subst h; funext j; exact j.elim0
  | succ g ih =>
      obtain ⟨u, q, γ⟩ := q
      have h1 := chain_walk_target cd q
      have h2 := γ.down
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [FamData.walkDat, Fin.snoc_last, chainFam]
        congr 1; exact Fin.ext (by simp; omega)
      · simp only [FamData.walkDat, Fin.snoc_castSucc]
        rw [ih q]; rfl

theorem chain_compMap {g : ℕ} {i w : Fin (L + 1)} (q : (chainFam cd).Walk g i w) :
    (chainFam cd).compMap q = ContinuousLinearMap.id ℝ ℝ := by
  induction g generalizing w with
  | zero => obtain ⟨h⟩ := q; subst h; rfl
  | succ g ih =>
      obtain ⟨u, q, γ⟩ := q
      show (ContinuousLinearMap.id ℝ ℝ).comp ((chainFam cd).compMap q) = _
      rw [ih q]; rfl

theorem chain_sum_walk {M : Type*} [AddCommMonoid M] {g : ℕ} {i w : Fin (L + 1)}
    (Φ : (chainFam cd).Walk g i w → M) :
    ∑ q, Φ q = if h : w.val = i.val + g then Φ (chainWalk cd g i w h) else 0 := by
  by_cases h : w.val = i.val + g
  · simp only [h, ↓reduceDIte]
    have := chain_walk_subsingleton cd g i w
    exact Finset.sum_eq_single_of_mem (chainWalk cd g i w h) (Finset.mem_univ _)
      (fun b _ hb => absurd (Subsingleton.elim b _) hb)
  · simp only [h, ↓reduceDIte]
    have : IsEmpty ((chainFam cd).Walk g i w) := ⟨fun q => h (chain_walk_target cd q)⟩
    exact Fintype.sum_empty _
end

end AVRegularity.Providers.PathDecomp
end
