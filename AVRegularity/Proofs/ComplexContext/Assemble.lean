-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.ComplexContext.RecCMap
import AVRegularity.Proofs.ComplexContext.StrainChild
import AVRegularity.EntryWeak.MolecularHilbertToRawSolution
import AVRegularity.Proofs.ComplexContext.Restrict
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Topology Metric Homogenization
open scoped ENNReal
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: the induction on generated expressions.** The invariant of an expression of any sort
with the structural majorant `genMode` (`GenInv`) holds for every scheduled expression whose
solved nodes lie in certified leaves (`genInv_of_denotes`), by induction on the evaluation
relation `Gen.Denotes`, one lemma per constructor:
* sums and products of each sort, time letters, `restrict`, `mean`, `famCell`, `transPrim`,
  `dInternal`, `dPhase`, `cellInv`, `evalChild`, `drift`, the own-frame Jacobian, inverse and
  metric letters, and the certified leaves (this directory);
* the strain letters, the child-frame letters and the recentering derivatives `dOld`,
  `dSlowFam`, `dSlowCell` are the hypotheses `ComplexContextInputs` of this conditional induction.
The standing facts are `ComplexContextBase`. The drift bound `ε_i^{1+α} ≤ C_d √(κ_iκ_{i-1})` is asked only
at the levels `DL` of the drift letters of the expression (`DriftIn`), so that one passage can use
the drift constant of its own level (weak entry). -/

section
open AVRegularity.Providers.ComplexFlow

/-- **The invariant of a generated expression** with the structural majorant. -/
def GenInv (D : OCData) (b : ℝ) (j₀ : ℕ) (κ : MajConsts) (Δ : ℝ)
    (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)) :
    {s : GenSort} → {i : ℕ} → {p : ℤ} → Gen s i p → s.Sem → Prop
  | .ctx, i, p, e, f => ∃ F, CtxInv D b j₀ i p f F (genMode D κ Δ leaf e)
  | .fam, i, p, e, f => ∃ G, FamInv D b j₀ i p f G (genMode D κ Δ leaf e)
  | .cell, i, p, e, f => ∃ W, CellInv D b j₀ i p f W (genMode D κ Δ leaf e)

/-- **The standing facts of the carrier calculus** and the choice of the letter profiles. -/
structure ComplexContextBase (D : OCData) (b CH Υ : ℝ) (j₀ : ℕ) (κ : MajConsts) (Cd : ℝ) : Prop where
  env : ChainEnv D b CH Υ j₀
  hκ : ∀ m, 0 < D.kap m
  hsmall : ∀ i, j₀ ≤ i → 1 ≤ i → ownSize D i ≤ 1 / 100
  hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
    2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2))
  geo_jac : ∀ a c h, κ.geo .own (.jac a c) h = if h = 0 then ENNReal.ofReal 2 else 0
  geo_jacInv : ∀ a c h, κ.geo .own (.jacInv a c) h = if h = 0 then ENNReal.ofReal 2 else 0
  geo_metric : ∀ a c h, κ.geo .own (.metric a c) h = if h = 0 then ENNReal.ofReal 2 else 0
  drift : ∀ c h, κ.drift c h = if h = 1 ∨ h = -1 then ENNReal.ofReal (Real.pi * Cd) else 0
  child : ∀ h, κ.child h = ENNReal.ofReal (Real.exp (-(6 * Real.pi * b * |(h : ℝ)|)))
  geo_ownStrain : ∀ a c h, κ.geo .own (.strain a c) h =
    if h = 0 then ENNReal.ofReal ComplexFlow.chainK else 0
  geo_child : ∀ p' (L : GeoLetter) h, L.isStrain = false →
    κ.geo (.child p') L h = ENNReal.ofReal (2 * Real.exp (-(6 * Real.pi * b * |(h : ℝ)|)))
  geo_childStrain : ∀ p' a c h, κ.geo (.child p') (.strain a c) h =
    ENNReal.ofReal (ComplexFlow.chainK * Real.exp (-(6 * Real.pi * b * |(h : ℝ)|)))
  hCold : ENNReal.ofReal (12 / b) ≤ κ.Cold
  hCslow : ENNReal.ofReal (12 / b) ≤ κ.Cslow

/-- Every drift letter of `e` outside the certified leaves is at a level of `DL`. -/
def DriftIn (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞))
    (DL : ℕ → Prop) : {s : GenSort} → {i : ℕ} → {p : ℤ} → Gen s i p → Prop
  | _, _, _, e@(.add a b) => (leaf e).isSome ∨ (DriftIn leaf DL a ∧ DriftIn leaf DL b)
  | _, _, _, e@(.mul a b) => (leaf e).isSome ∨ (DriftIn leaf DL a ∧ DriftIn leaf DL b)
  | _, _, _, e@(.dOld _ a) => (leaf e).isSome ∨ DriftIn leaf DL a
  | _, _, _, e@(.dPhase a) => (leaf e).isSome ∨ DriftIn leaf DL a
  | _, _, _, e@(.dSlowFam _ c) => (leaf e).isSome ∨ DriftIn leaf DL c
  | _, _, _, e@(.dSlowCell _ w) => (leaf e).isSome ∨ DriftIn leaf DL w
  | _, _, _, e@(.dInternal w) => (leaf e).isSome ∨ DriftIn leaf DL w
  | _, _, _, e@(.restrict a) => (leaf e).isSome ∨ DriftIn leaf DL a
  | _, _, _, e@(.cellInv F _ ι) =>
      (leaf e).isSome ∨ ((∀ k, DriftIn leaf DL (F k)) ∧ DriftIn leaf DL ι)
  | _, _, _, e@(.transPrim w) => (leaf e).isSome ∨ DriftIn leaf DL w
  | _, _, _, e@(.solved G v F q _ _ _ _ ι) => (leaf e).isSome ∨
      ((∀ a c, DriftIn leaf DL (G a c)) ∧ (∀ k, DriftIn leaf DL (v k)) ∧
        (∀ k, DriftIn leaf DL (F k)) ∧ DriftIn leaf DL q ∧ DriftIn leaf DL ι)
  | _, _, _, e@(.mean w) => (leaf e).isSome ∨ DriftIn leaf DL w
  | _, _, _, e@(.famCell c) => (leaf e).isSome ∨ DriftIn leaf DL c
  | _, _, _, e@(.evalChild _ c) => (leaf e).isSome ∨ DriftIn leaf DL c
  | _, _, _, .geo .. => True
  | _, i, _, .drift .. => DL i
  | _, _, _, .time .. => True

/-- With every level allowed, every expression has its drift letters at allowed levels. -/
theorem driftIn_true (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)) :
    ∀ {s : GenSort} {i : ℕ} {p : ℤ} (e : Gen s i p), DriftIn leaf (fun _ => True) e := by
  intro s i p e
  induction e <;> simp_all [DriftIn]

/-- **The constructors supplied separately**: the strain letters, the child-frame letters and the
recentering derivatives. -/
structure ComplexContextInputs (D : OCData) (b : ℝ) (j₀ : ℕ) (κ : MajConsts) (Δ : ℝ) : Prop where
  strainOwn : ∀ (i : ℕ) (p : ℤ), j₀ ≤ i → 1 ≤ i → Odd p → ∀ a c : Fin 2,
    ∃ F, CtxInv D b j₀ i p (GeoLetter.eval D i .own (.strain a c)) F
      (fun _ h _ => κ.geo .own (.strain a c) h)
  child : ∀ (i : ℕ) (p p' : ℤ), j₀ ≤ i → 1 ≤ i → Odd p → IsScheduledIn D i p' p →
    ∀ L : GeoLetter, ∃ F, CtxInv D b j₀ i p (GeoLetter.eval D i (.child p') L) F
      (fun _ h _ => κ.geo (.child p') L h)
  dOld : ∀ (i : ℕ) (p : ℤ), j₀ ≤ i → 1 ≤ i → Odd p → ∀ (j : Fin 2) (fa : GenSort.Sem .ctx)
    (F : Ext) (B : ℝ → ℤ → ℝ → ℝ≥0∞), CtxInv D b j₀ i p fa F B →
    ∃ F', CtxInv D b j₀ i p (fun t ch ζ => fderiv ℝ (fun h : Vec 2 =>
        fa t (ch.recenter D h) (ζ + (D.eps i)⁻¹ • h)) 0 (basisVec j)) F'
      (fun mres h t => derivCost κ.Cold (D.eps i) Δ mres (B (mres + Δ) h t) +
        (if j = transverseIndex p then ENNReal.ofReal (2 * Real.pi * |(h : ℝ)| / D.eps i)
          else 0) * B mres h t)
  dSlowFam : ∀ (i : ℕ) (p : ℤ), j₀ ≤ i → 1 ≤ i → Odd p → ∀ (j : Fin 2) (fc : GenSort.Sem .fam)
    (G : Ext) (B : ℝ → ℤ → ℝ → ℝ≥0∞), FamInv D b j₀ i p fc G B →
    ∃ G', FamInv D b j₀ i p (fun t ch => fderiv ℝ (fun h : Vec 2 =>
        fc t (ch.recenter D h)) 0 (basisVec j)) G'
      (fun mres h t => derivCost κ.Cslow (D.eps (i - 1)) Δ mres (B (mres + Δ) h t))
  dSlowCell : ∀ (i : ℕ) (p : ℤ), j₀ ≤ i → 1 ≤ i → Odd p → ∀ (j : Fin 2)
    (fw : GenSort.Sem .cell) (W : ℤ → Ext) (B : ℝ → ℤ → ℝ → ℝ≥0∞), CellInv D b j₀ i p fw W B →
    ∃ W', CellInv D b j₀ i p (fun t ch η => fderiv ℝ (fun h : Vec 2 =>
        fw t (ch.recenter D h) η) 0 (basisVec j)) W'
      (fun mres h t => derivCost κ.Cslow (D.eps (i - 1)) Δ mres (B (mres + Δ) h t))

section Induction

variable {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ} {κ : MajConsts} {Δ Cd : ℝ}
  {leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)}

/-- A certified leaf node satisfies the invariant. -/
theorem genInv_leaf (hL : LeavesCertified D b j₀ leaf) {i : ℕ} {p : ℤ} {e : Gen .ctx i p}
    {f : GenSort.Sem .ctx} (hden : Gen.Denotes D b j₀ e f) {B : ℝ → ℤ → ℝ≥0∞}
    (hB : leaf e = some B) (hgen : ∀ mres h t, genMode D κ Δ leaf e mres h t = B mres h) :
    ∃ F, CtxInv D b j₀ i p f F (genMode D κ Δ leaf e) := by
  obtain ⟨F, hF, hmode⟩ := hL.2 i p e B hB f hden
  exact ⟨F, (CtxInv.of_leaf hF hmode).mono fun mres h t _ _ _ => (hgen mres h t).ge⟩

end Induction
end

/-! **Carrier calculus: the induction theorem** (conditional on `ComplexContextInputs`). Every scheduled
expression of a level `i ≥ max 1 j₀` over an odd slot whose solved nodes lie in certified leaves
satisfies the invariant of its sort with the majorant `genMode` (`genInv_of_denotes`); the drift
bound is used only at the levels `DL` of its drift letters (`DriftIn`). One case
per constructor of `Gen.Denotes`; a certified leaf is not expanded. -/

section
open AVRegularity.Providers.ComplexFlow

variable {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ} {κ : MajConsts} {Δ Cd : ℝ}
  {leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)}

/-- **The induction on generated expressions.** -/
theorem genInv_of_denotes (hB : ComplexContextBase D b CH Υ j₀ κ Cd) (hP : ComplexContextInputs D b j₀ κ Δ)
    (hL : LeavesCertified D b j₀ leaf) (DL : ℕ → Prop)
    (hCd : ∀ i, DL i → 1 ≤ i → D.eps i ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap i * D.kap (i - 1))) :
    ∀ {s : GenSort} {i : ℕ} {p : ℤ} {e : Gen s i p} {f : s.Sem}, Gen.Denotes D b j₀ e f →
      Gen.IsScheduled D e → Gen.SolvedFree leaf e → DriftIn leaf DL e → j₀ ≤ i → 1 ≤ i →
        Odd p → GenInv D b j₀ κ Δ leaf e f := by
  have hΛ1 := hB.env.hΛ1
  have hb0 := hB.env.hb0
  intro s i p e f hden
  induction hden with
  | @geo i p fr L =>
    intro hsch _ _ hj hi hp
    show ∃ F, CtxInv D b j₀ i p (L.eval D i fr) F (genMode D κ Δ leaf (Gen.geo fr L))
    rcases hleaf : leaf (Gen.geo (i := i) (p := p) fr L) with _ | B
    · have hgen : ∀ mres h t, genMode D κ Δ leaf (Gen.geo (i := i) (p := p) fr L) mres h t =
          κ.geo fr L h := fun mres h t => by simp [genMode, hleaf]
      cases fr with
      | own =>
        cases L with
        | jac a c =>
          exact ⟨_, (CtxInv.geoOwn_jac (p := p) hB.env (hB.hsmall i hj hi) a c).mono
            fun mres h t _ _ _ => by rw [hgen, hB.geo_jac]⟩
        | jacInv a c =>
          exact ⟨_, (CtxInv.geoOwn_jacInv (p := p) hB.env (hB.hsmall i hj hi) a c).mono
            fun mres h t _ _ _ => by rw [hgen, hB.geo_jacInv]⟩
        | metric a c =>
          exact ⟨_, (CtxInv.geoOwn_metric (p := p) hB.env (hB.hsmall i hj hi) a c).mono
            fun mres h t _ _ _ => by rw [hgen, hB.geo_metric]⟩
        | strain a c =>
          obtain ⟨F, hF⟩ := hP.strainOwn i p hj hi hp a c
          exact ⟨F, hF.mono fun mres h t _ _ _ => by rw [hgen]⟩
      | child p' =>
        cases hsch with
        | geoChild _ _ hsched =>
          obtain ⟨F, hF⟩ := hP.child i p p' hj hi hp hsched L
          exact ⟨F, hF.mono fun mres h t _ _ _ => by rw [hgen]⟩
    · exact genInv_leaf hL (Gen.Denotes.geo fr L) hleaf (fun mres h t => by simp [genMode, hleaf])
  | @drift i p c =>
    intro _ _ hdl hj hi hp
    have hleaf : leaf (Gen.drift (i := i) (p := p) c) = none := hL.1 _ _ _ _ (by decide)
    refine ⟨_, (CellInv.drift (b := b) (j₀ := j₀) hΛ1 hB.env.hζ hB.hκ hp (hCd i hdl hi) c).mono
      fun mres h t _ _ _ => le_of_eq ?_⟩
    simp [genMode, hleaf, hB.drift]
  | @time s i p L =>
    intro _ _ _ hj hi hp
    have hc := continuous_timeLetter D hΛ1 hB.env.hζ hB.hκ L
    cases s with
    | ctx =>
      show ∃ F, CtxInv D b j₀ i p (GenSort.ofTime .ctx (L.eval D)) F
        (genMode D κ Δ leaf (Gen.time L))
      rcases hleaf : leaf (Gen.time (s := .ctx) (i := i) (p := p) L) with _ | B
      · exact ⟨_, (CtxInv.time hc).mono fun mres h t _ _ _ => le_of_eq (by simp [genMode, hleaf])⟩
      · exact genInv_leaf hL (Gen.Denotes.time L) hleaf (fun mres h t => by simp [genMode, hleaf])
    | fam =>
      have hleaf : leaf (Gen.time (s := .fam) (i := i) (p := p) L) = none :=
        hL.1 _ _ _ _ (by decide)
      exact ⟨_, (FamInv.time hc).mono fun mres t _ _ _ => le_of_eq (by simp [genMode, hleaf])⟩
    | cell =>
      have hleaf : leaf (Gen.time (s := .cell) (i := i) (p := p) L) = none :=
        hL.1 _ _ _ _ (by decide)
      exact ⟨_, (CellInv.time hc).mono fun mres h t _ _ _ => le_of_eq (by simp [genMode, hleaf])⟩
  | @add s i p a b' fa fb ha hb iha ihb =>
    intro hsch hsf hdl hj hi hp
    cases hsch with
    | add hsa hsb =>
    cases s with
    | ctx =>
      show ∃ F, CtxInv D b j₀ i p (GenSort.add .ctx fa fb) F (genMode D κ Δ leaf (Gen.add a b'))
      rcases hleaf : leaf (Gen.add a b') with _ | B
      · have hsf' : Gen.SolvedFree leaf a ∧ Gen.SolvedFree leaf b' := by
          simpa [Gen.SolvedFree, hleaf] using hsf
        have hdl' : DriftIn leaf DL a ∧ DriftIn leaf DL b' := by
          simpa [DriftIn, hleaf] using hdl
        obtain ⟨Fa, hFa⟩ := iha hsa hsf'.1 hdl'.1 hj hi hp
        obtain ⟨Fb, hFb⟩ := ihb hsb hsf'.2 hdl'.2 hj hi hp
        exact ⟨_, (hFa.add hb0 hFb).mono fun mres h t _ _ _ =>
          le_of_eq (by simp [genMode, hleaf])⟩
      · exact genInv_leaf hL (Gen.Denotes.add ha hb) hleaf
          (fun mres h t => by simp [genMode, hleaf])
    | fam =>
      have hleaf : leaf (Gen.add a b') = none := hL.1 _ _ _ _ (by decide)
      have hsf' : Gen.SolvedFree leaf a ∧ Gen.SolvedFree leaf b' := by
        simpa [Gen.SolvedFree, hleaf] using hsf
      have hdl' : DriftIn leaf DL a ∧ DriftIn leaf DL b' := by
        simpa [DriftIn, hleaf] using hdl
      obtain ⟨Ga, hGa⟩ := iha hsa hsf'.1 hdl'.1 hj hi hp
      obtain ⟨Gb, hGb⟩ := ihb hsb hsf'.2 hdl'.2 hj hi hp
      exact ⟨_, (hGa.add hGb).mono fun mres t _ _ _ => le_of_eq (by simp [genMode, hleaf])⟩
    | cell =>
      have hleaf : leaf (Gen.add a b') = none := hL.1 _ _ _ _ (by decide)
      have hsf' : Gen.SolvedFree leaf a ∧ Gen.SolvedFree leaf b' := by
        simpa [Gen.SolvedFree, hleaf] using hsf
      have hdl' : DriftIn leaf DL a ∧ DriftIn leaf DL b' := by
        simpa [DriftIn, hleaf] using hdl
      obtain ⟨Wa, hWa⟩ := iha hsa hsf'.1 hdl'.1 hj hi hp
      obtain ⟨Wb, hWb⟩ := ihb hsb hsf'.2 hdl'.2 hj hi hp
      exact ⟨_, (hWa.add hWb).mono fun mres h t _ _ _ => le_of_eq (by simp [genMode, hleaf])⟩
  | @mul s i p a b' fa fb ha hb iha ihb =>
    intro hsch hsf hdl hj hi hp
    cases hsch with
    | mul hsa hsb =>
    cases s with
    | ctx =>
      show ∃ F, CtxInv D b j₀ i p (GenSort.mul .ctx fa fb) F (genMode D κ Δ leaf (Gen.mul a b'))
      rcases hleaf : leaf (Gen.mul a b') with _ | B
      · have hsf' : Gen.SolvedFree leaf a ∧ Gen.SolvedFree leaf b' := by
          simpa [Gen.SolvedFree, hleaf] using hsf
        have hdl' : DriftIn leaf DL a ∧ DriftIn leaf DL b' := by
          simpa [DriftIn, hleaf] using hdl
        obtain ⟨Fa, hFa⟩ := iha hsa hsf'.1 hdl'.1 hj hi hp
        obtain ⟨Fb, hFb⟩ := ihb hsb hsf'.2 hdl'.2 hj hi hp
        exact ⟨_, (hFa.mul hb0 hFb).mono fun mres h t _ _ _ =>
          le_of_eq (by simp [genMode, hleaf])⟩
      · exact genInv_leaf hL (Gen.Denotes.mul ha hb) hleaf
          (fun mres h t => by simp [genMode, hleaf])
    | fam =>
      have hleaf : leaf (Gen.mul a b') = none := hL.1 _ _ _ _ (by decide)
      have hsf' : Gen.SolvedFree leaf a ∧ Gen.SolvedFree leaf b' := by
        simpa [Gen.SolvedFree, hleaf] using hsf
      have hdl' : DriftIn leaf DL a ∧ DriftIn leaf DL b' := by
        simpa [DriftIn, hleaf] using hdl
      obtain ⟨Ga, hGa⟩ := iha hsa hsf'.1 hdl'.1 hj hi hp
      obtain ⟨Gb, hGb⟩ := ihb hsb hsf'.2 hdl'.2 hj hi hp
      exact ⟨_, (hGa.mul hGb).mono fun mres t _ _ _ => le_of_eq (by simp [genMode, hleaf])⟩
    | cell =>
      have hleaf : leaf (Gen.mul a b') = none := hL.1 _ _ _ _ (by decide)
      have hsf' : Gen.SolvedFree leaf a ∧ Gen.SolvedFree leaf b' := by
        simpa [Gen.SolvedFree, hleaf] using hsf
      have hdl' : DriftIn leaf DL a ∧ DriftIn leaf DL b' := by
        simpa [DriftIn, hleaf] using hdl
      obtain ⟨Wa, hWa⟩ := iha hsa hsf'.1 hdl'.1 hj hi hp
      obtain ⟨Wb, hWb⟩ := ihb hsb hsf'.2 hdl'.2 hj hi hp
      exact ⟨_, (hWa.mul hΛ1 hb0 hWb).mono fun mres h t _ _ _ =>
        le_of_eq (by simp [genMode, hleaf])⟩
  | @dOld i p j a fa ha iha =>
    intro hsch hsf hdl hj hi hp
    cases hsch with
    | dOld _ hsa =>
    show ∃ F, CtxInv D b j₀ i p _ F (genMode D κ Δ leaf (Gen.dOld j a))
    rcases hleaf : leaf (Gen.dOld j a) with _ | B
    · have hsfa : Gen.SolvedFree leaf a := by simpa [Gen.SolvedFree, hleaf] using hsf
      have hdla : DriftIn leaf DL a := by simpa [DriftIn, hleaf] using hdl
      obtain ⟨F, hF⟩ := iha hsa hsfa hdla hj hi hp
      obtain ⟨F', hF'⟩ := hP.dOld i p hj hi hp j fa F _ hF
      exact ⟨F', hF'.mono fun mres h t _ _ _ => le_of_eq (by simp [genMode, hleaf])⟩
    · exact genInv_leaf hL (Gen.Denotes.dOld j ha) hleaf (fun mres h t => by simp [genMode, hleaf])
  | @dPhase i p a fa ha iha =>
    intro hsch hsf hdl hj hi hp
    cases hsch with
    | dPhase hsa =>
    show ∃ F, CtxInv D b j₀ i p _ F (genMode D κ Δ leaf (Gen.dPhase a))
    rcases hleaf : leaf (Gen.dPhase a) with _ | B
    · have hsfa : Gen.SolvedFree leaf a := by simpa [Gen.SolvedFree, hleaf] using hsf
      have hdla : DriftIn leaf DL a := by simpa [DriftIn, hleaf] using hdl
      obtain ⟨F, hF⟩ := iha hsa hsfa hdla hj hi hp
      exact ⟨_, (hF.dPhase hΛ1 hb0).mono fun mres h t _ _ _ =>
        le_of_eq (by simp [genMode, hleaf])⟩
    · exact genInv_leaf hL (Gen.Denotes.dPhase ha) hleaf (fun mres h t => by simp [genMode, hleaf])
  | @dSlowFam i p j c fc hc ihc =>
    intro hsch hsf hdl hj hi hp
    cases hsch with
    | dSlowFam _ hsc =>
    have hleaf : leaf (Gen.dSlowFam j c) = none := hL.1 _ _ _ _ (by decide)
    have hsfc : Gen.SolvedFree leaf c := by simpa [Gen.SolvedFree, hleaf] using hsf
    have hdlc : DriftIn leaf DL c := by simpa [DriftIn, hleaf] using hdl
    obtain ⟨G, hG⟩ := ihc hsc hsfc hdlc hj hi hp
    obtain ⟨G', hG'⟩ := hP.dSlowFam i p hj hi hp j fc G _ hG
    exact ⟨G', hG'.mono fun mres t _ _ _ => le_of_eq (by simp [genMode, hleaf])⟩
  | @dSlowCell i p j w fw hw ihw =>
    intro hsch hsf hdl hj hi hp
    cases hsch with
    | dSlowCell _ hsw =>
    have hleaf : leaf (Gen.dSlowCell j w) = none := hL.1 _ _ _ _ (by decide)
    have hsfw : Gen.SolvedFree leaf w := by simpa [Gen.SolvedFree, hleaf] using hsf
    have hdlw : DriftIn leaf DL w := by simpa [DriftIn, hleaf] using hdl
    obtain ⟨W, hW⟩ := ihw hsw hsfw hdlw hj hi hp
    obtain ⟨W', hW'⟩ := hP.dSlowCell i p hj hi hp j fw W _ hW
    exact ⟨W', hW'.mono fun mres h t _ _ _ => le_of_eq (by simp [genMode, hleaf])⟩
  | @dInternal i p w fw hw ihw =>
    intro hsch hsf hdl hj hi hp
    cases hsch with
    | dInternal hsw =>
    have hleaf : leaf (Gen.dInternal w) = none := hL.1 _ _ _ _ (by decide)
    have hsfw : Gen.SolvedFree leaf w := by simpa [Gen.SolvedFree, hleaf] using hsf
    have hdlw : DriftIn leaf DL w := by simpa [DriftIn, hleaf] using hdl
    obtain ⟨W, hW⟩ := ihw hsw hsfw hdlw hj hi hp
    exact ⟨_, (hW.dInternal hΛ1 hb0).mono fun mres h t _ _ _ =>
      le_of_eq (by simp [genMode, hleaf])⟩
  | @restrict i p a fa ha iha =>
    intro hsch hsf hdl hj hi hp
    cases hsch with
    | restrict hsa =>
    have hleaf : leaf (Gen.restrict a) = none := hL.1 _ _ _ _ (by decide)
    have hsfa : Gen.SolvedFree leaf a := by simpa [Gen.SolvedFree, hleaf] using hsf
    have hdla : DriftIn leaf DL a := by simpa [DriftIn, hleaf] using hdl
    obtain ⟨F, hF⟩ := iha hsa hsfa hdla hj hi hp
    exact ⟨_, (hF.restrict hΛ1 hb0).mono fun mres h t _ _ _ =>
      le_of_eq (by simp [genMode, hleaf])⟩
  | @cellInv i p F t₀ ι fF fι hF hι ihF ihι =>
    intro hsch hsf hdl hj hi hp
    cases hsch with
    | cellInv hsF =>
    cases hι with
    | time L =>
    have hleaf : leaf (Gen.cellInv F (D.slotStart i p) (Gen.time (.const 0))) = none :=
      hL.1 _ _ _ _ (by decide)
    have hsf' : (∀ k, Gen.SolvedFree leaf (F k)) ∧ Gen.SolvedFree leaf
        (Gen.time (s := .cell) (i := i) (p := p) (.const 0)) := by
      simpa [Gen.SolvedFree, hleaf] using hsf
    have hdl' : (∀ k, DriftIn leaf DL (F k)) ∧ DriftIn leaf DL
        (Gen.time (s := .cell) (i := i) (p := p) (.const 0)) := by
      simpa [DriftIn, hleaf] using hdl
    obtain ⟨W, hW⟩ := ihF (transverseIndex p) (hsF _) (hsf'.1 _) (hdl'.1 _) hj hi hp
    have hcs : 0 < D.cellScaleSq i := by
      unfold OCData.cellScaleSq
      exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ1) 2) (hB.hκ i)
    refine ⟨_, (CellInv.cellInv hΛ1 hb0 hcs hW
      (metricExtOf_spec (p := p) hB.env (hB.hsmall i hj hi))).mono fun mres h t _ _ _ => ?_⟩
    simp only [genMode, hleaf, Option.elim]
    exact le_add_self
  | @transPrim i p w fw hw ihw =>
    intro hsch hsf hdl hj hi hp
    cases hsch with
    | transPrim hsw =>
    have hleaf : leaf (Gen.transPrim w) = none := hL.1 _ _ _ _ (by decide)
    have hsfw : Gen.SolvedFree leaf w := by simpa [Gen.SolvedFree, hleaf] using hsf
    have hdlw : DriftIn leaf DL w := by simpa [DriftIn, hleaf] using hdl
    obtain ⟨W, hW⟩ := ihw hsw hsfw hdlw hj hi hp
    exact ⟨_, (hW.transPrim hΛ1 hb0).mono fun mres h t _ _ _ =>
      le_of_eq (by simp [genMode, hleaf])⟩
  | @solved i p G v F q t₀ t₁ c sZ ι fG fv fF fq fι ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    intro _ hsf _ _ _ _
    have hleaf : leaf (Gen.solved G v F q t₀ t₁ c sZ ι) = none := hL.1 _ _ _ _ (by decide)
    simp [Gen.SolvedFree, hleaf] at hsf
  | @mean i p w fw hw ihw =>
    intro hsch hsf hdl hj hi hp
    cases hsch with
    | mean hsw =>
    have hleaf : leaf (Gen.mean w) = none := hL.1 _ _ _ _ (by decide)
    have hsfw : Gen.SolvedFree leaf w := by simpa [Gen.SolvedFree, hleaf] using hsf
    have hdlw : DriftIn leaf DL w := by simpa [DriftIn, hleaf] using hdl
    obtain ⟨W, hW⟩ := ihw hsw hsfw hdlw hj hi hp
    exact ⟨_, (hW.mean hΛ1 hb0).mono fun mres t _ _ _ => le_of_eq (by simp [genMode, hleaf])⟩
  | @famCell i p c fc hc ihc =>
    intro hsch hsf hdl hj hi hp
    cases hsch with
    | famCell hsc =>
    have hleaf : leaf (Gen.famCell c) = none := hL.1 _ _ _ _ (by decide)
    have hsfc : Gen.SolvedFree leaf c := by simpa [Gen.SolvedFree, hleaf] using hsf
    have hdlc : DriftIn leaf DL c := by simpa [DriftIn, hleaf] using hdl
    obtain ⟨G, hG⟩ := ihc hsc hsfc hdlc hj hi hp
    exact ⟨_, hG.famCell.mono fun mres h t _ _ _ => le_of_eq (by simp [genMode, hleaf])⟩
  | @evalChild i p p' c fc hc ihc =>
    intro hsch hsf hdl hj hi hp
    cases hsch with
    | evalChild _ hodd hsched hsc =>
    show ∃ F, CtxInv D b j₀ i p _ F (genMode D κ Δ leaf (Gen.evalChild p' c))
    rcases hleaf : leaf (Gen.evalChild (i := i) (p := p) p' c) with _ | B
    · have hsfc : Gen.SolvedFree leaf c := by simpa [Gen.SolvedFree, hleaf] using hsf
      have hdlc : DriftIn leaf DL c := by simpa [DriftIn, hleaf] using hdl
      obtain ⟨G, hG⟩ := ihc hsc hsfc hdlc (by omega) (by omega) hodd
      exact ⟨_, (CtxInv.evalChild hB.env.hζ hΛ1 hb0 hB.env.hb1 hB.hstart hj hodd hsched
        hG).mono fun mres h t _ _ _ => le_of_eq (by simp [genMode, hleaf, hB.child])⟩
    · exact genInv_leaf hL (Gen.Denotes.evalChild p' hc) hleaf
        (fun mres h t => by simp [genMode, hleaf])
end

/-! **Carrier calculus: the constructors of `ComplexContextInputs`.** Under the standing facts `ComplexContextBase` and a
positive reserve loss `Δ`, every constructor left as a hypothesis of the induction holds
(`complexContextInputs`): the own-frame strain letter (`CtxInv.strainOwn`), the child-frame letters
(`CtxInv.geoChild`, `CtxInv.strainChild`), and the recentering derivatives (`CtxInv.dOld`,
`FamInv.dSlow`, `CellInv.dSlow`). -/

section
open AVRegularity.Providers.ComplexFlow

variable {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ} {κ : MajConsts} {Cd Δ : ℝ}

/-- **The constructors supplied separately hold.** -/
theorem complexContextInputs (hB : ComplexContextBase D b CH Υ j₀ κ Cd) (hΔ : 0 < Δ) :
    ComplexContextInputs D b j₀ κ Δ where
  strainOwn i p _ _ _ a c :=
    ⟨_, (CtxInv.strainOwn (i := i) (p := p) hB.env a c).mono fun _ h _ _ _ _ => by
      rw [hB.geo_ownStrain]⟩
  child i p p' hij _ _ hsch L := by
    cases hL : L.isStrain with
    | false =>
      obtain ⟨F, hF⟩ := CtxInv.geoChild hB.env hsch (hB.hsmall (i + 1) (by omega) (by omega)) L hL
      exact ⟨F, hF.mono fun _ h _ _ _ _ => by rw [hB.geo_child p' L h hL]⟩
    | true =>
      cases L with
      | strain a c =>
        exact ⟨_, (CtxInv.strainChild (i := i) (p := p) hB.env p' a c).mono fun _ h _ _ _ _ => by
          rw [hB.geo_childStrain]⟩
      | jac a c => simp [GeoLetter.isStrain] at hL
      | jacInv a c => simp [GeoLetter.isStrain] at hL
      | metric a c => simp [GeoLetter.isStrain] at hL
  dOld _ _ _ _ _ j _ _ _ hF := ⟨_, CtxInv.dOld hB.env hΔ hB.hCold j hF⟩
  dSlowFam _ _ _ _ _ j _ _ _ hF := ⟨_, FamInv.dSlow hB.env hΔ hB.hCslow j hF⟩
  dSlowCell _ _ _ _ _ j _ _ _ hF := ⟨_, CellInv.dSlow hB.env hΔ hB.hCslow j hF⟩
end

/-! **Carrier calculus: the constants and the standing facts.** The letter profiles and the Cauchy constants
(`complexContextKappa`): the own-frame Jacobian letters `2·[h = 0]`, the own-frame strain `K·[h = 0]`, the
child-frame letters `2e^{-6πb|h|}`, the child-frame strain `Ke^{-6πb|h|}`, the drift `πC_d` at
`h = ±1`, the evaluation at the appended child `e^{-6πb|h|}`, and `C_old = C_slow = 12/b`; they are
finite and decay (`complexContextKappa_majOK`). With `Υ ≥ 100` the carrier start gives the smallness
`K a_{i-1}(6/5)h_i ≤ 1/100` (`ownSize_le_of_carrierStart`), and the data of
`gen_carrier_calculus` give the standing facts `ComplexContextBase` (`complexContextBase_of_data`). -/

section
open AVRegularity.Providers.ComplexFlow

/-- **The letter profiles and the Cauchy constants of the carrier calculus.** -/
def complexContextKappa (b Cd : ℝ) : MajConsts where
  geo fr L h := match fr, L with
    | .own, .strain _ _ => if h = 0 then ENNReal.ofReal chainK else 0
    | .own, _ => if h = 0 then ENNReal.ofReal 2 else 0
    | .child _, .strain _ _ => ENNReal.ofReal (chainK * Real.exp (-(6 * Real.pi * b * |(h : ℝ)|)))
    | .child _, _ => ENNReal.ofReal (2 * Real.exp (-(6 * Real.pi * b * |(h : ℝ)|)))
  drift _ h := if h = 1 ∨ h = -1 then ENNReal.ofReal (Real.pi * Cd) else 0
  child h := ENNReal.ofReal (Real.exp (-(6 * Real.pi * b * |(h : ℝ)|)))
  Cold := ENNReal.ofReal (12 / b)
  Cslow := ENNReal.ofReal (12 / b)

theorem chainK_ge_two : (2 : ℝ) ≤ chainK := by rw [chainK_eq]; norm_num

/-- **The constants of the carrier calculus are finite and decay.** -/
theorem complexContextKappa_majOK {b Cd : ℝ} (hCd : 0 ≤ Cd) : MajOK b (complexContextKappa b Cd) := by
  set C : ℝ := chainK + Real.pi * Cd * Real.exp (6 * Real.pi * b) with hC
  have hK := chainK_ge_two
  have hπCd : 0 ≤ Real.pi * Cd * Real.exp (6 * Real.pi * b) := by
    have := Real.pi_pos; positivity
  have hKC : chainK ≤ C := by rw [hC]; linarith
  have hE : ∀ h : ℤ, 0 < Real.exp (-(6 * Real.pi * b * |(h : ℝ)|)) := fun h => Real.exp_pos _
  have hE0 : Real.exp (-(6 * Real.pi * b * |((0 : ℤ) : ℝ)|)) = 1 := by simp
  refine ⟨C, fun fr L h => ?_, fun c h => ?_, fun h => ?_, ENNReal.ofReal_ne_top,
    ENNReal.ofReal_ne_top⟩
  · cases fr with
    | own =>
      cases L <;> simp only [complexContextKappa] <;> split_ifs with h0 <;>
        first
        | exact zero_le
        | (subst h0; rw [hE0, mul_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
    | child p' =>
      cases L <;> simp only [complexContextKappa] <;> refine ENNReal.ofReal_le_ofReal ?_ <;>
        exact mul_le_mul_of_nonneg_right (by linarith) (hE h).le
  · simp only [complexContextKappa]
    split_ifs with h1
    · refine ENNReal.ofReal_le_ofReal ?_
      have habs : |(h : ℝ)| = 1 := by
        rcases h1 with h1 | h1 <;> subst h1 <;> simp
      rw [habs, mul_one]
      have e : Real.pi * Cd * Real.exp (6 * Real.pi * b) * Real.exp (-(6 * Real.pi * b)) =
          Real.pi * Cd := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      have h2 : chainK * Real.exp (-(6 * Real.pi * b)) ≥ 0 := by
        have := Real.exp_pos (-(6 * Real.pi * b)); positivity
      calc Real.pi * Cd = Real.pi * Cd * Real.exp (6 * Real.pi * b) * Real.exp (-(6 * Real.pi * b)) :=
            e.symm
        _ ≤ C * Real.exp (-(6 * Real.pi * b)) := by
            rw [hC, add_mul]; linarith
    · exact zero_le
  · simp only [complexContextKappa]
    refine ENNReal.ofReal_le_ofReal ?_
    calc Real.exp (-(6 * Real.pi * b * |(h : ℝ)|)) = 1 * Real.exp (-(6 * Real.pi * b * |(h : ℝ)|)) :=
          (one_mul _).symm
      _ ≤ C * Real.exp (-(6 * Real.pi * b * |(h : ℝ)|)) :=
          mul_le_mul_of_nonneg_right (by linarith) (hE h).le

/-- **The smallness of the carrier start** with `Υ ≥ 100`. -/
theorem ownSize_le_of_carrierStart {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ} (hΛ : 1 ≤ D.Λ)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 10000) (hCH : 1 ≤ CH) (hΥ : 100 ≤ Υ)
    (hcs : IsCarrierStart D.α D.q D.Λ b CH Υ j₀) {i : ℕ} (hij : j₀ ≤ i) (hi : 1 ≤ i) :
    ownSize D i ≤ 1 / 100 := by
  have h1 := hcs.1 (i - 1) (by omega)
  rw [show i - 1 + 1 = i by omega] at h1
  set a := ocA D.α D.q D.Λ (i - 1) with ha_def
  set h := ocTauPP D.α D.q D.Λ i with hh_def
  have ha : 0 ≤ a := Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _
  have hh : 0 ≤ h := (Construction.Stream.ocTauPP_pos hΛ).le
  have hah : 0 ≤ a * h := mul_nonneg ha hh
  have hπ : 9 ≤ Real.pi ^ 2 := by have := Real.pi_gt_three; nlinarith
  have hΥCH : 100 ≤ Υ * CH := by nlinarith
  have h2 : 200 * (a * h) ≤ 2 * Υ * CH * a * h := by
    have : 200 * (a * h) ≤ 2 * (Υ * CH) * (a * h) := mul_le_mul_of_nonneg_right (by linarith) hah
    linarith [show 2 * (Υ * CH) * (a * h) = 2 * Υ * CH * a * h by ring]
  have h3 : b / (64 * (8 * Real.pi ^ 2)) ≤ b / 4608 :=
    div_le_div_of_nonneg_left hb0.le (by norm_num) (by nlinarith)
  have h4 : a * h ≤ 1 / 9216000000 := by
    have : 200 * (a * h) ≤ 1 / 10000 / 4608 := by
      have := div_le_div_of_nonneg_right hb1 (by norm_num : (0 : ℝ) ≤ 4608)
      linarith
    linarith
  unfold ownSize
  rw [← ha_def, ← hh_def]
  have e : chainK * a * (6 / 5 * h) = chainK * (6 / 5) * (a * h) := by ring
  rw [e, chainK_eq]
  calc (33554432 : ℝ) * (6 / 5) * (a * h) ≤ 33554432 * (6 / 5) * (1 / 9216000000) :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ ≤ 1 / 100 := by norm_num

/-- **The standing facts of the carrier calculus from the data of `gen_carrier_calculus`.** -/
theorem complexContextBase_of_data {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {Λ : ℕ} (hΛ : 128 ≤ Λ) (Cd : ℝ) {bw : ℝ} (hbw0 : 0 < bw) (hbw1 : bw ≤ 1 / 10000) {CH Υ : ℝ} (hCΥ : CarrierOK 100 CH Υ)
    {j₀ : ℕ} (hcs : IsCarrierStart α q Λ bw CH Υ j₀) (D : OCData) (hDα : D.α = α) (hDq : D.q = q)
    (hDΛ : D.Λ = Λ) (hDζ : D.ζ = ζ) (hΦ : IsOCStreamSeq α q Λ ζ D.Φ) (M : ℕ)
    (hκ : IsOCBandChain α q Λ ζ M D.κ) (hterm : D.term = M) :
    ComplexContextBase D bw CH Υ j₀ (complexContextKappa bw Cd) Cd := by
  subst hDα hDq hDΛ hDζ hterm
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hvel := velC_spec hα₀ hα₁ hs₀ hs₁ hq hΛ hζ hΦ
  have hΥ100 : 100 ≤ Υ := (le_max_left _ _).trans hCΥ.2
  have hΥ1 : 1 ≤ Υ := by linarith
  have env : ChainEnv D bw CH Υ j₀ :=
    { hq := hq.1
      hΛ := hΛ
      hα := hα₁
      hζ := hζ
      hvel := fun m => (hvel m).1
      hag := fun m t x => (hvel m).2 t x
      hb0 := hbw0
      hb1 := hbw1
      hCH := hCΥ.1
      hΥ := hΥ1
      hcs := hcs }
  refine
    { env := env
      hκ := EntryWeakProofs.weakData_kap_pos D hΛ1 hζ hκ
      hsmall := fun i hij hi => ownSize_le_of_carrierStart hΛ1 hbw0 hbw1 hCΥ.1 hΥ100 hcs hij hi
      hstart := GenSem.startBound_of_carrierStart hΛ1 hCΥ.1 hΥ1 hcs
      geo_jac := fun _ _ _ => rfl
      geo_jacInv := fun _ _ _ => rfl
      geo_metric := fun _ _ _ => rfl
      drift := fun _ _ => rfl
      child := fun _ => rfl
      geo_ownStrain := fun _ _ _ => rfl
      geo_child := fun p' L h hL => ?_
      geo_childStrain := fun _ _ _ _ => rfl
      hCold := le_rfl
      hCslow := le_rfl }
  cases L with
  | strain a c => simp [GeoLetter.isStrain] at hL
  | jac a c => rfl
  | jacInv a c => rfl
  | metric a c => rfl
end

end AVRegularity.Providers.ComplexContext
end
