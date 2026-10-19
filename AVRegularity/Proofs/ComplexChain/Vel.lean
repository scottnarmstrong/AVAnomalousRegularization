-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.ComplexChain.Over
import AVRegularity.Construction.Stream.NextAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.List.GetD
import Mathlib.RingTheory.PicardGroup

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Topology Homogenization AVenhance Metric
namespace AVRegularity.Providers.ComplexFlow

/-! **The last family of a chain and the appended child**, along a scheduled chain. Over the
parameters
`x ∈ 𝔇_i(2;𝗉)` (`carrierC … 2`, an open set: `isOpen_carrierC`):
* `famAux`: the recursion of `geomAuxC` on families; `famAux_toGeom`: it computes `geomAuxC`;
* `Over.famAux`: along a scheduled chain every family is over its slot;
* `chainFam D dd n`: the last family of a chain with discrete data `dd` (`chainFam_toGeom`: its
  geometry is `geomC D dd x`), over the last slot (`chainFam_over`) when the data are scheduled
  (`ChainOK`) and the carrier start holds;
* `appFam D dd n p' t`: the child appended for the finer slot `p'` at the output time `t`, with
  center `ε_i d_i(s_{𝗉'}; t, ζ)` and phase `ζ + d_i(s_{𝗉'}; t, ζ)` (`ζ` the final phase); it is
  over `p'` when `p'` is scheduled in the last slot and `ϖ_{𝗉'}(t) ≠ 0` (`appFam_over`). -/

section
/-! ### The complex carrier -/

theorem isOpen_carrierC (D : OCData) (b : ℝ) (dd : ChainData) (n : ℕ) (mres : ℝ) :
    IsOpen (carrierC D b dd n mres) := by
  have hc1 : Continuous fun x : ChainParamsC n => ∑ a : Fin 2, |(x.1 a).im| :=
    continuous_finsetSum _ fun a _ =>
      (Complex.continuous_im.comp ((continuous_apply a).comp continuous_fst)).abs
  have hc2 : ∀ k : Fin n, Continuous fun x : ChainParamsC n => ∑ a : Fin 2, ‖(x.2.1 k).1 a‖ :=
    fun k => continuous_finsetSum _ fun a _ => ((continuous_apply a).comp
      (continuous_fst.comp ((continuous_apply k).comp (continuous_fst.comp continuous_snd)))).norm
  have hc3 : ∀ k : Fin n, Continuous fun x : ChainParamsC n =>
      |((x.2.1 k).2 (transverseIndex (dd.slots.getD k 0))).im| :=
    fun k => (Complex.continuous_im.comp ((continuous_apply _).comp
      (continuous_snd.comp ((continuous_apply k).comp (continuous_fst.comp continuous_snd))))).abs
  have hc4 : Continuous fun x : ChainParamsC n =>
      |(x.2.2 (transverseIndex (dd.slots.getLastD 0))).im| :=
    (Complex.continuous_im.comp ((continuous_apply _).comp (continuous_snd.comp continuous_snd))).abs
  have h2 : IsOpen {x : ChainParamsC n | ∀ k : Fin n,
      (∑ a : Fin 2, ‖(x.2.1 k).1 a‖) < (1 + mres) * b / 4 * D.eps (dd.baseLevel + 1 + k) ∧
        |((x.2.1 k).2 (transverseIndex (dd.slots.getD k 0))).im| < (3 + mres / 4) * b + b / 64} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun k =>
      (isOpen_lt (hc2 k) continuous_const).inter (isOpen_lt (hc3 k) continuous_const)
  exact (isOpen_lt hc1 continuous_const).inter (h2.inter (isOpen_lt hc4 continuous_const))

theorem carrierC_mono {D : OCData} {b : ℝ} (hb : 0 ≤ b) {dd : ChainData} {n : ℕ} {m m' : ℝ}
    (hm : m ≤ m') : carrierC D b dd n m ⊆ carrierC D b dd n m' := by
  have hε : ∀ k, 0 ≤ D.eps k := fun k => by
    unfold OCData.eps ocEpsilon; split_ifs <;> positivity
  rintro x ⟨h1, h2, h3⟩
  refine ⟨h1.trans_le ?_, fun k => ⟨(h2 k).1.trans_le ?_, (h2 k).2.trans_le ?_⟩, h3.trans_le ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by norm_num))
      (hε _)
  · exact mul_le_mul_of_nonneg_right (by nlinarith) (hε _)
  · nlinarith
  · nlinarith

/-! ### The recursion along a chain -/

namespace CFam

variable {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]

/-- The geometry of a family at the parameters `P`. -/
def toGeom (F : CFam Par) (P : Par) : CGeom := (F.fl P, F.ctr P, F.anc)

/-- The family after the children with parameters `cs` (the recursion of `geomAuxC`). -/
def famAux (D : OCData) : ℕ → List ℤ → List (Par → CVec × CVec) → CFam Par → CFam Par
  | k, pk :: pk1 :: rest, c :: cs, F =>
      famAux D (k + 1) (pk1 :: rest) cs
        (F.child D k pk (D.slotAnchor (k + 1) pk1) (fun P => (c P).1) (fun P => (c P).2))
  | _, _, _, F => F

omit [NormedAddCommGroup Par] [NormedSpace ℂ Par] in
/-- **The recursion on families computes the complex geometry.** -/
theorem famAux_toGeom (D : OCData) (hε : ∀ k, D.eps k ≠ 0) (P : Par) :
    ∀ (cs : List (Par → CVec × CVec)) (k : ℕ) (ps : List ℤ) (F : CFam Par),
      (famAux D k ps cs F).toGeom P = geomAuxC D k ps (cs.map fun c => c P) (F.toGeom P) := by
  intro cs
  induction cs with
  | nil =>
    intro k ps F
    rcases ps with _ | ⟨p, _ | ⟨p1, rest⟩⟩ <;> rfl
  | cons c cs ih =>
    intro k ps F
    rcases ps with _ | ⟨p, _ | ⟨p1, rest⟩⟩
    · rfl
    · rfl
    · show (famAux D (k + 1) (p1 :: rest) cs _).toGeom P =
        geomAuxC D (k + 1) (p1 :: rest) (cs.map fun c => c P)
          (childGeomC D k p (D.slotAnchor (k + 1) p1) (c P) (F.toGeom P))
      rw [ih]
      congr 1
      exact (child_eq_childGeomC D (hε k) p _ (fun P => (c P).1) (fun P => (c P).2) F P).symm

/-- **Along a scheduled chain every family is over its slot.** -/
theorem Over.famAux {D : OCData} {b : ℝ} {Ω : Set Par} (hζ : IsFastProfile D.ζ) {B : ℕ}
    (hS : ∀ l, B ≤ l → LevelScales D b l) :
    ∀ (cs : List (Par → CVec × CVec)) (l : ℕ) (p : ℤ) (ps : List ℤ) (F : CFam Par),
      B ≤ l → F.Over D b Ω l p → cs.length = ps.length →
      (∀ j, j < ps.length →
        IsScheduledIn D (l + 1 + j) ((p :: ps).getD (j + 1) 0) ((p :: ps).getD j 0)) →
      (∀ j, j < cs.length → DifferentiableOn ℂ (cs.getD j 0) Ω ∧
        (∀ P ∈ Ω, ‖(cs.getD j 0 P).1‖ ≤ 3 / 4 * b * D.eps (l + 1 + j)) ∧
        ∀ P ∈ Ω, |((cs.getD j 0 P).2 (transverseIndex ((p :: ps).getD j 0))).im| ≤ phB b) →
      (famAux D (l + 1) (p :: ps) cs F).Over D b Ω (l + cs.length) ((p :: ps).getLastD 0) := by
  intro cs
  induction cs with
  | nil =>
    intro l p ps F _ hF hlen _ _
    have hps : ps = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst hps
    exact hF
  | cons c cs ih =>
    intro l p ps F hl hF hlen hsch hcs
    obtain ⟨p1, ps', rfl⟩ : ∃ p1 ps', ps = p1 :: ps' := by
      rcases ps with _ | ⟨p1, ps'⟩
      · simp at hlen
      · exact ⟨p1, ps', rfl⟩
    have hlen' : cs.length = ps'.length := by simpa using hlen
    have h0 := hcs 0 (by simp)
    simp only [List.getD_cons_zero] at h0
    have hs0 : IsScheduledIn D (l + 1) p1 p := by simpa using hsch 0 (by simp)
    have hF' := hF.child (hS l hl) hζ hs0 h0.1.fst h0.1.snd h0.2.1 h0.2.2
    have hrec := ih (l + 1) p1 ps' _ (by omega) hF' hlen'
      (fun j hj => by
        have := hsch (j + 1) (by simp; omega)
        simp only [List.getD_cons_succ] at this
        rwa [show l + 1 + (j + 1) = l + 1 + 1 + j by omega] at this)
      (fun j hj => by
        have := hcs (j + 1) (by simp; omega)
        simp only [List.getD_cons_succ] at this
        rwa [show l + 1 + (j + 1) = l + 1 + 1 + j by omega] at this)
    have e1 : l + (c :: cs).length = l + 1 + cs.length := by simp; omega
    have e2 : (p :: p1 :: ps').getLastD 0 = (p1 :: ps').getLastD 0 := by
      simp
    rw [e1, e2]
    exact hrec

end CFam

/-! ### The last family of a chain -/

/-- The discrete data `dd` are those of a scheduled chain with `n` children whose base level is
at least `j₀ - 1`. -/
structure ChainOK (D : OCData) (j₀ : ℕ) (dd : ChainData) (n : ℕ) : Prop where
  base : j₀ ≤ dd.baseLevel + 1
  len : dd.slots.length = n + 1
  sched : ∀ k, k < n →
    IsScheduledIn D (dd.baseLevel + 1 + k) (dd.slots.getD (k + 1) 0) (dd.slots.getD k 0)

/-- **The last family of a chain** with discrete data `dd` and `n` children. -/
def chainFam (D : OCData) (dd : ChainData) (n : ℕ) : CFam (ChainParamsC n) :=
  CFam.famAux D (dd.baseLevel + 1) dd.slots (List.ofFn fun j (x : ChainParamsC n) => x.2.1 j)
    (CFam.baseFam (velC D.α D.q D.Λ D.ζ dd.baseLevel) (baseW D dd.baseLevel) (fun x => x.1)
      (D.slotAnchor (dd.baseLevel + 1) (dd.slots.headD 0)))

theorem chainFam_toGeom (D : OCData) (hε : ∀ k, D.eps k ≠ 0) (dd : ChainData) {n : ℕ}
    (x : ChainParamsC n) : (chainFam D dd n).toGeom x = geomC D dd x := by
  unfold chainFam geomC
  rw [CFam.famAux_toGeom D hε]
  congr 1
  rw [List.map_ofFn]
  rfl

theorem getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) {j : ℕ} (hj : j < n) :
    (List.ofFn f).getD j d = f ⟨j, hj⟩ := by
  simp [List.getD_eq_getElem?_getD, hj]

/-- **The last family of a scheduled chain is over the last slot.** -/
theorem chainFam_over {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ} (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (hα : D.α < 1 / 3) (hζ : IsFastProfile D.ζ)
    (hvel : ∀ m, ∃ V, HolField (velC D.α D.q D.Λ D.ζ m) (D.eps m / 50) (velA * ocA D.α D.q D.Λ m) V)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 10000) (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ)
    (hcs : IsCarrierStart D.α D.q D.Λ b CH Υ j₀) {dd : ChainData} {n : ℕ} (hdd : ChainOK D j₀ dd n) :
    (chainFam D dd n).Over D b (carrierC D b dd n 2) (dd.baseLevel + n) (dd.slots.getLastD 0) := by
  have hΛ1 : 1 ≤ D.Λ := by omega
  obtain ⟨p, ps, hsl⟩ : ∃ p ps, dd.slots = p :: ps := by
    rcases h : dd.slots with _ | ⟨p, ps⟩
    · have := hdd.len; rw [h] at this; simp at this
    · exact ⟨p, ps, rfl⟩
  have hlen : ps.length = n := by have := hdd.len; rw [hsl] at this; simpa using this
  have hS : ∀ l, dd.baseLevel ≤ l → LevelScales D b l := fun l hl =>
    levelScales_of_carrierStart hq hΛ hα hb0 hb1 hCH hΥ hcs (by have := hdd.base; omega)
  obtain ⟨V, hv⟩ := hvel dd.baseLevel
  have hbase := CFam.baseOver (Ω := carrierC D b dd n 2) hv hb0 hb1 hΛ1
    (smallness_of_carrierStart hΛ1 hCH hΥ hcs hdd.base) (isOpen_carrierC D b dd n 2)
    differentiableOn_fst (fun x hx => by
      have := hx.1
      show imL1 x.1 ≤ _
      unfold imL1
      linarith) p
  have hsch : ∀ j, j < ps.length →
      IsScheduledIn D (dd.baseLevel + 1 + j) ((p :: ps).getD (j + 1) 0) ((p :: ps).getD j 0) := by
    intro j hj
    have := hdd.sched j (by omega)
    rwa [hsl] at this
  have hchild : ∀ j, j < (List.ofFn fun j (x : ChainParamsC n) => x.2.1 j).length →
      DifferentiableOn ℂ ((List.ofFn fun j (x : ChainParamsC n) => x.2.1 j).getD j 0)
          (carrierC D b dd n 2) ∧
        (∀ P ∈ carrierC D b dd n 2,
          ‖((List.ofFn fun j (x : ChainParamsC n) => x.2.1 j).getD j 0 P).1‖ ≤
            3 / 4 * b * D.eps (dd.baseLevel + 1 + j)) ∧
        ∀ P ∈ carrierC D b dd n 2,
          |(((List.ofFn fun j (x : ChainParamsC n) => x.2.1 j).getD j 0 P).2
            (transverseIndex ((p :: ps).getD j 0))).im| ≤ phB b := by
    intro j hj
    have hjn : j < n := by simpa using hj
    rw [getD_ofFn _ _ hjn]
    refine ⟨(by fun_prop : Differentiable ℂ fun x : ChainParamsC n => x.2.1 ⟨j, hjn⟩).differentiableOn,
      fun x hx => ?_, fun x hx => ?_⟩
    · have h1 := (hx.2.1 ⟨j, hjn⟩).1
      dsimp only at h1
      refine (norm_le_l1 _).trans ?_
      unfold l1
      have e : (1 + 2) * b / 4 * D.eps (dd.baseLevel + 1 + j) =
          3 / 4 * b * D.eps (dd.baseLevel + 1 + j) := by ring
      linarith
    · have h1 := (hx.2.1 ⟨j, hjn⟩).2
      dsimp only at h1
      rw [hsl] at h1
      unfold phB
      linarith
  unfold chainFam
  rw [hsl]
  have hrec := CFam.Over.famAux hζ hS (List.ofFn fun j (x : ChainParamsC n) => x.2.1 j)
    dd.baseLevel p ps _ le_rfl hbase (by simp [hlen]) hsch hchild
  rw [List.length_ofFn] at hrec
  exact hrec
end

/-! **The appended child**.
For the finer slot `p'` and the output time `t`, the child `𝒜^♮` of the last family of a chain
has the anchor `s_{𝗉'}`, the center `ε_i d_i(s_{𝗉'}; t, ζ)` and the phase `ζ + d_i(s_{𝗉'}; t, ζ)`,
with `ζ` the final phase (`appFam`). On the outer carrier `𝔇_i(2;𝗉)` it is a family over `p'`
(`appFam_over`) when `p'` is scheduled in the last slot and `ϖ_{𝗉'}(t) ≠ 0`: its center is at most
`ε_i b/1000` (`norm_appCenter_le`) and its phase has the transverse imaginary part of `ζ`. Hence
its Jacobian at the center satisfies `‖F^♮_t - I‖ ≤ K a_i |t - s_{𝗉'}| ≤ K a_i (6/5) h_{i+1}`
(by `CFam.norm_jacC_sub_le`). -/

/-- The level `i` of the appended child of a chain with discrete data `dd` and `n` children. -/
abbrev appLevel (dd : ChainData) (n : ℕ) : ℕ := dd.baseLevel + n + 1

/-- The center `ε_i d_i(s_{𝗉'}; t, ζ)` of the appended child. -/
def appCenter (D : OCData) (dd : ChainData) (n : ℕ) (p' : ℤ) (t : ℝ) (x : ChainParamsC n) :
    CVec :=
  epsC D (appLevel dd n) • relDispC D (appLevel dd n) (dd.slots.getLastD 0)
    (D.slotAnchor (appLevel dd n + 1) p') t x.2.2

/-- The phase `ζ + d_i(s_{𝗉'}; t, ζ)` of the appended child. -/
def appPhase (D : OCData) (dd : ChainData) (n : ℕ) (p' : ℤ) (t : ℝ) (x : ChainParamsC n) :
    CVec :=
  x.2.2 + relDispC D (appLevel dd n) (dd.slots.getLastD 0) (D.slotAnchor (appLevel dd n + 1) p')
    t x.2.2

/-- **The child appended for the finer slot `p'` at the output time `t`.** -/
def appFam (D : OCData) (dd : ChainData) (n : ℕ) (p' : ℤ) (t : ℝ) : CFam (ChainParamsC n) :=
  (chainFam D dd n).child D (appLevel dd n) (dd.slots.getLastD 0)
    (D.slotAnchor (appLevel dd n + 1) p') (appCenter D dd n p' t) (appPhase D dd n p' t)

theorem differentiable_appCenter (D : OCData) (dd : ChainData) (n : ℕ) (p' : ℤ) (t : ℝ) :
    Differentiable ℂ (appCenter D dd n p' t) := by
  unfold appCenter
  have h1 : Differentiable ℂ fun x : ChainParamsC n => x.2.2 := by fun_prop
  have h2 := ((differentiable_relDispC D (appLevel dd n) (dd.slots.getLastD 0)
    (D.slotAnchor (appLevel dd n + 1) p') t).comp h1).const_smul (epsC D (appLevel dd n))
  exact h2

theorem differentiable_appPhase (D : OCData) (dd : ChainData) (n : ℕ) (p' : ℤ) (t : ℝ) :
    Differentiable ℂ (appPhase D dd n p' t) := by
  unfold appPhase
  have h1 : Differentiable ℂ fun x : ChainParamsC n => x.2.2 := by fun_prop
  exact h1.add ((differentiable_relDispC _ _ _ _ _).comp h1)

/-- The appended phase has the transverse imaginary part of the final phase. -/
theorem appPhase_transverse (D : OCData) (dd : ChainData) (n : ℕ) (p' : ℤ) (t : ℝ)
    (x : ChainParamsC n) :
    (appPhase D dd n p' t x (transverseIndex (dd.slots.getLastD 0))).im =
      (x.2.2 (transverseIndex (dd.slots.getLastD 0))).im := by
  unfold appPhase
  rw [Pi.add_apply, relDispC_transverse, add_zero]

/-- **The center of the appended child is small.** -/
theorem norm_appCenter_le {D : OCData} {b : ℝ} (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 10000) {dd : ChainData} {n : ℕ} {p' : ℤ} {t : ℝ}
    (hah : ocA D.α D.q D.Λ (appLevel dd n) * ocTauPP D.α D.q D.Λ (appLevel dd n + 1) ≤ b / 10000)
    (ht : t ∈ slotWin D (appLevel dd n + 1) p') {x : ChainParamsC n}
    (hx : x ∈ carrierC D b dd n 2) :
    ‖appCenter D dd n p' t x‖ ≤ 1 / 1000 * b * D.eps (appLevel dd n) := by
  set i := appLevel dd n
  have he : 0 < D.eps i := Construction.Stream.ocEpsilon_pos hΛ
  have ha0 : 0 ≤ ocA D.α D.q D.Λ i := Real.rpow_nonneg he.le _
  have hh0 : 0 ≤ ocTauPP D.α D.q D.Λ (i + 1) := (Construction.Stream.ocTauPP_pos hΛ).le
  have hX0 : 0 ≤ Real.exp (30 * Real.pi * b) := (Real.exp_pos _).le
  have hX := exp_small_le hb0.le hb1
  have h1 := norm_smul_relDispC_le D hζ he (dd.slots.getLastD 0) (D.slotAnchor (i + 1) p') t x.2.2
  have hst : |D.slotAnchor (i + 1) p' - t| ≤ 6 / 5 * ocTauPP D.α D.q D.Λ (i + 1) :=
    abs_sub_le_of_mem_slotWin D (anchor_mem_slotWin D hΛ (i + 1) p') ht
  have him : |(x.2.2 (transverseIndex (dd.slots.getLastD 0))).im| < (3 + 2 / 4) * b := hx.2.2
  have hexp : Real.exp (shearFreq D.q D.Λ i *
      (D.eps i * |(x.2.2 (transverseIndex (dd.slots.getLastD 0))).im|)) ≤
      Real.exp (30 * Real.pi * b) := by
    refine Real.exp_le_exp.mpr ?_
    have e1 : shearFreq D.q D.Λ i * (D.eps i * |(x.2.2 (transverseIndex (dd.slots.getLastD 0))).im|)
        = 2 * Real.pi * |(x.2.2 (transverseIndex (dd.slots.getLastD 0))).im| := by
      unfold shearFreq
      show 2 * Real.pi * (D.eps i)⁻¹ * (D.eps i * _) = _
      field_simp
    rw [e1]
    have := Real.pi_pos
    nlinarith
  have hA : shearAmp D.α D.q D.Λ i = 2 * Real.pi * ocA D.α D.q D.Λ i * D.eps i := shearAmp_eq he
  have h2 : ‖appCenter D dd n p' t x‖ ≤
      6 / 5 * ocTauPP D.α D.q D.Λ (i + 1) *
        (2 * Real.pi * ocA D.α D.q D.Λ i * D.eps i * Real.exp (30 * Real.pi * b)) := by
    refine h1.trans ?_
    rw [hA]
    exact mul_le_mul hst (mul_le_mul_of_nonneg_left hexp (by have := Real.pi_pos; positivity))
      (by have := Real.pi_pos; positivity) (by positivity)
  exact h2.trans (step_w_le he ha0 hh0 hah hX0 hX)

/-- **The appended child is over its slot.** -/
theorem appFam_over {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ} (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (hα : D.α < 1 / 3) (hζ : IsFastProfile D.ζ)
    (hvel : ∀ m, ∃ V, HolField (velC D.α D.q D.Λ D.ζ m) (D.eps m / 50) (velA * ocA D.α D.q D.Λ m) V)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 10000) (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ)
    (hcs : IsCarrierStart D.α D.q D.Λ b CH Υ j₀) {dd : ChainData} {n : ℕ} (hdd : ChainOK D j₀ dd n)
    {p' : ℤ} (hp' : IsScheduledIn D (appLevel dd n) p' (dd.slots.getLastD 0)) {t : ℝ}
    (ht : t ∈ slotWin D (appLevel dd n + 1) p') :
    (appFam D dd n p' t).Over D b (carrierC D b dd n 2) (appLevel dd n) p' := by
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hS : LevelScales D b (dd.baseLevel + n) :=
    levelScales_of_carrierStart hq hΛ hα hb0 hb1 hCH hΥ hcs (by have := hdd.base; omega)
  have hF := chainFam_over hq hΛ hα hζ hvel hb0 hb1 hCH hΥ hcs hdd
  refine hF.child hS hζ hp' (differentiable_appCenter D dd n p' t).differentiableOn
    (differentiable_appPhase D dd n p' t).differentiableOn (fun x hx => ?_) (fun x hx => ?_)
  · refine (norm_appCenter_le hζ hΛ1 hb0 hb1 hS.hah ht hx).trans ?_
    have he : 0 < D.eps (appLevel dd n) := Construction.Stream.ocEpsilon_pos hΛ1
    show 1 / 1000 * b * D.eps (appLevel dd n) ≤ 3 / 4 * b * D.eps (appLevel dd n)
    nlinarith [mul_pos hb0 he]
  · rw [appPhase_transverse]
    have h1 : |(x.2.2 (transverseIndex (dd.slots.getLastD 0))).im| < (3 + 2 / 4) * b := hx.2.2
    unfold phB
    linarith

/-! **The complex families restrict to the real geometry** (the complex chain at real parameters
is the real chain). For an admissible real chain:
* `chainOK_of_admissible`: its discrete data are scheduled (`ChainOK`);
* `ChainOK.slotWin_subset`: the windows of its slots lie in the window of the base slot;
* `baseFlowC_agree`: the complex base flow restricts to the real flow `X_{j'-1}` on the window;
* `chainFam_agree`: the last family at the real parameters restricts to `RealChain.geom` for
  times in the window of the base slot;
* `jacC` (the complex Jacobian matrix of a family at its center) and `jacC_chainFam_real`: at the
  real parameters it is the real Jacobian `famJac` (`jacMatrix_ofReal_eq`). -/

section
/-! ### Scheduled data of admissible chains -/

theorem chainOK_of_admissible {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ} {ch : RealChain}
    (h : IsAdmissibleChain D b j₀ i p ch) : ChainOK D j₀ ch.data ch.children.length where
  base := h.2.1
  len := h.2.2.1
  sched := fun k hk => by
    have hl := h.2.2.1
    have := h.2.2.2.2.2.1 k (by omega)
    show IsScheduledIn D (ch.baseLevel + 1 + k) (ch.slots.getD (k + 1) 0) (ch.slots.getD k 0)
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    exact this

/-- **The windows of the slots of a scheduled chain lie in the window of the base slot.** -/
theorem ChainOK.slotWin_subset {D : OCData} {j₀ : ℕ} {dd : ChainData} {n : ℕ}
    (hdd : ChainOK D j₀ dd n) (hΛ : 1 ≤ D.Λ)
    (hsep : ∀ m, j₀ ≤ m → ocTauPP D.α D.q D.Λ (m + 1) < ocTau D.α D.q D.Λ m / 48) :
    ∀ j, j ≤ n → slotWin D (dd.baseLevel + 1 + j) (dd.slots.getD j 0) ⊆
      slotWin D (dd.baseLevel + 1) (dd.slots.getD 0 0)
  | 0, _ => subset_rfl
  | j + 1, hj =>
    (AVRegularity.Providers.ComplexFlow.slotWin_subset D hΛ (hdd.sched j (by omega)) (hsep _ (by have := hdd.base; omega))).trans
      (ChainOK.slotWin_subset hdd hΛ hsep j (by omega))

/-! ### The base flow -/

/-- The window of the complex base flow anchored at the slot `p` of level `l + 1`. -/
theorem baseFlowWin {D : OCData} {b : ℝ} {l : ℕ} (hb1 : b ≤ 1 / 10000) (hΛ : 1 ≤ D.Λ)
    (hAH : ocA D.α D.q D.Λ l * ocTauPP D.α D.q D.Λ (l + 1) ≤ b / 10000) (p : ℤ) :
    FlowWin (D.eps l / 50) (baseW D l) (velA * ocA D.α D.q D.Λ l)
      (D.slotAnchor (l + 1) p - 3 / 5 * ocTauPP D.α D.q D.Λ (l + 1))
      (D.slotAnchor (l + 1) p + 3 / 5 * ocTauPP D.α D.q D.Λ (l + 1)) := by
  have hE : 0 < D.eps l := Construction.Stream.ocEpsilon_pos hΛ
  have hA0 : 0 ≤ ocA D.α D.q D.Λ l := Real.rpow_nonneg hE.le _
  have hH0 : 0 ≤ ocTauPP D.α D.q D.Λ (l + 1) := (Construction.Stream.ocTauPP_pos hΛ).le
  obtain ⟨_, c2, _, _, _⟩ := base_consts hb1 hE hA0 hH0 hAH
  have hba : (D.slotAnchor (l + 1) p + 3 / 5 * ocTauPP D.α D.q D.Λ (l + 1)) -
      (D.slotAnchor (l + 1) p - 3 / 5 * ocTauPP D.α D.q D.Λ (l + 1)) =
      6 / 5 * ocTauPP D.α D.q D.Λ (l + 1) := by ring
  have hvA : velA * ocA D.α D.q D.Λ l = 2 ^ 21 * ocA D.α D.q D.Λ l := by unfold velA; ring
  exact { hℓ' := by unfold baseW; positivity
          hℓℓ := by unfold baseW; linarith
          hab := by linarith
          hΓT := by rw [hba, hvA]; exact c2 }

/-- **The complex base flow restricts to the real flow** on its window. -/
theorem baseFlowC_agree {D : OCData} {k : ℕ} {ℓ Γ V a b : ℝ}
    (hv : HolField (velC D.α D.q D.Λ D.ζ k) ℓ Γ V) (hw : FlowWin ℓ (baseW D k) Γ a b)
    (hag : ∀ t x, velC D.α D.q D.Λ D.ζ k t (ofRealVec x) = ofRealVec (streamVel (D.Φ k) t x)) :
    ∀ u ∈ Icc a b, ∀ r ∈ Icc a b, ∀ y,
      baseFlowC D k u (ofRealVec y) r = ofRealVec (D.flowOf k u y r) := by
  intro u hu r hr y
  have hX := flow_isFlow (streamVel (D.Φ k)) (D.hΦ k).vel_continuous (D.hΦ k).vel_lipschitz
  have hz : ofRealVec y ∈ Z0 (baseW D k) Γ a b := by
    show imL1 (ofRealVec y) ≤ _
    rw [imL1_ofRealVec]
    have := ratio_lt_one hw
    exact mul_nonneg (by linarith) hw.hℓ'.le
  exact cflow_ofRealVec_eq hv.toStripField hw (D.hΦ k).vel_continuous hag hX
    (fun x s => continuous_iff_continuousAt.2 fun σ => (hX.2 x s σ).continuousAt) y hz hr u hu

/-! ### The last family at real parameters -/

/-- **The last family of an admissible chain restricts to its real geometry.** -/
theorem chainFam_agree {D : OCData} {b CH Υ : ℝ} {j₀ i : ℕ} {p : ℤ} (hΛ : 128 ≤ D.Λ)
    (hvel : ∀ m, ∃ V, HolField (velC D.α D.q D.Λ D.ζ m) (D.eps m / 50) (velA * ocA D.α D.q D.Λ m) V)
    (hag : ∀ m t x, velC D.α D.q D.Λ D.ζ m t (ofRealVec x) = ofRealVec (streamVel (D.Φ m) t x))
    (hb1 : b ≤ 1 / 10000) (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ)
    (hcs : IsCarrierStart D.α D.q D.Λ b CH Υ j₀) {ch : RealChain}
    (hch : IsAdmissibleChain D b j₀ i p ch) (ζ : Vec 2) :
    CGeomAgree (slotWin D (ch.baseLevel + 1) (ch.slots.headD 0))
      ((chainFam D ch.data ch.children.length).toGeom (ch.paramsC ζ)) (ch.geom D) := by
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hε : ∀ k, D.eps k ≠ 0 := fun k => (Construction.Stream.ocEpsilon_pos hΛ1).ne'
  have hdd := chainOK_of_admissible hch
  have hsep : ∀ m, j₀ ≤ m → ocTauPP D.α D.q D.Λ (m + 1) < ocTau D.α D.q D.Λ m / 48 :=
    fun m hm => separation_of_carrierStart hΛ1 hCH hcs hm
  have hhead : ch.slots.headD 0 = ch.slots.getD 0 0 := by
    rcases ch.slots with _ | ⟨q, qs⟩ <;> rfl
  obtain ⟨V, hv⟩ := hvel ch.baseLevel
  have hw := baseFlowWin hb1 hΛ1 (smallness_of_carrierStart hΛ1 hCH hΥ hcs hdd.base)
    (ch.slots.headD 0)
  have hbase := baseFlowC_agree hv hw (hag ch.baseLevel)
  rw [chainFam_toGeom D hε]
  refine (geomC_agree D ch ζ hbase (anchor_mem_slotWin D hΛ1 _ _) fun j hj => ?_).1
  have hl := hdd.len
  have hjn : j + 1 ≤ ch.children.length := by
    have : j + 1 < ch.slots.length := hj
    show j + 1 ≤ ch.children.length
    rw [show ch.slots.length = ch.children.length + 1 from hl] at this
    omega
  have hsub := hdd.slotWin_subset hΛ1 hsep (j + 1) hjn
  have hmem := anchor_mem_slotWin D hΛ1 (ch.baseLevel + 1 + (j + 1)) (ch.slots.getD (j + 1) 0)
  rw [hhead]
  have e : ch.slots[j + 1] = ch.slots.getD (j + 1) 0 := (List.getD_eq_getElem _ _ hj).symm
  rw [e]
  exact hsub hmem

/-! ### The complex Jacobian at the center -/

namespace CFam

variable {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]

/-- **The complex Jacobian matrix** `F_t(0)` of a family at the parameters `P`: the derivative of
`y ↦ 𝔛_P(t, y, s)` at the center point. -/
def jacC (F : CFam Par) (P : Par) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun a c => fderiv ℂ (fun y => F.fl P t y F.anc) (F.ctr P) (cbasis c) a

end CFam

/-- The component of the derivative is the derivative of the component. -/
theorem fderiv_coord_eq {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E → Fin 2 → 𝕜} {z : E}
    (hf : DifferentiableAt 𝕜 f z) (v : E) (a : Fin 2) :
    fderiv 𝕜 f z v a = fderiv 𝕜 (fun y => f y a) z v := by
  have h : HasFDerivAt (fun y => f y a)
      ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin 2 => 𝕜) a).comp (fderiv 𝕜 f z)) z :=
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin 2 => 𝕜) a).hasFDerivAt.comp z
      hf.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- **At a real point, the complex Jacobian of a map preserving real points is the real
Jacobian.** -/
theorem jacMatrix_ofReal_eq {U : Set CVec} (hU : IsOpen U) {F : CVec → CVec}
    (hF : DifferentiableOn ℂ F U) {f : Vec 2 → Vec 2} (hFf : ∀ y, F (ofRealVec y) = ofRealVec (f y))
    {x : Vec 2} (hx : ofRealVec x ∈ U) (a c : Fin 2) :
    fderiv ℂ F (ofRealVec x) (cbasis c) a = ((jacMatrix f x a c : ℝ) : ℂ) := by
  have hFa : DifferentiableOn ℂ (fun z => F z a) U := fun z hz =>
    (differentiableAt_pi.1 ((hF z hz).differentiableAt (hU.mem_nhds hz)) a).differentiableWithinAt
  have hFfa : ∀ y, (fun z => F z a) (ofRealVec y) = ((f y a : ℝ) : ℂ) := fun y => by
    show F (ofRealVec y) a = _
    rw [hFf]; rfl
  have h1 := fderiv_ofRealVec_eq hU hFa hFfa hx (basisVec c)
  rw [ofRealVec_basisVec] at h1
  rw [fderiv_coord_eq ((hF _ hx).differentiableAt (hU.mem_nhds hx)), h1]
  -- the real side
  have hfd : ∀ b : Fin 2, DifferentiableAt ℝ (fun y => f y b) x := by
    intro b
    have e : (fun y => f y b) = fun y => (F (ofRealVec y) b).re := by
      funext y; rw [hFf]; simp [ofRealVec]
    rw [e]
    have hD : DifferentiableAt ℝ F (ofRealVec x) :=
      ((hF _ hx).differentiableAt (hU.mem_nhds hx)).restrictScalars ℝ
    have h2 : DifferentiableAt ℝ (fun y => F (ofRealVec y)) x := hD.comp x ofRealVecCLM.differentiableAt
    exact Complex.reCLM.differentiableAt.comp x (differentiableAt_pi.1 h2 b)
  have hfx : DifferentiableAt ℝ f x := differentiableAt_pi.2 hfd
  unfold jacMatrix
  rw [Matrix.of_apply, fderiv_coord_eq hfx]
end

/-! **The complex Jacobian letter of a family** (for the letter `F_t(0)`). For a family with the
invariants on an open set of a finite-dimensional parameter space:
* `differentiableOn_jacC`: each entry of `jacC P t` is holomorphic in the parameters (the
  directional derivative of a jointly holomorphic map is holomorphic, `differentiableOn_fderiv_apply`);
* `norm_jacC_sub_le`: `|F_t(0)_{ac} − δ_{ac}| ≤ Λ |t − s|`;
* `measurable_jacC`: each entry is measurable in the time on every subset of the window, for a
  time-continuous family (difference quotients, `measurable_fderiv_of_continuousOn`). -/

section
/-- The partial derivative in the second variable is the full derivative in the direction
`(0, w)`. -/
theorem fderiv_snd_eq {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par] {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G] {Φ : Par × CVec → G} {P : Par} {y : CVec}
    (hΦ : DifferentiableAt ℂ Φ (P, y)) (w : CVec) :
    fderiv ℂ (fun y => Φ (P, y)) y w = fderiv ℂ Φ (P, y) (0, w) := by
  have hi : HasFDerivAt (fun y : CVec => (P, y)) (ContinuousLinearMap.inr ℂ Par CVec) y :=
    (hasFDerivAt_const P y).prodMk (hasFDerivAt_id y)
  have h : HasFDerivAt (fun y => Φ (P, y))
      ((fderiv ℂ Φ (P, y)).comp (ContinuousLinearMap.inr ℂ Par CVec)) y :=
    hΦ.hasFDerivAt.comp y hi
  rw [h.fderiv]
  rfl

/-- **Measurability in time of a derivative**, from joint continuity in time and point. -/
theorem measurable_fderiv_of_continuousOn {g : ℝ → CVec → CVec} {W : Set ℝ} {y₀ : CVec} {ρ : ℝ}
    (hρ : 0 < ρ) (hc : ContinuousOn (fun q : ℝ × CVec => g q.1 q.2) (W ×ˢ ball y₀ ρ))
    (hd : ∀ t ∈ W, DifferentiableAt ℂ (g t) y₀) {S : Set ℝ} (hS : S ⊆ W) (w : CVec) :
    Measurable fun t : S => fderiv ℂ (g t) y₀ w := by
  obtain ⟨N, hN⟩ := exists_nat_gt (‖w‖ / ρ)
  set c : ℕ → ℂ := fun n => ((n + N + 1 : ℕ) : ℂ) with hc_def
  have hcpos : ∀ n, (0 : ℝ) < (n + N + 1 : ℕ) := fun n => by positivity
  have hnc : ∀ n, ‖c n‖ = ((n + N + 1 : ℕ) : ℝ) := fun n => by
    rw [hc_def, Complex.norm_natCast]
  have hmem : ∀ n, y₀ + (c n)⁻¹ • w ∈ ball y₀ ρ := by
    intro n
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_inv, hnc]
    have h1 : ‖w‖ / ρ < (n + N + 1 : ℕ) := by
      have : (N : ℝ) ≤ (n + N + 1 : ℕ) := by push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      linarith
    rw [div_lt_iff₀ hρ] at h1
    rw [inv_mul_lt_iff₀ (hcpos n)]
    linarith
  have hy₀ : y₀ ∈ ball y₀ ρ := mem_ball_self hρ
  -- the difference quotients are continuous on `S`
  have hcont : ∀ z ∈ ball y₀ ρ, Continuous fun t : S => g t z := by
    intro z hz
    have h1 : ContinuousOn (fun t : ℝ => g t z) W :=
      hc.comp (continuous_id.prodMk continuous_const).continuousOn fun t ht => ⟨ht, hz⟩
    exact (h1.mono hS).domRestrict
  have hf : ∀ n, Measurable fun t : S => c n • (g t (y₀ + (c n)⁻¹ • w) - g t y₀) := fun n => by
    have h2 : Continuous fun t : S => g t (y₀ + (c n)⁻¹ • w) - g t y₀ :=
      (hcont _ (hmem n)).sub (hcont _ hy₀)
    exact (h2.const_smul (c n)).measurable
  refine measurable_of_tendsto_metrizable' atTop hf ?_
  rw [tendsto_pi_nhds]
  intro t
  have hl := (hd t (hS t.2)).hasFDerivAt.lim w (c := c) (l := atTop) (by
    simp_rw [hnc]
    exact tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩))
  exact hl

namespace CFam

variable {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]
variable {F : CFam Par} {Ω : Set Par} {W : Set ℝ} {ϱ Λ T : ℝ}

/-- The entries of the complex Jacobian are derivatives of the coordinates. -/
theorem jacC_apply (h : F.OK Ω W ϱ Λ T) {P : Par} (hP : P ∈ Ω) {t : ℝ} (ht : t ∈ W) (a c : Fin 2) :
    F.jacC P t a c = fderiv ℂ (fun q : Par × CVec => F.fl q.1 t q.2 F.anc a) (P, F.ctr P)
      (0, cbasis c) := by
  have hq : (P, F.ctr P) ∈ F.dom Ω ϱ F.anc :=
    ⟨hP, by rw [h.cur_anc P hP]; exact mem_ball_self h.hϱ⟩
  have hd := (h.hol t ht F.anc h.anc_mem).differentiableAt
    ((h.isOpen_dom h.anc_mem).mem_nhds hq)
  have hda : DifferentiableAt ℂ (fun q : Par × CVec => F.fl q.1 t q.2 F.anc a) (P, F.ctr P) :=
    differentiableAt_pi.1 hd a
  rw [← fderiv_snd_eq hda]
  have hy : DifferentiableAt ℂ (fun y => F.fl P t y F.anc) (F.ctr P) := by
    have := h.differentiableAt_fl hP ht h.anc_mem (y := F.ctr P)
      (by rw [h.cur_anc P hP]; exact mem_ball_self h.hϱ)
    exact this
  exact fderiv_coord_eq hy (cbasis c) a

/-- **The entries of the complex Jacobian are holomorphic in the parameters.** -/
theorem differentiableOn_jacC [FiniteDimensional ℂ Par] (h : F.OK Ω W ϱ Λ T) {t : ℝ}
    (ht : t ∈ W) (a c : Fin 2) : DifferentiableOn ℂ (fun P => F.jacC P t a c) Ω := by
  have hΦ : DifferentiableOn ℂ (fun q : Par × CVec => F.fl q.1 t q.2 F.anc a)
      (F.dom Ω ϱ F.anc) := fun q hq =>
    (differentiableAt_pi.1 ((h.hol t ht F.anc h.anc_mem).differentiableAt
      ((h.isOpen_dom h.anc_mem).mem_nhds hq)) a).differentiableWithinAt
  have hD := GenSem.differentiableOn_fderiv_apply (h.isOpen_dom h.anc_mem) hΦ (0, cbasis c)
  have hmaps : MapsTo (fun P => (P, F.ctr P)) Ω (F.dom Ω ϱ F.anc) := fun P hP =>
    ⟨hP, by rw [h.cur_anc P hP]; exact mem_ball_self h.hϱ⟩
  have hcomp := hD.comp (differentiableOn_id.prodMk h.ctr_hol) hmaps
  exact hcomp.congr fun P hP => jacC_apply h hP ht a c

/-- **The Jacobian bound for the entries.** -/
theorem norm_jacC_sub_le (h : F.OK Ω W ϱ Λ T) {P : Par} (hP : P ∈ Ω) {t : ℝ} (ht : t ∈ W)
    (a c : Fin 2) :
    ‖F.jacC P t a c - (if a = c then 1 else 0)‖ ≤ Λ * |t - F.anc| := by
  have hc : F.ctr P ∈ ball (F.cur P F.anc) ϱ := by
    rw [h.cur_anc P hP]; exact mem_ball_self h.hϱ
  have hJ := h.jac P hP t ht F.anc h.anc_mem (F.ctr P) hc
  set L := fderiv ℂ (fun y => F.fl P t y F.anc) (F.ctr P)
  have e : F.jacC P t a c - (if a = c then 1 else 0) =
      ((L - ContinuousLinearMap.id ℂ CVec) (cbasis c)) a := by
    show L (cbasis c) a - _ = _
    rw [sub_apply, ContinuousLinearMap.id_apply, Pi.sub_apply]
    congr 1
    unfold cbasis
    by_cases hac : a = c
    · subst hac; simp
    · simp [hac]
  rw [e]
  refine (norm_le_pi_norm _ a).trans ?_
  refine ((L - ContinuousLinearMap.id ℂ CVec).le_opNorm _).trans ?_
  rw [norm_cbasis, mul_one]
  exact hJ

/-- **The entries of the complex Jacobian are measurable in time.** -/
theorem measurable_jacC (h : F.OK Ω W ϱ Λ T) (hc : F.TimeCont Ω W ϱ) {P : Par} (hP : P ∈ Ω)
    {S : Set ℝ} (hS : S ⊆ W) (a c : Fin 2) : Measurable fun t : S => F.jacC P t a c := by
  have hcP := hc.slice hP h.anc_mem
  rw [h.cur_anc P hP] at hcP
  have hm := measurable_fderiv_of_continuousOn h.hϱ hcP (fun t ht =>
    h.differentiableAt_fl hP ht h.anc_mem (by rw [h.cur_anc P hP]; exact mem_ball_self h.hϱ))
    hS (cbasis c)
  exact (measurable_pi_apply a).comp hm

end CFam
end

end AVRegularity.Providers.ComplexFlow
end

section
open Set Homogenization
namespace AVRegularity.Providers.ComplexFlow

/-! **The phase symmetries of the complex chains** (clause (a) of
`IsHolExtension`). The complex shear `𝐮^ℂ_{i,p}(εθ)` depends only on the transverse coordinate of
`θ` and has period one in it (`ocShearVelC`). Hence the complex relative displacement is invariant
under real translations of its argument with integer transverse component (`relDispC_shift`), the
complex child geometry is invariant under such translations of the child phase
(`childGeomC_shift`), and the last family of a chain is invariant under the child-phase
translations `ChainParamsC.shiftChild` (`geomC_shiftChild`, `chainFam_shiftChild`). It does not
depend on the final phase at all (`chainFam_final`). -/

/-- **The complex shear is periodic in the transverse coordinate.** -/
theorem ocShearVelC_shift {α q : ℝ} {Λ m : ℕ} {p : ℤ} (hε : ocEpsilon q Λ m ≠ 0) (w : CVec)
    {v : Vec 2} (hv : ∃ k : ℤ, v (transverseIndex p) = k) :
    ocShearVelC α q Λ m p (w + (((ocEpsilon q Λ m : ℝ) : ℂ) • ofRealVec v)) =
      ocShearVelC α q Λ m p w := by
  obtain ⟨k, hk⟩ := hv
  have hper : ∀ a : Fin 2, v a = k →
      (shearFreq q Λ m : ℂ) * (w + (((ocEpsilon q Λ m : ℝ) : ℂ) • ofRealVec v)) a =
        (shearFreq q Λ m : ℂ) * w a + (k : ℂ) * (2 * Real.pi) := by
    intro a ha
    have hεC : ((ocEpsilon q Λ m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hε
    simp only [Pi.add_apply, Pi.smul_apply, ofRealVec, smul_eq_mul, ha, shearFreq]
    push_cast
    field_simp
  unfold ocShearVelC
  split_ifs with h1 h3
  · have hq : transverseIndex p = 0 := by
      simp [transverseIndex, show ¬ p % 4 = 3 by omega]
    rw [hq] at hk
    rw [hper 0 hk, Complex.cos_add_int_mul_two_pi]
  · have hq : transverseIndex p = 1 := by
      simp [transverseIndex, h3]
    rw [hq] at hk
    rw [hper 1 hk, Complex.cos_add_int_mul_two_pi]
  · rfl

/-- **The complex relative displacement is periodic in the transverse coordinate.** -/
theorem relDispC_shift (D : OCData) {i : ℕ} (hε : D.eps i ≠ 0) (p : ℤ) (u s : ℝ) (θ : CVec)
    {v : Vec 2} (hv : ∃ k : ℤ, v (transverseIndex p) = k) :
    relDispC D i p u s (θ + ofRealVec v) = relDispC D i p u s θ := by
  have h := ocShearVelC_shift (α := D.α) (q := D.q) (Λ := D.Λ) (m := i) (p := p) hε
    (((D.eps i : ℝ) : ℂ) • θ) hv
  unfold relDispC
  rw [smul_add]
  exact congrArg _ h

/-- **The complex child geometry is invariant under the child-phase translations.** -/
theorem childGeomC_shift (D : OCData) {k : ℕ} (hε : D.eps k ≠ 0) (pk : ℤ) (s' : ℝ)
    (c : CVec × CVec) (g : CGeom) {v : Vec 2} (hv : ∃ m : ℤ, v (transverseIndex pk) = m) :
    childGeomC D k pk s' (c.1, c.2 + ofRealVec v) g = childGeomC D k pk s' c g := by
  unfold childGeomC
  have e : ∀ X : CVec, epsInvC D k • X + (c.2 + ofRealVec v - epsInvC D k • (g.2.1 + c.1)) =
      (epsInvC D k • X + (c.2 - epsInvC D k • (g.2.1 + c.1))) + ofRealVec v := fun X => by
    abel
  simp only [e, relDispC_shift D hε pk _ _ _ hv]

/-- Congruence of the complex chain geometry under childwise equal child geometries. -/
theorem geomAuxC_congr (D : OCData) :
    ∀ (cs cs' : List (CVec × CVec)) (k : ℕ) (sl : List ℤ) (g : CGeom),
      cs.length = cs'.length →
      (∀ j (hj : j < cs.length) (hj' : j < cs'.length) (s' : ℝ) (g : CGeom),
        childGeomC D (k + j) (sl.getD j 0) s' cs[j] g = childGeomC D (k + j) (sl.getD j 0) s'
          cs'[j] g) →
      geomAuxC D k sl cs g = geomAuxC D k sl cs' g := by
  intro cs
  induction cs with
  | nil =>
    intro cs' k sl g hl _
    have : cs' = [] := List.eq_nil_of_length_eq_zero hl.symm
    subst this
    rfl
  | cons c cs ih =>
    intro cs' k sl g hl hc
    obtain ⟨c', cs', rfl⟩ : ∃ c' cs'', cs' = c' :: cs'' := by
      rcases cs' with _ | ⟨c', cs''⟩
      · simp at hl
      · exact ⟨c', cs'', rfl⟩
    rcases sl with _ | ⟨pk, _ | ⟨pk1, rest⟩⟩
    · rfl
    · rfl
    · simp only [geomAuxC]
      have h0 := hc 0 (by simp) (by simp) (D.slotAnchor (k + 1) pk1) g
      simp only [add_zero, List.getD_cons_zero, List.getElem_cons_zero] at h0
      rw [h0]
      refine ih cs' (k + 1) (pk1 :: rest) _ (by simpa using hl) ?_
      intro j hj hj' s' g'
      have := hc (j + 1) (by simp; omega) (by simp; omega) s' g'
      simpa [List.getD_cons_succ, add_assoc, add_comm 1 j] using this

/-- **The complex chain geometry is invariant under the child-phase translations.** -/
theorem geomC_shiftChild (D : OCData) (hε : ∀ k, D.eps k ≠ 0) (dd : ChainData) {n : ℕ}
    (x : ChainParamsC n) (k : Fin n) {v : Vec 2}
    (hv : ∃ m : ℤ, v (transverseIndex (dd.slots.getD k 0)) = m) :
    geomC D dd (x.shiftChild k v) = geomC D dd x := by
  unfold geomC
  refine geomAuxC_congr D _ _ _ _ _ (by simp) ?_
  intro j hj hj' s' g
  have hjn : j < n := by simpa using hj
  simp only [List.getElem_ofFn]
  by_cases hjk : j = (k : ℕ)
  · have hk : (⟨j, hjn⟩ : Fin n) = k := Fin.ext hjk
    simp only [ChainParamsC.shiftChild, hk, Function.update_self]
    subst hjk
    exact childGeomC_shift D (hε _) _ _ _ _ hv
  · have hk : (⟨j, hjn⟩ : Fin n) ≠ k := fun h => hjk (congrArg Fin.val h)
    simp only [ChainParamsC.shiftChild, Function.update_of_ne hk]

/-- The last family of a chain is invariant under the child-phase translations. -/
theorem chainFam_shiftChild (D : OCData) (hε : ∀ k, D.eps k ≠ 0) (dd : ChainData) {n : ℕ}
    (x : ChainParamsC n) (k : Fin n) {v : Vec 2}
    (hv : ∃ m : ℤ, v (transverseIndex (dd.slots.getD k 0)) = m) :
    (chainFam D dd n).fl (x.shiftChild k v) = (chainFam D dd n).fl x ∧
      (chainFam D dd n).ctr (x.shiftChild k v) = (chainFam D dd n).ctr x := by
  have e : (chainFam D dd n).toGeom (x.shiftChild k v) = (chainFam D dd n).toGeom x := by
    rw [chainFam_toGeom D hε, chainFam_toGeom D hε, geomC_shiftChild D hε dd x k hv]
  exact ⟨congrArg Prod.fst e, congrArg (fun g : CGeom => g.2.1) e⟩

/-- The last family of a chain does not depend on the final phase. -/
theorem chainFam_final (D : OCData) (hε : ∀ k, D.eps k ≠ 0) (dd : ChainData) {n : ℕ}
    (x : ChainParamsC n) (z : CVec) :
    (chainFam D dd n).fl (x.1, x.2.1, z) = (chainFam D dd n).fl x ∧
      (chainFam D dd n).ctr (x.1, x.2.1, z) = (chainFam D dd n).ctr x := by
  have e : (chainFam D dd n).toGeom (x.1, x.2.1, z) = (chainFam D dd n).toGeom x := by
    rw [chainFam_toGeom D hε, chainFam_toGeom D hε]
    rfl
  exact ⟨congrArg Prod.fst e, congrArg (fun g : CGeom => g.2.1) e⟩

/-- The jacobian of the last family is invariant under the child-phase translations. -/
theorem jacC_chainFam_shiftChild (D : OCData) (hε : ∀ k, D.eps k ≠ 0) (dd : ChainData) {n : ℕ}
    (x : ChainParamsC n) (k : Fin n) {v : Vec 2}
    (hv : ∃ m : ℤ, v (transverseIndex (dd.slots.getD k 0)) = m) (t : ℝ) :
    (chainFam D dd n).jacC (x.shiftChild k v) t = (chainFam D dd n).jacC x t := by
  obtain ⟨e1, e2⟩ := chainFam_shiftChild D hε dd x k hv
  unfold CFam.jacC
  rw [e1, e2]

/-- The jacobian of the last family does not depend on the final phase. -/
theorem jacC_chainFam_final (D : OCData) (hε : ∀ k, D.eps k ≠ 0) (dd : ChainData) {n : ℕ}
    (x : ChainParamsC n) (z : CVec) (t : ℝ) :
    (chainFam D dd n).jacC (x.1, x.2.1, z) t = (chainFam D dd n).jacC x t := by
  obtain ⟨e1, e2⟩ := chainFam_final D hε dd x z
  unfold CFam.jacC
  rw [e1, e2]

/-- The carrier is invariant under the child-phase translations. -/
theorem mem_carrierC_shiftChild_iff {D : OCData} {b : ℝ} {dd : ChainData} {n : ℕ} {mres : ℝ}
    (x : ChainParamsC n) (k : Fin n) (v : Vec 2) :
    x.shiftChild k v ∈ carrierC D b dd n mres ↔ x ∈ carrierC D b dd n mres := by
  have hc : ∀ j : Fin n, (x.shiftChild k v).2.1 j =
      if j = k then ((x.2.1 k).1, (x.2.1 k).2 + ofRealVec v) else x.2.1 j := by
    intro j
    by_cases hj : j = k
    · subst hj; simp [ChainParamsC.shiftChild]; rfl
    · simp [ChainParamsC.shiftChild, hj]
  unfold carrierC
  simp only [Set.mem_ofPred_eq]
  refine and_congr Iff.rfl (and_congr (forall_congr' fun j => ?_) Iff.rfl)
  rw [hc j]
  by_cases hj : j = k
  · subst hj; simp [ofRealVec]
  · simp [hj]

/-- The carrier is invariant under the final-phase translations. -/
theorem mem_carrierC_shiftFinal_iff {D : OCData} {b : ℝ} {dd : ChainData} {n : ℕ} {mres : ℝ}
    (x : ChainParamsC n) (v : Vec 2) :
    x.shiftFinal v ∈ carrierC D b dd n mres ↔ x ∈ carrierC D b dd n mres := by
  unfold carrierC ChainParamsC.shiftFinal
  simp

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Set Filter Topology Metric Complex
open scoped Interval
namespace AVRegularity.Providers.ComplexFlow

/-! **The velocity of a complex family** (`F_u(h)` is continuously differentiable in `u`, and
`‖∂_uF_u F_u^{-1}‖ ≤ 2Υa_k`). A velocity of a family `(𝔛, x, s)` is a field `V_P(t, y)`, holomorphic
in the parameters and the point, such that the two-time flow has the first-order expansion
`𝔛_P(u, y, t) = y + (u - t) V_P(t, y) + o(u - t)` as `u → t` in the window, uniformly on the ball of
radius `ϱ` around the transported center (`CFam.VelOK`).
* `hasDerivWithinAt_fderiv_of_expansion`: by the Cauchy formula on a circle, a uniform first-order
  expansion in time gives the time derivative of the directional derivatives;
* `VelOK.hasDerivWithinAt_jacC`: by the group law, the Jacobian `F_u(0)` of the family is
  differentiable in time with `∂_uF_u = 𝖲 F_u`, where the strain `𝖲 = DV_P(t, c_P(t))`
  (`strainMat`) is holomorphic in the parameters (`VelOK.differentiableOn_strainMat`);
* `VelOK.norm_fderiv_le`: the strain is bounded by the two-time rate `Λ`. -/

open AVRegularity.Providers.GenSem

/-! ### Time derivatives of directional derivatives -/

theorem norm_cauchyKernel {r : ℝ} (hr : 0 < r) (θ : ℝ) : ‖cauchyKernel r θ‖ = r⁻¹ := by
  rw [cauchyKernel, norm_mul, norm_I, one_mul, norm_inv, norm_circleMap_zero, abs_of_pos hr]

/-- The component of a derivative is the derivative of the component. -/
theorem fderiv_apply_proj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → CVec}
    {y : E} (hf : DifferentiableAt ℂ f y) (w : E) (c : Fin 2) :
    fderiv ℂ (fun z => f z c) y w = fderiv ℂ f y w c := by
  have h2 : HasFDerivAt (fun z => f z c)
      ((ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).comp (fderiv ℂ f y)) y :=
    (ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).hasFDerivAt.comp y hf.hasFDerivAt
  rw [h2.fderiv]
  rfl

/-- **The time derivative of a directional derivative** from a uniform first-order expansion in
time on a disc in the direction. -/
theorem hasDerivWithinAt_fderiv_of_expansion {G : ℝ → CVec → CVec} {H : CVec → CVec}
    {U : Set CVec} (hU : IsOpen U) {W : Set ℝ} {t : ℝ} (ht : t ∈ W)
    (hG : ∀ u ∈ W, DifferentiableOn ℂ (G u) U) (hH : DifferentiableOn ℂ H U) {y w : CVec}
    {r : ℝ} (hr : 0 < r) (hyU : ∀ ζ : ℂ, ‖ζ‖ ≤ r → y + ζ • w ∈ U)
    (hexp : ∀ ε > 0, ∀ᶠ u in 𝓝[W] t, ∀ ζ : ℂ, ‖ζ‖ ≤ r →
      ‖G u (y + ζ • w) - (y + ζ • w) - (u - t) • H (y + ζ • w)‖ ≤ ε * |u - t|) :
    HasDerivWithinAt (fun u => fderiv ℂ (G u) y w) (fderiv ℂ H y w) W t := by
  have hy : y ∈ U := by simpa using hyU 0 (by simp [hr.le])
  have hcirc : ∀ θ : ℝ, ‖circleMap 0 r θ‖ ≤ r := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hr]
  have hGt : ∀ ζ : ℂ, ‖ζ‖ ≤ r → G t (y + ζ • w) = y + ζ • w := by
    intro ζ hζ
    have h := ((hexp 1 one_pos).self_of_nhdsWithin ht) ζ hζ
    rw [sub_self, abs_zero, mul_zero, zero_smul, sub_zero, norm_le_zero_iff, sub_eq_zero] at h
    exact h
  have hdiffG : ∀ u ∈ W, DifferentiableAt ℂ (G u) y := fun u hu =>
    (hG u hu y hy).differentiableAt (hU.mem_nhds hy)
  have hdiffH : DifferentiableAt ℂ H y := (hH y hy).differentiableAt (hU.mem_nhds hy)
  have hproj : ∀ (f : CVec → CVec) (c : Fin 2), DifferentiableOn ℂ f U →
      DifferentiableOn ℂ (fun z => f z c) U := fun f c hf z hz =>
    (ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).differentiableAt.comp_differentiableWithinAt z
      (hf z hz)
  have hid : ∀ c : Fin 2, fderiv ℂ (fun z : CVec => z c) y w = w c := by
    intro c
    show fderiv ℂ (ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ) y w = w c
    rw [ContinuousLinearMap.fderiv]
    rfl
  -- the value at `u = t`
  have hval : ∀ c : Fin 2, fderiv ℂ (G t) y w c = w c := by
    intro c
    have h1 := fderiv_apply_eq_circle hU (hproj (G t) c (hG t ht)) hr hyU
    have h2 := fderiv_apply_eq_circle hU (hproj (fun z : CVec => z) c differentiableOn_id) hr hyU
    rw [← fderiv_apply_proj (hdiffG t ht), h1, ← hid c, h2]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hGt _ (hcirc θ)]
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c' hc'
  filter_upwards [hexp (c' * r) (by positivity), self_mem_nhdsWithin] with u hu huW
  have hC : 0 ≤ c' * ‖u - t‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg hC).mpr fun c => ?_
  set g : CVec → ℂ := fun z => G u z c - z c - ((u - t : ℝ) : ℂ) * H z c with hg
  have hgd : DifferentiableOn ℂ g U :=
    ((hproj (G u) c (hG u huW)).sub (hproj (fun z : CVec => z) c differentiableOn_id)).sub
      ((hproj H c hH).const_mul _)
  have hgval : (fderiv ℂ (G u) y w - fderiv ℂ (G t) y w - (u - t) • fderiv ℂ H y w) c =
      fderiv ℂ g y w := by
    have hA : HasFDerivAt (fun z => G u z c)
        ((ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).comp (fderiv ℂ (G u) y)) y :=
      (ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).hasFDerivAt.comp y (hdiffG u huW).hasFDerivAt
    have hB : HasFDerivAt (fun z : CVec => z c) (ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ) y :=
      (ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).hasFDerivAt
    have hCc : HasFDerivAt (fun z => H z c)
        ((ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).comp (fderiv ℂ H y)) y :=
      (ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).hasFDerivAt.comp y hdiffH.hasFDerivAt
    have hgD : HasFDerivAt g (((ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).comp
        (fderiv ℂ (G u) y) - (ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ)) -
        ((u - t : ℝ) : ℂ) • (ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).comp (fderiv ℂ H y)) y :=
      (hA.sub hB).sub (hCc.const_mul ((u - t : ℝ) : ℂ))
    rw [hgD.fderiv]
    simp only [Pi.sub_apply, Pi.smul_apply, hval c, sub_apply, smul_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply,
      Complex.real_smul, smul_eq_mul]
  rw [hgval, fderiv_apply_eq_circle hU hgd hr hyU, norm_smul]
  have hbd : ‖∫ θ in (0 : ℝ)..2 * Real.pi, cauchyKernel r θ • g (y + circleMap 0 r θ • w)‖ ≤
      r⁻¹ * (c' * r * |u - t|) * |2 * Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [norm_smul, norm_cauchyKernel hr]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := hu _ (hcirc θ)
    have e : g (y + circleMap 0 r θ • w) = (G u (y + circleMap 0 r θ • w) -
        (y + circleMap 0 r θ • w) - (u - t) • H (y + circleMap 0 r θ • w)) c := by
      simp only [hg, Pi.sub_apply, Pi.smul_apply, Complex.real_smul]
    rw [e]
    exact (norm_le_pi_norm _ c).trans h1
  have h2pi : ‖(2 * Real.pi * I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, norm_I, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_ofNat]
  rw [h2pi]
  refine (mul_le_mul_of_nonneg_left hbd (by positivity)).trans (le_of_eq ?_)
  rw [sub_zero, abs_of_pos Real.two_pi_pos, Real.norm_eq_abs]
  field_simp

/-- **Holomorphy of a directional derivative in the second variable** along a holomorphic
direction. -/
theorem differentiableOn_fderiv_snd_apply {Par : Type*} [NormedAddCommGroup Par]
    [NormedSpace ℂ Par] [FiniteDimensional ℂ Par] {Φ : Par × CVec → CVec}
    {U : Set (Par × CVec)} (hU : IsOpen U) (hΦ : DifferentiableOn ℂ Φ U)
    {g : Par × CVec → CVec} (hg : DifferentiableOn ℂ g U) :
    DifferentiableOn ℂ (fun q => fderiv ℂ (fun z => Φ (q.1, z)) q.2 (g q)) U := by
  have hΦc : ∀ c : Fin 2, DifferentiableOn ℂ (fun q => Φ q c) U := fun c q hq =>
    (ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).differentiableAt.comp_differentiableWithinAt q
      (hΦ q hq)
  have hD : ∀ (b c : Fin 2), DifferentiableOn ℂ
      (fun q => fderiv ℂ (fun q => Φ q c) q ((0 : Par), cbasis b)) U := fun b c =>
    differentiableOn_fderiv_apply hU (hΦc c) _
  have hR : DifferentiableOn ℂ (fun q => fun c => ∑ b : Fin 2,
      g q b * fderiv ℂ (fun q => Φ q c) q ((0 : Par), cbasis b)) U := by
    refine differentiableOn_pi.2 fun c => ?_
    refine DifferentiableOn.fun_sum fun b _ => ?_
    exact ((differentiableOn_pi.1 hg) b).mul (hD b c)
  refine hR.congr fun q hq => ?_
  have hdq : DifferentiableAt ℂ Φ q := (hΦ q hq).differentiableAt (hU.mem_nhds hq)
  have hinr : HasFDerivAt (fun z : CVec => ((q.1, z) : Par × CVec))
      (ContinuousLinearMap.inr ℂ Par CVec) q.2 :=
    (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
  have hch : HasFDerivAt (fun z => Φ (q.1, z))
      ((fderiv ℂ Φ q).comp (ContinuousLinearMap.inr ℂ Par CVec)) q.2 := by
    have := hdq.hasFDerivAt
    exact this.comp q.2 hinr
  rw [hch.fderiv]
  funext c
  have hv : ((0 : Par), g q) = ∑ b : Fin 2, g q b • ((0 : Par), cbasis b) := by
    refine Prod.ext ?_ ?_
    · simp
    · ext a
      fin_cases a <;> simp [cbasis]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inr_apply]
  rw [hv, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, fderiv_apply_proj hdq]

/-! ### The velocity of a family -/

namespace CFam

variable {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]

/-- **A velocity of a complex family**: a field `V_P(t, y)`, holomorphic in the parameters and the
point near the transported centers, with the uniform first-order expansion
`𝔛_P(u, y, t) = y + (u - t) V_P(t, y) + o(u - t)`. -/
structure VelOK (F : CFam Par) (Ω : Set Par) (W : Set ℝ) (ϱ : ℝ)
    (Vel : Par → ℝ → CVec → CVec) : Prop where
  hol : ∀ t ∈ W, DifferentiableOn ℂ (fun q : Par × CVec => Vel q.1 t q.2) (F.dom Ω ϱ t)
  lim : ∀ P ∈ Ω, ∀ t ∈ W, ∀ ε > 0, ∀ᶠ u in 𝓝[W] t, ∀ y ∈ ball (F.cur P t) ϱ,
    ‖F.fl P u y t - y - (u - t) • Vel P t y‖ ≤ ε * |u - t|

/-- The strain matrix `𝖲 = DV_P(t, c_P(t))`. -/
def strainMat (F : CFam Par) (Vel : Par → ℝ → CVec → CVec) (P : Par) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun a b => fderiv ℂ (Vel P t) (F.cur P t) (cbasis b) a

variable {F : CFam Par} {Ω : Set Par} {W : Set ℝ} {ϱ Λ T : ℝ} {Vel : Par → ℝ → CVec → CVec}

namespace VelOK

theorem vel_hol (hV : F.VelOK Ω W ϱ Vel) {P : Par} (hP : P ∈ Ω) {t : ℝ} (ht : t ∈ W) :
    DifferentiableOn ℂ (Vel P t) (ball (F.cur P t) ϱ) :=
  (hV.hol t ht).comp ((differentiableOn_const P).prodMk differentiableOn_id) fun _ hy => ⟨hP, hy⟩

/-- **The directional derivatives of the flow are differentiable in time.** -/
theorem hasDerivWithinAt_fderiv (h : F.OK Ω W ϱ Λ T) (hV : F.VelOK Ω W ϱ Vel) {P : Par}
    (hP : P ∈ Ω) {t : ℝ} (ht : t ∈ W) {y : CVec} (hy : y ∈ ball (F.cur P t) (ϱ / 2))
    (w : CVec) :
    HasDerivWithinAt (fun u => fderiv ℂ (fun z => F.fl P u z t) y w)
      (fderiv ℂ (Vel P t) y w) W t := by
  have hϱ := h.hϱ
  set r : ℝ := ϱ / 4 / (‖w‖ + 1) with hr_def
  have hw1 : 0 < ‖w‖ + 1 := by positivity
  have hr : 0 < r := by positivity
  have hyU : ∀ ζ : ℂ, ‖ζ‖ ≤ r → y + ζ • w ∈ ball (F.cur P t) ϱ := by
    intro ζ hζ
    have h1 : ‖ζ • w‖ ≤ ϱ / 4 := by
      rw [norm_smul]
      calc ‖ζ‖ * ‖w‖ ≤ r * (‖w‖ + 1) :=
            mul_le_mul hζ (by linarith) (norm_nonneg _) hr.le
        _ = ϱ / 4 := by rw [hr_def]; field_simp
    rw [mem_ball] at hy ⊢
    calc dist (y + ζ • w) (F.cur P t) ≤ dist y (F.cur P t) + ‖ζ • w‖ := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]; exact norm_add_le _ _
      _ < ϱ := by linarith
  refine hasDerivWithinAt_fderiv_of_expansion isOpen_ball ht
    (fun u hu => h.differentiableOn_fl hP hu ht) (hV.vel_hol hP ht) hr hyU fun ε hε => ?_
  filter_upwards [hV.lim P hP t ht ε hε] with u hu ζ hζ
  exact hu _ (hyU ζ hζ)

/-- The derivative of the flow at equal times is the identity. -/
theorem fderiv_fl_self (h : F.OK Ω W ϱ Λ T) {P : Par} (hP : P ∈ Ω) {t : ℝ} (ht : t ∈ W)
    {y : CVec} (hy : y ∈ ball (F.cur P t) ϱ) :
    fderiv ℂ (fun z => F.fl P t z t) y = ContinuousLinearMap.id ℂ CVec := by
  have e : (fun z => F.fl P t z t) =ᶠ[𝓝 y] id := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    exact h.init P hP t ht z hz
  rw [e.fderiv_eq, fderiv_id]

/-- **The strain is bounded by the two-time rate.** -/
theorem norm_fderiv_le (h : F.OK Ω W ϱ Λ T) (hV : F.VelOK Ω W ϱ Vel) {P : Par} (hP : P ∈ Ω)
    {t : ℝ} (ht : t ∈ W) (hne : (𝓝[W \ {t}] t).NeBot) {y : CVec}
    (hy : y ∈ ball (F.cur P t) (ϱ / 2)) (w : CVec) :
    ‖fderiv ℂ (Vel P t) y w‖ ≤ Λ * ‖w‖ := by
  have hy' : y ∈ ball (F.cur P t) ϱ := ball_subset_ball (by linarith [h.hϱ]) hy
  have hd := (hV.hasDerivWithinAt_fderiv h hP ht hy w)
  rw [hasDerivWithinAt_iff_tendsto_slope] at hd
  have := hne
  refine le_of_tendsto (hd.norm) ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu1 : u ∈ W := hu.1
  have hu2 : u ≠ t := hu.2
  have hJ := h.jac P hP u hu1 t ht y hy'
  rw [slope_def_module]
  simp only [fderiv_fl_self h hP ht hy', ContinuousLinearMap.id_apply]
  rw [norm_smul, norm_inv, Real.norm_eq_abs]
  have hpos : 0 < |u - t| := abs_pos.mpr (sub_ne_zero.mpr hu2)
  rw [inv_mul_le_iff₀ hpos]
  have e : fderiv ℂ (fun z => F.fl P u z t) y w - w =
      (fderiv ℂ (fun z => F.fl P u z t) y - ContinuousLinearMap.id ℂ CVec) w := by simp
  rw [e]
  calc ‖(fderiv ℂ (fun z => F.fl P u z t) y - ContinuousLinearMap.id ℂ CVec) w‖
      ≤ ‖fderiv ℂ (fun z => F.fl P u z t) y - ContinuousLinearMap.id ℂ CVec‖ * ‖w‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ Λ * |u - t| * ‖w‖ := mul_le_mul_of_nonneg_right hJ (norm_nonneg _)
    _ = |u - t| * (Λ * ‖w‖) := by ring

/-- The entries of the strain matrix are bounded by the two-time rate. -/
theorem norm_strainMat_le (h : F.OK Ω W ϱ Λ T) (hV : F.VelOK Ω W ϱ Vel) {P : Par} (hP : P ∈ Ω)
    {t : ℝ} (ht : t ∈ W) (hne : (𝓝[W \ {t}] t).NeBot) (a b : Fin 2) :
    ‖F.strainMat Vel P t a b‖ ≤ Λ := by
  have h1 := hV.norm_fderiv_le h hP ht hne (mem_ball_self (by linarith [h.hϱ])) (cbasis b)
  rw [norm_cbasis, mul_one] at h1
  exact (norm_le_pi_norm _ a).trans h1

/-- A linear map of `ℂ²` applied to a vector, in coordinates. -/
theorem clm_apply_eq_sum (L : CVec →L[ℂ] CVec) (v : CVec) (a : Fin 2) :
    L v a = ∑ b : Fin 2, L (cbasis b) a * v b := by
  have hv : v = ∑ b : Fin 2, v b • cbasis b := by
    ext c
    simp [cbasis, Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [hv]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **The Jacobian of the family is differentiable in time**: `∂_uF_u = 𝖲 F_u`. -/
theorem hasDerivWithinAt_jacC (h : F.OK Ω W ϱ Λ T) (hV : F.VelOK Ω W ϱ Vel) {P : Par}
    (hP : P ∈ Ω) {t : ℝ} (ht : t ∈ W) (a c : Fin 2) :
    HasDerivWithinAt (fun u => F.jacC P u a c) ((F.strainMat Vel P t * F.jacC P t) a c) W t := by
  have hϱ := h.hϱ
  set J : CVec := fderiv ℂ (fun y => F.fl P t y F.anc) (F.ctr P) (cbasis c) with hJ
  have hctr : F.ctr P ∈ ball (F.cur P F.anc) (ϱ / 4) := by
    rw [h.cur_anc P hP]; exact mem_ball_self (by linarith)
  -- the chain rule through the group law
  have hchain : ∀ u ∈ W, F.jacC P u a c =
      fderiv ℂ (fun z => F.fl P u z t) (F.cur P t) J a := by
    intro u hu
    have e : (fun y => F.fl P u y F.anc) =ᶠ[𝓝 (F.ctr P)]
        (fun z => F.fl P u z t) ∘ (fun y => F.fl P t y F.anc) := by
      filter_upwards [isOpen_ball.mem_nhds hctr] with y hy
      exact (h.group P hP u hu t ht F.anc h.anc_mem y hy).symm
    have hd1 : DifferentiableAt ℂ (fun y => F.fl P t y F.anc) (F.ctr P) :=
      h.differentiableAt_fl hP ht h.anc_mem (ball_subset_ball (by linarith) hctr)
    have hd2 : DifferentiableAt ℂ (fun z => F.fl P u z t) (F.fl P t (F.ctr P) F.anc) := by
      refine h.differentiableAt_fl hP hu ht ?_
      show F.cur P t ∈ ball (F.cur P t) ϱ
      exact mem_ball_self hϱ
    have hcomp := HasFDerivAt.comp (f := fun y => F.fl P t y F.anc) (F.ctr P) hd2.hasFDerivAt
      hd1.hasFDerivAt
    show fderiv ℂ (fun y => F.fl P u y F.anc) (F.ctr P) (cbasis c) a = _
    rw [e.fderiv_eq, hcomp.fderiv]
    rfl
  have hd := hasDerivWithinAt_pi.1 (hV.hasDerivWithinAt_fderiv h hP ht
    (mem_ball_self (by linarith : 0 < ϱ / 2)) J) a
  refine (hd.congr (fun u hu => hchain u hu) (hchain t ht)).congr_deriv ?_
  rw [clm_apply_eq_sum, Matrix.mul_apply]
  rfl

/-- **The strain is holomorphic in the parameters.** -/
theorem differentiableOn_strainMat [FiniteDimensional ℂ Par] (h : F.OK Ω W ϱ Λ T)
    (hV : F.VelOK Ω W ϱ Vel) {t : ℝ} (ht : t ∈ W) (a b : Fin 2) :
    DifferentiableOn ℂ (fun P => F.strainMat Vel P t a b) Ω := by
  have hD := differentiableOn_fderiv_snd_apply (h.isOpen_dom ht) (hV.hol t ht)
    (g := fun _ => cbasis b) (differentiableOn_const _)
  have hmaps : MapsTo (fun P => ((P, F.cur P t) : Par × CVec)) Ω (F.dom Ω ϱ t) :=
    fun P hP => ⟨hP, mem_ball_self h.hϱ⟩
  have h2 := hD.comp (differentiableOn_id.prodMk (h.cur_hol ht)) hmaps
  exact (differentiableOn_pi.1 h2) a

end VelOK

end CFam

end AVRegularity.Providers.ComplexFlow
end
