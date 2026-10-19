-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.ComplexChain.VelChild
public import AVRegularity.Proofs.ComplexChain.Vel
import AVRegularity.Construction.Stream.NextAdmissible
import Mathlib.RingTheory.PicardGroup

/-! **The velocity of the last family of a scheduled chain.** Along a scheduled chain
every family has a velocity (`chainFam_velOK`): the base family by `baseFam_velOK` (`baseVelOK`),
and each child by `ChildHyp.velOK`, with the child hypotheses of the step `Over.child`
(`Over.childHyp`) and the nondegenerate windows (`nhdsWithin_Icc_diff_neBot`); the induction along
the chain is `velOK_famAux`. -/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Homogenization AVenhance Metric

namespace AVRegularity.Providers.ComplexFlow

/-- A point of a nondegenerate closed interval is not isolated in it. -/
theorem nhdsWithin_Icc_diff_neBot {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) :
    (𝓝[Icc a b \ {t}] t).NeBot := by
  rcases lt_or_eq_of_le ht.2 with htb | htb
  · have h1 : Ioo t b ⊆ Icc a b \ {t} := fun x hx =>
      ⟨⟨ht.1.trans hx.1.le, hx.2.le⟩, ne_of_gt hx.1⟩
    have : (𝓝[Ioo t b] t).NeBot := by rw [nhdsWithin_Ioo_eq_nhdsGT htb]; infer_instance
    exact this.mono (nhdsWithin_mono t h1)
  · subst htb
    have h1 : Ioo a t ⊆ Icc a t \ {t} := fun x hx => ⟨⟨hx.1.le, hx.2.le⟩, ne_of_lt hx.2⟩
    have : (𝓝[Ioo a t] t).NeBot := by rw [nhdsWithin_Ioo_eq_nhdsLT hab]; infer_instance
    exact this.mono (nhdsWithin_mono t h1)

theorem slotWin_neBot {D : OCData} (hΛ : 1 ≤ D.Λ) (k : ℕ) (p : ℤ) {t : ℝ}
    (ht : t ∈ slotWin D k p) : (𝓝[slotWin D k p \ {t}] t).NeBot := by
  have hh : 0 < ocTauPP D.α D.q D.Λ k := Construction.Stream.ocTauPP_pos hΛ
  exact nhdsWithin_Icc_diff_neBot (by linarith) ht

namespace CFam

variable {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]
variable {F : CFam Par} {Ω : Set Par} {D : OCData} {b : ℝ}

/-- **The child hypotheses of the step `Over.child`.** -/
theorem Over.childHyp {l : ℕ} {p p' : ℤ} (hF : F.Over D b Ω l p) (hS : LevelScales D b l)
    (hζ : IsFastProfile D.ζ) (hp' : IsScheduledIn D (l + 1) p' p) {cc ph : Par → CVec}
    (hcc : DifferentiableOn ℂ cc Ω) (hph : DifferentiableOn ℂ ph Ω)
    (hBc : ∀ P ∈ Ω, ‖cc P‖ ≤ 3 / 4 * b * D.eps (l + 1))
    (hBph : ∀ P ∈ Ω, |((ph P) (transverseIndex p)).im| ≤ phB b) :
    CFam.ChildHyp D F Ω (slotWin D (l + 1) p) (slotWin D (l + 2) p') (8 * b * D.eps l)
      (chainK * ocA D.α D.q D.Λ l) (6 / 5 * ocTauPP D.α D.q D.Λ (l + 1)) (l + 1) p
      (D.slotAnchor (l + 2) p') cc ph (8 * b * D.eps (l + 1)) (6 / 5 * ocTauPP D.α D.q D.Λ (l + 2))
      (3 / 4 * b * D.eps (l + 1)) (phB b) (15 * b * D.eps (l + 1))
      (2 * Real.pi * ocA D.α D.q D.Λ (l + 1) * D.eps (l + 1) * Real.exp (30 * Real.pi * b))
      (4 * Real.pi ^ 2 * ocA D.α D.q D.Λ (l + 1) * Real.exp (30 * Real.pi * b + 1)) := by
  have hΛ1 : 1 ≤ D.Λ := by have := hS.hΛ; omega
  have he : 0 < D.eps (l + 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hE : 0 < D.eps l := Construction.Stream.ocEpsilon_pos hΛ1
  have hA0 : 0 ≤ ocA D.α D.q D.Λ l := Real.rpow_nonneg hE.le _
  have ha0 : 0 ≤ ocA D.α D.q D.Λ (l + 1) := Real.rpow_nonneg he.le _
  have hH0 : 0 ≤ ocTauPP D.α D.q D.Λ (l + 1) := (Construction.Stream.ocTauPP_pos hΛ1).le
  have hh0 : 0 ≤ ocTauPP D.α D.q D.Λ (l + 2) := (Construction.Stream.ocTauPP_pos hΛ1).le
  have hX0 : 0 ≤ Real.exp (30 * Real.pi * b) := (Real.exp_pos _).le
  have hY0 : 0 ≤ Real.exp (30 * Real.pi * b + 1) := (Real.exp_pos _).le
  have hX := exp_small_le hS.hb0.le hS.hb1
  have hY := exp_small_one_le hS.hb0.le hS.hb1
  have hshA : shearAmp D.α D.q D.Λ (l + 1) = 2 * Real.pi * ocA D.α D.q D.Λ (l + 1) * D.eps (l + 1) :=
    shearAmp_eq he
  have hfreq : shearFreq D.q D.Λ (l + 1) * (15 * b * D.eps (l + 1)) = 30 * Real.pi * b := by
    unfold shearFreq
    show 2 * Real.pi * (D.eps (l + 1))⁻¹ * (15 * b * D.eps (l + 1)) = 30 * Real.pi * b
    field_simp
    ring
  have hfreq0 : 0 ≤ shearFreq D.q D.Λ (l + 1) := (shearFreq_pos he).le
  have hAF : shearAmp D.α D.q D.Λ (l + 1) * shearFreq D.q D.Λ (l + 1) =
      4 * Real.pi ^ 2 * ocA D.α D.q D.Λ (l + 1) := by
    rw [hshA]
    unfold shearFreq
    show 2 * Real.pi * ocA D.α D.q D.Λ (l + 1) * D.eps (l + 1) * (2 * Real.pi * (D.eps (l + 1))⁻¹) = _
    field_simp
    ring
  have hMs : ∀ w : CVec, |(w (transverseIndex p)).im| ≤ 15 * b * D.eps (l + 1) →
      ‖ocShearVelC D.α D.q D.Λ (l + 1) p w‖ ≤
        2 * Real.pi * ocA D.α D.q D.Λ (l + 1) * D.eps (l + 1) * Real.exp (30 * Real.pi * b) := by
    intro w hw
    refine (norm_ocShearVelC_le _ _ _ _ _ he w).trans ?_
    rw [hshA, ← hfreq]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw hfreq0))
      (by have := Real.pi_pos; positivity)
  have hMs' : ∀ w : CVec, |(w (transverseIndex p)).im| ≤ 15 * b * D.eps (l + 1) →
      ‖fderiv ℂ (ocShearVelC D.α D.q D.Λ (l + 1) p) w‖ ≤
        4 * Real.pi ^ 2 * ocA D.α D.q D.Λ (l + 1) * Real.exp (30 * Real.pi * b + 1) := by
    intro w hw
    refine (norm_fderiv_ocShearVelC_le _ _ _ _ _ he w).trans ?_
    rw [hAF, ← hfreq]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_left hw hfreq0]))
      (by have := Real.pi_pos; positivity)
  have hu0 := step_u_nonneg hA0 hH0
  have hu := step_u_le hA0 hH0 hS.hAH
  have hw0 := step_w_nonneg (X := Real.exp (30 * Real.pi * b)) he ha0 hh0 hX0
  have hw := step_w_le he ha0 hh0 hS.hah hX0 hX
  have hrate := step_rate hS.hb0 hS.hb1 he hS.heps hA0 hS.hA hH0 hS.hAH hX0 hX hY0 hY
  have hwin := step_window hS.hb1 ha0 hh0 hS.hah
  have hT'0 : 0 ≤ 6 / 5 * ocTauPP D.α D.q D.Λ (l + 2) := by positivity
  have hC : CFam.ChildHyp D F Ω (slotWin D (l + 1) p) (slotWin D (l + 2) p') (8 * b * D.eps l)
      (chainK * ocA D.α D.q D.Λ l) (6 / 5 * ocTauPP D.α D.q D.Λ (l + 1)) (l + 1) p
      (D.slotAnchor (l + 2) p') cc ph (8 * b * D.eps (l + 1)) (6 / 5 * ocTauPP D.α D.q D.Λ (l + 2))
      (3 / 4 * b * D.eps (l + 1)) (phB b) (15 * b * D.eps (l + 1))
      (2 * Real.pi * ocA D.α D.q D.Λ (l + 1) * D.eps (l + 1) * Real.exp (30 * Real.pi * b))
      (4 * Real.pi ^ 2 * ocA D.α D.q D.Λ (l + 1) * Real.exp (30 * Real.pi * b + 1)) :=
    { hF := hF.ok
      hζ := hζ
      hε := he
      hcc := hcc
      hph := hph
      hW' := slotWin_subset D hΛ1 hp' hS.hsep
      hs' := anchor_mem_slotWin D hΛ1 (l + 2) p'
      hT' := fun u hu r hr => abs_sub_le_of_mem_slotWin D hu hr
      hϱ' := by have := hS.hb0; positivity
      hBc0 := by have := hS.hb0; positivity
      hBph0 := by unfold phB; have := hS.hb0; positivity
      hMs0 := by have := Real.pi_pos; positivity
      hMs'0 := by positivity
      hBc := hBc
      hBph := hBph
      hMs := hMs
      hMs' := hMs'
      hσ := step_sigma hS.hb0 hS.hb1 he hu hw
      hRa := step_Ra hS.hb0 hS.hb1 he hS.heps hu hw0 hw
      hRb := step_Rb hS.hb0 hS.hb1 he hS.heps hu hw
      hΛT' := (mul_le_mul_of_nonneg_right hrate hT'0).trans hwin }
  exact hC


/-- **The velocity of the base family over its slot.** -/
theorem baseVelOK {l : ℕ} {V : ℝ}
    (hv : HolField (velC D.α D.q D.Λ D.ζ l) (D.eps l / 50) (velA * ocA D.α D.q D.Λ l) V)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 10000) (hΛ : 1 ≤ D.Λ)
    (hAH : ocA D.α D.q D.Λ l * ocTauPP D.α D.q D.Λ (l + 1) ≤ b / 10000)
    {ctr : Par → CVec} (hB : ∀ P ∈ Ω, imL1 (ctr P) ≤ 15 / 1000 * D.eps l) (p : ℤ) :
    (baseFam (velC D.α D.q D.Λ D.ζ l) (baseW D l) ctr (D.slotAnchor (l + 1) p)).VelOK Ω
      (slotWin D (l + 1) p) (8 * b * D.eps l) (fun _ t y => velC D.α D.q D.Λ D.ζ l t y) := by
  have hE : 0 < D.eps l := Construction.Stream.ocEpsilon_pos hΛ
  have hA0 : 0 ≤ ocA D.α D.q D.Λ l := Real.rpow_nonneg hE.le _
  have hH0 : 0 ≤ ocTauPP D.α D.q D.Λ (l + 1) := (Construction.Stream.ocTauPP_pos hΛ).le
  obtain ⟨c1, c2, c3, c4, c5⟩ := base_consts hb1 hE hA0 hH0 hAH
  set s := D.slotAnchor (l + 1) p
  set h := ocTauPP D.α D.q D.Λ (l + 1)
  have hba : (s + 3 / 5 * h) - (s - 3 / 5 * h) = 6 / 5 * h := by ring
  have hvA : velA * ocA D.α D.q D.Λ l = 2 ^ 21 * ocA D.α D.q D.Λ l := by unfold velA; ring
  have hw : FlowWin (D.eps l / 50) (baseW D l) (velA * ocA D.α D.q D.Λ l) (s - 3 / 5 * h)
      (s + 3 / 5 * h) :=
    { hℓ' := by unfold baseW; positivity
      hℓℓ := by unfold baseW; linarith
      hab := by linarith
      hΓT := by rw [hba, hvA]; exact c2 }
  exact baseFam_velOK hv hw (W := slotWin D (l + 1) p) subset_rfl fun P hP r hr =>
    baseFam_ball_subset hv hw subset_rfl (B₀ := 15 / 1000 * D.eps l) hB
      (by have := hb0; positivity) (by rw [hba, hvA]; unfold baseW; exact c3)
      (anchor_mem_slotWin D hΛ (l + 1) p) hP hr

/-- **Along a scheduled chain every family has a velocity.** -/
theorem velOK_famAux [FiniteDimensional ℂ Par] (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) {B : ℕ}
    (hS : ∀ l, B ≤ l → LevelScales D b l) :
    ∀ (cs : List (Par → CVec × CVec)) (l : ℕ) (p : ℤ) (ps : List ℤ) (F : CFam Par)
      (Vel : Par → ℝ → CVec → CVec),
      B ≤ l → F.Over D b Ω l p → F.VelOK Ω (slotWin D (l + 1) p) (8 * b * D.eps l) Vel →
      cs.length = ps.length →
      (∀ j, j < ps.length →
        IsScheduledIn D (l + 1 + j) ((p :: ps).getD (j + 1) 0) ((p :: ps).getD j 0)) →
      (∀ j, j < cs.length → DifferentiableOn ℂ (cs.getD j 0) Ω ∧
        (∀ P ∈ Ω, ‖(cs.getD j 0 P).1‖ ≤ 3 / 4 * b * D.eps (l + 1 + j)) ∧
        ∀ P ∈ Ω, |((cs.getD j 0 P).2 (transverseIndex ((p :: ps).getD j 0))).im| ≤ phB b) →
      ∃ Vel', (famAux D (l + 1) (p :: ps) cs F).VelOK Ω
        (slotWin D (l + cs.length + 1) ((p :: ps).getLastD 0)) (8 * b * D.eps (l + cs.length))
        Vel' := by
  intro cs
  induction cs with
  | nil =>
    intro l p ps F Vel _ _ hV hlen _ _
    have hps : ps = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst hps
    exact ⟨Vel, hV⟩
  | cons c cs ih =>
    intro l p ps F Vel hl hF hV hlen hsch hcs
    obtain ⟨p1, ps', rfl⟩ : ∃ p1 ps', ps = p1 :: ps' := by
      rcases ps with _ | ⟨p1, ps'⟩
      · simp at hlen
      · exact ⟨p1, ps', rfl⟩
    have hlen' : cs.length = ps'.length := by simpa using hlen
    have h0 := hcs 0 (by simp)
    simp only [List.getD_cons_zero] at h0
    have hs0 : IsScheduledIn D (l + 1) p1 p := by simpa using hsch 0 (by simp)
    have hC := hF.childHyp (hS l hl) hζ hs0 h0.1.fst h0.1.snd h0.2.1 h0.2.2
    have hF' := hF.child (hS l hl) hζ hs0 h0.1.fst h0.1.snd h0.2.1 h0.2.2
    have hV' := hC.velOK hV fun t ht => slotWin_neBot hΛ (l + 1) p (hC.hW' ht)
    have hrec := ih (l + 1) p1 ps' _ _ (by omega) hF' hV' hlen'
      (fun j hj => by
        have := hsch (j + 1) (by simp; omega)
        simp only [List.getD_cons_succ] at this
        rwa [show l + 1 + (j + 1) = l + 1 + 1 + j by omega] at this)
      (fun j hj => by
        have := hcs (j + 1) (by simp; omega)
        simp only [List.getD_cons_succ] at this
        rwa [show l + 1 + (j + 1) = l + 1 + 1 + j by omega] at this)
    have e1 : l + (c :: cs).length = l + 1 + cs.length := by simp; omega
    have e2 : (p :: p1 :: ps').getLastD 0 = (p1 :: ps').getLastD 0 := by simp
    rw [e1, e2]
    exact hrec

end CFam

/-- **The last family of a scheduled chain has a velocity.** -/
theorem chainFam_velOK {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ} (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (hα : D.α < 1 / 3) (hζ : IsFastProfile D.ζ)
    (hvel : ∀ m, ∃ V, HolField (velC D.α D.q D.Λ D.ζ m) (D.eps m / 50) (velA * ocA D.α D.q D.Λ m) V)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 10000) (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ)
    (hcs : IsCarrierStart D.α D.q D.Λ b CH Υ j₀) {dd : ChainData} {n : ℕ} (hdd : ChainOK D j₀ dd n) :
    ∃ Vel, (chainFam D dd n).VelOK (carrierC D b dd n 2)
      (slotWin D (dd.baseLevel + n + 1) (dd.slots.getLastD 0)) (8 * b * D.eps (dd.baseLevel + n))
      Vel := by
  have hΛ1 : 1 ≤ D.Λ := by omega
  obtain ⟨p, ps, hsl⟩ : ∃ p ps, dd.slots = p :: ps := by
    rcases h : dd.slots with _ | ⟨p, ps⟩
    · have := hdd.len; rw [h] at this; simp at this
    · exact ⟨p, ps, rfl⟩
  have hlen : ps.length = n := by have := hdd.len; rw [hsl] at this; simpa using this
  have hS : ∀ l, dd.baseLevel ≤ l → LevelScales D b l := fun l hl =>
    levelScales_of_carrierStart hq hΛ hα hb0 hb1 hCH hΥ hcs (by have := hdd.base; omega)
  obtain ⟨V, hv⟩ := hvel dd.baseLevel
  have hB : ∀ x ∈ carrierC D b dd n 2, imL1 x.1 ≤ 15 / 1000 * D.eps dd.baseLevel := by
    intro x hx
    have := hx.1
    unfold imL1
    linarith
  have hbase := CFam.baseOver (Ω := carrierC D b dd n 2) hv hb0 hb1 hΛ1
    (smallness_of_carrierStart hΛ1 hCH hΥ hcs hdd.base) (isOpen_carrierC D b dd n 2)
    differentiableOn_fst hB p
  have hbaseV := CFam.baseVelOK (Ω := carrierC D b dd n 2) hv hb0 hb1 hΛ1
    (smallness_of_carrierStart hΛ1 hCH hΥ hcs hdd.base) (ctr := fun x => x.1) hB p
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
  have hrec := CFam.velOK_famAux hζ hΛ1 hS (List.ofFn fun j (x : ChainParamsC n) => x.2.1 j)
    dd.baseLevel p ps _ _ le_rfl hbase hbaseV (by simp [hlen]) hsch hchild
  rw [List.length_ofFn] at hrec
  exact hrec

end AVRegularity.Providers.ComplexFlow
