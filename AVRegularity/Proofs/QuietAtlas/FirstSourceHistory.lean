-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.QuietAtlas.FirstSourceHistoryGeom
import AVRegularity.Proofs.QuietAtlas.Successor.QuietMatching
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.GenSem.Jet.Chart

/-! **The first-source array reads only the history**
(`FirstSourceHistoryStatement`, the first-source analog of `transferAt_eq_of_histEq`). For two
admissible contexts with the same history geometry, the first-source flux at the center agrees:
* the Piola chart (centered map and inverse) at the output time agrees (`famMap_eq_of_histEq`);
* the context strain at every recentered context agrees (`contextStrain_eq_of_histEq`; the time
  derivative is read within the pulse window, endpoints included);
* the assembled diagonal mean flux agrees as a germ (`diagMeanFluxCtx_histGerm`): every active
  finer slot is scheduled, its appended children are admissible and have the same history, and
  the finer diagonal-label fluxes read only the history (the hypothesis);
* the covariance polynomial `𝖰_p` reads only that germ (`covPolyQ_eq_of_eventuallyEq`).
The proof is that of `firstSourceFlux_phase`, with two chains at one phase in place of one chain
at two phases. With it, `quietHistoryPreservation_of_firstSourceHistory` carries the invariant for
every presentation. -/

@[expose] public noncomputable section

open Homogenization Filter Topology

namespace AVRegularity.Providers.QuietAtlas

variable (D : OCData)

open scoped Classical in
/-- **One finer slot of the assembled diagonal mean flux** at two appended children with the same
chart and the same finer flux germs. -/
theorem diagTerm_histGerm (hζ : IsFastProfile D.ζ) {b : ℝ} {j₀ Dm m : ℕ} {ρ : ℝ}
    {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)} {t : ℝ} {A A' : RealChain}
    {k : ℤ} {n : ℕ}
    (hadm : IsAdmissibleChain D b j₀ m k A ↔ IsAdmissibleChain D b j₀ m k A')
    (hΨ : A.famMap D t = A'.famMap D t) (hΨi : A.famMapInv D t = A'.famMapInv D t)
    (hL : ∀ f, diagLabelFlux D Dm m ρ Cc0 k A n t f =ᶠ[𝓝 0]
      diagLabelFlux D Dm m ρ Cc0 k A' n t f) (g : Vec 2 → ℝ) :
    (fun x => if IsAdmissibleChain D b j₀ m k A then
        ocCutoff D.α D.q D.Λ m k t • pushFlux (A.famMap D t) (A.famMapInv D t)
          (diagLabelFlux D Dm m ρ Cc0 k A n t) g x
      else 0) =ᶠ[𝓝 0]
    (fun x => if IsAdmissibleChain D b j₀ m k A' then
        ocCutoff D.α D.q D.Λ m k t • pushFlux (A'.famMap D t) (A'.famMapInv D t)
          (diagLabelFlux D Dm m ρ Cc0 k A' n t) g x
      else 0) := by
  have hcont : Tendsto (A.famMapInv D t) (𝓝 0) (𝓝 0) := by
    have := (GenSem.contDiff_famMapInv (D := D) A t).continuous.tendsto 0
    rwa [GenSem.famMapInv_zero hζ] at this
  have hL' := (hL (g ∘ A.famMap D t)).comp_tendsto hcont
  filter_upwards [hL'] with x hx
  simp only [← hΨ, ← hΨi, ← hadm, pushFlux]
  split_ifs
  · simp only [Function.comp_apply] at hx
    rw [hx]
  · rfl

open scoped Classical in
/-- **The assembled diagonal mean flux** at two contexts of the same slot agrees as a germ when
each active finer slot does. -/
theorem diagMeanFluxCtx_histGerm (hΛ : 1 ≤ D.Λ) {b : ℝ} {j₀ Dm m : ℕ} {ρ : ℝ}
    {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)} {t : ℝ} {ch ch' : RealChain}
    (hslot : ch.slot = ch'.slot) {n : ℕ} {z : Vec 2} (g : Vec 2 → ℝ)
    (hterm : ∀ k : ℤ, Odd k → ocCutoff D.α D.q D.Λ m k t ≠ 0 →
      (fun x => if IsAdmissibleChain D b j₀ m k (ch.appendChild D k t z) then
        ocCutoff D.α D.q D.Λ m k t • pushFlux ((ch.appendChild D k t z).famMap D t)
          ((ch.appendChild D k t z).famMapInv D t)
          (diagLabelFlux D Dm m ρ Cc0 k (ch.appendChild D k t z) n t) g x
      else 0) =ᶠ[𝓝 0]
      (fun x => if IsAdmissibleChain D b j₀ m k (ch'.appendChild D k t z) then
        ocCutoff D.α D.q D.Λ m k t • pushFlux ((ch'.appendChild D k t z).famMap D t)
          ((ch'.appendChild D k t z).famMapInv D t)
          (diagLabelFlux D Dm m ρ Cc0 k (ch'.appendChild D k t z) n t) g x
      else 0)) :
    (fun x => diagMeanFluxCtx D b j₀ Dm m ρ Cc0 t ch z n g x) =ᶠ[𝓝 0]
      (fun x => diagMeanFluxCtx D b j₀ Dm m ρ Cc0 t ch' z n g x) := by
  have hF := CycleReference.ocCutoff_support_finite (α := D.α) (q := D.q) (Λ := D.Λ) (m := m)
    hΛ (t := t)
  have hev := (Filter.eventually_all_finite hF).2 fun k hk => hterm k.1 k.2 hk
  filter_upwards [hev] with x hx
  unfold diagMeanFluxCtx
  rw [hslot]
  refine finsum_congr fun k => finsum_congr fun hk => ?_
  by_cases hkt : ocCutoff D.α D.q D.Λ m k t = 0
  · simp only [hkt, zero_smul, ite_self]
  · exact hx ⟨k, hk.1⟩ hkt

/-- **The first-source array reads only the history** (`FirstSourceHistoryStatement`). -/
theorem firstSourceHistory : FirstSourceHistoryStatement := by
  intro D Dm b j₀ hΛ hζ hb hstart Mtop m hm p C C' hC hC' hh ρ s₀ N pc Cc0 hF t ht z d I
  have hl : C.WellSlotted := hC.2.2.1
  have hl' : C'.WellSlotted := hC'.2.2.1
  have hctx : C.ctxLevel = m := hC.1
  have hctx' : C'.ctxLevel = m := hC'.1
  have hslot : C.slot = p := hC.2.2.2.1
  have hslot' : C'.slot = p := hC'.2.2.2.1
  have hW : ocPulseWindow D.α D.q D.Λ m p ⊆ availInterval D Mtop m p :=
    ocPulseWindow_subset_availInterval D Mtop m p
  have htI : t ∈ availInterval D Mtop m p := hW ht
  have hτ : 0 < ocTau D.α D.q D.Λ m := Construction.Stream.ocTau_pos hΛ
  have hlr : ((p : ℝ) - 61 / 48) * ocTau D.α D.q D.Λ m < ((p : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m :=
    mul_lt_mul_of_pos_right (by linarith) hτ
  have hΦ := famMap_eq_of_histEq hh htI
  have hΦi := famMapInv_eq_of_famMap_eq hζ hΦ
  -- the context strain at every recentered context
  have hS : ∀ (y w : Vec 2), contextStrain D m p t (C.recenter D y) w =
      contextStrain D m p t (C'.recenter D y) w := fun y w =>
    contextStrain_eq_of_histEq D hζ (recenter_wellSlotted D hl y) (recenter_wellSlotted D hl' y)
      (histEq_recenter D hζ hl hl' hh y) hlr hW ht m p w
  -- the diagonal flux, as a germ
  have hdiag : ∀ g : Vec 2 → ℝ,
      (fun x => diagFluxCtx D b j₀ Dm (m + 1) ρ N Cc0 t C z g x) =ᶠ[𝓝 0]
        (fun x => diagFluxCtx D b j₀ Dm (m + 1) ρ N Cc0 t C' z g x) := by
    intro g
    have hn : ∀ n ∈ (insert 2 (Set.Icc 3 (N + 1)) : Set ℕ),
        (fun x => diagMeanFluxCtx D b j₀ Dm (m + 1) ρ Cc0 t C z n g x) =ᶠ[𝓝 0]
          (fun x => diagMeanFluxCtx D b j₀ Dm (m + 1) ρ Cc0 t C' z n g x) := by
      intro n hn
      refine diagMeanFluxCtx_histGerm D hΛ (by rw [hslot, hslot']) g fun k hk hkt => ?_
      have hsch : IsScheduledIn D m k p := ⟨t, Function.mem_support.mpr hkt, ht⟩
      have hA := GenSem.appendChild_admissible D hΛ hζ hb hstart m p C hC k hk hsch t hkt z
      have hA' := GenSem.appendChild_admissible D hΛ hζ hb hstart m p C' hC' k hk hsch t hkt z
      have hJ := availInterval_child_subset D hm hk hsch
      have hskJ := slotAnchor_mem_availInterval D Mtop (m + 1) k
      have happ := histEq_appendChild D hl hl' (by rw [hctx, hctx']) (by rw [hslot, hslot']) hh
        k t z (by rw [hctx]; exact hJ hskJ) hJ
      have hsame := (histEq_iff_sameHistory D _ _ happ.1).mp happ
      have htJ : t ∈ availInterval D Mtop (m + 1) k := mem_availInterval_of_ocCutoff D hΛ hkt
      have htw := GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero
        (Construction.Stream.ocTau_pos hΛ) hkt
      exact diagTerm_histGerm D hζ ⟨fun _ => hA', fun _ => hA⟩
        (famMap_eq_of_histEq happ htJ) (famMapInv_eq_of_famMap_eq hζ (famMap_eq_of_histEq happ htJ))
        (fun f => hF n hn k hk _ _ hA hA' hsame t htw f) g
    have h2 := hn 2 (Set.mem_insert _ _)
    have h3 := (Filter.eventually_all_finset (Finset.Icc 3 (N + 1))).2 fun n hn' =>
      hn n (Set.mem_insert_of_mem _ (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hn'))
    filter_upwards [h2, h3] with x hx2 hx3
    unfold diagFluxCtx
    rw [hx2, Finset.sum_congr rfl hx3]
  -- the flux at the center
  unfold fluxCoeff
  congr 1
  simp only [firstSourceFlux, pullFlux, GenSem.famMap_zero, hΦ, hΦi, hslot, hslot',
    Nat.add_sub_cancel, hS]
  congr 1
  refine covPolyQ_eq_of_eventuallyEq _ pc ?_
  filter_upwards [hdiag (covPolyP (ocCovariance D.α D.q D.Λ D.ζ (m + 1) (D.κ (m + 1))
    (D.κ m) s₀ t) pc ((fun Y => ∏ j, (Y - 0) (I j)) ∘ C'.famMapInv D t))] with x hx
  rw [hx]

/-! ### One-passage preservation of the carried invariant, for any presentation -/

end AVRegularity.Providers.QuietAtlas
