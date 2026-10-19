-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.PaperFacing.Basic
import AVRegularity.IterationPassage.Cascade.OutputData
import AVRegularity.Construction.Preservation.FullLift.UniformNativeNormalizedJointBounds
import AVRegularity.Construction.Preservation.Buffer.OrderZeroPhysicalWeakIdentity
import AVRegularity.Construction.Preservation.Buffer.KernelMaterialIncrement
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.CycleReference.FluxFastDiscrepancy

/-! # Solutions of admissible families at the parameters

* `paperStage_level_le`: a cascade stage has level at most that of its seed.
* `paperStage_solution`: existence and uniqueness of the order-zero solution of a cascade stage
  with its stage invariant (Schur price `θ ≤ 1/8`), from any start in its window: the operator of
  `nativeInvariantKernelOperator` (the route to `kernel_energy_torus`), `stageSol_exists` and
  `native_reg_solution_unique`.
* `paperFamily_solution`: the same for an admissible family (`IsPaperFamily`) of level
  `m ≥ m_E + 1` at the parameters; every premise of the operator is discharged from the
  parameters: `1 ≤ m`, `j₀ ≤ m` (`energy_start`), `m ≤ M` (the seed level is below `M`),
  `κ_m > 0` (band chain), `0 < c₀ ≤ 1` (`IsInvariantAdmissible`, `seed_c₀_le`),
  `k_I.H_prod = k_I.G₀ + H + 1` (`IsInvariantAdmissible`), `2 ≤ D_{H+1}`, and the Schur price
  `C_I ε_{m-1}^{qτ'} ≤ 1/8` (`energy_floor`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.PaperFacing

open AVRegularity.Finite.Assembly

/-- A cascade stage has level at most the level of its seed. -/
theorem paperStage_level_le {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {P : ProvParams}
    {Mn : SuccMenu} {seed G : GenStage D ScalarH Dm bw j₀} (hc : IsCascadeStage D P Mn seed G) :
    G.level ≤ seed.level := by
  induction hc with
  | seed => exact le_rfl
  | @step G G' _ hsucc ih =>
    calc (G'.retained G.level Mn.H Mn.J).level = G'.level := rfl
      _ = G.level - 1 := hsucc.2.1
      _ ≤ seed.level := by omega

/-- Existence and uniqueness of the order-zero solution of a cascade stage with its invariant
(Schur price `θ ≤ 1/8`) from every start `s ∈ [t_A, t_f]`. -/
theorem paperStage_solution {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (law : BirthLaw) (P : ProvParams) (Mn : SuccMenu) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (Mnat : ℕ) (kI : InvConsts) (tA tf S θ : ℝ)
    (seed G : GenStage D ScalarH Dm bw j₀) (m : ℕ) (hlev : G.level = m)
    (hI : IsStageInvariant law P seedK freshK φ₀ hφ₀ Mnat kI tA tf S θ G)
    (hseed : ∀ v : CompIn seed.comps, v.1.births = [])
    (hc : IsCascadeStage D P Mn seed G) (hk : kI.Hprod = kI.G0 + Mn.H + 1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hi : 1 ≤ m) (hj : j₀ ≤ m) (hterm : m ≤ D.term)
    (hb : 0 < bw) (hκ : 0 < D.κ m) (hc₀ : 0 < kI.c₀) (hc₀1 : kI.c₀ ≤ 1) (hD : 2 ≤ Dm)
    (hθ : θ ≤ 1 / 8) (s : ℝ) (hs : tA ≤ s) (hst : s ≤ tf)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) :
    (∃ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
        (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
        (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
      G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ m) (streamVel (D.Φ m)) 0 s tf f
        (fun _ _ => 0) (fun _ _ => 0) U Uw Uk) ∧
    ∀ (U U' : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Uw Uw' : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
      (Uk Uk' : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
      G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ m) (streamVel (D.Φ m)) 0 s tf f
        (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
      G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ m) (streamVel (D.Φ m)) 0 s tf f
        (fun _ _ => 0) (fun _ _ => 0) U' Uw' Uk' →
      ∀ v, ∀ t ∈ Set.Icc s tf, U v t = U' v t := by
  refine ⟨IterationPassage.Cascade.stageSol_exists law P Mn seedK freshK φ₀ hφ₀ Mnat kI tA tf S θ
    seed G m hlev hI hseed hc hk hq hΛ hi hj hterm hb hκ hc₀ hc₀1 hD hθ s hs hst f, ?_⟩
  intro U U' Uw Uw' Uk Uk' hU hU'
  subst hlev
  have he (i : ℕ) : 0 < D.eps i := (Scales.epsilon_basic (m := i) hq hΛ).1
  have hνeq : D.kap G.level = D.κ G.level := by rw [OCData.kap, min_eq_left hterm]
  have hν : 0 < D.kap G.level := hνeq ▸ hκ
  have hρ : 0 < rhoStar D kI.c₀ G.level :=
    mul_pos hc₀ (lt_min (he _) (Real.sqrt_pos.mpr
      (div_pos hκ (Real.rpow_pos_of_pos (he _) _))))
  have hρε : rhoStar D kI.c₀ G.level ≤ D.eps (G.level - 1) :=
    ((mul_le_mul_of_nonneg_left (min_le_left _ _) hc₀.le).trans
      (mul_le_of_le_one_left (he _).le hc₀1)).trans
      (EntryScales.epsilon_antitone hq hΛ (Nat.sub_le _ _))
  let P₀ := Construction.Preservation.Buffer.nativeInvariantKernelOperator law P Mn seedK freshK
    φ₀ hφ₀ Mnat kI tA tf S θ seed G hI hseed hc hk hq hΛ hi hj hb (he _) (hs.trans hst) hν hρ hρε
    hD hθ 0 (Nat.zero_le _) (fun _ => 1) (Or.inl rfl)
  let P₁ := Construction.Preservation.Buffer.kernelOperator_time_restrict P₀
    (Set.Icc_subset_Icc hs le_rfl) hst
  rw [← hνeq] at hU hU'
  have hsmall : (1 : ℝ) * rhoStar D kI.c₀ G.level / (2 * rhoStar D kI.c₀ G.level) ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hρ)).mpr
    ring_nf
    exact le_rfl
  exact Construction.Preservation.FullLift.native_reg_solution_unique P seedK freshK φ₀ hφ₀ G
    P₁ rfl rfl rfl (D.hΦ G.level) 0 1 (2 * rhoStar D kI.c₀ G.level) (le_refl 0) (le_refl 1)
    (mul_pos (by norm_num) hρ) hsmall
    (by simpa using (div_pos hν (by norm_num : (0 : ℝ) < 8)).le)
    (fun _ _ _ hl _ => by omega) f U U' Uw Uw' Uk Uk' hU hU'

/-- Existence and uniqueness of the order-zero solution of an admissible family of level
`m ≥ m_E + 1` at the parameters, from every start `s ∈ [t_A, t_f]`. -/
theorem paperFamily_solution {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (P : PaperParameters α s q ζ Λ Jw t₀ T₀) (hΛ : 128 ≤ Λ) {D : OCData}
    (hDq : D.q = P.ready.cfg.q) (hDΛ : D.Λ = P.ready.cfg.Λ) {M : ℕ}
    (hband : IsOCBandChain P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ P.ready.cfg.ζ M D.κ)
    (hterm : D.term = M) (Mnat : ℕ) (law : BirthLaw) (seedK freshK : ℕ → KernelSpec)
    (G : GenStage D ScalarH (paperFamilyOrder P.ready.cfg) P.ready.cfg.bw P.ready.cfg.j₀)
    (m : ℕ) (tA tf : ℝ)
    (hG : IsPaperFamily P.ready.cfg M Mnat law seedK freshK G m tA tf)
    (hm : P.mEnergy + 1 ≤ m) (s₀ : ℝ) (hs : tA ≤ s₀) (hst : s₀ ≤ tf)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) :
    (∃ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
        (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
        (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ →
          TorusHk (0 + paperFamilyOrder P.ready.cfg - 1) (ScalarH u.1.root)),
      G.IsRegSolution (paperProv P.ready.cfg D) seedK freshK P.ready.cfg.φ₀ P.ready.cfg.hφ₀
        (D.κ m) (streamVel (D.Φ m)) 0 s₀ tf f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk) ∧
    ∀ (U U' : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Uw Uw' : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
      (Uk Uk' : ∀ v u (_ : G.fam.Γ v u), ℝ →
        TorusHk (0 + paperFamilyOrder P.ready.cfg - 1) (ScalarH u.1.root)),
      G.IsRegSolution (paperProv P.ready.cfg D) seedK freshK P.ready.cfg.φ₀ P.ready.cfg.hφ₀
        (D.κ m) (streamVel (D.Φ m)) 0 s₀ tf f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
      G.IsRegSolution (paperProv P.ready.cfg D) seedK freshK P.ready.cfg.φ₀ P.ready.cfg.hφ₀
        (D.κ m) (streamVel (D.Φ m)) 0 s₀ tf f (fun _ _ => 0) (fun _ _ => 0) U' Uw' Uk' →
      ∀ v, ∀ t ∈ Set.Icc s₀ tf, U v t = U' v t := by
  obtain ⟨tS, seed, n, _htS, ⟨hgen, _hmol, hnM, _hlen⟩, hc, hlev, hI⟩ := hG
  have hvalid := P.ready.valid
  have hΛc : 128 ≤ P.ready.cfg.Λ := by rw [P.ready.base.2.2.2.2.1]; exact hΛ
  have hmn : m ≤ n := by
    have h := paperStage_level_le hc
    rw [hlev, hgen.1] at h
    exact h
  obtain ⟨hc₀eq, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, hHprod, _⟩ := P.invariant
  have hθ : P.ready.cfg.CI * D.eps (m - 1) ^ (P.ready.cfg.q * paperTauPrime P.ready.cfg) ≤ 1 / 8 := by
    have h := P.energy_floor (m - 1) (by omega)
    change P.ready.cfg.CI * ocEpsilon D.q D.Λ (m - 1) ^ _ ≤ _
    rw [hDq, hDΛ]
    exact h
  exact paperStage_solution law (paperProv P.ready.cfg D) (paperMenu P.ready.cfg Mnat) seedK freshK
    P.ready.cfg.φ₀ P.ready.cfg.hφ₀ Mnat P.ready.cfg.kI tA tf _ _ seed G m hlev hI hgen.2.1 hc
    hHprod (by rw [hDq]; exact hvalid.hq.1) (by rw [hDΛ]; exact hΛc) (by omega)
    (P.energy_start.trans (by omega)) (by rw [hterm]; omega) hvalid.hbw
    (CycleReference.bandChain_pos (by omega) hvalid.hζ hband (by omega))
    (by rw [hc₀eq]; exact hvalid.hc₀) (by rw [hc₀eq]; exact P.seed_c₀_le)
    (by change 2 ≤ succSchedD _ _ _ _ + 2 * _ + 4 * _ + 4; omega) hθ s₀ hs hst f

end AVRegularity.PaperFacing
