-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryTerminal.Ingredients.SeedStruct.SeedStruct
public import AVRegularity.EntryTerminal.Assembly.Seed.SeedLedgerAssembly
public import AVRegularity.Construction.StageEnvelopes.SuccessorPreparation
public import AVRegularity.Construction.StageEnvelopes.Cauchy.Assembly
import AVRegularity.Construction.Preservation.FullLift.NativeHigherRetainedFromSameOrder
import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm
import AVRegularity.EntryTerminal.Assembly.Seed.OfParts
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.EntryTerminal.Ingredients.SeedQuiet.Proof
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal

section
section
/-! **The identity maps of the terminal seed have norm at most one** (sampled bound). The weak
stage carries `‖C_γ‖ ≤ 1`.
- A root path of such maps has norm `≤ 1` (`rootPathMap_norm_le_one`).
- The maps of a successor source are identity maps of the stage
  (`succSource_maps_norm_le_one`), so the actual successor's maps have norm `≤ 1`
  (`actualSuccessor_map_norm_le_one`).
- The re-rooting copies the maps (`seed_map_norm_le_one_of_encoding`).

Special cases: the empty path (the identity or `0`); a path through a zero map. -/

@[expose] public noncomputable section

namespace AVRegularity.EntryTerminal.Ingredients

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- A root path of maps of norm `≤ 1` has norm `≤ 1`. -/
theorem rootPathMap_norm_le_one : ∀ (r₀ : ℕ) (l : List (Σ (a c : ℕ), hr a →L[ℝ] hr c)) (r : ℕ),
    (∀ x ∈ l, ‖x.2.2‖ ≤ 1) → ‖rootPathMap hr r₀ l r‖ ≤ 1
  | r₀, [], r, _ => EntryWeakProofs.rootPathMap_empty_norm_le_one (hr := hr) r₀ r
  | r₀, ⟨a, c, f⟩ :: rest, r, hl => by
    have hrest := rootPathMap_norm_le_one c rest r fun x hx => hl x (List.mem_cons_of_mem _ hx)
    simp only [rootPathMap]
    split_ifs with h
    · have hf : ‖(h ▸ f : hr r₀ →L[ℝ] hr c)‖ ≤ 1 := by
        subst h
        exact hl _ List.mem_cons_self
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul hrest hf (norm_nonneg _) zero_le_one).trans (mul_one 1).le)
    · simp

/-- The maps of a successor source are identity maps of the stage. -/
theorem succSource_maps_norm_le_one {G : GenStage D hr Dm b j₀}
    (hG : ∀ v u (γ : G.fam.Γ v u), ‖(G.fam.identity v u γ).map‖ ≤ 1) (s : SuccSource G) :
    ∀ x ∈ s.maps, ‖x.2.2‖ ≤ 1 := by
  have hpath : ∀ {h : ℕ} (π : StagePath G h), ∀ x ∈ π.mapList, ‖x.2.2‖ ≤ 1 := by
    intro h π x hx
    rw [StagePath.mapList, List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    exact hG _ _ _
  cases s with
  | copyDir t v u γ =>
    intro x hx
    simp only [SuccSource.maps, List.mem_singleton] at hx
    subst hx
    exact hG v u γ
  | copyQuad t h π => exact hpath π
  | letterDiag t u => intro x hx; simp [SuccSource.maps] at hx
  | letterMean t n h π => exact hpath π
  | letterCov t n h a a' π => exact hpath π

/-- The identity maps of an actual successor have norm `≤ 1` when those of the stage do. -/
theorem actualSuccessor_map_norm_le_one {P : ProvParams} {Mn : SuccMenu}
    {G G' : GenStage D hr Dm b j₀} (hact : IsActualSuccessor D P Mn G G')
    (hG : ∀ v u (γ : G.fam.Γ v u), ‖(G.fam.identity v u γ).map‖ ≤ 1) :
    ∀ v u (γ : G'.fam.Γ v u), ‖(G'.fam.identity v u γ).map‖ ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, e, _, _, _, _, hall⟩ := hact
  intro v u γ
  rw [(hall v u γ).2.1]
  exact rootPathMap_norm_le_one _ _ _ (succSource_maps_norm_le_one hG _)

/-- The re-rooting copies the identity maps. -/
theorem seed_map_norm_le_one_of_encoding {Dt Ds : ℕ} {Pt : ProvParams} {lawT : BirthLaw}
    {rootM rootR : ℕ → ℝ} {seedKt freshKt seedKc : ℕ → KernelSpec}
    {Gt : GenStage D ScalarH Dt b j₀} {seed : GenStage D ScalarH Ds b j₀}
    {ι : CompIn Gt.comps ≃ CompIn seed.comps}
    (he : IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc Gt seed ι)
    (hGt : ∀ v u (γ : Gt.fam.Γ v u), ‖(Gt.fam.identity v u γ).map‖ ≤ 1) :
    ∀ v u (γ : seed.fam.Γ v u), ‖(seed.fam.identity v u γ).map‖ ≤ 1 := by
  obtain ⟨-, -, -, -, -, -, e, _idx, -, hdata⟩ := he
  intro v u γ
  obtain ⟨v₀, rfl⟩ := ι.surjective v
  obtain ⟨u₀, rfl⟩ := ι.surjective u
  obtain ⟨γ₀, rfl⟩ := (e v₀ u₀).surjective γ
  obtain ⟨-, -, hmap, -⟩ := hdata v₀ u₀ γ₀
  rw [hmap]
  exact hGt v₀ u₀ γ₀

end AVRegularity.EntryTerminal.Ingredients
end
end

section
/-! **The higher lengths of the seed against its molecular radius** (E5 part 4, the envelope
input). At late terminal levels `M`, for every `c₀, c_r > 0` and `C_L`:
- the fresh length `ρ = c_r√(Bh) = ρ_enh(M)` is at most `ρ_*(c₀, M−1)`, by
  `uniform_enhanced_radius_le_parent_molecular`;
- the weak lengths satisfy `C_L ε_{M+1} ≤ c_r ε_M ≤ c_r √(κ_{M-1} τ''_M) = ρ`. The first step uses
  `ε_{M+1} ≤ 2ε_M^q` and the decay of `ε_M^{q−1}`; the second is `ε_M ≤ ℓ_lift(M)` from the
  pass scales (as in `successor_higher_lengths`).

Special cases: `C_L ≤ 0` (trivial); `c_r = 1`; `c₀` small (the threshold grows, the radius
comparison stays). -/

@[expose] public noncomputable section

open Homogenization Filter
open scoped Topology

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.EntryTerminal.Route

/-- **The seed's envelope radius dominates the terminal lengths** at late levels. -/
theorem seedEnv_scales (X : TermConstruction) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ (c₀ cr CL : ℝ), 0 < c₀ → 0 < cr →
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M → ∀ D : OCData, D.α = X.α → D.q = X.q → D.Λ = Λ →
      D.ζ = X.ζ → IsOCBandChain X.α X.q Λ X.ζ M D.κ → D.term = M →
      D.termRho cr M ≤ rhoStar D c₀ (M - 1) ∧ CL * D.eps (M + 1) ≤ rhoStar D c₀ (M - 1) := by
  obtain ⟨Λr, hΛr, hradius⟩ :=
    Construction.Preservation.FullLift.uniform_enhanced_radius_le_parent_molecular X.hα₀ X.hα₁
      X.hs₀ X.hs₁ X.hq X.hζ
  obtain ⟨Cu, -, Λp, -, hpass⟩ := Providers.CascadeInvariants.exists_passScales X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq
    X.hζ
  refine ⟨max Λr Λp, le_trans hΛr (le_max_left _ _), fun Λ hΛ c₀ cr CL hc₀ hcr => ?_⟩
  have h128 : 128 ≤ Λ := le_trans hΛr (le_trans (le_max_left _ _) hΛ)
  have hq1 : 1 < X.q := X.hq.1
  obtain ⟨mr, hmr, hrad⟩ := hradius Λ (le_trans (le_max_left _ _) hΛ) c₀ cr hc₀ hcr
  have hδ := (Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq).2.1
  have hdecay := Construction.Preservation.Buffer.preparation_parent_power_tendsto_zero hq1 h128
    (mul_pos (by norm_num : (0 : ℝ) < 3) hδ)
  have hlim : Tendsto (fun m : ℕ => Cu * ocEpsilon X.q Λ (m - 1) ^ (3 * ocDelta X.α X.q))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdecay
  obtain ⟨mp, hmp⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds zero_lt_one))
  have hc0 : 0 ≤ max (CL / cr) 0 := le_max_right _ _
  obtain ⟨Mb, hMb⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 h128
    (sub_pos.mpr hq1) (c := (2 * max (CL / cr) 0 + 1)⁻¹) (by positivity)
  refine ⟨max (max 2 mr) (max mp Mb), le_trans (le_max_left _ _) (le_max_left _ _),
    fun M hM D hDα hDq hDΛ hDζ hband hterm => ?_⟩
  have hM2 : 2 ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hMr : mr ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hMp : mp ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hMb' : Mb ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    rw [hDα, hDq, hDΛ, hDζ, hterm]; exact hband
  -- the fresh length
  have hρ : D.termRho cr M ≤ rhoStar D c₀ (M - 1) :=
    hrad D hDα hDq hDΛ hDζ hbandD M hMr (le_of_eq hterm.symm)
  refine ⟨hρ, ?_⟩
  -- `ε_M ≤ ℓ_lift(M)`
  have hpass' := hpass D hDα hDq hDζ (by rw [hDΛ]; exact le_trans (le_max_right _ _) hΛ)
    (by rw [hDΛ, hterm]; exact hband) M hM2
    (le_of_eq hterm.symm)
  have hsmall : Cu * D.eps (M - 1) ^ (3 * ocDelta D.α D.q) ≤ 1 := by
    simpa only [OCData.eps, hDα, hDq, hDΛ] using hmp M hMp
  have hεlift : D.eps M ≤ liftLength D M := by
    have hds : ocDStar D.q D.Λ M (D.kap M) (D.kap (M - 1)) / liftLength D M ≤ 1 :=
      hpass'.hDρ.trans hsmall
    exact hpass'.hεd.trans ((div_le_one hpass'.hρ0).mp hds)
  -- `C_L ε_{M+1} ≤ c_r ε_M`
  obtain ⟨hε, -, -⟩ := Scales.epsilon_basic (m := M) hq1 h128
  have hstep := Scales.epsilon_q_step hq1 X.hq.2.1 h128 (by omega : 1 ≤ M + 1)
  rw [Nat.add_sub_cancel] at hstep
  have hlen : CL / cr * ocEpsilon X.q Λ (M + 1) ≤ ocEpsilon X.q Λ M :=
    Ingredients.seedStruct_len_le hε (Scales.epsilon_basic (m := M + 1) hq1 h128).1.le le_rfl hstep
      (Ingredients.seedStruct_small_le hc0 (hMb M hMb'))
  have hlen' : CL * D.eps (M + 1) ≤ cr * D.eps M := by
    simp only [OCData.eps, hDq, hDΛ]
    calc CL * ocEpsilon X.q Λ (M + 1) = cr * (CL / cr * ocEpsilon X.q Λ (M + 1)) := by
          field_simp
      _ ≤ cr * ocEpsilon X.q Λ M := mul_le_mul_of_nonneg_left hlen hcr.le
  calc CL * D.eps (M + 1) ≤ cr * D.eps M := hlen'
    _ ≤ cr * liftLength D M := mul_le_mul_of_nonneg_left hεlift hcr.le
    _ = D.termRho cr M := rfl
    _ ≤ rhoStar D c₀ (M - 1) := hρ

end AVRegularity.EntryTerminal.Ingredients
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open AVRegularity.Construction.StageEnvelopes
namespace AVRegularity.EntryTerminal.Ingredients

/-! **The envelope input at the seed is proved** (`seedEnvInputPart`). It follows the
template `successor_context_envelope_preparation`.
- The parameters are `successorEnvelopeParameters` at the seed constants. They read only the
  skeleton of `k_S`: the reserves `2/(H_prod+1)` and `1/(H_prod+1)`, the orders `K_s, K_an, L_an,
  J_m`, and `D̄_s`.
- The floors `C_a^O`, `C_m^O` of the part are the constants of the shared estimate at these
  parameters, so the plan meets them (`SeedFloors.Meets` reads them at `seedSkeleton k_S`).
- The input at the seed:
   - data, stream and carrier: from `IsTermData` and a carrier pair `(1, Υ')` with
     `CarrierOK 100` (`common_carrier_constants`);
   - naturalness and certificate: the premises;
   - level `M − 1`: from the encoding and the successor;
   - the radius `ρ_* = c₀ min(ε, √(κ/A))`, with `0 < c₀ ≤ 1` from the plan;
   - the reserves: the seed's components are roots (grade 0), so `compReserve ≥ 2/(H_prod+1)`
     by `retained_compReserve_ge`;
   - the inner reserve: from the seed allocation;
   - the higher lengths: `actual_successor_higher_lengths` with the weak lengths
     `C_L ε_{M+1}` and the fresh length `ρ`, both `≤ ρ_*(c₀, M−1)` by `seedEnv_scales`, carried
     along the encoding (records and orders are copied).

Special cases: an empty seed (every per-component clause vacuous); `c₀ = 1`; `j₀ = M − 1`. -/

open AVRegularity.EntryTerminal.Route

/-- The envelope parameters of the seed at the constants `k` (they read its skeleton only). -/
def seedEnvParams {X : TermConstruction} (A : TermArgs X) (h128 : 128 ≤ A.Λ) (hb : 0 < A.bw)
    (hb1 : A.bw ≤ 1 / 10000) (k : InvConsts) : ContextEnvelopeParameters :=
  successorEnvelopeParameters X.α X.s X.q A.Λ X.ζ X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq h128 X.hζ A.bw hb hb1
    k A.Ds

/-- The shared envelope estimate at a parameter set. -/
def seedEnvEst (p : ContextEnvelopeParameters) : ContextEnvelopeEstimate p :=
  Classical.choice (Cauchy.context_stage_envelopes p)

/-- **The level and the higher lengths of the seed**: `seed.level = M − 1`, and every identity of
order `≥ 3` has length `≤ ρ_*(c₀, M−1)`, given the fresh length and the weak lengths below
`ρ_*(c₀, M−1)` (`seedEnv_scales`). -/
theorem seedEnv_higherLength {X : TermConstruction} {A : TermArgs X} {sXT sZT : ℕ} {nW : ℕ+}
    {cr CL Cχ : ℝ} {kW : InvConsts} {cP CP cH Cw : ℝ} {j₀ M : ℕ} {D : OCData} {a : ℝ}
    {lawW : BirthLaw} {PW : ProvParams} {Gw : GenStage D ScalarH A.Dt A.bw j₀} {aM tp : ℝ}
    {lawT : BirthLaw} {Gt' : GenStage D ScalarH A.Dt A.bw j₀}
    {seed : GenStage D ScalarH A.Ds A.bw j₀} {rootM rootR : ℕ → ℝ} {seedKc : ℕ → KernelSpec}
    {ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps}
    (hctx : SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed
      rootM rootR seedKc ι) {c₀ : ℝ} (hρ : D.termRho cr M ≤ rhoStar D c₀ (M - 1))
    (hCL : CL * D.eps (M + 1) ≤ rhoStar D c₀ (M - 1)) :
    seed.level = M - 1 ∧ ∀ v u (γ : seed.fam.Γ v u), 3 ≤ (seed.fam.identity v u γ).maxOrder →
      (seed.fam.identity v u γ).record.length ≤ rhoStar D c₀ seed.level := by
  obtain ⟨-, hW, -, -, -, -, hsucc, henc, -, -, -⟩ := hctx
  obtain ⟨-, -, hlevW, -, -, ⟨hseedW, -, -⟩, hrecW, -, -, hinv⟩ := hW
  have hseedlev : seed.level = M - 1 := by
    rw [(seedEncoding_struct henc).1]
    show Gt'.level = M - 1
    rw [hsucc.2.1, hlevW]
  have hGt := actual_successor_higher_lengths (hasTags_of_seed hinv.2.1 hseedW) hsucc
    (ρ := rhoStar D c₀ (M - 1)) (fun v u γ _ => (hrecW v u γ).2.2.1.trans hCL) hρ
  refine ⟨hseedlev, ?_⟩
  obtain ⟨-, -, -, -, -, -, e, _idx, -, hdata⟩ := henc
  intro v u γ h3
  obtain ⟨v₀, rfl⟩ := ι.surjective v
  obtain ⟨u₀, rfl⟩ := ι.surjective u
  obtain ⟨γ₀, rfl⟩ := (e v₀ u₀).surjective γ
  obtain ⟨-, -, -, hrecd, hord, -⟩ := hdata v₀ u₀ γ₀
  rw [hord] at h3
  rw [hrecd, hseedlev]
  exact hGt ⟨v₀.1, Finset.filter_subset _ _ v₀.2⟩ ⟨u₀.1, Finset.filter_subset _ _ u₀.2⟩ γ₀ h3

/-- **The envelope input of the seed.** -/
theorem seedEnvInputPart : SeedEnvInputPart := by
  intro X
  obtain ⟨Λs, hΛs, hsc⟩ := seedEnv_scales X
  refine ⟨Λs, hΛs, fun A hΛ hA Kout => ⟨0, 0, fun sXT sZT _ _ => ?_⟩⟩
  have h128 : 128 ≤ A.Λ := le_trans hΛs hΛ
  have hb : 0 < A.bw := hA.2.2.1.1
  have hb1 : A.bw ≤ 1 / 10000 := hA.2.2.1.2
  let F : SeedFloors :=
    { cker := fun _ _ => 0
      Γk := fun _ => 0
      Cwid := fun _ => 0
      Ca := fun _ => 0
      Cm := fun _ _ => 0
      CaO := fun _ k => (seedEnvEst (seedEnvParams A h128 hb hb1 k)).Ca
      CmO := fun _ k j => (seedEnvEst (seedEnvParams A h128 hb hb1 k)).Cm j }
  refine ⟨0, F, fun Lt nW cr kS hplan cK CL Cχ kW _ _ _ cP CP _ => ?_⟩
  obtain ⟨-, -, -, -, hcr0, -, -, hc0, hc0m, -, -, -, -, halloc, -, hF⟩ := hplan
  obtain ⟨-, -, -, -, -, hCaO, hCmO⟩ := hF
  have hCa : (seedEnvEst (seedEnvParams A h128 hb hb1 kS)).Ca ≤ kS.Ca := hCaO
  have hCm : ∀ j, (seedEnvEst (seedEnvParams A h128 hb hb1 kS)).Cm j ≤ kS.Cm j := hCmO
  have hc01 : kS.c₀ ≤ 1 := hc0m.trans (min_le_left _ _)
  obtain ⟨-, -, -, -, -, -, -, -, hHprod, hmEnv0, hmEnv⟩ := halloc
  obtain ⟨Υ', hcarrier, -⟩ := Cauchy.common_carrier_constants (α := X.α) (q := X.q) (b := A.bw) h128
    (le_refl (1 : ℝ)) one_pos
  obtain ⟨Ms, -, hMs⟩ := hsc A.Λ hΛ kS.c₀ cr CL hc0 hcr0
  intro cH Cw _ _
  refine ⟨0, 1, Υ', le_rfl, lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hcarrier.2),
    fun _ _ j₀ hj₀ => ?_⟩
  refine ⟨max (max Ms (j₀ + 2)) ((seedEnvEst (seedEnvParams A h128 hb hb1 kS)).levelFloor + 2),
    fun M hM => ?_⟩
  have hMs' : Ms ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hMj : j₀ + 2 ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hMf : (seedEnvEst (seedEnvParams A h128 hb hb1 kS)).levelFloor + 2 ≤ M :=
    le_trans (le_max_right _ _) hM
  intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hnat hcert
  have hctx' := hctx
  obtain ⟨hD, -, -, -, -, -, -, henc, -, -, -⟩ := hctx
  obtain ⟨hDα, hDq, hDΛ, hDζ, hstream, hband, hterm⟩ := hD
  obtain ⟨-, hsb, -, -, -, -⟩ := seedEncoding_struct henc
  obtain ⟨hρ, hCL⟩ := hMs M hMs' D hDα hDq hDΛ hDζ hband hterm
  obtain ⟨hseedlev, hhl⟩ := seedEnv_higherLength hctx' hρ hCL
  -- scale facts
  have hqD : 1 < D.q := hDq ▸ X.hq.1
  have hΛD : 128 ≤ D.Λ := hDΛ ▸ h128
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hζD : IsFastProfile D.ζ := hDζ ▸ X.hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    rw [hDα, hDq, hDΛ, hDζ, hterm]; exact hband
  have hε (i : ℕ) : 0 < D.eps i := Construction.Stream.ocEpsilon_pos hΛ1
  have hκ : 0 < D.κ seed.level := CycleReference.bandChain_pos hΛ1 hζD hbandD
    (by rw [hseedlev, hterm]; omega)
  have hrho : 0 < rhoStar D kS.c₀ seed.level := mul_pos hc0
    (lt_min (hε _) (Real.sqrt_pos.mpr (div_pos hκ (Real.rpow_pos_of_pos (hε _) _))))
  have hrhoe : rhoStar D kS.c₀ seed.level ≤ D.eps seed.level :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hc0.le).trans
      (mul_le_of_le_one_left (hε _).le hc01)
  refine ⟨seedEnvParams A h128 hb hb1 kS, seedEnvEst (seedEnvParams A h128 hb hb1 kS), ?_,
    by rw [hseedlev]; omega, hCa, hCm⟩
  refine { bw_eq := rfl
           alpha_eq := hDα
           q_eq := hDq
           base_eq := hDΛ
           profile_eq := hDζ
           stream := hstream
           natural := ⟨_, hnat⟩
           certified := hcert
           level_pos := by rw [hseedlev]; omega
           carrier_start := by rw [hseedlev]; omega
           carrier_environment := ⟨1, Υ', hcarrier, by rw [hDα, hDq, hDΛ]; exact hj₀⟩
           q_pos := hqD
           large := hΛD
           kap_pos := by
             unfold OCData.kap
             exact CycleReference.bandChain_pos hΛ1 hζD hbandD (Nat.min_le_right _ _)
           radius_pos := hrho
           radius_le := hrhoe
           wavelength_le := Providers.CascadeInvariants.eps_le_of_le hqD hΛD (Nat.sub_le _ _)
           inner_nonneg := hmEnv0
           inner_le := ?_
           reserve_le := ?_
           reserve_upper := fun v =>
             (Construction.Preservation.Buffer.compReserve_le_one kS v.1).trans (by norm_num)
           slot_order := le_rfl
           slow_order := le_rfl
           fast_order := le_rfl
           molecular_order := le_rfl
           source_order := fun v u γ => (seed.fam.identity v u γ).le_D
           higher_length := hhl }
  · change kS.mEnv ≤ 1 / ((kS.Hprod : ℝ) + 1)
    exact hmEnv.le
  · intro v
    change 2 / ((kS.Hprod : ℝ) + 1) ≤ compReserve kS v.1
    exact retained_compReserve_ge hHprod (by simp [compGrade, hsb v])

end AVRegularity.EntryTerminal.Ingredients
end
end

section
section
/-! **The sampled coefficient bound of the seed is proved** (`seedSampledPart`).
At one level, for `ϱ ≤ ε_{M-1}`, `k ≤ K_s` and `2 ≤ d ≤ D_γ`:

    coefficientSeminorm ϱ k (physCoeff γ d) ≤ C_e · size γ · κ_{M-1} · length γ^(d−2).

- `uniform_native_physical_kernel_price` at the seed, with `r = length γ`, bounds the left side
  by `κ_{M-1} length^(d−2)` times `K_k ‖C_γ‖ D_γ size γ`, with a constant `K_k` of the order `k`
  fixed before the data. The factor `max 1 ((length/r)^(D_γ−2))` is `1`.
- `‖C_γ‖ ≤ 1`: the weak maps, through the successor and the re-rooting (`MapNorms.lean`).
- Its inputs at the seed:
   - the certificate and naturalness are premises;
   - slot transversality comes from `terminalSuccessor_generation` (`seedE1_slotTransverse`, as in `seedCertAtM_of`);
   - the reserves, from the seed allocation and grade `0`;
   - the higher lengths `≤ ρ_* ≤ ε_{M-1}` (`seedEnv_higherLength`).
- The seminorm is finite (`native_physCoeff_all_order_seminorm_finite`), so the `toReal` bound
  lifts.
- `C_e ≥ Σ_{k ≤ K_s} K_k`; the level threshold is above every starting level `m₀(k)`.

Special cases: `d = 2` (no length factor); an identity of order `2` (no higher length); an empty
seed (vacuous). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev
open AVRegularity.Construction.StageEnvelopes

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.EntryTerminal.Route

/-- **The slot transversality of the seed** at one level, from `terminalSuccessor_generation` at the carrier pair
`(1, 1)` (as in `seedCertAtM_of`). -/
theorem seedE1_slotTransverse {X : TermConstruction} {A : TermArgs X} {sXT sZT : ℕ} {nW : ℕ+}
    {cr : ℝ} {CL Cχ : ℝ} {kW : InvConsts} {cP CP cH Cw : ℝ} {j₀ M : ℕ} {D : OCData} {a : ℝ}
    {lawW : BirthLaw} {PW : ProvParams} {Gw : GenStage D ScalarH A.Dt A.bw j₀} {aM tp : ℝ}
    {lawT : BirthLaw} {Gt' : GenStage D ScalarH A.Dt A.bw j₀}
    {seed : GenStage D ScalarH A.Ds A.bw j₀} {rootM rootR : ℕ → ℝ} {seedKc : ℕ → KernelSpec}
    {ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps}
    (hA : A.Valid) (h128 : 128 ≤ A.Λ) (hcar : IsCarrierStart X.α X.q A.Λ A.bw 1 1 j₀)
    (hX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT) (hcr0 : 0 < cr)
    (hctx : SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed
      rootM rootR seedKc ι) : seed.IsSlotTransverse := by
  obtain ⟨hD, hW, -, -, -, -, hsucc, henc, -, -, -⟩ := hctx
  obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := hD
  have hN : 2 ≤ A.NT := two_le_NT_of_valid A hA
  have hDW : 1 ≤ A.DW := hA.2.2.2.2.2.2.2.2
  have hb : 0 < A.bw := hA.2.2.1.1
  have hΛ1 : 1 ≤ D.Λ := by rw [hΛD]; omega
  have hζ : IsFastProfile D.ζ := by rw [hζD]; exact X.hζ
  have hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    rw [hα, hq, hΛD, hζD, hterm]; exact hband
  have hcar' : IsCarrierStart D.α D.q D.Λ A.bw 1 1 j₀ := by rw [hα, hq, hΛD]; exact hcar
  have hgate := Providers.GenSem.terminalSuccessor_generation hΛ1 hζ hκ hb le_rfl le_rfl hcar' hterm hW
    hN hDW hcr0.ne' hX hZ hsucc
  exact seed_isSlotTransverse_of_encoding henc
    (hgate.2.restrict _ (Finset.filter_subset (IsRetained M 1 A.RT) Gt'.comps))

/-- The price of one identity with `r` its length, `‖C_γ‖ ≤ 1` and `D_γ ≤ D̄`. -/
theorem seedE1_price_le {m Q Cs mo S T Dm L : ℝ} {k e : ℕ} (hm : m ≤ 1)
    (hQ : 0 ≤ Q) (hCs : 0 ≤ Cs) (hmo0 : 0 ≤ mo) (hmo : mo ≤ Dm) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hL : 0 < L) :
    4 * (2 : ℝ) ^ k * m * Q * Cs * max 1 ((L / L) ^ e) * mo * S * T ≤
      4 * (2 : ℝ) ^ k * Q * Cs * Dm * T * S := by
  rw [div_self hL.ne', one_pow, max_self]
  have h1 : m * mo ≤ 1 * Dm := mul_le_mul hm hmo hmo0 zero_le_one
  have hc : 0 ≤ 4 * (2 : ℝ) ^ k * Q * Cs * T := by positivity
  calc 4 * (2 : ℝ) ^ k * m * Q * Cs * 1 * mo * S * T
        = (4 * (2 : ℝ) ^ k * Q * Cs * T) * (m * mo * S) := by ring
    _ ≤ (4 * (2 : ℝ) ^ k * Q * Cs * T) * (1 * Dm * S) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hS) hc
    _ = 4 * (2 : ℝ) ^ k * Q * Cs * Dm * T * S := by ring

/-- **The sampled bound piece of `SeedEnvelopePart`: the sampled coefficient bound of the seed.** -/
theorem seedSampledPart : SeedSampledPart := by
  intro X
  obtain ⟨Λs, hΛs, hsc⟩ := seedEnv_scales X
  refine ⟨Λs, hΛs, fun A hΛ hA Kout => ⟨max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2,
    max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2, fun sXT sZT hX hZ => ⟨0, seedStructFloors, ?_⟩⟩⟩
  intro Lt nW cr kS hplan cK CL Cχ kW _ _ _ cP CP _
  have h128 : 128 ≤ A.Λ := le_trans hΛs hΛ
  have hb : 0 < A.bw := hA.2.2.1.1
  obtain ⟨-, -, -, -, hcr0, -, -, hc0, hc0m, -, -, -, -, halloc, -, -⟩ := hplan
  have hc01 : kS.c₀ ≤ 1 := hc0m.trans (min_le_left _ _)
  obtain ⟨-, -, -, -, -, -, -, -, hHprod, -, -⟩ := halloc
  obtain ⟨Ms, -, hMs⟩ := hsc A.Λ hΛ kS.c₀ cr CL hc0 hcr0
  have hprice := fun n : ℕ =>
    Construction.Preservation.FullLift.uniform_native_physical_kernel_price X.α X.s X.q X.hα₀
      X.hα₁ X.hs₀ X.hs₁ X.hq A.Λ h128 X.ζ X.hζ A.bw hb n (kS.Ks + A.Ds)
  choose C Cs hC hCs m₀ hm₀ hphys using hprice
  let T : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (n + 1), (2 : ℝ) ^ j / (j.factorial : ℝ)
  let Q : ℕ → ℝ := fun n => ((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C n *
    (3 * (kS.Ks + A.Ds + 1 : ℕ) * 2 ^ (kS.Ks + A.Ds) * C n) ^ A.Ds
  let K : ℕ → ℝ := fun n => 4 * (2 : ℝ) ^ A.Ds * Q n * Cs n * (A.Ds : ℝ) * T n
  have hT : ∀ n, 0 ≤ T n := fun n => Finset.sum_nonneg fun j _ =>
    div_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _)
  have hQ : ∀ n, 0 ≤ Q n := fun n => by
    have := zero_le_one.trans (hC n)
    dsimp only [Q]
    positivity
  have hK : ∀ n, 0 ≤ K n := fun n => by
    have := hQ n
    have := hCs n
    have := hT n
    dsimp only [K]
    positivity
  intro cH Cw _ _
  refine ⟨∑ n ∈ Finset.range (kS.Ks + 1), K n, 1, 1, le_rfl, one_pos, fun Ce hCe j₀ hj₀ => ?_⟩
  refine ⟨Ms + j₀ + 3 + ∑ n ∈ Finset.range (kS.Ks + 1), m₀ n, fun M hM => ?_⟩
  intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hnat hcert ϱ hϱ hϱe k hk
    v u γ d hd2 hdo
  have hslot := seedE1_slotTransverse hA h128 hj₀ hX hZ hcr0 hctx
  have hctx' := hctx
  obtain ⟨hD, hW, -, -, -, -, hsucc, henc, -, -, -⟩ := hctx
  obtain ⟨hDα, hDq, hDΛ, hDζ, hstream, hband, hterm⟩ := hD
  obtain ⟨-, -, -, -, -, -, hrecW, -, -, -⟩ := hW
  obtain ⟨-, hsb, -, -, -, -⟩ := seedEncoding_struct henc
  obtain ⟨hρ, hCL⟩ := hMs M (by omega) D hDα hDq hDΛ hDζ hband hterm
  obtain ⟨hseedlev, hhl⟩ := seedEnv_higherLength hctx' hρ hCL
  -- the maps
  have hmap : ‖(seed.fam.identity v u γ).map‖ ≤ 1 :=
    seed_map_norm_le_one_of_encoding henc
      (fun v u γ => actualSuccessor_map_norm_le_one hsucc (fun v u γ => (hrecW v u γ).2.2.2)
        ⟨v.1, Finset.filter_subset _ _ v.2⟩ ⟨u.1, Finset.filter_subset _ _ u.2⟩ γ) v u γ
  -- scales
  have hqD : 1 < D.q := hDq ▸ X.hq.1
  have hΛD : 128 ≤ D.Λ := hDΛ ▸ h128
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hζD : IsFastProfile D.ζ := hDζ ▸ X.hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    rw [hDα, hDq, hDΛ, hDζ, hterm]; exact hband
  have hε (i : ℕ) : 0 < D.eps i := Construction.Stream.ocEpsilon_pos hΛ1
  have hm₀k : m₀ k ≤ ∑ n ∈ Finset.range (kS.Ks + 1), m₀ n :=
    Finset.single_le_sum (fun n _ => Nat.zero_le (m₀ n)) (Finset.mem_range.2 (by omega))
  have hlev : m₀ k + 1 ≤ seed.level := by rw [hseedlev]; omega
  have hν : 0 < D.kap seed.level := by
    unfold OCData.kap
    exact CycleReference.bandChain_pos hΛ1 hζD hbandD (Nat.min_le_right _ _)
  have hkap : D.kap seed.level = D.κ (M - 1) := by
    rw [hseedlev]
    unfold OCData.kap
    rw [hterm, Nat.min_eq_left (Nat.sub_le M 1)]
  have hEE : D.eps seed.level ≤ D.eps (seed.level - 1) :=
    Providers.CascadeInvariants.eps_le_of_le hqD hΛD (Nat.sub_le _ _)
  have hϱe' : ϱ ≤ D.eps seed.level := by rw [hseedlev]; exact hϱe
  have hrhoe : rhoStar D kS.c₀ seed.level ≤ D.eps seed.level :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hc0.le).trans
      (mul_le_of_le_one_left (hε _).le hc01)
  have hRE : 3 ≤ (seed.fam.identity v u γ).maxOrder →
      (seed.fam.identity v u γ).record.length ≤ D.eps (seed.level - 1) :=
    fun h3 => ((hhl v u γ h3).trans hrhoe).trans hEE
  -- the reserves
  have hres : 2 / ((kS.Hprod : ℝ) + 1) ≤ compReserve kS v.1 :=
    retained_compReserve_ge hHprod (by simp [compGrade, hsb v])
  have hm : 0 ≤ compReserve kS v.1 := le_trans (by positivity) hres
  have hm2 : compReserve kS v.1 ≤ 2 :=
    (Construction.Preservation.Buffer.compReserve_le_one kS v.1).trans (by norm_num)
  have hD' := (seed.fam.identity v u γ).le_D
  have hL := (seed.fam.identity v u γ).record.length_pos
  have hp := hphys k ScalarH D hDα hDq hDΛ hDζ hstream A.Ds j₀ (M + A.Jw) seed kS hcert hnat hlev
    (by rw [hseedlev]; omega) (by rw [hseedlev]; omega) (hε _) (hε _) hν hslot
    (tp + D.termH M) (a + A.T₀) v u γ hm hm2 A.Ds d hD' hd2 (hdo.trans hD') (by omega)
    ϱ (seed.fam.identity v u γ).record.length hϱ hL (hϱe'.trans hEE) hϱe' hRE
  have hfin := Construction.Preservation.FullLift.native_physCoeff_all_order_seminorm_finite hcert
    hslot hnat (by rw [hseedlev]; omega) (by rw [hseedlev]; omega) hb (hε _) (tp + D.termH M)
    (a + A.T₀) v u γ hm hm2 ϱ hϱ (hϱe'.trans hEE) k d
  -- the price constant
  have hmo : ((seed.fam.identity v u γ).maxOrder : ℝ) ≤ (A.Ds : ℝ) := by exact_mod_cast hD'
  have hP := seedE1_price_le (k := A.Ds) (e := (seed.fam.identity v u γ).maxOrder - 2)
    hmap (hQ k) (hCs k) (Nat.cast_nonneg _) hmo
    (seed.fam.identity v u γ).record.size_nonneg (hT k) hL
  have hKC : K k ≤ Ce := (Finset.single_le_sum (fun n _ => hK n)
    (Finset.mem_range.2 (by omega))).trans hCe
  have hden : 0 < D.kap seed.level * (seed.fam.identity v u γ).record.length ^ (d - 2) :=
    mul_pos hν (pow_pos hL _)
  have hS := (seed.fam.identity v u γ).record.size_nonneg
  have hZ0 : 0 ≤ D.κ (M - 1) * (seed.fam.identity v u γ).record.length ^ (d - 2) := by
    rw [← hkap]; exact hden.le
  have h1 := (div_le_iff₀ hden).1 (hp.trans hP)
  rw [hkap] at h1
  have htoReal : (coefficientSeminorm ϱ k (tp + D.termH M) (a + A.T₀)
      (seed.physCoeff v u γ d)).toReal ≤
      Ce * (seed.fam.identity v u γ).record.size * D.κ (M - 1) *
        (seed.fam.identity v u γ).record.length ^ (d - 2) :=
    calc _ ≤ K k * (seed.fam.identity v u γ).record.size *
          (D.κ (M - 1) * (seed.fam.identity v u γ).record.length ^ (d - 2)) := h1
      _ ≤ Ce * (seed.fam.identity v u γ).record.size *
          (D.κ (M - 1) * (seed.fam.identity v u γ).record.length ^ (d - 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC hS) hZ0
      _ = _ := by ring
  exact (ENNReal.ofReal_toReal hfin).symm.le.trans (ENNReal.ofReal_le_ofReal htoReal)

end AVRegularity.EntryTerminal.Ingredients
end
end

section
/-! **The seed clauses conditional only on the seed's ledger and Schur bound**. The
sampled bound (`seedSampledPart`) and the envelope input (`seedEnvInputPart`) are proved, so
`seedEnvelopePart_of_pieces` leaves the ledger and the Schur bound (`SeedLedgerPart`, `SeedSchurPart`), and
`seedClauses_of_env` gives the seed clauses.

Special cases: those of the four pieces. -/

@[expose] public noncomputable section

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.EntryTerminal.Route

/-- **The seed clauses, part 4, from the ledger and the Schur bound of the seed.** -/
theorem seedEnvelopePart_of_ledger_schur (h3 : SeedLedgerPart) (h4 : SeedSchurPart) :
    SeedEnvelopePart :=
  seedEnvelopePart_of_pieces seedSampledPart h3 h4 seedEnvInputPart

/-- **The seed clauses from the ledger and the Schur bound of the seed.** -/
theorem seedClauses_of_ledger_schur (h3 : SeedLedgerPart) (h4 : SeedSchurPart) :
    SeedClausesStatement :=
  seedClauses_of_env (seedEnvelopePart_of_ledger_schur h3 h4)

end AVRegularity.EntryTerminal.Ingredients
end
end
end
