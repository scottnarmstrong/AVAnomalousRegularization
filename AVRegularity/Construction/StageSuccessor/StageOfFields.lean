-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.StageSuccessor.Assembly.SuccessorExistsOfIngredients
import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets
import AVRegularity.Proofs.CascadeInvariants.ReserveGrade
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Proofs.WeakGen.InhFacts
public import AVRegularity.Proofs.WeakGen.PhaseLatticeLiftData
public import AVRegularity.EntryWeakAssembly.ReadoutLinearLevel
public import AVRegularity.Proofs.GenSem.First.Identity
import AVRegularity.CycleDamping.ReferenceSourceMode
import AVRegularity.CycleReference.FluxFastDiscrepancy
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.GenSem.LiftOn.Omega

section
section
/-! Exact positive records and supported orders of the shared successor's sources. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.StageSuccessor
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {P : ProvParams} {Mn : SuccMenu}
  {G : GenStage D hr Dm b j₀}

/-- Every tag on a path is the tag of an actual input identity. -/
theorem path_tags_property {h : ℕ} (π : StagePath G h) (Q : ProvTags → Prop)
    (hQ : ∀ v u (γ : G.fam.Γ v u), Q ((G.prov v u γ).tags P)) :
    ∀ t ∈ Prov.pathTags P π.provList, Q t := by
  intro t ht
  rw [Providers.CascadeInvariants.pathTags_eq_map] at ht
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ht
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  exact hQ _ _ _

/-- The tagged positive witness of a new source is nonnegative. -/
theorem source_witness_nonneg (hi : Input P Mn G) (s : SuccSource G) :
    0 ≤ ((s.prov G.level).tags P).witness := by
  have hold v u (γ : G.fam.Γ v u) : 0 ≤ ((G.prov v u γ).tags P).witness := by
    rw [← (hi.tags v u γ).1.1]
    exact (G.fam.identity v u γ).record.size_nonneg
  have hpath {h : ℕ} (π : StagePath G h) :
      0 ≤ ((Prov.pathTags P π.provList).map ProvTags.witness).prod :=
    List.prod_nonneg (fun t ht => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
      exact path_tags_property π (fun q => 0 ≤ q.witness) hold q hq)
  have hf (l : WordLetter) (path : List (Comp × Comp × Prov))
      (hp : 0 ≤ ((Prov.pathTags P path).map ProvTags.witness).prod) :
      0 ≤ ((Prov.letter G.level l path).tags P).witness :=
    mul_nonneg (mul_nonneg (mul_nonneg (hi.birth_weights _) hi.witness_constant)
      (Real.rpow_nonneg (hi.birth_scales _).le _)) hp
  cases s with
  | copyDir w v u γ => exact mul_nonneg hi.witness_constant (hold v u γ)
  | copyQuad w h π =>
      simp only [SuccSource.prov, Prov.tags]
      split
      · exact hi.witness_constant
      · exact mul_nonneg hi.witness_constant (hpath π)
  | letterDiag w u => exact hf .diag [] (by simp [Prov.pathTags])
  | letterMean w n h π => exact hf (.mean n h) π.provList (hpath π)
  | letterCov w n h a a' π => exact hf (.covariance n h a a') π.provList (hpath π)

/-- Positive original length and width, kept literally through direct and quadratic copies. -/
theorem source_geometry_pos (hi : Input P Mn G) (s : SuccSource G) :
    0 < ((s.prov G.level).tags P).length ∧ 0 < ((s.prov G.level).tags P).width := by
  have hold v u (γ : G.fam.Γ v u) :
      0 < ((G.prov v u γ).tags P).length ∧ 0 < ((G.prov v u γ).tags P).width := by
    rw [← (hi.tags v u γ).1.2.2.2.1, ← (hi.tags v u γ).1.2.2.2.2.1]
    exact ⟨(G.fam.identity v u γ).record.length_pos, (G.fam.identity v u γ).record.width_pos⟩
  have hf : 0 < P.Rb (G.level - 1) ∧ 0 < P.rb (G.level - 1) :=
    ⟨hi.birth_length, hi.birth_width⟩
  cases s with
  | copyDir w v u γ => exact hold v u γ
  | copyQuad w h π =>
      cases he : widestTags (Prov.pathTags P π.provList) with
      | none => simpa only [SuccSource.prov, Prov.tags, he] using hf
      | some t =>
          simpa only [SuccSource.prov, Prov.tags, he] using
            path_tags_property π (fun q => 0 < q.length ∧ 0 < q.width) hold t
              (Preservation.FullLift.widestTags_mem he)
  | letterDiag => exact hf
  | letterMean => exact hf
  | letterCov => exact hf

/-- Supported current orders fit the original birth order and the ambient cap. -/
theorem source_order_bounds (hi : Input P Mn G) (s : SuccSource G) (hs : s.Valid Mn.A Mn.J) :
    2 ≤ ((s.prov G.level).tags P).order ∧
      ((s.prov G.level).tags P).order ≤ Dm ∧
      ((s.prov G.level).tags P).order ≤ ((s.prov G.level).tags P).birthExcess + 2 := by
  have hletter l (hl : l ∈ Mn.A) (path : List (Comp × Comp × Prov)) :
      2 ≤ ((Prov.letter G.level l path).tags P).order ∧
        ((Prov.letter G.level l path).tags P).order ≤ Dm ∧
        ((Prov.letter G.level l path).tags P).order ≤
          ((Prov.letter G.level l path).tags P).birthExcess + 2 := by
    obtain ⟨hlo, hhi⟩ := hi.letter_orders l hl
    exact ⟨hlo, hhi, by change letterOrder P.N P.p l ≤ letterOrder P.N P.p l - 2 + 2; omega⟩
  cases s with
  | copyDir w v u γ =>
      have ht := (hi.tags v u γ)
      change 2 ≤ ((G.prov v u γ).tags P).order ∧
        ((G.prov v u γ).tags P).order ≤ Dm ∧
        ((G.prov v u γ).tags P).order ≤ ((G.prov v u γ).tags P).birthExcess + 2
      rw [← ht.2, ← ht.1.2.2.1]
      exact ⟨(G.fam.identity v u γ).two_le, (G.fam.identity v u γ).le_D,
        (G.fam.identity v u γ).le_birth⟩
  | copyQuad w h π =>
      have hh : 1 ≤ h := hs.2.2
      have hcap := (G.fam.identity _ _ (π.step ⟨0, hh⟩).2.2).le_D
      have hlo := (G.fam.identity _ _ (π.step ⟨0, hh⟩).2.2).two_le
      simp only [SuccSource.prov, Prov.tags]
      split <;> change 2 ≤ 2 ∧ 2 ≤ Dm ∧ 2 ≤ 0 + 2
      all_goals exact ⟨le_rfl, by omega, le_rfl⟩
  | letterDiag w u => exact hletter .diag (hs.2.1 _ rfl).2 []
  | letterMean w n h π => exact hletter (.mean n h) (hs.2.1 _ rfl).2 π.provList
  | letterCov w n h a a' π => exact hletter (.covariance n h a a') (hs.2.1 _ rfl).2 π.provList

/-- A source record is precisely its provenance tags. -/
def sourceRecord (hi : Input P Mn G) (s : SuccSource G) : ConstituentRecord where
  size := ((s.prov G.level).tags P).witness
  size_nonneg := source_witness_nonneg hi s
  birthLevel := ((s.prov G.level).tags P).birthLevel
  birthExcess := ((s.prov G.level).tags P).birthExcess
  length := ((s.prov G.level).tags P).length
  length_pos := (source_geometry_pos hi s).1
  width := ((s.prov G.level).tags P).width
  width_pos := (source_geometry_pos hi s).2
  births := ((s.prov G.level).tags P).births

end AVRegularity.Construction.StageSuccessor
end
end

section
/-! Sharp support of the first-source flux array. Grade-n means have differential
order n-1; chart changes and the two covariance polynomials give order N+4p. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.StageSuccessor
open AVRegularity.Providers.GenSem

/-- A chart transformation preserves an input support smaller than its truncation. -/
theorem chart_array_support {L : ℕ} (M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (N Ψ : Vec 2 → Vec 2) (K : ℕ) (A : Fin 2 → CArr)
    (hA : ∀ c, ArrSupp L (A c)) (c : Fin 2) : ArrSupp L (chartArr M N Ψ K A c) := by
  intro m' hm' γ
  funext p z
  simp only [chartArr, chartCoef, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun α _ => ?_, mul_zero]
  by_cases hm : L < m
  · rw [hA k m hm α, Pi.zero_apply, Pi.zero_apply, zero_mul]
  · rw [arrSupp_fdbArr Ψ α m' (by omega) γ, Pi.zero_apply, Pi.zero_apply, mul_zero]

/-- Composition uses the actual supports on both sides, irrespective of truncation. -/
theorem composed_array_support {L K : ℕ} (J : ℕ) {C B : CArr}
    (hC : ArrSupp L C) (hB : ArrSupp K B) (z0 : Vec 2) :
    ArrSupp (L + K) (compArr J C B z0) := by
  intro m' hm' β
  funext X z
  unfold compArr
  refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun α _ => ?_
  by_cases hm : L < m
  · rw [hC m hm α, Pi.zero_apply, Pi.zero_apply, zero_mul]
  · have hz := arrSupp_iterSlow α hB m' (by omega) β
    simp only [hz, Pi.zero_apply, mul_zero]

variable {D : OCData} {b : ℝ} {j₀ Dm m : ℕ} {ρ : ℝ} {N p : ℕ} {s₀ : ℝ}
  {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

/-- The diagonal assembled mean has its sharp differential order n-1. -/
theorem diagonal_mean_array_support (S : Finset ℤ) (t : ℝ) (ch : RealChain) (ζ : Vec 2)
    (n : ℕ) (c : Fin 2) : ArrSupp (n - 1) (dmArr D b j₀ Dm m ρ Cc0 S t ch ζ n c) := by
  classical
  unfold dmArr
  refine ArrSupp.sum _ fun k _ => ?_
  split_ifs
  · apply ArrSupp.smul
    exact chart_array_support _ _ _ n _
      (fun a => arrSupp_pmArr D m ρ _ _ n t a) c
  · exact ArrSupp.zero _

/-- The diagonal flux through cell degree N+1 has differential order N. -/
theorem diagonal_flux_array_support (hN : 1 ≤ N) (S : Finset ℤ) (t : ℝ)
    (ch : RealChain) (ζ : Vec 2) (c : Fin 2) :
    ArrSupp N (dfArr D b j₀ Dm m ρ N Cc0 S t ch ζ c) := by
  unfold dfArr
  refine ((diagonal_mean_array_support S t ch ζ 2 c).mono (by omega) |>.sub
    ((matGradArr_supp _ c).mono hN)).add (ArrSupp.sum _ fun n hn => ?_)
  exact (diagonal_mean_array_support S t ch ζ n c).mono (by
    have := Finset.mem_Icc.mp hn; omega)

/-- The sharp first-source array order, for every covariance anchor. -/
theorem first_source_array_support (hN : 1 ≤ N) (S : Finset ℤ) (t : ℝ)
    (ch : RealChain) (ζ : Vec 2) (c : Fin 2) :
    ArrSupp (N + 4 * p) (fsArr D b j₀ Dm m ρ N p s₀ Cc0 S t ch ζ c) := by
  classical
  unfold fsArr
  apply chart_array_support
  intro k
  have hw : ArrSupp (N + 2 * p) (wArr D b j₀ Dm m ρ N p s₀ Cc0 S t ch ζ k) := by
    unfold wArr
    refine (ArrSupp.sum _ fun l hl => ?_).neg.add ?_
    · apply ArrSupp.smul
      apply ArrSupp.sum
      intro a ha
      have hlp := Finset.mem_Icc.mp hl
      have hal := Finset.mem_range.mp ha
      have he : ArrSupp (2 * a + (1 + 2 * (l - 1 - a)))
          (eArr D m s₀ t ch ζ l a k) :=
        arrSupp_compArr (2 * a) _ 0 (arrSupp_compArr 1 _ 0 (covArrPow_supp _ _))
      exact he.mono (by omega)
    · exact composed_array_support _ (diagonal_flux_array_support hN S t ch ζ k)
        (polyArr_supp _ p wPcoef) 0
  have hs := arrSupp_compArr (2 * p) (polyArr (covMat D m s₀ t) p wQcoef) 0 hw
  convert hs using 1
  omega

/-- An array with support below the tested word length has zero extracted coefficient. -/
theorem extracted_array_above_support {K L : ℕ} {A : Fin 2 → CArr}
    (hs : ∀ c, ArrSupp L (A c)) (d : ℕ) (I : DerivativeWord2 (d - 1))
    (hd : L < d - 1) : fluxCoeff (fun f y c => applyArr K (A c) f y 0) d I 0 = 0 := by
  funext c
  unfold fluxCoeff
  simp only [Pi.smul_apply, smul_eq_mul]
  change ((d - 1).factorial : ℝ)⁻¹ * applyArr K (A c) (mono 0 I) 0 0 = 0
  by_cases hLK : L ≤ K
  · have he := applyArr_mono_scaled K ((hs c).mono hLK) 1 0 0 I
    simp only [one_mul] at he
    rw [he]
    simp only [hs c (d - 1) hd, Pi.zero_apply, Finset.sum_const_zero, mul_zero]
  · have he : applyArr K (A c) (mono 0 I) 0 0 = 0 := by
      unfold applyArr
      refine Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun α _ => ?_
      rw [orderedDerivative_mono_of_ne 0 I α (by have := Finset.mem_range.mp hr; omega), mul_zero]
    rw [he, mul_zero]

end AVRegularity.Construction.StageSuccessor
end
end

section
/-! The cascade supplies every incoming certificate of the shared qualitative producer.
Only the starting level depends on the carrier start; no analytic constant is selected here. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.StageSuccessor

/-- Every producer letter has a legitimate order inside the common ambient cap. -/
theorem successor_letter_orders (r₀ D₀ H J N p npad : ℕ) (hp : 1 ≤ p) :
    ∀ l ∈ succAlphabetOf r₀ D₀ H J N p npad,
      2 ≤ letterOrder N p l ∧ letterOrder N p l ≤ succSchedD D₀ N p (H + 1) := by
  intro l hl
  have hnext : succSchedD D₀ N p (H + 1) = succSchedD D₀ N p H + 2 * N + 4 * p + 4 := rfl
  cases l with
  | diag => simp only [letterOrder]; omega
  | mean n h =>
      have hn := Providers.CascadeInvariants.mean_mem_succAlphabet hl
      simp only [letterOrder]
      omega
  | covariance n h a a' =>
      have hn := Providers.CascadeInvariants.cov_mem_succAlphabet hl
      simp only [letterOrder]
      omega
  | eddy n => simp [succAlphabetOf, succAlphabet] at hl
  | padding n => simp only [letterOrder]; omega

/-- The two combinatorial facts used by the terminal instance of the shared producer.
The lower order bound uses the positive terminal cutoff; the depth assumption is
exactly the weak graph's depth bound, and imposes no carrier start. -/
theorem terminal_source_orders_and_paths
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (G : GenStage D hr Dm b j₀)
    (NT pT DW dW : ℕ) (hNT : 1 ≤ NT) (hdepth : G.fam.HasDepthAtMost dW) :
    (∀ l ∈ termAlphabet NT pT DW dW, 2 ≤ letterOrder NT pT l ∧
      letterOrder NT pT l ≤ termD0bar NT pT DW dW) ∧
    (∀ h, StagePath G h → h ≤ dW) := by
  refine ⟨?_, fun _ π => Providers.CascadeInvariants.stagePath_length_le (G := G) hdepth π⟩
  intro l hl
  refine ⟨?_, ?_⟩
  · cases l with
    | diag => simp only [letterOrder]; omega
    | mean n h =>
      have hn := Providers.CascadeInvariants.mean_mem_succAlphabet hl
      simp only [letterOrder]; omega
    | covariance n h a a' =>
      have hn := Providers.CascadeInvariants.cov_mem_succAlphabet hl
      simp only [letterOrder]; omega
    | eddy n => simp [termAlphabet, succAlphabet] at hl
    | padding n => simp only [letterOrder]; omega
  · exact le_trans (Finset.le_sup (f := letterOrder NT pT) hl)
      (le_trans (le_max_right _ _) (le_max_right _ _))

/-- Uniform cascade-to-shared-producer adapter. It uses neither a future successor nor
quiet matching; all path and birth information comes from the supplied seed and cascade. -/
theorem cascade_successor_inputs (α s q : ℝ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    CascadeSuccessorInputsStatement α s q ζ := by
  refine ⟨128, le_rfl, ?_⟩
  intro Λ hΛ
  refine ⟨1, zero_lt_one, ?_⟩
  intro φ₀ hφ₀ _hφsmooth _hφpos _hφint _hφsupport bw hbw _hbwupper Q T₀ _hQ _hT₀
    Ce τe kS r₀ D₀ _hCe _hτe _hc₀ _hc₀upper hcr _hcrupper _hσf _hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    _hNaux _hNout _halloc _hsX _hsZ
  refine ⟨kS, 1, 1, le_rfl, zero_lt_one, ?_⟩
  intro kI hkI
  have hcrI : 0 < kI.cr := hkI.2.1.symm ▸ hcr
  have hN : 2 ≤ N := hsched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hp : 1 ≤ p := hsched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ hledger _hstart
  refine ⟨j₀ + 2, ?_⟩
  intro D hDα hDq hDΛ hDζ _hseq M hband hterm Mnat _hMnat law _hlaw
    hr _ _ _ _ _ _ seedK freshK _hfresh seed n tS tf hseed m hm _hn hnM G hcascade hlevel hG
  have hbase : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hprofile : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    rw [hDα, hDq, hDΛ, hDζ, hterm]
    exact hband
  have hκ : 0 < D.κ (G.level - 1) := by
    exact CycleReference.bandChain_pos hbase hprofile hbandD (by rw [hlevel, hterm]; omega)
  have hlength : 0 < freshLength D kI.cr (G.level - 1) :=
    mul_pos hcrI (Real.sqrt_pos.2 (mul_pos hκ (Construction.Stream.ocTauPP_pos hbase)))
  obtain ⟨tA, _htA, hG⟩ := hG
  refine ⟨hbase, hprofile, hbandD, hbw, by rw [hlevel]; exact hm,
    (by rw [hlevel, hterm]; omega),
    (by have := Preservation.Buffer.preparation_schedule_order_ge_two D₀ N p H; omega), (by exact (by omega : 1 ≤ N)), zero_lt_one,
    hG.1, hG.2.1, ⟨kI, hG.2.2.2.2.2.1⟩, ?_, ?_, hledger.2.2.2.le,
    (fun _ => zero_le_one), (fun _ => Construction.Stream.ocEpsilon_pos hbase),
    hlength, ?_, rfl, rfl, successor_letter_orders r₀ D₀ H J N p npad hp⟩
  · exact (Providers.CascadeInvariants.depthInv_of_cascade hseed.2.1 hseed.2.2.2.2.1 hcascade).2.1
  · exact ⟨succSchedR r₀ J H, fun _ π =>
      Providers.CascadeInvariants.cascade_path_length_le_of_generatedSeed hseed hcascade π⟩
  · exact mul_pos hlength (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos hbase) _)

end AVRegularity.Construction.StageSuccessor
end
end

section
/-! Local path models from an arbitrary stage's holomorphic context certificate.
The proof uses the holomorphic extension, not the weak stage's no-export registry or its
scalar component spaces. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology Metric
namespace AVRegularity.Construction.StageSuccessor
open AVRegularity.Sobolev AVRegularity.EntryWeakProofs AVRegularity.WeakEntryProofs
open AVRegularity.Providers.GenSem AVRegularity.Providers.WeakGen
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)]

/-- Smoothness, window measurability, and local compact jets of a lifted path coefficient. -/
theorem context_path_edge_local_data {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    (G : GenStage D hr Dm b j₀) {kI : InvConsts} (hgen : G.IsContextCertified kI)
    {h : ℕ} (π : StagePath G h) (k : ℤ) (hk : Odd k) (ρ : ℝ)
    (A : RealChain) (hA : IsAdmissibleChain D b j₀ G.level k A)
    (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (γ : Constituent d.1 ℝ ℝ)
    (hγ : γ ∈ (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)).edge v u d)
    (β : DerivativeWord2 (d.1 - 1)) (c : Fin 2) :
    let Ω := ladderOmega D b j₀ G.level k A ρ
    let T := Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
    (∀ t ∈ T, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun X : Vec 2 × Vec 2 => γ.coeff β t X.2 X.1 c) {X | X.2 ∈ Ω}) ∧
    (∀ Y ∈ Ω, Measurable (fun Z : T × Vec 2 => γ.coeff β Z.1 Y Z.2 c)) ∧
    (∀ K : Set (Vec 2 × Vec 2), IsCompact K → K ⊆ {X | X.2 ∈ Ω} → ∀ n,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ T, ∀ X ∈ K,
        ‖iteratedFDeriv ℝ n (fun Z : Vec 2 × Vec 2 => γ.coeff β t Z.2 Z.1 c) X‖ ≤ B) := by
  have hc := weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  simp only [familyLiftData, liftEdges, List.mem_map] at hγ
  obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
  simp only [pathEdges] at hγ₀
  split_ifs at hγ₀ with hvu hd
  · simp only [List.mem_singleton] at hγ₀
    subst hγ₀
    obtain ⟨θ, _, _, hθ⟩ := hgen _ _ (π.step ⟨u, hvu.2⟩).2.2
    obtain ⟨f, F, hF, _⟩ := hθ d.1 β c
    have hval := fun p => (hF p).2.2
    let T := Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
    let Ω := ladderOmega D b j₀ G.level k A ρ
    have hclock : MapsTo (fun t => D.cellScaleSq G.level * t) T
        (ocPulseWindow D.α D.q D.Λ G.level k) :=
      fun _ ht => cellScaleSq_mul_mem_ocPulseWindow hc ht
    obtain ⟨hr, hm, hj⟩ := holomorphic_recenter_data hΛ hb (hF ⟨k, hk⟩).2.1 A ρ T
      (fun t => D.cellScaleSq G.level * t) (continuous_const.mul continuous_id) hclock
    have he t (ht : t ∈ T) (X : Vec 2 × Vec 2) (hX : X.2 ∈ Ω) :
        G.fam.flux ⟨k, hk⟩ ⟨A, hA⟩ _ _ (π.step ⟨u, hvu.2⟩).2.2 d.1 β
            (D.cellScaleSq G.level * t) ((ρ / D.eps (G.level - 1)) • X.2) X.1 c =
          f ⟨k, hk⟩ (D.cellScaleSq G.level * t) (A.recenter D (ρ • X.2)) X.1 := by
      rw [hval ⟨k, hk⟩ ⟨A, hA⟩ _ (hclock ht), smul_smul, mul_div_cancel₀ _ hε]
      simp only [show IsAdmissibleChain D b j₀ G.level k (A.recenter D (ρ • X.2)) from hX,
        ↓reduceIte]
    refine ⟨fun t ht => (hr t ht).congr (fun X hX => he t ht X hX), ?_, ?_⟩
    · intro Y hY
      convert hm Y hY using 1
      funext Z
      exact he Z.1 Z.1.2 (Z.2, Y) hY
    · intro K hK hKO n
      obtain ⟨B, hB, hbound⟩ := hj K hK hKO n
      refine ⟨B, hB, fun t ht X hX => ?_⟩
      have heq : (fun Z : Vec 2 × Vec 2 =>
          G.fam.flux ⟨k, hk⟩ ⟨A, hA⟩ _ _ (π.step ⟨u, hvu.2⟩).2.2 d.1 β
            (D.cellScaleSq G.level * t) ((ρ / D.eps (G.level - 1)) • Z.2) Z.1 c) =ᶠ[𝓝 X]
          (fun Z => f ⟨k, hk⟩ (D.cellScaleSq G.level * t) (A.recenter D (ρ • Z.2)) Z.1) := by
        filter_upwards [((isOpen_ladderOmega D b j₀ G.level k A ρ).preimage
          continuous_snd).mem_nhds (hKO hX)] with Z hZ
        exact he t ht Z hZ
      rw [(heq.iteratedFDeriv ℝ n).self_of_nhds]
      exact hbound t ht X hX
  · simp at hγ₀
  · simp at hγ₀

/-- One common cutoff gives reserved edge models on a neighborhood of each admissible offset. -/
theorem context_path_local_reserves {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    (G : GenStage D hr Dm b j₀) {kI : InvConsts} (hgen : G.IsContextCertified kI)
    {h : ℕ} (π : StagePath G h) (k : ℤ) (hk : Odd k) (ρ : ℝ)
    (A : RealChain) (hA : IsAdmissibleChain D b j₀ G.level k A) :
    let Ω := ladderOmega D b j₀ G.level k A ρ
    let a := D.slotStart G.level k / D.cellScaleSq G.level
    let b₁ := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let edge := (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)).edge
    ∀ H Y₀, Y₀ ∈ Ω → ∃ (V : Set (Vec 2))
      (edge' : ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ)), IsOpen V ∧ Y₀ ∈ V ∧
      (∀ t ∈ Icc a b₁, SlowOpenEdgeEq V t edge edge') ∧
      Nonempty (∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
        JointSourceReserve H (fun t z Y => γ.coeff β t Y z)) := by
  classical
  dsimp only
  intro H Y₀ hY
  let Ω := ladderOmega D b j₀ G.level k A ρ
  let a := D.slotStart G.level k / D.cellScaleSq G.level
  let b₁ := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let edge := (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)).edge
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp (isOpen_ladderOmega D b j₀ G.level k A ρ) Y₀ hY
  let U := ball Y₀ (r / 2)
  have hU : IsOpen U := isOpen_ball
  have hsub : closure U ⊆ Ω := by
    rw [closure_ball Y₀ (div_pos hr (by norm_num)).ne']
    intro Y hY
    exact hrΩ (mem_ball.mpr ((mem_closedBall.mp hY).trans_lt (half_lt_self hr)))
  have hK : IsCompact (closure U) := by
    rw [closure_ball Y₀ (div_pos hr (by norm_num)).ne']
    exact isCompact_closedBall _ _
  obtain ⟨χ, Qχ, hs, hχ⟩ := local_slow_cutoff_reserve_exists H U hU Y₀
    (mem_ball_self (div_pos hr (by norm_num)))
  obtain ⟨δ, hδ, hδχ⟩ := Metric.mem_nhds_iff.mp hχ
  let V := ball Y₀ δ
  let edge' := weakCutoffEdges χ (weakTimeClampEdges a b₁ edge)
  refine ⟨V, edge', isOpen_ball, mem_ball_self hδ, ?_, ?_⟩
  · intro t ht v u d
    have ht' : t ∈ Icc a b₁ := ht
    dsimp only [edge', weakCutoffEdges, weakTimeClampEdges]
    rw [List.map_map, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun γ _ => ⟨rfl, fun β Y hY z => by
      simp only [Function.comp_apply, min_eq_right ht'.2, max_eq_right ht'.1,
        show χ Y = 1 from hδχ hY, one_smul]⟩
  · have hres : ∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
        Nonempty (JointSourceReserve H (fun t z Y => γ.coeff β t Y z)) := by
      intro v u d γ hγ β
      obtain ⟨γ₁, hγ₁, rfl⟩ := List.mem_map.mp hγ
      obtain ⟨γ₀, hγ₀, rfl⟩ := List.mem_map.mp hγ₁
      have hQ (c : Fin 2) : Nonempty (JointSourceReserve H
          (fun t z Y => χ Y * γ₀.coeff β (max a (min b₁ t)) Y z c)) := by
        obtain ⟨hf, hm, hj⟩ := context_path_edge_local_data hΛ hζ hκ hb G hgen π k hk ρ A hA
          v u d γ₀ hγ₀ β c
        exact compact_window_cutoff_reserve H a b₁
          (weakData_lift_window D hΛ hζ hκ G.level k) Ω U hU hK hsub χ hs Qχ
          (fun t z Y => γ₀.coeff β t Y z c)
          (fun t ht => (hf t ht).of_le (by exact_mod_cast (show (H : ℕ∞) ≤ ⊤ from le_top)))
          (fun t Y j z => congrFun (γ₀.periodic β t Y j z) c) hm hj
      exact ⟨vectorJointReserve H _ (fun c => (hQ c).some)⟩
    exact ⟨fun v u d γ hγ β => (hres v u d γ hγ β).some⟩

end AVRegularity.Construction.StageSuccessor
end
end
end

section
section
/-! Local path lifts and full grade-zero lifts for the shared successor producer.
The length is the menu's actual length, including the terminal factor cr. -/
@[expose] public noncomputable section
open Homogenization Set AVRegularity.Sobolev
namespace AVRegularity.Construction.StageSuccessor
open AVRegularity.EntryWeakProofs AVRegularity.WeakEntryProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {G : GenStage D hr Dm b j₀}

/-- Canonical path array, restricted to admissible slow offsets. -/
def pathLiftFamily (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (ρ : ℝ) (N : ℕ) {h : ℕ} (π : StagePath G h) :
    ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ) := by
  classical
  exact fun k A => if hA : IsAdmissibleChain D b j₀ G.level k A ∧ Odd k then
    let Q := familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩)
    let a := D.slotStart G.level k / D.cellScaleSq G.level
    let b₁ := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    weakLiftCarrierRestriction (ladderOmega D b j₀ G.level k A ρ)
      (weakLiftInverseCoefficients Q (fun Y => nativeWindowResponseLinear D hζ G.level k hA.2
        A ρ (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩) 1 le_rfl a b₁
          (weakData_lift_window_strict D hΛ hζ hband G.level k).le Y) N)
    else 0

/-- One path array satisfies every finite regularity reserve. -/
theorem path_lift_family {P : ProvParams} {Mn : SuccMenu}
    (hi : Input P Mn G) {h : ℕ} (π : StagePath G h) (sX sZ : ℕ)
    (k : ℤ) (A : RealChain) (hA : IsAdmissibleChain D b j₀ G.level k A ∧ Odd k) :
    IsLiftSequenceOn (ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level))
      (familyLiftData D G.level k A (Mn.lenFactor * liftLength D G.level)
        (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩)) sX sZ
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Mn.N h
      (pathLiftFamily hi.base hi.profile hi.band (Mn.lenFactor * liftLength D G.level) Mn.N π k A) := by
  classical
  obtain ⟨kI, hcontext⟩ := hi.context
  simp only [pathLiftFamily, dite_eq_left hA]
  exact native_full_lift_all_orders D hi.profile hi.base G.level
    (weakData_kap_pos D hi.base hi.profile hi.band G.level) k hA.2 A hA.1.2.2.1
    (Mn.lenFactor * liftLength D G.level) (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩) _ _
    (weakData_lift_window_strict D hi.base hi.profile hi.band G.level k) Mn.N h hi.order _
    (Providers.GenSem.isOpen_ladderOmega _ _ _ _ _ _ _)
    (context_path_local_reserves hi.base hi.profile hi.band hi.bandwidth G hcontext π k hA.2 _ A hA.1)
    sX sZ

/-- Path arrays for every source; the direct and diagonal source lift clauses are vacuous. -/
def sourceLiftFamilies (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (ρ : ℝ) (N : ℕ) :
    (s : SuccSource G) → ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)
  | .copyQuad _ _ π | .letterMean _ _ _ π | .letterCov _ _ _ _ _ π =>
      pathLiftFamily hΛ hζ hband ρ N π
  | .copyDir .. | .letterDiag .. => fun _ _ => 0

/-- The shared path arrays give all lift clauses of the actual successor relation. -/
theorem source_lift_families {P : ProvParams} {Mn : SuccMenu} (hi : Input P Mn G) :
    ∀ s : SuccSource G, s.IsLiftFamily Mn
      (sourceLiftFamilies hi.base hi.profile hi.band (Mn.lenFactor * liftLength D G.level) Mn.N s) := by
  intro s
  cases s with
  | copyDir => trivial
  | letterDiag => trivial
  | copyQuad w h π | letterMean w n h π | letterCov w n h a a' π =>
      exact fun k A hA => path_lift_family hi π Mn.sX Mn.sZ k A hA

/-- Grade-zero arrays on every admissible family, at the actual slow length. -/
def diagonalLiftFamily (D : OCData) (Dm : ℕ) (b : ℝ) (j₀ level : ℕ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (ρ : ℝ) (N : ℕ) :
    ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ) := by
  classical
  exact fun k A => if hA : IsAdmissibleChain D b j₀ level k A ∧ Odd k then
    let edge : ConstituentEdges Dm (fun _ : Fin 1 => ℝ) := fun _ _ _ => []
    let a := D.slotStart level k / D.cellScaleSq level
    let b₁ := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ level) / D.cellScaleSq level
    weakLiftInverseCoefficients (familyLiftData D level k A ρ edge)
      (fun Y => nativeWindowResponseLinear D hζ level k hA.2 A ρ edge 1 le_rfl a b₁
        (weakData_lift_window_strict D hΛ hζ hband level k).le Y) N
    else 0

/-- The diagonal array satisfies the full, unrestricted grade-zero relation. -/
theorem diagonal_lift_family {P : ProvParams} {Mn : SuccMenu} (hi : Input P Mn G) :
    IsDiagLifts D Dm b j₀ Mn G.level
      (diagonalLiftFamily D Dm b j₀ G.level hi.base hi.profile hi.band
        (Mn.lenFactor * liftLength D G.level) Mn.N) := by
  classical
  intro k A hk hA
  simp only [diagonalLiftFamily, dite_eq_left (show _ ∧ Odd k from ⟨hA, hk⟩)]
  exact native_empty_full_lift_all_orders D hi.profile hi.base G.level
    (weakData_kap_pos D hi.base hi.profile hi.band G.level) k hk A hA.2.2.1
    (Mn.lenFactor * liftLength D G.level) _ _
    (weakData_lift_window_strict D hi.base hi.profile hi.band G.level k) Mn.N hi.order Mn.sX Mn.sZ

end AVRegularity.Construction.StageSuccessor
end
end

section
/-! Transport the shared path lifts through integer child-phase shifts.
The proof uses the stage context certificate. -/
@[expose] public noncomputable section
open Homogenization Set AVRegularity.Sobolev
namespace AVRegularity.Construction.StageSuccessor
open AVRegularity.EntryWeakProofs AVRegularity.WeakEntryProofs
open AVRegularity.Providers.GenSem AVRegularity.Providers.WeakGen
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)]

/-- Weak holomorphic generation gives integer child-phase invariance on the output window. -/
theorem context_flux_phase_lattice {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (hΛ : 1 ≤ D.Λ) (hb : 0 < b) (G : GenStage D hr Dm b j₀) {kI : InvConsts} (hgen : G.IsContextCertified kI)
    (p : OddSlot) (A B : StageCtx D b j₀ G.level p)
    (hphase : WeakChainPhaseLatticeEquivalent A.1 B.1)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1))
    (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1) (X z : Vec 2) :
    G.fam.flux p A v u γ d I t X z = G.fam.flux p B v u γ d I t X z := by
  funext c
  obtain ⟨θ, _, _, hθ⟩ := hgen v u γ
  obtain ⟨f, F, hF, _⟩ := hθ d I c
  have hval := fun p => (hF p).2.2
  rw [hval p A t ht, hval p B t ht]
  have hr := hphase.recenter D hΛ B.2.2.2.2.2.1 (D.eps (G.level - 1) • X)
  by_cases hA : IsAdmissibleChain D b j₀ G.level p.1
      (A.1.recenter D (D.eps (G.level - 1) • X))
  · have hB := hr.admissible D b j₀ G.level p.1 hA
    rw [ite_eq_left hA, ite_eq_left hB]
    exact holExtension_phase_lattice hΛ hb (hF p).2.1 _ _ hA hr t ht z
  · have hB : ¬ IsAdmissibleChain D b j₀ G.level p.1
        (B.1.recenter D (D.eps (G.level - 1) • X)) :=
      fun hB => hA (hr.symm.admissible D b j₀ G.level p.1 hB)
    rw [ite_eq_right hA, ite_eq_right hB]

/-- The lifted path edges agree on every slow offset throughout their original window. -/
theorem context_lifted_edges_phase_lattice {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    (G : GenStage D hr Dm b j₀) {kI : InvConsts} (hgen : G.IsContextCertified kI)
    {h : ℕ} (π : StagePath G h) (k : ℤ) (hk : Odd k) (ρ : ℝ)
    (A B : RealChain) (hA : IsAdmissibleChain D b j₀ G.level k A)
    (hB : IsAdmissibleChain D b j₀ G.level k B)
    (hphase : WeakChainPhaseLatticeEquivalent A B) (t : ℝ)
    (ht : t ∈ Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)) :
    SlowOpenEdgeEq univ t
      (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)).edge
      (familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)).edge := by
  have ht' := cellScaleSq_mul_mem_ocPulseWindow
    (weakData_cellScaleSq_pos D hΛ hζ hband G.level) ht
  intro v u d
  simp only [familyLiftData, liftEdges, pathEdges]
  split_ifs with hvu hd
  · refine List.Forall₂.cons ⟨rfl, ?_⟩ .nil
    intro I X _ z
    exact context_flux_phase_lattice hΛ hb G hgen ⟨k, hk⟩ ⟨A, hA⟩ ⟨B, hB⟩
      hphase _ _ (π.step ⟨u, hvu.2⟩).2.2 d.1 I _ ht' _ z
  · exact .nil
  · exact .nil

/-- Transport a path lift along an integer phase change of its history. -/
theorem context_path_lift_transport {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    (G : GenStage D hr Dm b j₀) {kI : InvConsts} (hgen : G.IsContextCertified kI)
    {h : ℕ} (π : StagePath G h) (k : ℤ) (hk : Odd k) (ρ : ℝ)
    (A B : RealChain) (hA : IsAdmissibleChain D b j₀ G.level k A)
    (hB : IsAdmissibleChain D b j₀ G.level k B)
    (hphase : WeakChainPhaseLatticeEquivalent A B) (sX sZ N : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hc : IsLiftSequenceOn (ladderOmega D b j₀ G.level k B ρ)
      (familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)) sX sZ
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Cc) :
    IsLiftSequenceOn (ladderOmega D b j₀ G.level k A ρ)
      (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)) sX sZ
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Cc := by
  have hΩ := hphase.ladderOmega D hΛ hB.2.2.2.2.1 b j₀ G.level k ρ
  rw [← hΩ] at hc
  let Q := familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)
  let edge := (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)).edge
  have he : ∀ t ∈ Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level),
      SlowOpenEdgeEq (ladderOmega D b j₀ G.level k A ρ) t Q.edge edge := by
    intro t ht v u d
    exact (context_lifted_edges_phase_lattice hΛ hζ hband hb G hgen π k hk ρ B A hB hA
      hphase.symm t ht v u d).imp (fun _ _ hh =>
        ⟨hh.1, fun I X _ z => hh.2 I X (mem_univ X) z⟩)
  have hs := isLiftSequenceOn_edge_window_congr (isOpen_ladderOmega D b j₀ G.level k A ρ)
    Q edge _ _ sX sZ N h Cc hc he
  change IsLiftSequenceOn _
    (familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)) _ _ _ _ _ _ _ at hs
  rw [familyLiftData_geometry_congr D G.level k B A hB.2.2.1 hA.2.2.1
    (hphase.geom D hΛ hB.2.2.2.2.1).symm ρ] at hs
  exact hs


/-- Select source arrays at one representative of every integer phase orbit. -/
def phaseNormalizedSourceLifts {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    {G : GenStage D hr Dm b j₀}
    (Cc : ∀ s : SuccSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)) :
    ∀ s : SuccSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ) :=
  fun s k A => Cc s k (phaseRepresentative A)

/-- Phase normalization preserves all localized source lift clauses. -/
theorem phase_normalized_source_lifts {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm b j₀}
    (hi : Input P Mn G)
    (Cc : ∀ s : SuccSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (hc : ∀ s : SuccSource G, s.IsLiftFamily Mn (Cc s)) :
    ∀ s : SuccSource G, s.IsLiftFamily Mn (phaseNormalizedSourceLifts Cc s) := by
  obtain ⟨kI, hcontext⟩ := hi.context
  intro s
  cases s with
  | copyDir => trivial
  | letterDiag => trivial
  | copyQuad w h π =>
    intro k A hA
    have hp := phaseRepresentative_equivalent A
    have hB := hp.admissible D b j₀ G.level k hA.1
    exact context_path_lift_transport hi.base hi.profile hi.band hi.bandwidth G hcontext
      π k hA.2 (Mn.lenFactor * liftLength D G.level) A (phaseRepresentative A) hA.1 hB hp
      Mn.sX Mn.sZ Mn.N _ (hc (.copyQuad w h π) k (phaseRepresentative A) ⟨hB, hA.2⟩)

  | letterMean w n h π =>
    intro k A hA
    have hp := phaseRepresentative_equivalent A
    have hB := hp.admissible D b j₀ G.level k hA.1
    exact context_path_lift_transport hi.base hi.profile hi.band hi.bandwidth G hcontext
      π k hA.2 (Mn.lenFactor * liftLength D G.level) A (phaseRepresentative A) hA.1 hB hp
      Mn.sX Mn.sZ Mn.N _ (hc (.letterMean w n h π) k (phaseRepresentative A) ⟨hB, hA.2⟩)

  | letterCov w n h a a' π =>
    intro k A hA
    have hp := phaseRepresentative_equivalent A
    have hB := hp.admissible D b j₀ G.level k hA.1
    exact context_path_lift_transport hi.base hi.profile hi.band hi.bandwidth G hcontext
      π k hA.2 (Mn.lenFactor * liftLength D G.level) A (phaseRepresentative A) hA.1 hB hp
      Mn.sX Mn.sZ Mn.N _ (hc (.letterCov w n h a a' π) k (phaseRepresentative A) ⟨hB, hA.2⟩)

end AVRegularity.Construction.StageSuccessor
end
end

section
/-! Phase-invariant source operators from normalized path arrays. The covariance
anchor remains the menu anchor, so this proof also applies to terminal entry. -/
@[expose] public noncomputable section
open Homogenization Set AVRegularity.Sobolev
namespace AVRegularity.Construction.StageSuccessor
open AVRegularity.EntryWeakProofs AVRegularity.WeakEntryProofs
open AVRegularity.Providers.GenSem AVRegularity.Providers.WeakGen
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {G : GenStage D hr Dm b j₀}

theorem direct_flux_phase (hΛ : 1 ≤ D.Λ) (hb : 0 < b) {kI : InvConsts}
    (hgen : G.IsContextCertified kI) (k : OddSlot)
    (A B : StageCtx D b j₀ G.level k) (hp : WeakChainPhaseLatticeEquivalent A.1 B.1)
    {v u : CompIn G.comps} (γ : G.fam.Γ v u) (ords : Finset ℕ)
    (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k.1) :
    directFlux G k A γ ords t = directFlux G k B γ ords t := by
  funext f y
  unfold directFlux
  congr 1
  funext d
  congr 1
  funext I
  congr 1
  exact congrArg fieldCellMean (funext fun z =>
    context_flux_phase_lattice hΛ hb G hgen k A B hp v u γ d I t ht _ z)

/-- The common normalized array yields equal path means throughout the active pulse. -/
theorem normalized_path_mean_phase (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    {kI : InvConsts} (hgen : G.IsContextCertified kI) {h : ℕ} (π : StagePath G h)
    (ρ : ℝ) (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (k : OddSlot) (A B : StageCtx D b j₀ G.level k)
    (hp : WeakChainPhaseLatticeEquivalent A.1 B.1) (n : ℕ)
    (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k.1) :
    pathMeanFlux D G.level ρ (familyLiftData D G.level k.1 A.1 ρ (pathEdges G π k A))
      (Cc k.1 (phaseRepresentative A.1)) n t =
    pathMeanFlux D G.level ρ (familyLiftData D G.level k.1 B.1 ρ (pathEdges G π k B))
      (Cc k.1 (phaseRepresentative B.1)) n t := by
  rw [phaseRepresentative_eq hp]
  have he := context_lifted_edges_phase_lattice hΛ hζ hband hb G hgen π k.1 k.2
    ρ A.1 B.1 A.2 B.2 hp _ (physical_pulse_cell_time hΛ hζ hband G.level k.1 t ht)
  have hQ : {familyLiftData D G.level k.1 A.1 ρ (pathEdges G π k A) with
      edge := (familyLiftData D G.level k.1 B.1 ρ (pathEdges G π k B)).edge} =
      familyLiftData D G.level k.1 B.1 ρ (pathEdges G π k B) := familyLiftData_geometry_congr D G.level k.1 A.1 B.1 A.2.2.2.1 B.2.2.2.1
    (hp.geom D hΛ B.2.2.2.2.2.1) ρ (pathEdges G π k B)
  have hh := pathMeanFlux_edge_time_congr D G.level ρ
    (familyLiftData D G.level k.1 A.1 ρ (pathEdges G π k A))
    (familyLiftData D G.level k.1 B.1 ρ (pathEdges G π k B)).edge
    (Cc k.1 (phaseRepresentative B.1)) n t he
  rw [hQ] at hh
  exact hh

/-- Every non-diagonal source, including covariance letters, is phase invariant on
its physical pulse. The diagonal source's fluxOp is zero by definition. -/
theorem normalized_source_phase {P : ProvParams} {Mn : SuccMenu} (hi : Input P Mn G)
    (Cc : ∀ s : SuccSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (s : SuccSource G) (k : ℤ) (A B : RealChain)
    (hp : WeakChainPhaseLatticeEquivalent A B) (t : ℝ)
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) :
    s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor
      (phaseNormalizedSourceLifts Cc s) k t A =
    s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor
      (phaseNormalizedSourceLifts Cc s) k t B := by
  classical
  obtain ⟨kI, hgen⟩ := hi.context
  by_cases hA : IsAdmissibleChain D b j₀ G.level k A ∧ Odd k
  · have hB : IsAdmissibleChain D b j₀ G.level k B ∧ Odd k :=
      ⟨hp.admissible D b j₀ G.level k hA.1, hA.2⟩
    cases s with
    | copyDir w v u γ =>
      simp only [SuccSource.fluxOp, dite_eq_left hA, dite_eq_left hB]
      exact direct_flux_phase hi.base hi.bandwidth hgen ⟨k, hA.2⟩ ⟨A, hA.1⟩ ⟨B, hB.1⟩ hp γ _ t ht
    | letterDiag => simp only [SuccSource.fluxOp, dite_eq_left hA, dite_eq_left hB]
    | copyQuad w h π =>
      simp only [SuccSource.fluxOp, dite_eq_left hA, dite_eq_left hB, phaseNormalizedSourceLifts]
      exact normalized_path_mean_phase hi.base hi.profile hi.band hi.bandwidth hgen π _ _
        ⟨k, hA.2⟩ ⟨A, hA.1⟩ ⟨B, hB.1⟩ hp 2 t ht
    | letterMean w n h π =>
      simp only [SuccSource.fluxOp, dite_eq_left hA, dite_eq_left hB, phaseNormalizedSourceLifts]
      rw [normalized_path_mean_phase hi.base hi.profile hi.band hi.bandwidth hgen π _ (Cc (.letterMean w n h π))
        ⟨k, hA.2⟩ ⟨A, hA.1⟩ ⟨B, hB.1⟩ hp n t ht]
      funext f y
      congr 1
      split_ifs with hh
      · exact congrFun (congrFun (direct_flux_phase hi.base hi.bandwidth hgen
          ⟨k, hA.2⟩ ⟨A, hA.1⟩ ⟨B, hB.1⟩ hp (π.step ⟨0, by omega⟩).2.2 {n} t ht) f) y
      · rfl
    | letterCov w n h a a' π =>
      simp only [SuccSource.fluxOp, dite_eq_left hA, dite_eq_left hB, phaseNormalizedSourceLifts]
      rw [normalized_path_mean_phase hi.base hi.profile hi.band hi.bandwidth hgen π _ (Cc (.letterCov w n h a a' π))
        ⟨k, hA.2⟩ ⟨A, hA.1⟩ ⟨B, hB.1⟩ hp n t ht]
      have hg := hp.geom D hi.base hB.1.2.2.2.2.1
      have hmap : A.famMap D t = B.famMap D t := by
        funext x
        exact congrArg (fun K : ChainGeom => K.1 t (K.2.1 + x) K.2.2 - K.1 t K.2.1 K.2.2) hg
      have hinv : A.famMapInv D t = B.famMapInv D t := by
        funext x
        exact congrArg (fun K : ChainGeom => K.1 K.2.2 (K.1 t K.2.1 K.2.2 + x) t - K.2.1) hg
      rw [hmap, hinv]
  · have hB : ¬ (IsAdmissibleChain D b j₀ G.level k B ∧ Odd k) := by
      rintro ⟨hB, hk⟩
      exact hA ⟨hp.symm.admissible D b j₀ G.level k hB, hk⟩
    simp only [SuccSource.fluxOp, dite_eq_right hA, dite_eq_right hB]

end AVRegularity.Construction.StageSuccessor
end
end

section
/-! Periodicity of the first-source coefficients for canonical grade-zero arrays.
The covariance anchor and the slow length are arbitrary. -/
@[expose] public noncomputable section
open Homogenization Set AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.StageSuccessor
open AVRegularity.EntryWeakProofs AVRegularity.WeakEntryProofs
open AVRegularity.Providers.GenSem AVRegularity.Providers.WeakGen
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ m : ℕ}
  {hΛ : 1 ≤ D.Λ} {hζ : IsFastProfile D.ζ}
  {hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ} {ρ : ℝ} {N : ℕ}

/-- Canonical diagonal arrays depend only on the stored geometry. -/
theorem diagonal_lifts_geometry (k : ℤ) (hk : Odd k) (A B : RealChain)
    (hA : IsAdmissibleChain D b j₀ m k A) (hB : IsAdmissibleChain D b j₀ m k B)
    (hg : A.geom D = B.geom D) :
    diagonalLiftFamily D Dm b j₀ m hΛ hζ hband ρ N k A =
      diagonalLiftFamily D Dm b j₀ m hΛ hζ hband ρ N k B := by
  classical
  simp only [diagonalLiftFamily, dite_eq_left (show _ ∧ Odd k from ⟨hA, hk⟩),
    dite_eq_left (show _ ∧ Odd k from ⟨hB, hk⟩)]
  exact native_full_lift_geometry_congr D hζ m k hk A B hA.2.2.1 hB.2.2.1 hg
    ρ (fun _ _ _ => []) 1 le_rfl _ _ _ N

/-- The diagonal label mean is unchanged by an integer child-phase shift. -/
theorem diagonal_label_phase (k : ℤ) (hk : Odd k) (A B : RealChain)
    (hA : IsAdmissibleChain D b j₀ m k A) (hp : WeakChainPhaseLatticeEquivalent A B)
    (n : ℕ) (t : ℝ) :
    diagLabelFlux D Dm m ρ (diagonalLiftFamily D Dm b j₀ m hΛ hζ hband ρ N) k A n t =
    diagLabelFlux D Dm m ρ (diagonalLiftFamily D Dm b j₀ m hΛ hζ hband ρ N) k B n t := by
  have hB := hp.admissible D b j₀ m k hA
  have hg := hp.geom D hΛ hB.2.2.2.2.1
  unfold diagLabelFlux
  rw [diagonal_lifts_geometry k hk A B hA hB hg,
    familyLiftData_geometry_congr D m k A B hA.2.2.1 hB.2.2.1 hg]

/-- The diagonal mean at a coarse context is periodic in its final phase. -/
theorem diagonal_mean_phase (ch : RealChain) (hslot : Odd ch.slot) (t : ℝ) (n : ℕ) :
    IsZ2Periodic (fun z => diagMeanFluxCtx D b j₀ Dm m ρ
      (diagonalLiftFamily D Dm b j₀ m hΛ hζ hband ρ N) t ch z n) := by
  classical
  intro v z
  funext f x
  unfold diagMeanFluxCtx
  refine finsum_congr fun k => finsum_congr fun hk => ?_
  have hp := weak_appendChild_phase_lattice D hΛ ch hslot k t z v
  by_cases hA : IsAdmissibleChain D b j₀ m k (ch.appendChild D k t (z + latticeShift v))
  · have hB := hp.admissible D b j₀ m k hA
    rw [ite_eq_left hA, ite_eq_left hB]
    have hg := hp.geom D hΛ hB.2.2.2.2.1
    have hmap : (ch.appendChild D k t (z + latticeShift v)).famMap D t =
        (ch.appendChild D k t z).famMap D t := by
      funext x
      exact congrArg (fun K : ChainGeom => K.1 t (K.2.1 + x) K.2.2 - K.1 t K.2.1 K.2.2) hg
    have hinv : (ch.appendChild D k t (z + latticeShift v)).famMapInv D t =
        (ch.appendChild D k t z).famMapInv D t := by
      funext x
      exact congrArg (fun K : ChainGeom => K.1 K.2.2 (K.1 t K.2.1 K.2.2 + x) t - K.2.1) hg
    rw [hmap, hinv, diagonal_label_phase k hk.1 _ _ hA hp]
  · have hB : ¬ IsAdmissibleChain D b j₀ m k (ch.appendChild D k t z) :=
      fun hh => hA (hp.symm.admissible D b j₀ m k hh)
    rw [ite_eq_right hA, ite_eq_right hB]

/-- Cell scaling makes the coarse label shear periodic. -/
theorem label_shear_periodic (D : OCData) (hΛ : 1 ≤ D.Λ) (i : ℕ) (pc : ℤ)
    (hp : Odd pc) (t : ℝ) : IsZ2Periodic (labelShear D i pc t) := by
  intro n z
  unfold labelShear
  congr 1
  funext a
  simpa only [zero_add, OCData.eps] using
    (CycleDamping.cell_shear_component_periodic (α := D.α) (q := D.q) (m := i) hΛ hp 0 a n z)

/-- The context strain is periodic in the final phase, including its shear Jacobian. -/
theorem context_strain_periodic (D : OCData) (hΛ : 1 ≤ D.Λ) (i : ℕ) (pc : ℤ)
    (hp : Odd pc) (t : ℝ) (ch : RealChain) : IsZ2Periodic (contextStrain D i pc t ch) := by
  intro n z
  have hs := label_shear_periodic D hΛ i pc hp t
  have hfun : (fun x => labelShear D i pc t (x + latticeShift n)) = labelShear D i pc t :=
    funext (hs n)
  have hj : jacMatrix (labelShear D i pc t) (z + latticeShift n) =
      jacMatrix (labelShear D i pc t) z := by
    unfold jacMatrix
    rw [← fderiv_comp_add_right, hfun]
  simp only [contextStrain, hs n z, hj]

/-- The complete first-source operator is periodic before coefficient extraction. -/
theorem first_source_phase (ch : RealChain) (hslot : Odd ch.slot) (p : ℕ) (s₀ t : ℝ) :
    IsZ2Periodic (fun z => firstSourceFlux D b j₀ Dm m ρ N p s₀
      (diagonalLiftFamily D Dm b j₀ m hΛ hζ hband ρ N) t ch z) := by
  intro n z
  have hd : ∀ z, diagFluxCtx D b j₀ Dm m ρ N
      (diagonalLiftFamily D Dm b j₀ m hΛ hζ hband ρ N) t ch (z + latticeShift n) =
      diagFluxCtx D b j₀ Dm m ρ N
      (diagonalLiftFamily D Dm b j₀ m hΛ hζ hband ρ N) t ch z := by
    intro z
    funext f x
    have hh : ∀ k, diagMeanFluxCtx D b j₀ Dm m ρ
        (diagonalLiftFamily D Dm b j₀ m hΛ hζ hband ρ N) t ch (z + latticeShift n) k =
        diagMeanFluxCtx D b j₀ Dm m ρ
        (diagonalLiftFamily D Dm b j₀ m hΛ hζ hband ρ N) t ch z k :=
      fun k => diagonal_mean_phase ch hslot t k n z
    simp only [diagFluxCtx, hh]
  unfold firstSourceFlux
  have hstrain : ∀ x, contextStrain D (m - 1) ch.slot t (ch.recenter D (ch.famMapInv D t x))
      ((z + latticeShift n) + (D.eps (m - 1))⁻¹ • ch.famMapInv D t x) =
      contextStrain D (m - 1) ch.slot t (ch.recenter D (ch.famMapInv D t x))
      (z + (D.eps (m - 1))⁻¹ • ch.famMapInv D t x) := by
    intro x
    rw [add_right_comm]
    exact context_strain_periodic D hΛ _ ch.slot hslot t _ n _
  simp only [hstrain, hd]

end AVRegularity.Construction.StageSuccessor
end
end

section
/-! Finite structural assembly of the shared successor from its literal coefficient fields.
The source codes, old records, natural pieces and provenance injectivity are reused. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.StageSuccessor
open scoped Classical
open Preservation.Ledger WeakEntryProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {P : ProvParams} {Mn : SuccMenu}
  {G : GenStage D hr Dm b j₀}

/-- The identities on an outgoing edge are exactly its valid sources. -/
def sourceEdge (G : GenStage D hr Dm b j₀) (Mn : SuccMenu)
    (v u : CompIn (succExtComps G.level Mn.A Mn.J G.comps)) :=
  {s : SuccSource G // s.Valid Mn.A Mn.J ∧ s.srcComp G.level = u.1 ∧ s.tgtComp G.level = v.1}

@[instance_reducible] def sourceEdgeFintype (hi : Input P Mn G)
    (v u : CompIn (succExtComps G.level Mn.A Mn.J G.comps)) :
    Fintype (sourceEdge G Mn v u) := by
  let H := hi.finite_paths.choose
  have hH := hi.finite_paths.choose_spec
  have hb (s : SuccSource G) : s.pathLen ≤ H := by
    cases s with
    | copyDir => exact Nat.zero_le _
    | letterDiag => exact Nat.zero_le _
    | copyQuad w h π | letterMean w n h π | letterCov w n h a a' π => exact hH h π
  let enc : sourceEdge G Mn v u → SourceCode G Mn.A Mn.J H :=
    fun s => encodeSource Mn.A Mn.J H s.1 s.2.1 (hb s.1)
  have hen : Function.Injective enc := by
    intro s t he
    apply Subtype.ext
    have hh := congrArg decodeSource he
    rw [decode_encode_source, decode_encode_source] at hh
    exact Option.some.inj hh
  haveI : Finite (sourceEdge G Mn v u) := Finite.of_injective enc hen
  exact Fintype.ofFinite _

/-- Constant path map and literal tagged record of an outgoing identity. -/
def sourceIdentity (hi : Input P Mn G)
    (v u : CompIn (succExtComps G.level Mn.A Mn.J G.comps)) (s : sourceEdge G Mn v u) :
    CoefficientIdentity Dm (hr u.1.root) (hr v.1.root) where
  map := rootPathMap hr u.1.root s.1.maps v.1.root
  record := sourceRecord hi s.1
  maxOrder := ((s.1.prov G.level).tags P).order
  two_le := (source_order_bounds hi s.1 s.2.1).1
  le_D := (source_order_bounds hi s.1 s.2.1).2.1
  le_birth := (source_order_bounds hi s.1 s.2.1).2.2

/-- Assemble the natural next family after the coefficient realization has been supplied. -/
def stageOfFields (hi : Input P Mn G)
    (Cc : ∀ s : SuccSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hc : TransferFields G P Mn Cc Cc0) : GenStage D hr Dm b j₀ where
  level := G.level - 1
  comps := succExtComps G.level Mn.A Mn.J G.comps
  fam :=
    { Γ := sourceEdge G Mn
      fintypeΓ := sourceEdgeFintype hi
      identity := sourceIdentity hi
      piece := fun p => weakNaturalPiece D Mn.M (G.level - 1) p.1
      flux := fun p c v u s d I t X z => if 2 ≤ d then
        sourceTransferredFlux G P Mn Cc Cc0 p c s.1 d I t X z else 0
      flux_periodic := by
        intro p c v u s d I t X
        by_cases hd : 2 ≤ d
        · simpa only [ite_eq_left hd] using hc.2.2.1 p c s.1 s.2.1 d I t X
        · intro n z
          simp only [ite_eq_right hd]
      flux_zero := by
        intro p c v u s d I hd
        funext t X z
        by_cases htwo : 2 ≤ d
        · rw [ite_eq_left htwo]
          apply hc.2.2.2 p c s.1 s.2.1 d I t X z
          change ¬ (2 ≤ d ∧ d ≤ ((s.1.prov G.level).tags P).order) at hd
          omega
        · rw [ite_eq_right htwo]
      weight := fun p => ocCutoff D.α D.q D.Λ (G.level - 1) p.1
      weight_nonneg := fun _ _ => Real.smoothTransition.nonneg _
      weight_zero := fun p t ht => ocCutoff_zero_off_output D.α D.q D.Λ _
        (Construction.Stream.ocTau_pos hi.base) p.1 t ht
      locally_finite := weak_output_locally_finite D.α D.q D.Λ _ (Construction.Stream.ocTau_pos hi.base)
      weight_sum := fun t _ => ocCutoff_finsum_one D.α D.q D.Λ _ (Construction.Stream.ocTau_pos hi.base) t }
  prov := fun _ _ s => s.1.prov G.level
  actual := fun p => ⟨nativeChain (G.level - 1) p.1,
    nativeChain_isCarrier D b j₀ _ p.1 2 (by have := hi.level; omega)
      (by have := hi.level; omega) p.2 0⟩
  exports := G.exports

/-- Finite assembly satisfies every clause of the actual successor relation. -/
theorem stageOfFields_isActualSuccessor (hi : Input P Mn G)
    (Cc : ∀ s : SuccSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hc : TransferFields G P Mn Cc Cc0) :
    IsActualSuccessor D P Mn G (stageOfFields hi Cc Cc0 hc) := by
  have hm : 1 ≤ G.level := by have := hi.level; omega
  refine ⟨hm, rfl, rfl, ?_, ?_, (fun _ _ _ => Iff.rfl), (fun _ _ => Equiv.refl _),
    Cc, Cc0, hc.1, hc.2.1, ?_⟩
  · refine ⟨fun p => weakNaturalPiece_isNatural D Mn.M _ p.1, (fun _ _ => rfl),
      (fun _ => rfl), ?_⟩
    intro v u s s' hprov
    apply Subtype.ext
    exact Uniqueness.succSource_eq_of_prov hm hi.natural.2.2.2 hi.old_births s.1 s'.1
      s.2.1 s'.2.1 hprov (s.2.2.1.trans s'.2.2.1.symm) (s.2.2.2.trans s'.2.2.2.symm)
  · intro v u s
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · intro v u s
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro hnd p c d I t X z hd
      change (if 2 ≤ d then sourceTransferredFlux G P Mn Cc Cc0 p c s.1 d I t X z else 0) = _
      rw [ite_eq_left hd]
      have hnd' : ¬ s.1.IsDiag := hnd
      simp only [sourceTransferredFlux, ite_eq_right hnd']
      rfl
    · intro hdg p c d I t X z hd
      change (if 2 ≤ d then sourceTransferredFlux G P Mn Cc Cc0 p c s.1 d I t X z else 0) = _
      rw [ite_eq_left hd]
      have hdg' : s.1.IsDiag := hdg
      simp only [sourceTransferredFlux, ite_eq_left hdg']
      rfl

end AVRegularity.Construction.StageSuccessor
end
end
end
