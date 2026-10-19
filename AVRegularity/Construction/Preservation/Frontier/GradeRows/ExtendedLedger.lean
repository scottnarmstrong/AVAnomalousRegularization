-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.KernelEnergy.TorusKernelResidualODE
import AVRegularity.Construction.Preservation.Ledger.TaggedRecurrence
public import AVRegularity.KernelEnergy.TorusKernelFiniteTraceLimit
public import AVRegularity.Proofs.CascadeInvariants.ReserveGrade
public import AVRegularity.Statements.Construction.IsOCStreamSeq
import AVRegularity.Construction.InitialValue.Cascade

section
/-! Kernel routing uses widths, not witness sizes. In particular, changing the readout
exponent in provenance parameters does not change the original kernel selected by a stage. -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Frontier

/-- The provenance information used to select a kernel. -/
def frontierKernelTag (t : ProvTags) := (t.width, t.kernel)

/-- Select the widest kernel, preserving the provenance tie convention. -/
def frontierWidestKernelTag : List (ℝ × KernelKey) → Option (ℝ × KernelKey)
  | [] => none
  | t :: ts => match frontierWidestKernelTag ts with
    | none => some t
    | some t' => if t.1 < t'.1 then some t' else some t

private theorem widest_kernel_tag_map (ts : List ProvTags) :
    (widestTags ts).map frontierKernelTag = frontierWidestKernelTag (ts.map frontierKernelTag) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [widestTags, List.map_cons, frontierWidestKernelTag]
    cases h : widestTags ts with
    | none => simp only [h, Option.map_none] at ih ⊢; rw [← ih]; rfl
    | some t' =>
      simp only [h, Option.map_some] at ih ⊢
      rw [← ih]
      change (if t.width < t'.width then some t' else some t).map frontierKernelTag =
        if t.width < t'.width then some (frontierKernelTag t') else some (frontierKernelTag t)
      split <;> rfl

mutual
/-- Width and kernel tags are independent of all witness and order parameters. -/
theorem frontier_prov_kernel_tag_congr (P P' : ProvParams) (hrb : P.rb = P'.rb) (src : Prov) :
    ((src.tags P).width, (src.tags P).kernel) =
      ((src.tags P').width, (src.tags P').kernel) := by
  cases src with
  | seed k tag => rfl
  | dir m src => exact frontier_prov_kernel_tag_congr P P' hrb src
  | letter m l path => simp only [Prov.tags, hrb]
  | quad m path =>
    have he : (widestTags (Prov.pathTags P path)).map frontierKernelTag =
        (widestTags (Prov.pathTags P' path)).map frontierKernelTag := by
      rw [widest_kernel_tag_map, widest_kernel_tag_map,
        frontier_prov_path_kernel_tag_congr P P' hrb path]
    cases h : widestTags (Prov.pathTags P path) <;>
      cases h' : widestTags (Prov.pathTags P' path) <;>
      simp only [h, h', Option.map_none, Option.map_some, Option.some.injEq,
        reduceCtorEq] at he
    · simp only [Prov.tags, h, h', hrb]
    · simpa only [Prov.tags, h, h', frontierKernelTag] using he
termination_by sizeOf src

theorem frontier_prov_path_kernel_tag_congr (P P' : ProvParams)
    (hrb : P.rb = P'.rb) (path : List (Comp × Comp × Prov)) :
    (Prov.pathTags P path).map frontierKernelTag = (Prov.pathTags P' path).map frontierKernelTag := by
  cases path with
  | nil => rfl
  | cons e rest =>
    obtain ⟨v, u, src⟩ := e
    simp only [Prov.pathTags, List.map_cons, List.cons.injEq]
    exact ⟨frontier_prov_kernel_tag_congr P P' hrb src,
      frontier_prov_path_kernel_tag_congr P P' hrb rest⟩
termination_by sizeOf path
end

open MeasureTheory Homogenization AVRegularity.Sobolev
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The stage's kernel operator is unchanged when witness exponents change.
The degenerate cases are included: empty and singleton families and edgeless stages; ties use the
same first widest tag. -/
theorem frontier_sysS_parameters_congr (G : GenStage D hr Dm bw j₀)
    (P P' : ProvParams) (hrb : P.rb = P'.rb) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) :
    G.sysS P seedK freshK φ₀ hφ₀ = G.sysS P' seedK freshK φ₀ hφ₀ := by
  funext v u γ t
  have he := congrArg Prod.snd (frontier_prov_kernel_tag_congr P P' hrb (G.prov v u γ))
  change (Prov.tags P (G.prov v u γ)).kernel = (Prov.tags P' (G.prov v u γ)).kernel at he
  unfold GenStage.sysS GenStage.kernelOf
  rw [he]

end AVRegularity.Construction.Preservation.Frontier
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Frontier

/-! Kernel regularization and record lengths of the extended successor. The original seed
kernels are retained, even when their source root changes. Quadratic records have no higher
birth excess; copied higher lengths and fresh lengths give the required wavelength bound. -/

section
open FullLift AVRegularity.Providers.CascadeInvariants
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Higher record lengths before retention; the proof is the source calculation used in
length_le_eps_of_cascade. Empty or singleton families and edgeless seeds need no
extra identity, and quadratic sources have zero birth excess. -/
theorem extended_successor_record_lengths (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm bw j₀) (hs : IsActualSuccessor D P Mn G G')
    (htags : G.HasTags P)
    (hold : ∀ v u (γ : G.fam.Γ v u), 1 ≤ (G.fam.identity v u γ).record.birthExcess →
      (G.fam.identity v u γ).record.length ≤ D.eps G.level)
    (hanti : D.eps G.level ≤ D.eps G'.level)
    (hfresh : P.Rb (G.level - 1) ≤ D.eps G'.level) :
    ∀ v u (γ : G'.fam.Γ v u), 1 ≤ (G'.fam.identity v u γ).record.birthExcess →
      (G'.fam.identity v u γ).record.length ≤ D.eps G'.level := by
  obtain ⟨_, _, _, _, htags', _, e, _, _, _, _, hall⟩ := hs
  intro v u γ hbe
  obtain ⟨hT, _⟩ := htags' v u γ
  obtain ⟨hprov, _⟩ := hall v u γ
  rw [hT.2.2.1, hprov] at hbe
  rw [hT.2.2.2.1, hprov]
  generalize (e v u γ).1 = src at hbe ⊢
  cases src with
  | copyDir t v₀ u₀ γ₀ =>
    simp only [SuccSource.prov] at hbe ⊢
    rw [(Prov.tags_dir P _ _).1]
    rw [(Prov.tags_dir P _ _).2] at hbe
    obtain ⟨hT₀, _⟩ := htags v₀ u₀ γ₀
    rw [← hT₀.2.2.1] at hbe
    rw [← hT₀.2.2.2.1]
    exact (hold v₀ u₀ γ₀ hbe).trans hanti
  | copyQuad t h π =>
    simp only [SuccSource.prov, Prov.tags_quad_birthExcess] at hbe
    omega
  | letterDiag t u₀ => simpa only [SuccSource.prov, Prov.tags_letter_length] using hfresh
  | letterMean t n h π => simpa only [SuccSource.prov, Prov.tags_letter_length] using hfresh
  | letterCov t n h a a' π => simpa only [SuccSource.prov, Prov.tags_letter_length] using hfresh

variable [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]

/-- Original kernel properties pass to the full successor, with transfer between roots.
No positive width or new seed kernel is assumed by the inheritance step. -/
theorem extended_successor_kernel_regularizers (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm bw j₀) (hs : IsActualSuccessor D P Mn G G')
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (ρ a b : ℝ) (k : ℕ) (c : ℕ → ℝ)
    (hold : ∀ v u (γ : G.fam.Γ v u), IsSpatialRegularizerTorus ρ k Dm a b c
      (G.kernelOf P seedK freshK v u γ).width (G.sysS P seedK freshK φ₀ hφ₀ v u γ))
    (hfresh : IsSpatialRegularizerTorus (G := ℝ) ρ k Dm a b c
      (freshK (G.level - 1)).width ((freshK (G.level - 1)).op φ₀ hφ₀)) :
    ∀ v u (γ : G'.fam.Γ v u), IsSpatialRegularizerTorus ρ k Dm a b c
      (G'.kernelOf P seedK freshK v u γ).width (G'.sysS P seedK freshK φ₀ hφ₀ v u γ) := by
  let lookup : KernelKey → KernelSpec := fun key => match key with
    | .seed i => seedK i
    | .fresh i => freshK i
  let Q : KernelKey → Prop := fun key => ∀ r : ℕ,
    IsSpatialRegularizerTorus (G := hr r) ρ k Dm a b c (lookup key).width
      ((lookup key).op φ₀ hφ₀)
  have hOld : ∀ v u (γ : G.fam.Γ v u), Q ((G.prov v u γ).tags P).kernel := by
    intro v u γ r
    exact kernel_regularizer_transfer (F := hr r) φ₀ hφ₀
      (G.kernelOf P seedK freshK v u γ) (hold v u γ)
  have hFresh : Q (.fresh (G.level - 1)) := fun r =>
    kernel_regularizer_of_scalar (F := hr r) φ₀ hφ₀ (freshK (G.level - 1)) hfresh
  have hkeys := actual_successor_kernel_key_property P Mn G G' hs Q hOld hFresh
  intro v u γ
  exact hkeys v u γ u.1.root
end

/-! The actual flux of arbitrary supplied higher Sobolev inputs exists at every time.
When those inputs agree with the original kernels almost everywhere in time, the flux is
almost everywhere the canonical flux, so the time-L² theorem applies. This preserves
the all-time realization even at the exceptional times of the supplied lifts. -/

section
open AVRegularity.KernelEnergy
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j γ, NormedAddCommGroup (G i j γ)]
  [∀ i j γ, InnerProductSpace ℝ (G i j γ)] [∀ i j γ, FiniteDimensional ℝ (G i j γ)]
  [∀ i j γ, MeasurableSpace (G i j γ)] [∀ i j γ, BorelSpace (G i j γ)]
  [∀ i j γ, CompleteSpace (G i j γ)] {a b ρ ν : ℝ} {k Dm : ℕ}

/-- The coefficient action on a supplied higher Sobolev input, without a kernel equation. -/
def gradeRowSuppliedFluxTerm
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k Dm)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (Z : ∀ i j (γ : Γ i j), TorusHk (k + Dm - 1) (G i j γ))
    (i j : ι) (γ : Γ i j) (d : ↥(Finset.Icc 2 Dm)) :
    TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  torusKernelFluxTerm (m := d.1 - 2) (r := d.1 - 1)
    (by have := Finset.mem_Icc.1 d.2; omega) ρ P.radius_pos a b
    (P.B i j γ d) (P.hB_fin i j γ d) t ht (P.hB_smooth i j γ d t ht) (P.hB_per i j γ d t ht)
    (truncateTorusHk (by have := Finset.mem_Icc.1 d.2; omega) (Z i j γ))

/-- The supplied action realizes exactly its raw coefficient/jet expression at every time. -/
theorem grade_row_supplied_flux_term_raw
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k Dm)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (Z : ∀ i j (γ : Γ i j), TorusHk (k + Dm - 1) (G i j γ))
    (i j : ι) (γ : Γ i j) (d : ↥(Finset.Icc 2 Dm)) :
    (gradeRowSuppliedFluxTerm P t ht Z i j γ d).toFunction.jet (valueIndex2 k)
      =ᵐ[volume.restrict AVenhance.unitCube] fun x =>
        P.B i j γ d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (Z i j γ).toFunction.jet ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
  have hd := Finset.mem_Icc.1 d.2
  have hr : d.1 - 1 = (d.1 - 2) + 1 := by omega
  have hlow : k + ((d.1 - 2) + 1) ≤ k + Dm - 1 := by omega
  have hb := torusKernelFluxTerm_base_ae hr ρ P.radius_pos a b (P.B i j γ d)
    (P.hB_fin i j γ d) t ht (P.hB_smooth i j γ d t ht) (P.hB_per i j γ d t ht)
    (truncateTorusHk hlow (Z i j γ))
  have hj : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ word : DerivativeWord2 (d.1 - 1),
      (truncateTorusHk hlow (Z i j γ)).toFunction.jet ⟨⟨d.1 - 1, by omega⟩, word⟩ x =
      (Z i j γ).toFunction.jet ⟨⟨d.1 - 1, by omega⟩, word⟩ x :=
    ae_all_iff.mpr fun word => truncateTorusHk_toFunction_jet_ae hlow (Z i j γ) _
  filter_upwards [hb, hj] with x hx hjx
  exact hx.trans (congrArg (P.B i j γ d t x) (PiLp.ext fun word => hjx word))

/-- The finite sum is clamped in coefficient time outside its declared window only. -/
def gradeRowSuppliedFlux
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k Dm)
    (Z : ∀ i j (γ : Γ i j), ℝ → TorusHk (k + Dm - 1) (G i j γ))
    (i : ι) (t : ℝ) : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  ∑ j, ∑ γ, ∑ d, gradeRowSuppliedFluxTerm P (Set.projIcc a b P.htime t)
    (Set.projIcc a b P.htime t).property (fun v u γ => Z v u γ t) i j γ d

/-- No exceptional times are removed from the realization assertion.
The sum is kept literally, also when it is empty or has a single term. -/
theorem grade_row_supplied_flux_raw
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k Dm)
    (Z : ∀ i j (γ : Γ i j), ℝ → TorusHk (k + Dm - 1) (G i j γ))
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    (gradeRowSuppliedFlux P Z i t).toFunction.jet (valueIndex2 k)
      =ᵐ[volume.restrict AVenhance.unitCube] fun x =>
        ∑ j, ∑ γ, ∑ d, P.B i j γ d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (Z i j γ t).toFunction.jet
            ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
  classical
  unfold gradeRowSuppliedFlux
  simp only [Set.projIcc_of_mem P.htime ht]
  apply torusJet_sum_ae_of_eq
  intro j
  apply torusJet_sum_ae_of_eq
  intro γ
  apply torusJet_sum_ae_of_eq
  intro d
  exact grade_row_supplied_flux_term_raw P t ht _ i j γ d

/-- At times when the supplied values agree, uniqueness of Sobolev jets identifies the sum
with the canonical flux. -/
theorem grade_row_supplied_flux_eq_canonical
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k Dm)
    (Z : ∀ i j (γ : Γ i j), ℝ → TorusHk (k + Dm - 1) (G i j γ))
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i)) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hv : ∀ i j γ, (Z i j γ t).val (valueIndex2 (k + Dm - 1)) =
      P.S i j γ t ((P.C i j γ).compLp ((w j t).val (valueIndex2 (k + 1))))) (i : ι) :
    gradeRowSuppliedFlux P Z i t = P.carrierFlux w i t := by
  have he : (fun v u γ => Z v u γ t) = P.lift t ht (fun j => w j t) := by
    funext v u γ
    apply TorusHk.ext_value
    exact (hv v u γ).trans (P.lift_value t ht (fun j => w j t) v u γ).symm
  unfold gradeRowSuppliedFlux
  simp only [Set.projIcc_of_mem P.htime ht]
  rw [he, P.carrierFlux_of_mem w i t ht]
  exact P.assembledFlux_eq_flux t ht (fun j => w j t) i

/-- The row producer inherits time-L² from the canonical kernel flux, not from an unstated
measurability assumption on the supplied higher lifts. -/
theorem grade_row_supplied_flux_memLp
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k Dm)
    (Z : ∀ i j (γ : Γ i j), ℝ → TorusHk (k + Dm - 1) (G i j γ))
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)))
    (hv : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i j γ,
      (Z i j γ t).val (valueIndex2 (k + Dm - 1)) =
        P.S i j γ t ((P.C i j γ).compLp ((w j t).val (valueIndex2 (k + 1))))) (i : ι) :
    MemLp (gradeRowSuppliedFlux P Z i) 2 (volume.restrict (Set.Icc a b)) := by
  have he : gradeRowSuppliedFlux P Z i =ᵐ[volume.restrict (Set.Icc a b)] P.carrierFlux w i := by
    filter_upwards [hv, ae_restrict_mem measurableSet_Icc] with t hvt ht
    exact grade_row_supplied_flux_eq_canonical P Z w t ht hvt i
  exact (memLp_congr_ae he).mpr (P.carrierFlux_memLp_of_family w hw i)
end

end AVRegularity.Construction.Preservation.Frontier
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier

/-! The uniform scale absorption of the marked ledger applies to the entire extended family. The recurrence
is the full form of the same source-sum proof; no fresh-price estimate is repeated. -/

open AVRegularity.Construction.Preservation.Assembly

/-- Uniform ledger bound before retention. The statement
covers all families, including empty ones, and every passage of length at least two. -/
def ExtendedMarkedLedgerStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
  IsAdmissibleQ α s q → IsFastProfile ζ →
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ mStar : ℕ,
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ tA : ℝ, tS ≤ tA →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∀ κc : MajConsts,
      (∀ v' u' (γ' : G'.fam.Γ v' u'), Providers.CascadeInvariants.LedgerConcl kI κc G' v' u' γ') →
      let Gr := G'
      markedLedger (Gr.mass law) (Gr.marker law) Gr.fam ≤
        CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe

/-- The proved full tagged recurrence and the scale-absorption theorem supply
exactly the same thresholds as for the marked ledger, now for the extended family. -/
theorem extended_marked_ledger
    (α s q : ℝ) (ζ : ℝ → ℝ) : ExtendedMarkedLedgerStatement α s q ζ := by
  classical
  intro hα₀ hα₁ hs₀ hs₁ hq hζ
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hη := FullLift.successor_eta0_pos hα₀ hα₁ hs₀ hs₁ hq
  refine ⟨128, le_rfl, ?_⟩
  intro Λ hΛ
  refine ⟨1, zero_lt_one, ?_⟩
  intro φ₀ hφ₀ _hφsmooth _hφnonneg _hφmass _hφsupport bw _hbw _hbwmax Q T₀ _hQ _hT
    Ce τe kS r₀ D₀ hCe hτe _hcS _hcSmax _hcr _hcrmax _hσf _hlam H J N p nk Lc Lf Lpr Acl Naux Nout
    Kres npad sX sZ σ₀ a σ hsched _haux _hres _halloc
  obtain ⟨_, _, _, _, _, hσeq, ha, haσ, _, hσD, _⟩ := hsched
  have hσ₀ : 0 ≤ σ₀ := by linarith only [hσeq, ha, haσ]
  refine ⟨kS, 1, 100, le_rfl, by norm_num, ?_⟩
  intro kI _hkI
  refine ⟨1, 1, ?_⟩
  intro CI Cw j₀ hledger _hstart
  have hCI : 0 < CI := lt_of_lt_of_le (by linarith only [hCe] : 0 < Ce) hledger.1
  let Tw := (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card
  let A := ledgerTransportConstant Cw Tw
  let B := ledgerBirthConstant α q s Cw Tw (succAlphabetOf r₀ D₀ H J N p npad).card
  let τ := min (ocDelta α q / 4) τe
  have hτ : 0 < τ := lt_min (div_pos hδ (by norm_num)) hτe
  have hθ : τ < succTheta1 α q s σ₀ (succDstar D₀ N p H) := by
    have hηle : succEta0 α q s ≤ ocDelta α q / 8 := min_le_left _ _
    have hτle : τ ≤ ocDelta α q / 4 := min_le_left _ _
    dsimp only [succTheta1]
    linarith only [hδ, hηle, hτle, hσD]
  have hCw : 0 < Cw := hledger.2.2.2
  have hA : 1 ≤ A := by
    dsimp only [A, ledgerTransportConstant]
    have ht : 0 ≤ (Tw : ℝ) := Nat.cast_nonneg _
    have hc := hledger.2.2.2
    nlinarith only [ht, hc]
  have hB : 0 ≤ B := by
    dsimp only [B, ledgerBirthConstant]
    positivity
  obtain ⟨mStar, hmStar, hsmall⟩ := Ledger.ledger_scale_absorption q Λ hq.1 hq.2.1 hΛ τ
    (succTheta1 α q s σ₀ (succDstar D₀ N p H)) A B CI hτ hθ hA hB hCI
  refine ⟨mStar, ?_⟩
  intro D hDα hDq hDΛ _hDζ _hstream M _hband _hterm Mnat _hMnat law hlaw hr _ _ _ _ _ _ _
    seedK freshK _hfresh seed n tS tf hseed m hm _hmn _hnM tA _htA G G' hc hlevel hInv hs κc _hgate
  have hletter : ∀ l ∈ (succAlphabetOf r₀ D₀ H J N p npad),
      letterOrder N p l - 2 ≤ succDstar D₀ N p H := by
    intro l hl
    have hnext : succSchedD D₀ N p (H + 1) = succSchedD D₀ N p H + 2 * N + 4 * p + 4 := rfl
    cases l with
    | diag => simp only [letterOrder, succDstar]; omega
    | mean n h =>
      have hn := (Providers.CascadeInvariants.mean_mem_succAlphabet hl).2.1
      simp only [letterOrder, succDstar]
      omega
    | covariance n h a a' =>
      have hf := Providers.CascadeInvariants.cov_mem_succAlphabet hl
      simp only [letterOrder, succDstar]
      omega
    | eddy n =>
      simp [succAlphabetOf, succAlphabet] at hl
    | padding n => simp only [letterOrder]; omega
  have hold := InitialValue.cascade_invariant hseed.2.1 hc
  have hbounds := hsmall m hm
  have hε : D.eps m = ocEpsilon q Λ m := by simp only [OCData.eps, hDq, hDΛ]
  have hE : D.eps (m - 1) = ocEpsilon q Λ (m - 1) := by simp only [OCData.eps, hDq, hDΛ]
  have hrec' := Ledger.full_tagged_ledger_recurrence hr D _ bw j₀ α s q hDα hDq hq.1 (hDΛ.symm ▸ hΛ) hη Cw kI.cr σ₀ N p
    (succDstar D₀ N p H) (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s))
    hledger.2.2.2 hσ₀ hletter law hlaw G G' hInv.2.1 (fun v hv => (hold v hv).1) hs
    (by omega) (CI * D.eps m ^ τ) (mul_nonneg hCI.le (Real.rpow_nonneg (by
      rw [hε]; exact (Scales.epsilon_basic hq.1 hΛ).1.le) _)) hInv.2.2.2.2.2.2.2.1
    (by simpa only [A, Tw, succMenu, hε] using hbounds.1)
  rw [hlevel] at hrec'
  exact hrec'.trans (by simpa only [A, B, Tw, succMenu, hε, hE] using hbounds.2)

end AVRegularity.Construction.Preservation.Frontier
end
end
