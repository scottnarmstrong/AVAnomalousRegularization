-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients
public import AVRegularity.EntryWeakAssembly.FiniteStagePaths
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.EntryWeakAssembly.RelabelStage

@[expose] public noncomputable section

section
open AVRegularity.WeakEntryProofs
namespace AVRegularity.EntryTerminal.Route

/-! Terminal re-rooting separates the structural relabeling from positivity of its weights. -/

/-- Re-root all components, copy each finite identity once, raise its order bound,
and preserve exports. The prescribed root weights extend the old weights by one. -/
def SeedStructuralRelabelStatement : Prop :=
  ∀ {D : OCData} {Dt Ds : ℕ} {b : ℝ} {j₀ : ℕ}, Dt ≤ Ds →
    ∀ (Pt : ProvParams) (law : BirthLaw) (seedKt freshKt : ℕ → KernelSpec)
      (Gt : GenStage D ScalarH Dt b j₀),
    ∃ (seed : GenStage D ScalarH Ds b j₀) (seedKc : ℕ → KernelSpec)
      (ι : CompIn Gt.comps ≃ CompIn seed.comps),
      IsSeedEncoding Pt law (weakRootWeight Gt.comps (Gt.mass law))
        (weakRootWeight Gt.comps (Gt.readoutWeight law)) seedKt freshKt seedKc Gt seed ι ∧
      ∀ (i : ℕ) (p : ℤ) (e : Gen .ctx i p), seed.exports e ↔ Gt.exports e

/-- The structural re-rooting yields E4; all weight positivity follows from the OC regime. -/
theorem seedEncoding_of_ingredients (hstruct : SeedStructuralRelabelStatement) :
    SeedEncodingStatement := by
  intro D Dt Ds b j₀ hD hq hΛ Pt law seedKt freshKt Gt
  obtain ⟨seed, seedKc, ι, hseed, hexports⟩ := hstruct hD Pt law seedKt freshKt Gt
  refine ⟨seed, weakRootWeight Gt.comps (Gt.mass law),
    weakRootWeight Gt.comps (Gt.readoutWeight law), seedKc, ι, hseed, ?_, ?_, hexports⟩
  · exact weakRootWeight_pos _ _ (fun v =>
      Construction.Preservation.Buffer.birth_compMass_pos hq hΛ law v.1)
  · apply weakRootWeight_pos
    intro v
    apply mul_pos (law.rootReadout_pos v.1.root)
    apply List.prod_pos
    intro x hx
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
    exact pow_pos (Real.rpow_pos_of_pos (Scales.epsilon_basic
      (m := e.scale) hq hΛ).1 _) _

/-! Re-root a finite scalar stage and retain its identities, kernels and exports. -/

section
open scoped Classical

variable {D : OCData} {Dt Ds : ℕ} {b : ℝ} {j₀ : ℕ}

private abbrev Edges (G : GenStage D ScalarH Dt b j₀) :=
  Σ v : CompIn G.comps, Σ u : CompIn G.comps, G.fam.Γ v u

private def edgeLabel (G : GenStage D ScalarH Dt b j₀) (e : Edges G) : ℕ :=
  (Fintype.equivFin (Edges G) e).val

private theorem edgeLabel_injective (G : GenStage D ScalarH Dt b j₀) :
    Function.Injective (edgeLabel G) :=
  fun _ _ h => (Fintype.equivFin (Edges G)).injective (Fin.ext h)

private def raiseIdentity (hD : Dt ≤ Ds) (i : CoefficientIdentity Dt ℝ ℝ) :
    CoefficientIdentity Ds ℝ ℝ where
  map := i.map
  record := i.record
  maxOrder := i.maxOrder
  two_le := i.two_le
  le_D := i.le_D.trans hD
  le_birth := i.le_birth

private def reseedStage (hD : Dt ≤ Ds) (Pt : ProvParams)
    (G : GenStage D ScalarH Dt b j₀) : GenStage D ScalarH Ds b j₀ where
  level := G.level
  comps := G.comps
  fam :=
    { Γ := G.fam.Γ
      fintypeΓ := G.fam.fintypeΓ
      identity := fun v u γ => raiseIdentity hD (G.fam.identity v u γ)
      piece := G.fam.piece
      flux := G.fam.flux
      flux_periodic := G.fam.flux_periodic
      flux_zero := G.fam.flux_zero
      weight := G.fam.weight
      weight_nonneg := G.fam.weight_nonneg
      weight_zero := G.fam.weight_zero
      locally_finite := G.fam.locally_finite
      weight_sum := G.fam.weight_sum }
  prov := fun v u γ => .seed (edgeLabel G ⟨v, u, γ⟩) (seedTagOf ((G.prov v u γ).tags Pt))
  actual := G.actual
  exports := G.exports

/-- Re-rooting preserves every structural clause, without any analytic premise. -/
theorem seedStructuralRelabel : SeedStructuralRelabelStatement := by
  intro D Dt Ds b j₀ hD Pt law seedKt freshKt G
  let e := weakRootEquiv G.comps
  let G' := relabelWeakStage G (weakRootComps G.comps) e
  let seed := reseedStage hD Pt G'
  let table := Function.extend (edgeLabel G')
    (fun x : Edges G' => G'.kernelOf Pt seedKt freshKt x.1 x.2.1 x.2.2)
    (fun _ => seedKt 0)
  let idx := fun v u (γ : G.fam.Γ v u) =>
    edgeLabel G' ⟨e v, e u, relabelWeakEdge G _ e v u γ⟩
  refine ⟨seed, table, e, ?_, fun _ _ _ => Iff.rfl⟩
  refine ⟨rfl, fun _ => rfl, ?_, fun _ => rfl, fun _ => rfl, fun _ _ => rfl,
    fun v u => relabelWeakEdge G _ e v u, idx, ?_, ?_⟩
  · intro v
    exact ⟨weakRootWeight_label G.comps (G.mass law) v,
      weakRootWeight_label G.comps (G.readoutWeight law) v⟩
  · intro v u γ v' u' γ' hidx
    have h := edgeLabel_injective G' hidx
    have hv : v = v' := e.injective (congrArg Sigma.fst h)
    subst v'
    have hu : u = u' := e.injective (by
      have h' := Sigma.mk.inj_iff.mp h
      exact congrArg Sigma.fst (eq_of_heq h'.2))
    subst u'
    have hγ : γ = γ' := (relabelWeakEdge G _ e v u).injective (by
      have h' := Sigma.mk.inj_iff.mp h
      have h'' := Sigma.mk.inj_iff.mp (eq_of_heq h'.2)
      exact eq_of_heq h''.2)
    subst γ'
    exact ⟨rfl, rfl, HEq.rfl⟩
  · intro v u γ
    have hp := relabelWeakStage_prov G _ e v u γ
    have hi := relabelWeakStage_identity G _ e v u γ
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · change Prov.seed (idx v u γ) (seedTagOf ((G'.prov (e v) (e u)
        (relabelWeakEdge G _ e v u γ)).tags Pt)) = _
      rw [hp]
    · change table (edgeLabel G' ⟨e v, e u, relabelWeakEdge G _ e v u γ⟩) = _
      calc
        _ = G'.kernelOf Pt seedKt freshKt (e v) (e u) (relabelWeakEdge G _ e v u γ) :=
          (edgeLabel_injective G').extend_apply _ _ _
        _ = G.kernelOf Pt seedKt freshKt v u γ := by
          unfold GenStage.kernelOf
          rw [hp]
    · exact congrArg CoefficientIdentity.map hi
    · exact congrArg CoefficientIdentity.record hi
    · exact congrArg CoefficientIdentity.maxOrder hi
    · intro p c c' hc d I t X z
      have hcc : c = c' := Subtype.ext hc
      subst c'
      exact congrFun (congrFun (congrFun (congrFun (congrFun
        (relabelWeakStage_flux G _ e v u γ p c) d) I) t) X) z

/-- The revised terminal seed encoding, including positive root weights everywhere. -/
theorem seedEncoding : SeedEncodingStatement :=
  seedEncoding_of_ingredients seedStructuralRelabel
end

end AVRegularity.EntryTerminal.Route
end
