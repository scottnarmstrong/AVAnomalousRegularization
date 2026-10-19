-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.FamilyVariableWindowWeightedFunctionalSourceProduction
import AVRegularity.CycleComparison.Lift.SecondCrossMean

section
section
/-! Genuine earlier productions supply all independent forcing fields and native predecessor germs.
-/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H D N R count K hh n : ℕ} {BG BV BE B : ℝ}
  (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
  (P : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
    IndependentScalarCoefficientProduction (2 + d) K q S.a S.b S.U
      (fun Y => S.Cc (independentStoredParameterProjection d Y) p q)
      (independentIntrinsicSlowProjection d) m α v u (finiteMatrixPower S.M p v u) B)

theorem independentLiftPredecessorFields_translation_invariant (δ : Vec (2 + d))
    (hP : ∀ p q hpq m hm α v u,
      IndependentSourceTranslationInvariant δ (P p q hpq m hm α v u).field)
    (p q m : ℕ) (α : DerivativeWord2 m) (v u : ι) :
    IndependentSourceTranslationInvariant δ (fun t z Y => independentLiftPredecessorFields S P p q m α t z Y v u) := by
  intro t z Y
  dsimp only [independentLiftPredecessorFields]
  by_cases hpq : p < hh ∨ (p = hh ∧ q < n)
  · simp only [dite_eq_left hpq, independentCoefficientProductionFields]
    by_cases hm : m ≤ q
    · simp only [dite_eq_left hm]
      exact hP p q hpq m hm (canonicalDerivativeWord α) v u t z Y
    · simp only [dite_eq_right hm]
  · simp only [dite_eq_right hpq]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Normalizing genuine forcing before inversion retains each positive stored birth weight. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {A E : Type*} {d H : ℕ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem family_variable_window_cross_natural_weighted_functional_independent_meanfree_source_extensions_exist {a b : A → ℝ} (hab : ∀ x, a x < b x)
    (N K S : ℕ) (hN : N + 2 ≤ H) (hH : N + (K + N) + 1 ≤ H)
    (hS : S ≤ N) (hSK : S + 4 ≤ K)
    {G : A → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {g : A → ℝ → Vec 2 → Vec d → E} (ℓ : E →L[ℝ] ℝ)
    (QG : ∀ x, IndependentParameterMetricReserve H (G x))
    (Qg : ∀ x, IndependentParameterSourceReserve H (fun t z Y => ℓ (g x t z Y)))
    (BG Bs : ℕ → ℝ) (hBG : ∀ n, 0 ≤ BG n) (hBs : ∀ n, 0 ≤ Bs n)
    (hQG : ∀ x n, n ≤ H → (QG x).budget n ≤ BG n)
    (θ : A → ℝ) (hθ : ∀ x, 0 < θ x)
    (hQg : ∀ x n, n ≤ H → (Qg x).budget n ≤ θ x * Bs n)
    (P : A → Vec d → MolecularData)
    (hP : ∀ x Y, dataCoefficients (P x Y) = ⟨(fun t _ => G x t Y), (P x Y).v, 0, 0⟩)
    (v : A → ℝ → Vec 2 → Vec 2) (hv : ∀ x, IsCellDrift (v x))
    (hPv : ∀ x Y, (P x Y).v = v x)
    (V : ∀ x Y K, K ≤ H → MolecularFiniteDriftBudget (P x Y) K)
    (hg : ∀ x t, t ≤ (a x) → ∀ z Y, ℓ (g x t z Y) = 0)
    (hmean : ∀ x t Y, fieldCellMean (fun z => ℓ (g x t z Y)) = 0)
    (Rel : A → Vec d → Vec d → Prop)
    (hGR : ∀ x Y Z, Rel x Y Z → ∀ t, G x t Y = G x t Z)
    (hgR : ∀ x Y Z, Rel x Y Z → ∀ t z, ℓ (g x t z Y) = ℓ (g x t z Z))
    (sZ : ℕ) (C : A → ℝ → Vec d → Vec 2 → E) (U : A → Set (Vec d))
    (hactual : ∀ x Y, Y ∈ U x → IsCellFieldInverse (P x Y).G (P x Y).v sZ (a x) (b x) 0
      (fun t z => g x t z Y) (fun t z => C x t Y z)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ (fext : A → ℝ → Vec 2 → Vec d → ℝ)
      (Qext : ∀ x, IndependentParameterSourceReserve S (fext x)),
      (∀ x r, r ≤ S → (Qext x).budget r ≤ θ x * (((d : ℝ) + 1) ^ r * B)) ∧
      (∀ x t Y, fieldCellMean (fun z => fext x t z Y) = 0) ∧
      (∀ x t, t ≤ (a x) → ∀ z Y, fext x t z Y = 0) ∧
      (∀ x t, t ∈ Icc (a x) (b x) → ∀ Y ∈ U x, ∀ z, fext x t z Y = ℓ (C x t Y z)) ∧
      (∀ x t Y Z, Rel x Y Z → ∀ z, fext x t z Y = fext x t z Z) ∧
      ∀ x x' Y Z, θ x = θ x' → a x = a x' → b x = b x' → v x = v x' →
        (∀ t, G x t Y = G x' t Z) →
        (∀ t z, ℓ (g x t z Y) = ℓ (g x' t z Z)) →
        ∀ t z, fext x t z Y = fext x' t z Z := by
  let L := fun x => (θ x)⁻¹ • ContinuousLinearMap.id ℝ ℝ
  let gn := fun x t z Y => (θ x)⁻¹ • g x t z Y
  let Qn : ∀ x, IndependentParameterSourceReserve H (fun t z Y => ℓ (gn x t z Y)) := fun x =>
    ((Qg x).map (L x)).congrSource (by
      funext t z Y
      change (θ x)⁻¹ • ℓ (g x t z Y) = ℓ ((θ x)⁻¹ • g x t z Y)
      exact (ℓ.map_smul _ _).symm)
  have hL x : ‖L x‖ = (θ x)⁻¹ := by
    rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hθ x))]
  have hQn x r (hr : r ≤ H) : (Qn x).budget r ≤ Bs r := by
    dsimp only [Qn]
    rw [IndependentParameterSourceReserve.congrSource_budget]
    change ‖L x‖ * (Qg x).budget r ≤ Bs r
    rw [hL]
    calc
      (θ x)⁻¹ * (Qg x).budget r ≤ (θ x)⁻¹ * (θ x * Bs r) :=
        mul_le_mul_of_nonneg_left (hQg x r hr) (inv_nonneg.mpr (hθ x).le)
      _ = Bs r := by rw [← mul_assoc, inv_mul_cancel₀ (hθ x).ne', one_mul]
  have han x Y (hY : Y ∈ U x) : IsCellFieldInverse (P x Y).G (P x Y).v sZ (a x) (b x) 0
      (fun t z => gn x t z Y) (fun t z => (θ x)⁻¹ • C x t Y z) := by
    have hh := cellFieldInverse_const_smul _ _ sZ (a x) (b x) 0 _ _ (hactual x Y hY) (θ x)⁻¹
    have hz : (fun z : Vec 2 => (θ x)⁻¹ • (0 : Vec 2 → E) z) = 0 := by
      funext z
      exact smul_zero _
    rw [hz] at hh
    exact hh
  obtain ⟨B, hB, fn, Qf, hb, hm, hp, he, hnat, hcross⟩ :=
    family_variable_window_cross_natural_functional_independent_meanfree_source_extensions_exist hab N K S hN hH hS hSK
      ℓ QG Qn BG Bs hBG hBs hQG hQn P hP v hv hPv V
      (fun x t ht z Y => by
        change ℓ ((θ x)⁻¹ • g x t z Y) = 0
        rw [map_smul, hg x t ht z Y, smul_zero])
      (fun x t Y => by
        change fieldCellMean (fun z => ℓ ((θ x)⁻¹ • g x t z Y)) = 0
        simp_rw [map_smul]
        rw [fieldCellMean_smul, hmean x t Y, smul_zero])
      Rel hGR (fun x Y Z hYZ t z => by
        change ℓ ((θ x)⁻¹ • g x t z Y) = ℓ ((θ x)⁻¹ • g x t z Z)
        simp only [map_smul]
        rw [hgR x Y Z hYZ])
      sZ (fun x t Y z => (θ x)⁻¹ • C x t Y z) U han
  let R := fun x => θ x • ContinuousLinearMap.id ℝ ℝ
  let fe := fun x t z Y => R x (fn x t z Y)
  let Qe := fun x => (Qf x).map (R x)
  refine ⟨B, hB, fe, Qe, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x r hr
    change ‖R x‖ * (Qf x).budget r ≤ _
    have hR : ‖R x‖ = θ x := by
      rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs, abs_of_pos (hθ x)]
    rw [hR]
    exact mul_le_mul_of_nonneg_left (hb x r hr) (hθ x).le
  · intro x t Y
    change fieldCellMean (fun z => θ x • fn x t z Y) = 0
    rw [fieldCellMean_smul, hm x t Y, smul_zero]
  · intro x t ht z Y
    change R x (fn x t z Y) = 0
    rw [hp x t ht z Y, map_zero]
  · intro x t ht Y hY z
    change θ x • fn x t z Y = ℓ (C x t Y z)
    rw [he x t ht Y hY z, map_smul, smul_smul, mul_inv_cancel₀ (hθ x).ne', one_smul]

  · intro x t Y Z hYZ z
    change R x (fn x t z Y) = R x (fn x t z Z)
    rw [hnat x t Y Z hYZ z]

  · intro x x' Y Z hθEq ha hb hvEq hG hforce t z
    have heq := hcross x x' Y Z ha hb hvEq hG (by
      intro r w
      change ℓ ((θ x)⁻¹ • g x r w Y) = ℓ ((θ x')⁻¹ • g x' r w Z)
      simp only [map_smul, hθEq, hforce r w]) t z
    change θ x • fn x t z Y = θ x' • fn x' t z Z
    rw [hθEq, heq]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine primitive and earlier-production translation identities, before the next rank is
produced. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

structure IndependentLiftNaturalPredecessorDatum (ι : Type*) [Fintype ι] [DecidableEq ι]
    (d H D N R count hh n qs : ℕ) (BG BV BE B : ℝ)
    extends IndependentLiftPredecessorDatum ι d H D N R count hh n qs BG BV BE B where
  translations : Set (Vec (2 + d))
  metric_translation : ∀ δ ∈ translations, ∀ t Y, primitive.G t (Y + δ) = primitive.G t Y
  edge_translation : ∀ δ ∈ translations, ∀ v u e γ, γ ∈ primitive.edge v u e → ∀ α,
    IndependentSourceTranslationInvariant δ (primitive.edgeField v u e γ α)
  earlier_translation : ∀ δ ∈ translations, ∀ p q hpq m hm α v u,
    IndependentSourceTranslationInvariant δ (earlier p q hpq m hm α v u).field

end AVRegularity.EntryWeakProofs
end
end

section
/-! Full independent dimensional flux fields on the bounded histories used by weak production. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

structure WeakStageProductionContext (D : OCData) (bw : ℝ) (j₀ level minBase cap : ℕ) where
  slot : OddSlot
  chain : StageCtx D bw j₀ level slot
  base_bound : minBase ≤ chain.1.baseLevel
  depth_bound : chain.1.children.length ≤ cap

def WeakStageProductionContext.atParameter {D : OCData} {bw : ℝ} {j₀ level minBase cap : ℕ}
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (Y : Vec (2 + 4 * c.chain.1.children.length))
    (hY : Y ∈ actualIndependentCoarseProductionCarrier D c.chain.1 bw (D.eps (level - 1))
      j₀ level c.slot.1) : StageCtx D bw j₀ level c.slot :=
  ⟨actualIndependentCoarseParameterChain D c.chain.1
    (independentStoredParameterProjection (4 * c.chain.1.children.length) Y),
    actualIndependentCoarseNativeCarrier_admissible D c.chain.1 bw j₀ level c.slot.1 c.chain.2 Y hY.1.1⟩

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

structure IndependentWeakStageFluxProduction (G : GenStage D hr Dm bw j₀)
    (minBase cap H : ℕ) (B : ℝ) where
  field : ∀ c : WeakStageProductionContext D bw j₀ G.level minBase cap,
    ∀ v u, G.fam.Γ v u → ∀ d, DerivativeWord2 (d - 1) →
      ℝ → Vec 2 → Vec (2 + 4 * c.chain.1.children.length) → Vec 2
  reserve : ∀ c v u γ d word, 2 ≤ d → d ≤ (G.fam.identity v u γ).maxOrder →
    IndependentParameterSourceReserve H (field c v u γ d word)
  budget : ∀ c v u γ d word hd hdn n, n ≤ H →
    (reserve c v u γ d word hd hdn).budget n ≤
      (G.fam.identity v u γ).record.size *
        (D.κ D.term * D.eps (G.level + 1) ^ ((G.fam.identity v u γ).maxOrder - 2) *
          D.eps G.level ^ ((d : ℝ) - ((G.fam.identity v u γ).maxOrder : ℝ)) * B)
  phase : ∀ (c : WeakStageProductionContext D bw j₀ G.level minBase cap) v u γ d word
    (δ : Vec (2 + 4 * c.chain.1.children.length)), δ ∈ independentFreshPhaseTranslations c.chain.1.children.length →
    IndependentSourceTranslationInvariant δ (field c v u γ d word)
  native_copy : ∀ (c : WeakStageProductionContext D bw j₀ G.level minBase cap) v u γ d word,
    2 ≤ d → d ≤ (G.fam.identity v u γ).maxOrder →
    ∀ Y : Vec (2 + 4 * c.chain.1.children.length),
    ∀ hY : Y ∈ actualIndependentCoarseProductionCarrier D c.chain.1 bw (D.eps (G.level - 1))
      j₀ G.level c.slot.1, ∀ t z,
    field c v u γ d word t z Y =
      G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) c.slot
        (c.atParameter Y hY) v u γ d word t
        (D.eps (G.level - 1) • independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y) z
  geometry : ∀ c c' : WeakStageProductionContext D bw j₀ G.level minBase cap,
    c.slot = c'.slot → c.chain.1.children.length = c'.chain.1.children.length →
    ∀ v u γ d word, 2 ≤ d → d ≤ (G.fam.identity v u γ).maxOrder →
    ∀ (P : Vec (4 * c.chain.1.children.length)) (Q : Vec (4 * c'.chain.1.children.length)),
    (∀ j, ‖independentFreshChildProjection j false P‖ ≤ 3 / 16) →
    (∀ j, ‖independentFreshChildProjection j false Q‖ ≤ 3 / 16) →
    (actualIndependentCoarseParameterChain D c.chain.1 P).geom D =
      (actualIndependentCoarseParameterChain D c'.chain.1 Q).geom D →
    ∀ X : Vec 2, ‖X‖ < 1 / 8 → ∀ t z,
    field c v u γ d word t z (independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P) =
      field c' v u γ d word t z (independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q)

theorem independentWeakStageFluxProduction_root (G : GenStage D hr Dm bw j₀)
    (top r : ℕ) (hroot : IsWeakRoot top r G) (minBase cap H : ℕ) (B : ℝ) :
    Nonempty (IndependentWeakStageFluxProduction G minBase cap H B) := by
  let : ∀ v u, IsEmpty (G.fam.Γ v u) := hroot.2.2.1
  exact ⟨{
    field := fun _ _ _ γ => isEmptyElim γ
    reserve := fun _ _ _ γ => isEmptyElim γ
    budget := fun _ _ _ γ => isEmptyElim γ
    phase := fun _ _ _ γ => isEmptyElim γ
    native_copy := fun _ _ _ γ => isEmptyElim γ
    geometry := fun _ _ _ _ _ _ γ => isEmptyElim γ }⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! Time measurability and fast periodicity of the globally extended physical Piola matrix. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance
namespace AVRegularity.EntryWeakProofs

theorem independentFreshClampedTransferMatrix_entry_measurable (r : ℕ)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (family : Vec (4 * r) → RealChain) (hfamily : ∀ p, (family p).WellSlotted)
    (pslot : ℤ) (hs : ∀ p, (family p).slot = pslot) (hp : Odd pslot)
    (harea : ∀ p, GeomAreaPreserving ((family p).geom D))
    (m : ℕ) (hm : ∀ p, (family p).ctxLevel = m)
    (ρ : ℝ) (slot : ℤ) (Y : Vec (2 + 4 * r)) (h : Vec 2) (i j : Fin 2) :
    Measurable (fun X : ℝ × Vec 2 =>
      independentFreshClampedTransferMatrix r D family m ρ slot X.1 (X.2, Y) h i j) := by
  let Z := independentFreshGeometryClamp r Y
  let p := independentStoredParameterProjection (4 * r) Z
  let C := (family p).recenter D (ρ • independentIntrinsicSlowProjection (4 * r) Z)
  obtain ⟨hc, hslot, hw⟩ := weak_recenter_ctxLevel_slot D (family p)
    (ρ • independentIntrinsicSlowProjection (4 * r) Z)
  have hcm : C.ctxLevel = m := hc.trans (hm p)
  have hcp : Odd C.slot := by
    change Odd ((family p).recenter D _).slot
    rw [hslot, hs]
    exact hp
  have hca : GeomAreaPreserving (C.geom D) := by
    change GeomAreaPreserving (((family p).recenter D _).geom D)
    rw [geom_recenter D _ (hfamily p) _]
    exact harea p
  have hh := weak_transfer_inverse_time_fast_entry_measurable D hΛ hζ C
    (hw.mpr (hfamily p)) hcp hca slot ((D.eps m)⁻¹ • h) i j
  have hE : D.eps m ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have he : (fun X : ℝ × Vec 2 =>
      independentFreshClampedTransferMatrix r D family m ρ slot X.1 (X.2, Y) h i j) =
      fun X : ℝ × Vec 2 =>
        (childTransition D slot X.1 (C.recenter D (D.eps C.ctxLevel • ((D.eps m)⁻¹ • h)))
          (X.2 + (D.eps C.ctxLevel)⁻¹ • (D.eps C.ctxLevel • ((D.eps m)⁻¹ • h))))⁻¹ i j := by
    funext X
    rw [independentFreshClampedTransferMatrix_literal r D hΛ, hcm, smul_inv_smul₀ hE]
  rw [he]
  exact hh

theorem independentFreshClampedTransferMatrix_entry_periodic (r : ℕ)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (family : Vec (4 * r) → RealChain) (hfamily : ∀ p, (family p).WellSlotted)
    (pslot : ℤ) (hs : ∀ p, (family p).slot = pslot) (hp : Odd pslot)
    (m : ℕ) (hm : ∀ p, (family p).ctxLevel = m)
    (ρ : ℝ) (slot : ℤ) (t : ℝ) (Y : Vec (2 + 4 * r)) (h : Vec 2) (i j : Fin 2) :
    IsZ2Periodic (fun z =>
      independentFreshClampedTransferMatrix r D family m ρ slot t (z, Y) h i j) := by
  let Z := independentFreshGeometryClamp r Y
  let p := independentStoredParameterProjection (4 * r) Z
  let C := (family p).recenter D (ρ • independentIntrinsicSlowProjection (4 * r) Z)
  obtain ⟨hc, hslot, hw⟩ := weak_recenter_ctxLevel_slot D (family p)
    (ρ • independentIntrinsicSlowProjection (4 * r) Z)
  have hcm : C.ctxLevel = m := hc.trans (hm p)
  have hcp : Odd C.slot := by
    change Odd ((family p).recenter D _).slot
    rw [hslot, hs]
    exact hp
  have hh := weak_transfer_matrix_joint_fast_periodic D hΛ hζ C
    (hw.mpr (hfamily p)) hcp slot t ((D.eps m)⁻¹ • h) i j
  have hE : D.eps m ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have he : (fun z =>
      independentFreshClampedTransferMatrix r D family m ρ slot t (z, Y) h i j) =
      fun z =>
        (childTransition D slot t (C.recenter D (D.eps C.ctxLevel • ((D.eps m)⁻¹ • h)))
          (z + (D.eps C.ctxLevel)⁻¹ • (D.eps C.ctxLevel • ((D.eps m)⁻¹ • h))))⁻¹ i j := by
    funext z
    rw [independentFreshClampedTransferMatrix_literal r D hΛ, hcm, smul_inv_smul₀ hE]
  rw [he]
  exact hh

end AVRegularity.EntryWeakProofs
end
end

section
/-! Native zero-child charts may be recentered at every spatial point within the same production menu. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw : ℝ} {j₀ level minBase cap : ℕ}

def WeakStageProductionContext.recenterEmpty
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (hc : c.chain.1.children = []) (h : Vec 2) :
    WeakStageProductionContext D bw j₀ level minBase cap where
  slot := c.slot
  chain := ⟨c.chain.1.recenter D h,
    weak_admissible_recenter_empty D bw j₀ level c.slot.1 c.chain.1 hc c.chain.2 h⟩
  base_bound := by
    change minBase ≤ (c.chain.1.recenter D h).baseLevel
    rw [Providers.GenSem.recenter_nil D c.chain.1 hc]
    exact c.base_bound
  depth_bound := by
    change (c.chain.1.recenter D h).children.length ≤ cap
    rw [Providers.GenSem.recenter_nil D c.chain.1 hc]
    exact c.depth_bound

theorem WeakStageProductionContext.recenterEmpty_children
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (hc : c.chain.1.children = []) (h : Vec 2) :
    (c.recenterEmpty hc h).chain.1.children = [] := by
  change (c.chain.1.recenter D h).children = []
  rw [Providers.GenSem.recenter_nil D c.chain.1 hc]
  exact hc

theorem actualIndependentCoarseProductionCarrier_empty_native
    (D : OCData) (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (A : RealChain) (hc : A.children = []) (bw ρ : ℝ) (hbw : bw ≤ 1 / 10000)
    (j₀ level : ℕ) (slot : ℤ) (hA : IsAdmissibleChain D bw j₀ level slot A)
    (X : Vec 2) (hX : ‖X‖ < 1 / 8) :
    independentIntrinsicParameterPacking (4 * A.children.length) X (independentFreshCoarseChainPacking D A) ∈
      actualIndependentCoarseProductionCarrier D A bw ρ j₀ level slot := by
  refine ⟨actualIndependentCoarseLiftCarrier_native D hq hΛ A bw ρ hbw j₀ level slot hA X hX.le ?_, ?_⟩
  · exact weak_admissible_recenter_empty D bw j₀ level slot A hc hA _
  · change ‖independentIntrinsicSlowProjection (4 * A.children.length)
        (independentIntrinsicParameterPacking _ X (independentFreshCoarseChainPacking D A))‖ < 1 / 8
    rw [independentIntrinsicParameterPacking_slow]
    exact hX

end AVRegularity.EntryWeakProofs
end
end

section
/-! A finite common stage budget preserves the actual produced fields. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {Dm : ℕ} {bw B : ℝ} {j₀ minBase cap H : ℕ}
  {G : GenStage D (fun _ => ℝ) Dm bw j₀}

def IndependentWeakStageFluxProduction.enlargeBudget
    (S : IndependentWeakStageFluxProduction G minBase cap H B)
    (hκ : 0 ≤ D.κ D.term) (hε : ∀ i, 0 < D.eps i) (B' : ℝ) (hBB' : B ≤ B') :
    IndependentWeakStageFluxProduction G minBase cap H B' where
  field := S.field
  reserve := S.reserve
  budget c v u γ d word hd hdn k hk := (S.budget c v u γ d word hd hdn k hk).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBB'
      (mul_nonneg (mul_nonneg hκ (pow_nonneg (hε _).le _))
        (Real.rpow_pos_of_pos (hε _) _).le)) (G.fam.identity v u γ).record.size_nonneg)
  phase := S.phase
  native_copy := S.native_copy
  geometry := S.geometry

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! Every actual stored-chain geometry retains the full phase lattice symmetry. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem actualIndependentCoarseParameterChain_geom_translation
    (D : OCData) (hΛ : 1 ≤ D.Λ) (A : RealChain) {bw : ℝ} {j₀ i : ℕ} {slot : ℤ}
    (hA : IsAdmissibleChain D bw j₀ i slot A)
    (δ : Vec (2 + 4 * A.children.length)) (hδ : δ ∈ independentFreshPhaseTranslations A.children.length)
    (P : Vec (4 * A.children.length)) :
    (actualIndependentCoarseParameterChain D A (P + independentStoredParameterProjection (4 * A.children.length) δ)).geom D =
      (actualIndependentCoarseParameterChain D A P).geom D := by
  rw [actualIndependentCoarseParameterChain_eq_fresh D A hA.2.2.1,
    actualIndependentCoarseParameterChain_eq_fresh D A hA.2.2.1,
    independentFreshStoredFamily_eq_chain, independentFreshStoredFamily_eq_chain]
  apply independentFreshChain_geom_phase_translation A.children.length D hΛ
    (independentFreshBaseChain A) _ _ ?_ δ hδ P
  have hs : (independentFreshBaseChain A).slots ++
      List.ofFn (fun j : Fin A.children.length => realChainSlotSeq A (j + 1)) = A.slots := by
    change [realChainSlotSeq A 0] ++ _ = _
    rw [← realChain_slots_ofFn A hA.2.2.1, List.ofFn_succ]
    rfl
  intro p hp
  rw [hs] at hp
  exact hA.2.2.2.2.1 p hp

end AVRegularity.EntryWeakProofs
end
end

section
/-! Every nonnegative stored matrix weight is retained, including zero response components. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {A E : Type*} {d H : ℕ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem family_variable_window_nonnegative_functional_independent_meanfree_source_extensions_exist {a b : A → ℝ} (hab : ∀ x, a x < b x)
    (N K S : ℕ) (hN : N + 2 ≤ H) (hH : N + (K + N) + 1 ≤ H)
    (hS : S ≤ N) (hSK : S + 4 ≤ K)
    {G : A → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {g : A → ℝ → Vec 2 → Vec d → E} (ℓ : E →L[ℝ] ℝ)
    (QG : ∀ x, IndependentParameterMetricReserve H (G x))
    (Qg : ∀ x, IndependentParameterSourceReserve H (fun t z Y => ℓ (g x t z Y)))
    (BG Bs : ℕ → ℝ) (hBG : ∀ n, 0 ≤ BG n) (hBs : ∀ n, 0 ≤ Bs n)
    (hQG : ∀ x n, n ≤ H → (QG x).budget n ≤ BG n)
    (θ : A → ℝ) (hθ : ∀ x, 0 ≤ θ x)
    (hQg : ∀ x n, n ≤ H → (Qg x).budget n ≤ θ x * Bs n)
    (P : A → Vec d → MolecularData)
    (hP : ∀ x Y, dataCoefficients (P x Y) = ⟨(fun t _ => G x t Y), (P x Y).v, 0, 0⟩)
    (v : A → ℝ → Vec 2 → Vec 2) (hv : ∀ x, IsCellDrift (v x))
    (hPv : ∀ x Y, (P x Y).v = v x)
    (V : ∀ x Y K, K ≤ H → MolecularFiniteDriftBudget (P x Y) K)
    (hg : ∀ x t, t ≤ (a x) → ∀ z Y, ℓ (g x t z Y) = 0)
    (hmean : ∀ x t Y, fieldCellMean (fun z => ℓ (g x t z Y)) = 0)
    (sZ : ℕ) (C : A → ℝ → Vec d → Vec 2 → E) (U : A → Set (Vec d))
    (hactual : ∀ x Y, Y ∈ U x → IsCellFieldInverse (P x Y).G (P x Y).v sZ (a x) (b x) 0
      (fun t z => g x t z Y) (fun t z => C x t Y z)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ (fext : A → ℝ → Vec 2 → Vec d → ℝ)
      (Qext : ∀ x, IndependentParameterSourceReserve S (fext x)),
      (∀ x r, r ≤ S → (Qext x).budget r ≤ θ x * (((d : ℝ) + 1) ^ r * B)) ∧
      (∀ x t Y, fieldCellMean (fun z => fext x t z Y) = 0) ∧
      (∀ x t, t ≤ (a x) → ∀ z Y, fext x t z Y = 0) ∧
      ∀ x t, t ∈ Icc (a x) (b x) → ∀ Y ∈ U x, ∀ z, fext x t z Y = ℓ (C x t Y z) := by
  classical
  let Ap := {x : A // 0 < θ x}
  obtain ⟨B, hB, fe, Qe, hb, hm, hp, he⟩ :=
    family_variable_window_weighted_functional_independent_meanfree_source_extensions_exist (A := Ap)
      (fun x => hab x.val) N K S hN hH hS hSK ℓ (fun x => QG x.val) (fun x => Qg x.val)
      BG Bs hBG hBs (fun x => hQG x.val) (fun x => θ x.val) (fun x => x.property)
      (fun x => hQg x.val) (fun x => P x.val) (fun x => hP x.val)
      (fun x => v x.val) (fun x => hv x.val) (fun x => hPv x.val) (fun x => V x.val)
      (fun x => hg x.val) (fun x => hmean x.val) sZ (fun x => C x.val)
      (fun x => U x.val) (fun x => hactual x.val)
  have hx (x : A) : ∃ f : ℝ → Vec 2 → Vec d → ℝ,
      ∃ Q : IndependentParameterSourceReserve S f,
      (∀ r, r ≤ S → Q.budget r ≤ θ x * (((d : ℝ) + 1) ^ r * B)) ∧
      (∀ t Y, fieldCellMean (fun z => f t z Y) = 0) ∧
      (∀ t, t ≤ (a x) → ∀ z Y, f t z Y = 0) ∧
      ∀ t, t ∈ Icc (a x) (b x) → ∀ Y ∈ U x, ∀ z, f t z Y = ℓ (C x t Y z) := by
    by_cases hpos : 0 < θ x
    · exact ⟨fe ⟨x, hpos⟩, Qe ⟨x, hpos⟩, hb ⟨x, hpos⟩,
        hm ⟨x, hpos⟩, hp ⟨x, hpos⟩, he ⟨x, hpos⟩⟩
    · have hzθ : θ x = 0 := le_antisymm (le_of_not_gt hpos) (hθ x)
      have hgzero (t : ℝ) (z : Vec 2) (Y : Vec d) : ℓ (g x t z Y) = 0 := by
        have hv := (Qg x).derivative_bound 0 (Nat.zero_le _) t (z, Y)
        simp only [norm_iteratedFDeriv_zero] at hv
        have hb0 := hQg x 0 (Nat.zero_le H)
        rw [hzθ, zero_mul] at hb0
        exact norm_eq_zero.mp (le_antisymm (hv.trans hb0) (norm_nonneg _))
      refine ⟨(fun _ _ _ => 0), IndependentParameterSourceReserve.zero S, ?_, ?_, ?_, ?_⟩
      · intro r _
        change 0 ≤ θ x * _
        rw [hzθ, zero_mul]
      · intro t Y
        exact fieldCellMean_zero
      · intro t ht z Y
        rfl
      · intro t ht Y hY z
        exact (dataActual_inverse_zero_functional (hab x).le (P x Y) _ _ ℓ sZ
          (hactual x Y hY) (fun t _ z => hgzero t z Y) t ht z).symm
  choose f Q hbudget hmean' hpast hcopy using hx
  exact ⟨B, hB, f, Q, hbudget, hmean', hpast, hcopy⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! Scheduled successors and natural physical pieces stay inside the finite production menu. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def WeakStageProductionContext.zeroChild {D : OCData} (hΛ : 1 ≤ D.Λ)
    {bw : ℝ} (hbw : 0 < bw) {j₀ level minBase cap : ℕ}
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (slot : OddSlot) (hs : IsScheduledIn D level slot.1 c.slot.1) :
    WeakStageProductionContext D bw j₀ (level + 1) minBase (cap + 1) where
  slot := slot
  chain := ⟨weakZeroChildAnchor c.chain.1 slot.1,
    weakZeroChildAnchor_admissible D hΛ bw hbw j₀ level c.slot.1 slot.1 c.chain.1 c.chain.2 slot.2 hs⟩
  base_bound := c.base_bound
  depth_bound := by
    change (c.chain.1.children ++ [(⟨0, 0⟩ : ChainChild)]).length ≤ cap + 1
    rw [List.length_append, List.length_singleton]
    exact Nat.add_le_add_right c.depth_bound 1

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

def WeakStageProductionContext.actual (G : GenStage D hr Dm bw j₀)
    (M : ℕ) (hG : G.IsNatural M) (minBase cap : ℕ)
    (hbase : minBase ≤ G.level - 1) (p : OddSlot) :
    WeakStageProductionContext D bw j₀ G.level minBase cap where
  slot := p
  chain := G.actual p
  base_bound := by rw [hG.2.2.1 p]; exact hbase
  depth_bound := by
    rw [hG.2.2.1 p]
    exact Nat.zero_le cap

end AVRegularity.EntryWeakProofs
end
end

section
/-! Every nonnegative stored matrix weight is retained, including zero response components. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {A E : Type*} {d H : ℕ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem family_variable_window_cross_natural_nonnegative_functional_independent_meanfree_source_extensions_exist {a b : A → ℝ} (hab : ∀ x, a x < b x)
    (N K S : ℕ) (hN : N + 2 ≤ H) (hH : N + (K + N) + 1 ≤ H)
    (hS : S ≤ N) (hSK : S + 4 ≤ K)
    {G : A → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {g : A → ℝ → Vec 2 → Vec d → E} (ℓ : E →L[ℝ] ℝ)
    (QG : ∀ x, IndependentParameterMetricReserve H (G x))
    (Qg : ∀ x, IndependentParameterSourceReserve H (fun t z Y => ℓ (g x t z Y)))
    (BG Bs : ℕ → ℝ) (hBG : ∀ n, 0 ≤ BG n) (hBs : ∀ n, 0 ≤ Bs n)
    (hQG : ∀ x n, n ≤ H → (QG x).budget n ≤ BG n)
    (θ : A → ℝ) (hθ : ∀ x, 0 ≤ θ x)
    (hQg : ∀ x n, n ≤ H → (Qg x).budget n ≤ θ x * Bs n)
    (P : A → Vec d → MolecularData)
    (hP : ∀ x Y, dataCoefficients (P x Y) = ⟨(fun t _ => G x t Y), (P x Y).v, 0, 0⟩)
    (v : A → ℝ → Vec 2 → Vec 2) (hv : ∀ x, IsCellDrift (v x))
    (hPv : ∀ x Y, (P x Y).v = v x)
    (V : ∀ x Y K, K ≤ H → MolecularFiniteDriftBudget (P x Y) K)
    (hg : ∀ x t, t ≤ (a x) → ∀ z Y, ℓ (g x t z Y) = 0)
    (hmean : ∀ x t Y, fieldCellMean (fun z => ℓ (g x t z Y)) = 0)
    (Rel : A → Vec d → Vec d → Prop)
    (hGR : ∀ x Y Z, Rel x Y Z → ∀ t, G x t Y = G x t Z)
    (hgR : ∀ x Y Z, Rel x Y Z → ∀ t z, ℓ (g x t z Y) = ℓ (g x t z Z))
    (sZ : ℕ) (C : A → ℝ → Vec d → Vec 2 → E) (U : A → Set (Vec d))
    (hactual : ∀ x Y, Y ∈ U x → IsCellFieldInverse (P x Y).G (P x Y).v sZ (a x) (b x) 0
      (fun t z => g x t z Y) (fun t z => C x t Y z)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ (fext : A → ℝ → Vec 2 → Vec d → ℝ)
      (Qext : ∀ x, IndependentParameterSourceReserve S (fext x)),
      (∀ x r, r ≤ S → (Qext x).budget r ≤ θ x * (((d : ℝ) + 1) ^ r * B)) ∧
      (∀ x t Y, fieldCellMean (fun z => fext x t z Y) = 0) ∧
      (∀ x t, t ≤ (a x) → ∀ z Y, fext x t z Y = 0) ∧
      (∀ x t, t ∈ Icc (a x) (b x) → ∀ Y ∈ U x, ∀ z, fext x t z Y = ℓ (C x t Y z)) ∧
      (∀ x t Y Z, Rel x Y Z → ∀ z, fext x t z Y = fext x t z Z) ∧
      ∀ x x' Y Z, θ x = θ x' → a x = a x' → b x = b x' → v x = v x' →
        (∀ t, G x t Y = G x' t Z) →
        (∀ t z, ℓ (g x t z Y) = ℓ (g x' t z Z)) →
        ∀ t z, fext x t z Y = fext x' t z Z := by
  classical
  let Ap := {x : A // 0 < θ x}
  obtain ⟨B, hB, fe, Qe, hb, hm, hp, he, hnat, hcross⟩ :=
    family_variable_window_cross_natural_weighted_functional_independent_meanfree_source_extensions_exist (A := Ap)
      (fun x => hab x.val) N K S hN hH hS hSK ℓ (fun x => QG x.val) (fun x => Qg x.val)
      BG Bs hBG hBs (fun x => hQG x.val) (fun x => θ x.val) (fun x => x.property)
      (fun x => hQg x.val) (fun x => P x.val) (fun x => hP x.val)
      (fun x => v x.val) (fun x => hv x.val) (fun x => hPv x.val) (fun x => V x.val)
      (fun x => hg x.val) (fun x => hmean x.val) (fun x => Rel x.val) (fun x => hGR x.val) (fun x => hgR x.val) sZ (fun x => C x.val)
      (fun x => U x.val) (fun x => hactual x.val)
  let f : A → ℝ → Vec 2 → Vec d → ℝ := fun x =>
    if hpos : 0 < θ x then fe ⟨x, hpos⟩ else fun _ _ _ => 0
  let Q : ∀ x, IndependentParameterSourceReserve S (f x) := fun x =>
    if hpos : 0 < θ x then
      (Qe ⟨x, hpos⟩).congrSource (by simp only [f, dite_eq_left hpos])
    else (IndependentParameterSourceReserve.zero S).congrSource (by simp only [f, dite_eq_right hpos])
  refine ⟨B, hB, f, Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x r hr
    by_cases hpos : 0 < θ x
    · simpa only [Q, dite_eq_left hpos, IndependentParameterSourceReserve.congrSource_budget]
        using hb ⟨x, hpos⟩ r hr
    · have hzθ : θ x = 0 := le_antisymm (le_of_not_gt hpos) (hθ x)
      simp only [Q, dite_eq_right hpos, IndependentParameterSourceReserve.congrSource_budget,
        IndependentParameterSourceReserve.zero, hzθ, zero_mul, le_refl]
  · intro x t Y
    by_cases hpos : 0 < θ x
    · simpa only [f, dite_eq_left hpos] using hm ⟨x, hpos⟩ t Y
    · simp only [f, dite_eq_right hpos, fieldCellMean_zero]
  · intro x t ht z Y
    by_cases hpos : 0 < θ x
    · simpa only [f, dite_eq_left hpos] using hp ⟨x, hpos⟩ t ht z Y
    · simp only [f, dite_eq_right hpos]
  · intro x t ht Y hY z
    by_cases hpos : 0 < θ x
    · simpa only [f, dite_eq_left hpos] using he ⟨x, hpos⟩ t ht Y hY z
    · have hzθ : θ x = 0 := le_antisymm (le_of_not_gt hpos) (hθ x)
      have hgzero (r : ℝ) (w : Vec 2) (Z : Vec d) : ℓ (g x r w Z) = 0 := by
        have hv0 := (Qg x).derivative_bound 0 (Nat.zero_le _) r (w, Z)
        simp only [norm_iteratedFDeriv_zero] at hv0
        have hb0 := hQg x 0 (Nat.zero_le H)
        rw [hzθ, zero_mul] at hb0
        exact norm_eq_zero.mp (le_antisymm (hv0.trans hb0) (norm_nonneg _))
      simpa only [f, dite_eq_right hpos] using
        (dataActual_inverse_zero_functional (hab x).le (P x Y) _ _ ℓ sZ
          (hactual x Y hY) (fun r _ w => hgzero r w Y) t ht z).symm
  · intro x t Y Z hYZ z
    by_cases hpos : 0 < θ x
    · simpa only [f, dite_eq_left hpos] using hnat ⟨x, hpos⟩ t Y Z hYZ z
    · simp only [f, dite_eq_right hpos]
  · intro x x' Y Z hθEq ha hb hvEq hG hforce t z
    by_cases hpos : 0 < θ x
    · have hpos' : 0 < θ x' := by rw [← hθEq]; exact hpos
      simpa only [f, dite_eq_left hpos, dite_eq_left hpos'] using
        hcross ⟨x, hpos⟩ ⟨x', hpos'⟩ Y Z hθEq ha hb hvEq hG hforce t z
    · have hpos' : ¬ 0 < θ x' := by rw [← hθEq]; exact hpos
      simp only [f, dite_eq_right hpos, dite_eq_right hpos']

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine predecessor productions transfer their forcing across equivalent primitive slow germs.
-/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H D N R count hh n qs : ℕ} {BG BV BE B : ℝ} {U : Set (Vec 2)}

theorem independentLiftPredecessorSource_slow_slice_congr
    (x y : IndependentLiftPredecessorDatum ι d H D N R count hh n qs BG BV BE B)
    (Y Z : Vec (2 + d)) (hU : IsOpen U)
    (he : IndependentLiftPrimitiveSlowSliceEq x.primitive y.primitive U Y Z)
    (hc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m α v u,
      IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
        (fun t z W => independentLiftPredecessorFields x.primitive x.earlier p q m α t z W v u)
        (fun t z W => independentLiftPredecessorFields y.primitive y.earlier p q m α t z W v u))
    (A : Vec 2 →L[ℝ] ℝ) (hn : 1 ≤ n) (hnD : n ≤ D) (out inp : ι) :
    IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
      (independentLiftPredecessorSource x.primitive x.earlier A out inp)
      (independentLiftPredecessorSource y.primitive y.earlier A out inp) := by
  dsimp only [independentLiftPredecessorSource]
  rw [← he.edge, ← he.drift]
  apply independentLiftCoefficientCellSource_slow_slice_congr x.primitive.edge
    x.primitive.edgeField y.primitive.edgeField (independentIntrinsicSlowEmbedding d)
    (independentIntrinsicSlowEmbedding_norm_le d) Y Z A 1 x.primitive.G y.primitive.G x.primitive.v
    _ _ hh n hn hnD out inp
  · intro i j
    exact (x.primitive.metric_entries i j).restrictOrder (D + 1) (by omega)
  · intro i j
    exact (y.primitive.metric_entries i j).restrictOrder (D + 1) (by omega)
  · intro i
    exact (x.primitive.drift_entries i).restrictOrder D (by omega)
  · intro p q hpq m α v u
    exact (independentLiftPredecessorFields_reserve x.primitive x.earlier p q hpq m α v u).restrictOrder
      (2 * D + 2) (by omega)
  · intro p q hpq m α v u
    exact (independentLiftPredecessorFields_reserve y.primitive y.earlier p q hpq m α v u).restrictOrder
      (2 * D + 2) (by omega)
  · intro v u e γ hγ α
    exact (x.primitive.edges v u e γ hγ α).restrictOrder (D + 1) (by omega)
  · intro v u e γ hγ α
    have hγ' : γ ∈ y.primitive.edge v u e := by rw [← he.edge]; exact hγ
    exact (y.primitive.edges v u e γ hγ' α).restrictOrder (D + 1) (by omega)
  · exact hU
  · exact he.metric
  · exact he.edge_fields
  · exact hc

end AVRegularity.EntryWeakProofs
end
end

section
/-! Changing a proved context-level index preserves every stored coordinate literally. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def WeakStageProductionContext.relevel {D : OCData} {bw : ℝ}
    {j₀ level next minBase cap : ℕ}
    (c : WeakStageProductionContext D bw j₀ level minBase cap) (he : level = next) :
    WeakStageProductionContext D bw j₀ next minBase cap where
  slot := c.slot
  chain := ⟨c.chain.1, he ▸ c.chain.2⟩
  base_bound := c.base_bound
  depth_bound := c.depth_bound

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual produced mean arrays retain the complete reserve, phase and reference geometry needed by one weak step. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

def weakStageMeanClockWindow (D : OCData) (level : ℕ) (slot : ℤ) : Set ℝ :=
  Icc (D.slotStart level slot / D.cellScaleSq level)
    ((((slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ level) / D.cellScaleSq level)

structure IndependentWeakMeanArrayProduction
    (D : OCData) (bw : ℝ) (j₀ level minBase cap H n : ℕ) (θ B : ℝ)
    (native : ∀ p : OddSlot, StageCtx D bw j₀ level p → ∀ d,
      DerivativeWord2 (d - 1) → ℝ → Vec 2) where
  field : ∀ c : WeakStageProductionContext D bw j₀ level minBase cap,
    ∀ d, DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec (2 + 4 * c.chain.1.children.length) → Vec 2
  reserve : ∀ c d word, IndependentParameterSourceReserve H (field c d word)
  budget : ∀ c d word k, k ≤ H → (reserve c d word).budget k ≤
    θ * (D.κ D.term * D.eps level ^ (n - 2) * D.eps (level - 1) ^ ((d : ℝ) - (n : ℝ)) * B)
  phase : ∀ (c : WeakStageProductionContext D bw j₀ level minBase cap) d word
    (δ : Vec (2 + 4 * c.chain.1.children.length)), δ ∈ independentFreshPhaseTranslations c.chain.1.children.length →
    IndependentSourceTranslationInvariant δ (field c d word)
  geometry : ∀ c c', c.slot = c'.slot → c.chain.1.children.length = c'.chain.1.children.length →
    ∀ d word (P : Vec (4 * c.chain.1.children.length)) (Q : Vec (4 * c'.chain.1.children.length)),
    (∀ j, ‖independentFreshChildProjection j false P‖ ≤ 3 / 16) →
    (∀ j, ‖independentFreshChildProjection j false Q‖ ≤ 3 / 16) →
    (actualIndependentCoarseParameterChain D c.chain.1 P).geom D =
      (actualIndependentCoarseParameterChain D c'.chain.1 Q).geom D →
    ∀ X : Vec 2, ‖X‖ < 1 / 8 → ∀ t z,
    field c d word t z (independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P) =
      field c' d word t z (independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q)
  native_copy : ∀ c d word, 2 ≤ d → d ≤ n → ∀ t,
    (D.cellScaleSq level)⁻¹ * t ∈ weakStageMeanClockWindow D level c.slot.1 → ∀ z,
    field c d word t z (independentIntrinsicParameterPacking (4 * c.chain.1.children.length) 0
      (independentFreshCoarseChainPacking D c.chain.1)) = native c.slot c.chain d word t

end AVRegularity.EntryWeakProofs
end
end
end
