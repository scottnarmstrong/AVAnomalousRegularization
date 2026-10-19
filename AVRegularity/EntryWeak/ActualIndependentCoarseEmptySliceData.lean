-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.ActualIndependentCoarseSampledPiolaDatumCast
public import AVRegularity.CycleComparison.Lift.SettingLiftALeftTermsActionOfCoefficients
import AVRegularity.CycleJoint.PlaneImageJetMomentNorm

section
section
/-! Actual inverse tests retain every nonnegative matrix entry through independent coefficient production. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {A ι : Type*} [Fintype ι] [DecidableEq ι] {d H : ℕ}

theorem family_variable_window_cross_natural_independent_coefficient_productions_exist {a b : A → ℝ} (hab : ∀ x, a x < b x)
    (N K S n m : ℕ) (hm : m ≤ n) (hN : N + 2 ≤ H) (hH : N + (K + N) + 1 ≤ H)
    (hS : S ≤ N) (hSK : S + 4 ≤ K)
    {G : A → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {g : A → (Fin (m + 1) × Fin (n + 1)) → ℝ → Vec 2 → Vec d → ι → ℝ}
    (out inp : ι)
    (QG : ∀ x, IndependentParameterMetricReserve H (G x))
    (Qg : ∀ x p, IndependentParameterSourceReserve H (fun t z Y => g x p t z Y out))
    (BG Bs : ℕ → ℝ) (hBG : ∀ n, 0 ≤ BG n) (hBs : ∀ n, 0 ≤ Bs n)
    (hQG : ∀ x n, n ≤ H → (QG x).budget n ≤ BG n)
    (θ : A → ℝ) (hθ : ∀ x, 0 ≤ θ x)
    (hQg : ∀ x p r, r ≤ H → (Qg x p).budget r ≤ θ x * Bs r)
    (P : A → Vec d → MolecularData)
    (hP : ∀ x Y, dataCoefficients (P x Y) = ⟨(fun t _ => G x t Y), (P x Y).v, 0, 0⟩)
    (v : A → ℝ → Vec 2 → Vec 2) (hv : ∀ x, IsCellDrift (v x))
    (hPv : ∀ x Y, (P x Y).v = v x)
    (V : ∀ x Y K, K ≤ H → MolecularFiniteDriftBudget (P x Y) K)
    (hg : ∀ x p t, t ≤ (a x) → ∀ z Y, g x p t z Y out = 0)
    (hmean : ∀ x p t Y, fieldCellMean (fun z => g x p t z Y out) = 0)
    (Rel : A → Vec d → Vec d → Prop)
    (hGR : ∀ x Y Z, Rel x Y Z → ∀ t, G x t Y = G x t Z)
    (hgR : ∀ x p Y Z, Rel x Y Z → ∀ t z, g x p t z Y out = g x p t z Z out)
    (sZ : ℕ) (c : A → Vec d → LiftCoeff ι (fun _ => ℝ))
    (slowPoint : A → Vec d → Vec 2) (U : A → Set (Vec d))
    (hc : ∀ x Y β (σ : Equiv.Perm (Fin m)), c x Y m (β ∘ σ) = c x Y m β)
    (α : DerivativeWord2 m) (lam : ℝ) (hlam : lam ≠ 0)
    (hactual : ∀ x p Y, Y ∈ U x → IsCellFieldInverse (P x Y).G (P x Y).v sZ (a x) (b x) 0
      (fun t z => g x p t z Y)
      (fun t z => (Real.exp ((lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) (slowPoint x Y)))⁻¹ •
        liftApply n (c x Y) (fun _ Z => Real.exp ((lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) Z) •
          (Pi.single inp (1 : ℝ) : ι → ℝ)) t (slowPoint x Y) z)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ Q : ∀ x,
      IndependentScalarCoefficientProduction d S n (a x) (b x) (U x) (c x) (slowPoint x)
        m α out inp (θ x) B,
      (∀ x t Y Z, Rel x Y Z → ∀ z, (Q x).field t z Y = (Q x).field t z Z) ∧
      ∀ x x' Y Z, θ x = θ x' → a x = a x' → b x = b x' → v x = v x' →
        (∀ t, G x t Y = G x' t Z) →
        (∀ p t z, g x p t z Y out = g x' p t z Z out) →
        ∀ t z, (Q x).field t z Y = (Q x').field t z Z := by
  obtain ⟨B, hB, f, Q, hb, hmean, hpast, hcopy, hnat, hcross⟩ :=
    family_variable_window_cross_natural_nonnegative_independent_dual_coefficient_extensions_exist hab N K S n m hm hN hH hS hSK
      out inp QG Qg BG Bs hBG hBs hQG θ hθ hQg P hP v hv hPv V hg hmean Rel hGR hgR sZ c
      slowPoint U hc α lam hlam hactual
  refine ⟨((d : ℝ) + 1) ^ S * B, mul_nonneg (pow_nonneg (by positivity) _) hB,
    (fun x => ⟨f x, Q x, ?_, hcopy x, fun _ => hmean x, fun _ => hpast x⟩), hnat, hcross⟩
  intro r hr
  exact (hb x r hr).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact le_add_of_nonneg_left (Nat.cast_nonneg d) : (1 : ℝ) ≤ (d : ℝ) + 1) hr) hB)
    (hθ x))

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual windowed sampled source is independent of choices of reserve witnesses. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

def actualWeakSampledPiolaArray (D : OCData) (A : RealChain) (ell : ℝ) (slot : ℤ)
    (I : Set ℝ)
    (f : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ → Vec 2 →
      Vec (2 + 4 * (A.children.length + 1)) → Vec 2)
    (d : ℕ) (word : DerivativeWord2 (d - 1)) (t : ℝ) (z : Vec 2)
    (Y : Vec (2 + 4 * A.children.length)) : Vec 2 :=
  fun a => independentTimeWindowSource I
    (independentFreshCoarseAppendedSource A.children.length D A.ctxLevel A.slot slot ell
      (fun t z W => f d word t z W a)) t z Y

def actualWeakSampledPiolaField (D : OCData) (A : RealChain) (ρ ell : ℝ) (slot : ℤ)
    (I : Set ℝ) (n : ℕ)
    (f : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ → Vec 2 →
      Vec (2 + 4 * (A.children.length + 1)) → Vec 2)
    (d : ℕ) (word : DerivativeWord2 (d - 1)) (t : ℝ) (z : Vec 2)
    (Y : Vec (2 + 4 * A.children.length)) : Vec 2 :=
  fun a => independentTimeWindowSource I
    (fun tt zz W => transportedCoeff
      (fun w => independentFreshClampedTransferMatrix A.children.length D
        (actualIndependentCoarseParameterChain D A) A.ctxLevel ρ slot tt (zz, W) w) n
      (fun e β => actualWeakSampledPiolaArray D A ell slot I f e β tt zz W) (d - 1) word 0 a) t z Y

theorem IndependentPiolaWindowDatum.source_eq_actualWeakSampledPiolaField
    {H N n : ℕ} {E C θ κ e B₀ : ℝ}
    (D : OCData) (A : RealChain) (ρ ell : ℝ) (slot : ℤ) (I : Set ℝ)
    (f : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ → Vec 2 →
      Vec (2 + 4 * (A.children.length + 1)) → Vec 2)
    (T : IndependentPiolaWindowDatum (Vec (2 + 4 * A.children.length)) H N n n E C θ κ e B₀)
    (hw : T.window = I)
    (hM : T.matrix = fun t z Y w => independentFreshClampedTransferMatrix A.children.length D
      (actualIndependentCoarseParameterChain D A) A.ctxLevel ρ slot t (z, Y) w)
    (hf : T.array = actualWeakSampledPiolaArray D A ell slot I f)
    (d : ℕ) (word : DerivativeWord2 (d - 1)) :
    T.source (d - 1) word = actualWeakSampledPiolaField D A ρ ell slot I n f d word := by
  unfold IndependentPiolaWindowDatum.source actualWeakSampledPiolaField
  rw [hw, hM, hf]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Phase symmetry of the literal sampled field needs no choice of a Piola reserve. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

theorem actualWeakSampledPiolaField_phase
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (A : RealChain) {bw : ℝ} {j₀ i : ℕ} {p : ℤ}
    (hA : IsAdmissibleChain D bw j₀ i p A)
    (ρ ell : ℝ) (slot : ℤ) (I : Set ℝ) (n : ℕ)
    (f : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ → Vec 2 →
      Vec (2 + 4 * (A.children.length + 1)) → Vec 2)
    (hf : ∀ d word δ, δ ∈ independentFreshPhaseTranslations (A.children.length + 1) →
      IndependentSourceTranslationInvariant δ (f d word))
    (δ : Vec (2 + 4 * A.children.length)) (hδ : δ ∈ independentFreshPhaseTranslations A.children.length)
    (d : ℕ) (word : DerivativeWord2 (d - 1)) :
    IndependentSourceTranslationInvariant δ (actualWeakSampledPiolaField D A ρ ell slot I n f d word) := by
  classical
  have hK t z Y w := independentFreshClampedTransferMatrix_phase_translation A.children.length D hΛ hζ
    (actualIndependentCoarseParameterChain D A)
    (actualIndependentCoarseParameterChain_wellSlotted D A hA.2.2.1)
    A.ctxLevel (actualIndependentCoarseParameterChain_ctxLevel D A)
    A.slot (actualIndependentCoarseParameterChain_slot D A) δ hδ
    (actualIndependentCoarseParameterChain_geom_translation D hΛ A hA δ hδ) ρ slot t z w Y
  have hB e β : IndependentSourceTranslationInvariant δ (actualWeakSampledPiolaArray D A ell slot I f e β) :=
    independentFreshCoarseClockSampledArray_translation A.children.length D A.ctxLevel A.slot slot ell
      (fun t => t) I (f e β) (hf e β) δ hδ
  have he := independentPiolaSource_translation δ
    (fun t z Y w => independentFreshClampedTransferMatrix A.children.length D
      (actualIndependentCoarseParameterChain D A) A.ctxLevel ρ slot t (z, Y) w)
    hK n (d - 1) (actualWeakSampledPiolaArray D A ell slot I f) hB word
  intro t z Y
  funext a
  change (if t ∈ I then _ else 0) = (if t ∈ I then _ else 0)
  have hh := congrFun (he t z Y) a
  dsimp only at hh ⊢
  rw [hh]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Literal native copies pass through the explicit actual sampled Piola field. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

theorem actualWeakSampledPiolaField_native_copy
    (D : OCData) (A : RealChain) (ρ ell : ℝ) (slot : ℤ) (I : Set ℝ) (n : ℕ)
    (f : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ → Vec 2 →
      Vec (2 + 4 * (A.children.length + 1)) → Vec 2)
    (d : ℕ) (word : DerivativeWord2 (d - 1))
    (t : ℝ) (ht : t ∈ I) (z : Vec 2) (Y : Vec (2 + 4 * A.children.length))
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (B : ∀ e : ℕ, DerivativeWord2 (e - 1) → Vec 2)
    (hK : (fun w => independentFreshClampedTransferMatrix A.children.length D
      (actualIndependentCoarseParameterChain D A) A.ctxLevel ρ slot t (z, Y) w) = K)
    (hB : ∀ e ∈ Finset.Icc (d - 1 + 1) n, ∀ β,
      actualWeakSampledPiolaArray D A ell slot I f e β t z Y = B e β) :
    actualWeakSampledPiolaField D A ρ ell slot I n f d word t z Y =
      transportedCoeff K n B (d - 1) word 0 := by
  classical
  have he := CycleJointProofs.transportedCoeff_source_congr K n
    (fun e β => actualWeakSampledPiolaArray D A ell slot I f e β t z Y) B (d - 1) word 0 hB
  funext a
  change (if t ∈ I then _ else 0) = _
  rw [ite_eq_left ht]
  dsimp only
  rw [hK]
  exact congrFun he a

end AVRegularity.EntryWeakProofs
end
end

section
/-! The full admissible lift carrier licenses equality of the extended metric and its native germ. -/
@[expose] public noncomputable section
open Homogenization Set Filter Topology
namespace AVRegularity.EntryWeakProofs

theorem actualIndependentCoarseScaledExtendedMetric_lift_carrier_copy
    (D : OCData) (A : RealChain) (bw ρ a b t : ℝ) (j₀ level : ℕ) (slot : ℤ)
    (χ : Vec (2 + 4 * A.children.length) → ℝ)
    (hχ : ∀ Y, ‖independentFreshCarrierCoordinates A.children.length Y‖ < 1 / 4 →
      χ =ᶠ[𝓝 Y] fun _ => 1) (ht : t ∈ Icc a b)
    (Y : Vec (2 + 4 * A.children.length))
    (hY : Y ∈ actualIndependentCoarseLiftCarrier D A bw ρ j₀ level slot) :
    actualIndependentCoarseScaledExtendedMetric D A ρ χ a b t Y =
      actualIndependentCoarseScaledMetric D A ρ t Y := by
  have he : χ Y = 1 := (hχ Y hY.1.2).eq_of_nhds
  simp only [actualIndependentCoarseScaledExtendedMetric, clampedParameterMetric,
    min_eq_right ht.2, max_eq_right ht.1, cutoffParameterMetric, he, one_smul, add_sub_cancel]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine stage production supplies every incoming path field and its retained witness matrix. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ minBase cap H : ℕ} {B : ℝ}
  {G : GenStage D hr Dm bw j₀} {h : ℕ}

def IndependentWeakStageFluxProduction.pathIncomingField
    (S : IndependentWeakStageFluxProduction G minBase cap H B) (π : StagePath G h)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (j : Fin h) (d : Finset.Icc 2 Dm) (word : DerivativeWord2 (d.val - 1)) :
    ℝ → Vec 2 → Vec (2 + 4 * c.chain.1.children.length) → Vec 2 :=
  S.incomingField c _ _ (π.step j).2.2 d.val word

theorem IndependentWeakStageFluxProduction.incomingField_slice_native_copy
    (S : IndependentWeakStageFluxProduction G minBase cap H B)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (word : DerivativeWord2 (d - 1))
    (hd : 2 ≤ d) (hdn : d ≤ (G.fam.identity v u γ).maxOrder)
    (Y : Vec (2 + 4 * c.chain.1.children.length))
    (hY : Y ∈ actualIndependentCoarseProductionCarrier D c.chain.1 bw (D.eps (G.level - 1))
      j₀ G.level c.slot.1)
    (X : Vec 2) (hX : X ∈ independentIntrinsicSliceCarrier (4 * c.chain.1.children.length)
      (actualIndependentCoarseProductionCarrier D c.chain.1 bw (D.eps (G.level - 1))
        j₀ G.level c.slot.1) Y) (t : ℝ) (z : Vec 2) :
    G.fam.flux c.slot (c.atParameter Y hY) v u γ d word (D.cellScaleSq G.level * t) X z =
      S.incomingField c v u γ d word t z
        (independentIntrinsicSlowEmbedding (4 * c.chain.1.children.length) X +
          independentIntrinsicSliceOffset (4 * c.chain.1.children.length) Y) := by
  let W := independentIntrinsicSlowEmbedding (4 * c.chain.1.children.length) X +
    independentIntrinsicSliceOffset (4 * c.chain.1.children.length) Y
  have he : c.atParameter W hX = c.atParameter Y hY := by
    apply Subtype.ext
    change actualIndependentCoarseParameterChain D c.chain.1
      (independentStoredParameterProjection _ W) = _
    rw [independentStoredParameterProjection_slice]
    rfl
  rw [S.incomingField_native_copy hΛ hζ hband c v u γ d word hd hdn W hX t z, he]
  rw [independentIntrinsicSlowProjection_slice]

theorem IndependentWeakStageFluxProduction.pathIncomingField_translation
    (S : IndependentWeakStageFluxProduction G minBase cap H B) (π : StagePath G h)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (δ : Vec (2 + 4 * c.chain.1.children.length))
    (hδ : δ ∈ independentFreshPhaseTranslations c.chain.1.children.length)
    (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (γ : Constituent d.val ℝ ℝ)
    (word : DerivativeWord2 (d.val - 1)) :
    IndependentSourceTranslationInvariant δ
      (independentPathTemplateField (S.pathIncomingField π c) v u d γ word) := by
  apply independentPathTemplateField_translation δ (S.pathIncomingField π c)
  intro j d word
  exact S.incomingField_translation c _ _ (π.step j).2.2 d.val word δ hδ

end AVRegularity.EntryWeakProofs
end
end

section
/-! The stage's common reference ball passes to every genuine incoming path label. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ minBase cap H : ℕ} {B : ℝ}
  {G : GenStage D hr Dm bw j₀}

theorem IndependentWeakStageFluxProduction.incomingField_geometry
    (S : IndependentWeakStageFluxProduction G minBase cap H B)
    (c c' : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (hslot : c.slot = c'.slot) (hdepth : c.chain.1.children.length = c'.chain.1.children.length)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (word : DerivativeWord2 (d - 1))
    (hd : 2 ≤ d) (hdn : d ≤ (G.fam.identity v u γ).maxOrder)
    (P : Vec (4 * c.chain.1.children.length)) (Q : Vec (4 * c'.chain.1.children.length))
    (hP : ∀ j, ‖independentFreshChildProjection j false P‖ ≤ 3 / 16)
    (hQ : ∀ j, ‖independentFreshChildProjection j false Q‖ ≤ 3 / 16)
    (hgeom : (actualIndependentCoarseParameterChain D c.chain.1 P).geom D =
      (actualIndependentCoarseParameterChain D c'.chain.1 Q).geom D)
    (X : Vec 2) (hX : ‖X‖ < 1 / 8) (t : ℝ) (z : Vec 2) :
    S.incomingField c v u γ d word t z
        (independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P) =
      S.incomingField c' v u γ d word t z
        (independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q) := by
  exact congrArg (fun w : Vec 2 => (D.kap G.level * D.eps G.level ^ (d - 2))⁻¹ • w)
    (S.geometry c c' hslot hdepth v u γ d word hd hdn P Q hP hQ hgeom X hX
      (D.cellScaleSq G.level * t) z)

theorem IndependentWeakStageFluxProduction.pathTemplateField_geometry
    (S : IndependentWeakStageFluxProduction G minBase cap H B)
    {h : ℕ} (π : StagePath G h)
    (c c' : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (hslot : c.slot = c'.slot) (hdepth : c.chain.1.children.length = c'.chain.1.children.length)
    (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (γ : Constituent d.val ℝ ℝ)
    (anchor : StageCtx D bw j₀ G.level c.slot)
    (hγ : γ ∈ pathEdges G π c.slot anchor v u d) (word : DerivativeWord2 (d.val - 1))
    (P : Vec (4 * c.chain.1.children.length)) (Q : Vec (4 * c'.chain.1.children.length))
    (hP : ∀ j, ‖independentFreshChildProjection j false P‖ ≤ 3 / 16)
    (hQ : ∀ j, ‖independentFreshChildProjection j false Q‖ ≤ 3 / 16)
    (hgeom : (actualIndependentCoarseParameterChain D c.chain.1 P).geom D =
      (actualIndependentCoarseParameterChain D c'.chain.1 Q).geom D)
    (X : Vec 2) (hX : ‖X‖ < 1 / 8) (t : ℝ) (z : Vec 2) :
    independentPathTemplateField (S.pathIncomingField π c) v u d γ word t z
        (independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P) =
      independentPathTemplateField (S.pathIncomingField π c') v u d γ word t z
        (independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q) := by
  unfold pathEdges at hγ
  split at hγ
  next hvu =>
    split at hγ
    next hd =>
      dsimp only [independentPathTemplateField]
      rw [dite_eq_left hvu.2, dite_eq_left hvu.2]
      exact S.incomingField_geometry c c' hslot hdepth _ _ (π.step ⟨u.val, hvu.2⟩).2.2
        d.val word (Finset.mem_Icc.mp d.property).1 hd P Q hP hQ hgeom X hX t z
    · exact (List.not_mem_nil hγ).elim
  · exact (List.not_mem_nil hγ).elim

end AVRegularity.EntryWeakProofs
end
end

section
/-! The symmetric positive mean-flux array acts intrinsically, without a transverse lift setting. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {D : ℕ}

theorem positiveMeanFluxCoefficient_intrinsic_apply
    (Q : LiftOperatorData ι (fun _ => ℝ) D) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k : Fin 2) (t : ℝ) (X z : Vec 2) (v : ι)
    (hv : Continuous (fun y => Q.v t y k))
    (hc : ∀ m ≤ n - 1, ∀ α : DerivativeWord2 m, ∀ u,
      Continuous (fun y => Cc hh (n - 1) m α t X y v u))
    (hsource : ∀ j ≤ min (D - 1) (n - 1), ∀ m ≤ n - 1 - j,
      ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j)
        (fun X z => Cc (hh - 1) (n - 1 - j) m α t X z u u'))
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsBoxSmooth 0 0 (fun X z => γ.coeff α t X z k)) :
    liftApply (n - 1) (positiveMeanFluxCoefficient Q Cc hh n k) (fun _ => f) t X z v =
      fieldCellMean (fun y => (Real.sqrt Q.η * Q.v t y k) •
        liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t X y v) -
      Real.sqrt Q.η • fieldCellMean (fun y =>
        ∑ j ∈ Finset.range (min (D - 1) (n - 1) + 1),
          sourceFluxComponentCoefficient Q.edge Q.η t
            (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j)) (fun _ => f) t)
            k j v X y) := by
  let c := weightedLiftCoefficientMean (Cc hh (n - 1))
    (fun t z => Real.sqrt Q.η * Q.v t z k)
  let d : LiftCoeff ι (fun _ => ℝ) := fun m α t X z v u =>
    sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k m α t X z v u
  change liftApply (n - 1) (fun m α t X z v u => c m α t X z v u -
    Real.sqrt Q.η • d m α t X z v u) (fun _ => f) t X z v = _
  rw [liftApply_coefficient_sub, liftApply_coefficient_smul]
  simp only [Pi.sub_apply, Pi.smul_apply]
  rw [weightedLiftCoefficientMean_apply (n - 1) _ _ _ t X z v
    (continuous_const.mul hv) hc]
  have hd : liftApply (n - 1) d (fun _ => f) t X z v =
      fieldCellMean (fun y =>
        ∑ j ∈ Finset.range (min (D - 1) (n - 1) + 1),
          sourceFluxComponentCoefficient Q.edge Q.η t
            (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j)) (fun _ => f) t)
            k j v X y) :=
    by
      simpa only [liftApply, d] using
        sourceFluxMeanCoefficient_apply Q.edge Q.η t (n - 1) (Cc (hh - 1)) k
          hsource hΓ f hf X z v
  rw [hd]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Native positive mean coefficient arrays depend only on earlier germs inside the carrier. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {hv : ι → Type*}
  [∀ i, NormedAddCommGroup (hv i)] [∀ i, InnerProductSpace ℝ (hv i)] {D : ℕ} {U : Set (Vec 2)}

theorem positiveMeanFluxCoefficient_slow_local_congr (hU : IsOpen U)
    (Q : LiftOperatorData ι hv D) (Cc Dc : ℕ → ℕ → LiftCoeff ι hv)
    (hh n : ℕ) (hn : 1 ≤ n) (hhpos : hh ≠ 0) (t : ℝ)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m ≤ q, ∀ α X,
      X ∈ U → ∀ z v u, Cc p q m α t X z v u = Dc p q m α t X z v u)
    (k : Fin 2) (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m)
    (X : Vec 2) (hX : X ∈ U) (z : Vec 2) (v u : ι) :
    positiveMeanFluxCoefficient Q Cc hh n k m α t X z v u =
      positiveMeanFluxCoefficient Q Dc hh n k m α t X z v u := by
  unfold positiveMeanFluxCoefficient
  apply congrArg₂ (fun a b => a - Real.sqrt Q.η • b)
  · unfold weightedLiftCoefficientMean
    apply congrArg fieldCellMean
    funext y
    rw [he hh (n - 1) (Or.inr ⟨rfl, by omega⟩) m hm α X hX y v u]
  · exact sourceFluxMeanCoefficient_slow_local_congr hU Q.edge Q.η t (n - 1)
      (Cc (hh - 1)) (Dc (hh - 1))
      (fun q _ m hm α X hX z v u => he (hh - 1) q (Or.inl (by omega)) m hm α X hX z v u)
      k m α X hX z v u

end AVRegularity.EntryWeakProofs
end
end

section
/-! Positive mean arrays are unchanged by genuine local constituent replacements. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {hv : ι → Type*}
  [∀ i, NormedAddCommGroup (hv i)] [∀ i, InnerProductSpace ℝ (hv i)]
  {D : ℕ} {U : Set (Vec 2)}

theorem positiveMeanFluxCoefficient_slow_local_edge_congr (hU : IsOpen U)
    (Q Q' : LiftOperatorData ι hv D) (hη : Q.η = Q'.η) (hdrift : Q.v = Q'.v)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι hv) (hh n : ℕ)
    (hn : 1 ≤ n) (hhpos : hh ≠ 0) (t : ℝ)
    (hΓ : SlowOpenEdgeEq U t Q.edge Q'.edge)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m ≤ q, ∀ α X,
      X ∈ U → ∀ z v u, Cc p q m α t X z v u = Dc p q m α t X z v u)
    (k : Fin 2) (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m)
    (X : Vec 2) (hX : X ∈ U) (z : Vec 2) (v u : ι) :
    positiveMeanFluxCoefficient Q Cc hh n k m α t X z v u =
      positiveMeanFluxCoefficient Q' Dc hh n k m α t X z v u := by
  unfold positiveMeanFluxCoefficient
  rw [← hη, ← hdrift]
  apply congrArg₂ (fun a b => a - Real.sqrt Q.η • b)
  · unfold weightedLiftCoefficientMean
    apply congrArg fieldCellMean
    funext y
    rw [he hh (n - 1) (Or.inr ⟨rfl, by omega⟩) m hm α X hX y v u]
  · exact sourceFluxMeanCoefficient_slow_local_edge_congr hU Q.edge Q'.edge Q.η t
      (n - 1) (Cc (hh - 1)) (Dc (hh - 1)) hΓ
      (fun q _ m hm α X hX z v u =>
        he (hh - 1) q (Or.inl (by omega)) m hm α X hX z v u)
      k m α X hX z v u

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine scheduled stream data produce full incoming transfer jets, with a threshold before the data. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem uniform_fresh_coarse_clamped_transfer_jet_production (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (J : ℕ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      ∀ A : RealChain, M ≤ A.baseLevel → A.WellSlotted → A.children = [] →
      ∀ p : ℕ → ℤ, A.slots = [p 0] → (∀ n ≤ J, Odd (p n)) →
      (∀ n < J, IsScheduledIn D (A.baseLevel + 1 + n) (p (n + 1)) (p n)) →
      ∀ r < J, ∀ K t,
      ocCutoff D.α D.q D.Λ (A.ctxLevel + r + 1) (p (r + 1)) t ≠ 0 →
      ∀ X : Vec 2 × Vec (2 + 4 * r), ∀ n ≤ K, ∀ i j : Fin 2,
      ‖iteratedFDeriv ℝ n (fun Y : (Vec 2 × Vec (2 + 4 * r)) × Vec 2 =>
        independentFreshClampedTransferMatrix r D
          (fun P => independentFreshChain A (fun j : Fin r => p (j + 1))
            (fun j => D.eps (A.baseLevel + j)) P)
          (A.ctxLevel + r) (D.eps (A.baseLevel + r)) (p (r + 1)) t Y.1
          (D.eps (A.ctxLevel + r) • Y.2) i j) (X, 0)‖ ≤
        K.factorial * independentMovingTransferJetCost K
          (nativeMixedChartBudget (K + 2) r (1 / 2 + (0 + 2 * Real.pi))) 0 *
            independentFreshGeometryClampJetCost r K ^ K := by
  obtain ⟨M₀, hM₀, hchart⟩ := uniform_fresh_native_coarse_chart_production
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J
  obtain ⟨M₁, _, hshear⟩ := uniform_weak_transfer_shear_eventually_small
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ
  refine ⟨max M₀ M₁, hM₀.trans (le_max_left _ _), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq A hAM hl hchildren p hslots hp hs r hr K t hcut X n hn i j
  have hΛ' : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ
  have hΛ₁ : 1 ≤ D.Λ := by omega
  have hq' : IsAdmissibleQ D.α s D.q := by rw [hDα, hDq]; exact hq
  have hctx : A.ctxLevel = A.baseLevel + 1 := by
    simp only [RealChain.ctxLevel, RealChain.lastLevel, hchildren, List.length_nil, Nat.add_zero]
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hα' : D.α < 1 := by rw [hDα]; linarith only [hα₁]
  have hδ' : 0 ≤ ocDelta D.α D.q := by
    simpa only [hDα, hDq] using hδ.le
  have hτ := renewal_window_antitone hα' hδ' hq'.1 hΛ'
  have ha : D.slotAnchor (A.ctxLevel + r + 1) (p (r + 1)) ∈
      nativeWeakChartWindow D A.baseLevel J p r := by
    have hh := nativeWeakChartWindow_subset_parent D hΛ₁ A.baseLevel J p r (by omega)
      (hτ (by omega)) (hs r hr)
      (nativeWeakChartWindow_anchor D hΛ₁ A.baseLevel J p (r + 1))
    simpa only [hctx, Nat.add_assoc] using hh
  have hslot : Odd ((A.slots ++ List.ofFn (fun j : Fin r => p (j + 1))).getLastD 0) := by
    have he : A.slots ++ List.ofFn (fun j : Fin r => p (j + 1)) =
        List.ofFn (fun j : Fin (r + 1) => p j) := by
      rw [hslots, List.ofFn_succ]
      rfl
    rw [he, List.ofFn_succ']
    simpa using hp r (by omega)
  have hscale := native_weak_chart_scale_step D hq'.1 hΛ' A hchildren r
  let family := fun P => independentFreshChain A (fun j : Fin r => p (j + 1))
    (fun j => D.eps (A.baseLevel + j)) P
  let pslot := (A.slots ++ List.ofFn (fun j : Fin r => p (j + 1))).getLastD 0
  have hm : ∀ P, (family P).ctxLevel = A.ctxLevel + r :=
    fun P => independentFreshChain_ctxLevel A _ _ P
  have hsP : ∀ P, (family P).slot = pslot := fun _ => rfl
  apply independentFreshClampedTransferMatrix_normalized_jet_bound r D hΛ₁
    (by rw [hDζ]; exact hζ) family
    (fun P => independentFreshChain_wellSlotted A hl _ _ P)
    (A.ctxLevel + r) pslot hm hsP hslot ?_
    (D.eps (A.baseLevel + r))
    (D.eps (A.baseLevel + r + 1) / D.eps (A.baseLevel + r))
    hscale.1 hscale.2.1 hscale.2.2.2.2.1 (p (r + 1)) t
    (hshear D hDα hDq hDΛ (A.ctxLevel + r)
      (by have hm := (le_max_right M₀ M₁).trans hAM; rw [hctx]; omega) _ t hcut)
    (independentFreshChainChart_joint_smooth D A hl _ _ _ _)
    K n hn _ _ (zero_le_one.trans (nativeMixedChartBudget_ge_one _ _ _))
    (independentFreshGeometryClampJetCost_ge_one r K)
    (independentFreshGeometryClampJetCost_bound r K) ?_ X i j
  · intro P
    dsimp only [family]
    rw [independentFreshChain_geom_eq_indexed D A p hchildren hslots
      (fun j => D.eps (A.baseLevel + j)) P]
    exact finiteWeakChainGeom_area_preserving D hΛ₁ A.baseLevel A.base p _ r
      (fun j hj => hp j (by omega))
  · intro P hP a ha₁ haK Z hZ
    exact hchart D hDα hDq hDΛ hDζ hseq A ((le_max_left _ _).trans hAM)
      hl hchildren p hslots hp hs r (by omega) (K + 2) (1 / 2 + (0 + 2 * Real.pi))
      _ ha (P, Z) hP hZ false a ha₁ haK

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! Actual admissible stored families inherit the uniform clamped incoming transition reserve. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem uniform_actual_coarse_clamped_transfer_jets (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (J : ℕ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      ∀ A : RealChain, M ≤ A.baseLevel → A.children.length ≤ J →
      ∀ bw j₀, 0 < bw → IsAdmissibleChain D bw j₀ A.ctxLevel A.slot A →
      ∀ slot, Odd slot → IsScheduledIn D A.ctxLevel slot A.slot → ∀ K t,
      ocCutoff D.α D.q D.Λ (A.ctxLevel + 1) slot t ≠ 0 →
      ∀ X : Vec 2 × Vec (2 + 4 * A.children.length), ∀ n ≤ K, ∀ a b : Fin 2,
      ‖iteratedFDeriv ℝ n (fun Z : (Vec 2 × Vec (2 + 4 * A.children.length)) × Vec 2 =>
        independentFreshClampedTransferMatrix A.children.length D
          (actualIndependentCoarseParameterChain D A) A.ctxLevel
          (D.eps (A.baseLevel + A.children.length)) slot t Z.1 (D.eps A.ctxLevel • Z.2) a b) (X, 0)‖ ≤
        K.factorial * independentMovingTransferJetCost K
          (nativeMixedChartBudget (K + 2) A.children.length (1 / 2 + (0 + 2 * Real.pi))) 0 *
            independentFreshGeometryClampJetCost A.children.length K ^ K := by
  choose M hM htransfer using fun r => uniform_fresh_coarse_clamped_transfer_jet_production
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ (r + 1)
  let M₀ := ∑ r ∈ Finset.range (J + 1), M r
  have hle r (hr : r ≤ J) : M r ≤ M₀ :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  refine ⟨M₀, (hM 0).trans (hle 0 (Nat.zero_le J)), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq A hbase hdepth bw j₀ hbw hA slot hslot hs K t hcut X n hn a b
  have hΛ₁ : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hAw : A.WellSlotted := hA.2.2.1
  let r := A.children.length
  let B := weakZeroChildAnchor A slot
  have hBa : IsAdmissibleChain D bw j₀ (A.ctxLevel + 1) slot B :=
    weakZeroChildAnchor_admissible D hΛ₁ bw hbw j₀ A.ctxLevel A.slot slot A hA hslot hs
  have hBlen : B.children.length = r + 1 := by
    simp only [B, weakZeroChildAnchor, List.length_append, List.length_singleton, r]
  have hctx : (independentFreshBaseChain B).ctxLevel + r = A.ctxLevel := by
    change A.baseLevel + 0 + 1 + r = A.baseLevel + A.children.length + 1
    dsimp only [r]
    omega
  have hlast : realChainSlotSeq B (r + 1) = slot := weakZeroChildAnchor_slotSeq_last A hAw slot
  have hslots : (independentFreshBaseChain B).slots = [realChainSlotSeq B 0] := rfl
  have hfam : (fun P => independentFreshChain (independentFreshBaseChain B)
      (fun j : Fin r => realChainSlotSeq B (j + 1)) (fun j => D.eps (B.baseLevel + j)) P) =
      actualIndependentCoarseParameterChain D A := by
    funext P
    rw [actualIndependentCoarseParameterChain_eq_fresh D A hAw,
      independentFreshStoredFamily_eq_chain, weakZeroChildAnchor_baseChain A hAw slot]
    congr 1
    funext j
    exact weakZeroChildAnchor_slotSeq_prefix A hAw slot (j + 1) (by dsimp only [r] at j; omega)
  have hh := htransfer r D hDα hDq hDΛ hDζ hseq (independentFreshBaseChain B)
    ((hle r hdepth).trans hbase) (independentFreshBaseChain_wellSlotted B) rfl
    (realChainSlotSeq B) hslots
    (fun k hk => realChainSlotSeq_odd D B hBa k (by omega))
    (fun k hk => realChainSlotSeq_scheduled D B hBa k (by omega)) r (Nat.lt_succ_self r) K t
    (by simpa only [hctx, hlast] using hcut) X n hn a b
  have hbaseB : (independentFreshBaseChain B).baseLevel = B.baseLevel := rfl
  rw [hctx, hlast, hbaseB, hfam] at hh
  exact hh

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine primitive reserves and the carrier-local paper clauses used by finite coefficient production. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

def liftProductionRankMax (N R : ℕ) : ℕ := ambientRecurrenceRank N R N

def liftProductionOrder (base D N R hh n : ℕ) : ℕ :=
  weakJointRecurrenceReserve (4 * (D + 4)) base (liftProductionRankMax N R) (ambientRecurrenceRank N hh n)

def liftProductionTopOrder (base D N R : ℕ) : ℕ := 4 * liftProductionOrder base D N R 0 0 + 2 * D + 7

structure LocalLiftProductionData (ι : Type*) [Fintype ι] [DecidableEq ι]
    (base D N R L : ℕ) (BG BV BE : ℝ) where
  a : ℝ
  b : ℝ
  window : a < b
  sZ : ℕ
  U : Set (Vec 2)
  open_carrier : IsOpen U
  Q : LiftOperatorData ι (fun _ => ℝ) D
  contrast : Q.η = 1
  Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)
  M : ι → ι → ℝ
  matrix_nonneg : ∀ v u, 0 ≤ M v u
  initial : ∀ a₀ : Vec 2 → ι → ℝ, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Icc a b, ∀ X z,
    liftApply 0 (Cc 0 0) (fun _ => a₀) t X z = a₀ X
  positive_zero_degree : ∀ hh, 1 ≤ hh → hh ≤ R → ∀ m α t X z v u, Cc hh 0 m α t X z v u = 0
  above_degree : ∀ hh, hh ≤ R → ∀ n, N < n → ∀ m α t X z v u, Cc hh n m α t X z v u = 0
  support : ∀ hh, hh ≤ R → ∀ n m, n < m → ∀ α t X z v u, Cc hh n m α t X z v u = 0
  symmetric : ∀ hh, hh ≤ R → ∀ n m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)),
    Cc hh n m (α ∘ σ) = Cc hh n m α
  inverse : ∀ hh, hh ≤ R → ∀ n, 1 ≤ n → n ≤ N →
    ∀ a₀ : Vec 2 → ι → ℝ, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ Y ∈ U,
      IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v sZ a b 0
        (fun t z => liftCellSource Q Cc (fun _ => a₀) hh n t Y z)
        (fun t z => liftApply n (Cc hh n) (fun _ => a₀) t Y z)
  metric_entries : ∀ i j, JointSourceReserve (liftProductionTopOrder base D N R) (fun t _ Y => Q.G t Y i j)
  drift_entries : ∀ i, JointSourceReserve (liftProductionTopOrder base D N R) (fun t z _ => Q.v t z i)
  edges : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
    JointSourceReserve (liftProductionTopOrder base D N R) (fun t z Y => γ.coeff α t Y z)
  metric_bound : ∀ i j k, k ≤ liftProductionTopOrder base D N R → (metric_entries i j).budget k ≤ BG
  drift_bound : ∀ i k, k ≤ liftProductionTopOrder base D N R → (drift_entries i).budget k ≤ BV
  edge_bound : ∀ v u d γ hγ α k, k ≤ liftProductionTopOrder base D N R →
    (edges v u d γ hγ α).budget k ≤ M v u * BE
  edge_maps : ∀ v u d γ, γ ∈ Q.edge v u d → ‖γ.map‖ ≤ 1
  edge_lengths : ∀ v u d, (Q.edge v u d).length ≤ L
  metric : ParameterMetricReserve (liftProductionTopOrder base D N R) (fun t Y => Matrix.of (Q.G t Y))
  metric_reserve_bound : ∀ k ≤ liftProductionTopOrder base D N R, metric.budget k ≤ BG
  molecular : Vec 2 → MolecularData
  molecular_coefficients : ∀ Y, dataCoefficients (molecular Y) =
    ⟨matrixParameterJet (fun t Y => Matrix.of (Q.G t Y)) 0 Y, (molecular Y).v, 0, 0⟩
  molecular_metric : ∀ Y, (molecular Y).G = fun t => Matrix.of (Q.G t Y)
  molecular_drift : ∀ Y, (molecular Y).v = Q.v
  molecular_budget : ∀ Y k, k ≤ 3 * liftProductionOrder base D N R 0 0 + 5 →
    MolecularFiniteDriftBudget (molecular Y) k

structure LocalScalarCoefficientProduction {ι : Type*}
    (H n : ℕ) (a b : ℝ) (U : Set (Vec 2)) (c : LiftCoeff ι (fun _ => ℝ))
    (m : ℕ) (α : DerivativeWord2 m) (v u : ι) (θ C : ℝ) where
  field : ℝ → Vec 2 → Vec 2 → ℝ
  reserve : JointSourceReserve H field
  bound : ∀ k ≤ H, reserve.budget k ≤ θ * C
  copy : ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z, field t z Y = c m α t Y z v u 1
  mean_zero : 1 ≤ n → ∀ t Y, fieldCellMean (fun z => field t z Y) = 0
  past_zero : 1 ≤ n → ∀ t, t ≤ a → ∀ z Y, field t z Y = 0

end AVRegularity.EntryWeakProofs
end
end

section
/-! Earlier proved coefficient productions retain their actual germ and centering under reserve
restriction. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} {H n m : ℕ} {a b θ C : ℝ} {U : Set (Vec 2)}
  {c : LiftCoeff ι (fun _ => ℝ)} {α : DerivativeWord2 m} {v u : ι}

def LocalScalarCoefficientProduction.monoOrder
    (P : LocalScalarCoefficientProduction H n a b U c m α v u θ C)
    (H' : ℕ) (hH : H' ≤ H) : LocalScalarCoefficientProduction H' n a b U c m α v u θ C where
  field := P.field
  reserve := P.reserve.mono H' hH
  bound k hk := P.bound k (hk.trans hH)
  copy := P.copy
  mean_zero := P.mean_zero
  past_zero := P.past_zero

def LocalScalarCoefficientProduction.enlargeBudget
    (P : LocalScalarCoefficientProduction H n a b U c m α v u θ C)
    (C' : ℝ) (hC : C ≤ C') (hθ : 0 ≤ θ) : LocalScalarCoefficientProduction H n a b U c m α v u θ C' where
  field := P.field
  reserve := P.reserve
  bound k hk := (P.bound k hk).trans (mul_le_mul_of_nonneg_left hC hθ)
  copy := P.copy
  mean_zero := P.mean_zero
  past_zero := P.past_zero

end AVRegularity.EntryWeakProofs
end
end

section
/-! Fixed primitive orders and geometric predecessor orders pay every actual inverse step. -/
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs
open AVRegularity.CycleComparison.Lift

theorem liftProductionRank_le (N R hh n : ℕ) (hhh : hh ≤ R) (hn : n ≤ N) :
    ambientRecurrenceRank N hh n ≤ liftProductionRankMax N R := by
  exact Nat.add_le_add (Nat.mul_le_mul_right (N + 1) hhh) hn

theorem liftProductionOrder_le_initial (base D N R hh n : ℕ) :
    liftProductionOrder base D N R hh n ≤ liftProductionOrder base D N R 0 0 := by
  have h := weakJointRecurrenceReserve_metric_room base D (liftProductionRankMax N R)
    (ambientRecurrenceRank N hh n)
  simpa only [liftProductionOrder, ambientRecurrenceRank, Nat.zero_mul, Nat.zero_add]
    using Nat.le_of_add_le_add_right h

theorem liftProductionOrder_predecessor_room (base D N R hh n p q : ℕ)
    (hhh : hh ≤ R) (hn : n ≤ N) (hq : q ≤ N)
    (hpq : p < hh ∨ (p = hh ∧ q < n)) :
    4 * liftProductionOrder base D N R hh n + 2 * D + 7 ≤
      liftProductionOrder base D N R p q := by
  have hr := liftProductionRank_le N R hh n hhh hn
  have hprior : ambientRecurrenceRank N p q < ambientRecurrenceRank N hh n := by
    rcases hpq with hp | ⟨rfl, hq⟩
    · exact ambientRecurrenceRank_height N hh n p q hp hq
    · exact ambientRecurrenceRank_composition N p n p q le_rfl hn hq
  exact weakJointRecurrenceReserve_composition_source_room base D (liftProductionRankMax N R)
    (ambientRecurrenceRank N hh n) (ambientRecurrenceRank N p q) hr hprior

def ParameterMetricReserve.mono {H : ℕ}
    {G : ℝ → Homogenization.Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : ParameterMetricReserve H G) (H' : ℕ) (hH : H' ≤ H) : ParameterMetricReserve H' G where
  regular := Q.regular
  measurable := Q.measurable
  metric := Q.metric
  budget := Q.budget
  budget_nonneg := Q.budget_nonneg
  derivative_bound n hn := Q.derivative_bound n (hn.trans hH)

end AVRegularity.EntryWeakProofs
end
end

section
/-! The finite initial reserve order for independent lift production. -/
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

def independentLiftPrimitiveTopOrder (base D N R : ℕ) : ℕ :=
  4 * liftProductionOrder base D N R 0 0 + 5

end AVRegularity.EntryWeakProofs
end
end

section
/-! The literal physical piece equals its finite produced source array and is spatially regular. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {Dm : ℕ} {bw B : ℝ} {j₀ minBase cap H : ℕ}
  {G G' : GenStage D (fun _ => ℝ) Dm bw j₀}

theorem weakStagePhysicalPiece_eq_array (G : GenStage D (fun _ => ℝ) Dm bw j₀)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (hd : 2 ≤ d) (t : ℝ) (p : OddSlot) :
    weakPhysicalPieceCoefficient G.fam (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
      G.actual v u γ d t p =
    fun x => CycleJointProofs.nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map
      (fun a A => transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material t).symm)
        (G.fam.identity v u γ).maxOrder
        (fun e I => weakStagePhysicalSourceArray G v u γ t p e I x) (d - 1) A x a) := by
  funext x
  unfold weakPhysicalPieceCoefficient
  congr 1
  funext a A
  exact congrFun (weakStagePhysicalSourceArray_transport_eq G v u γ t p d hd A x).symm a

theorem IndependentWeakStageFluxProduction.physical_piece_contDiff
    (S : IndependentWeakStageFluxProduction G' minBase cap H B)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hbw : bw ≤ 1 / 10000) (hB : 0 ≤ B)
    (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P)
    (Mtop : ℕ) (hG : G'.IsNatural Mtop) (hbase : minBase ≤ G'.level - 1)
    (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) (d : ℕ) (hd : 2 ≤ d)
    (Ks : ℕ) (hKs : Ks ≤ H) (t : ℝ) (p : OddSlot) :
    ContDiff ℝ (Ks : ℕ)
      (weakPhysicalPieceCoefficient G'.fam (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1))
        G'.actual v u γ d t p) := by
  rw [weakStagePhysicalPiece_eq_array G' v u γ d hd t p]
  apply CycleJointProofs.nativeArrayAssembly_spatial_smooth
  intro a A
  apply CycleJointProofs.transportedCoeff_spatial_smooth
    (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
    (CycleJointProofs.chartInvJacobian_homeomorph_smooth ((G'.fam.piece p).material t)
      ((G'.fam.piece p).material_smooth t) ((G'.fam.piece p).material_symm_smooth t))
  intro e I i
  exact contDiff_pi.mp ((S.physical_source_array_contDiff hq hΛ hζ hband hbw hB P Mn rW Din hp ht
    Mtop hG hbase v u γ t p e I).of_le (by exact_mod_cast hKs)) i

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual coherent inherited families supply scheduled Piola data at every parent chart. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory Set AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B : ℝ} {j₀ minBase cap H N n level fine : ℕ}
  {native : ∀ p : OddSlot, StageCtx D bw j₀ fine p → ∀ d,
    DerivativeWord2 (d - 1) → ℝ → Vec 2}

theorem IndependentWeakMeanArrayProduction.sampled_piola
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (he : level + 1 = fine) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hbw : 0 < bw)
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (slot : OddSlot) (hs : IsScheduledIn D level slot.1 c.slot.1)
    (ρ ell : ℝ) (hell : |ell| ≤ 1) (hscale : D.eps c.chain.1.ctxLevel = ρ * ell)
    (I : Set ℝ) (hI : MeasurableSet I)
    (hsmall : ∀ t ∈ I, |D.slotAnchor (c.chain.1.ctxLevel + 1) slot.1 - t| *
      ocA D.α D.q D.Λ c.chain.1.ctxLevel ≤ 1)
    (C : ℝ) (hKC : ∀ t ∈ I, ∀ X : Vec 2 × Vec (2 + 4 * c.chain.1.children.length),
      ∀ a b j, j ≤ N → ‖iteratedFDeriv ℝ j
        (fun Z : (Vec 2 × Vec (2 + 4 * c.chain.1.children.length)) × Vec 2 =>
          independentFreshClampedTransferMatrix c.chain.1.children.length D
            (actualIndependentCoarseParameterChain D c.chain.1) c.chain.1.ctxLevel ρ slot.1 t Z.1
            (D.eps c.chain.1.ctxLevel • Z.2) a b) (X, 0)‖ ≤ C)
    (hκ : 0 ≤ D.κ D.term) :
    let cf := (c.zeroChild hΛ hbw slot hs).relevel he
    ∃ T : IndependentPiolaWindowDatum (Vec (2 + 4 * c.chain.1.children.length)) H N n n
      (D.eps level) C θ
      (D.κ D.term) (D.eps fine)
      (H.factorial * B * (1 + (2 * Real.pi) ^ (H + 1)) ^ H),
      T.window = I ∧
      T.matrix = (fun t z Y w => independentFreshClampedTransferMatrix c.chain.1.children.length D
        (actualIndependentCoarseParameterChain D c.chain.1) level ρ slot.1 t (z, Y) w) ∧
      T.array = (fun d word t z Y a => independentTimeWindowSource I
        (independentFreshCoarseAppendedSource c.chain.1.children.length D level c.slot.1 slot.1 ell
          (fun t z (W : Vec (2 + 4 * (c.chain.1.children.length + 1))) => M.field cf d word t z
            (Eq.rec (motive := fun r _ => Vec (2 + 4 * r)) W
              (show c.chain.1.children.length + 1 = cf.chain.1.children.length by
              simp only [cf, WeakStageProductionContext.relevel, WeakStageProductionContext.zeroChild,
                weakZeroChildAnchor, List.length_append, List.length_singleton])) a)) t z Y) := by
  let cf := (c.zeroChild hΛ hbw slot hs).relevel he
  have hlen : cf.chain.1.children.length = c.chain.1.children.length + 1 := by
    simp only [cf, WeakStageProductionContext.relevel, WeakStageProductionContext.zeroChild,
      weakZeroChildAnchor, List.length_append, List.length_singleton]
  have hctx : c.chain.1.ctxLevel = level := c.chain.2.1
  have hlevel : c.chain.1.ctxLevel + 1 = fine := (congrArg (fun j => j + 1) hctx).trans he
  have hQ d word a k (hk : k ≤ H) :
      ((M.reserve cf d word).coordinate a).budget k ≤
        θ * (D.κ D.term * D.eps (c.chain.1.ctxLevel + 1) ^ (n - 2) *
          D.eps c.chain.1.ctxLevel ^ ((d : ℝ) - (n : ℝ)) * B) := by
    calc
      _ ≤ θ * (D.κ D.term * D.eps fine ^ (n - 2) *
          D.eps (fine - 1) ^ ((d : ℝ) - (n : ℝ)) * B) := M.budget cf d word k hk
      _ = _ := by rw [← hlevel, Nat.add_sub_cancel]
  have hprod := actualIndependentCoarseSampledPiolaDatum_cast H N n n D hΛ hζ c.chain.1 c.chain.2
    ρ ell hell hscale slot.1 I hI hsmall C hKC (fun t => t) measurable_id
    cf.chain.1.children.length hlen (M.field cf)
    (fun d word a => (M.reserve cf d word).coordinate a) θ (D.κ D.term)
    (D.eps (c.chain.1.ctxLevel + 1)) B hθ hκ (Construction.Stream.ocEpsilon_pos hΛ).le hB hQ
    (fun d word δ hδ => M.phase cf d word δ hδ)
  have hslot : c.chain.1.slot = c.slot.1 := c.chain.2.2.2.2.1
  rw [hctx, hslot, he] at hprod
  exact hprod

end AVRegularity.EntryWeakProofs
end
end

section
/-! Named native and extended slice operators retain their literal family and coefficient arrays. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

def actualIndependentCoarseSliceLiftData (D : OCData) (A : RealChain) (ρ : ℝ) (slot : ℤ)
    (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (Y : Vec (2 + 4 * A.children.length)) :
    LiftOperatorData ι (fun _ => ℝ) Dm :=
  familyLiftData D A.ctxLevel slot
    (actualIndependentCoarseParameterChain D A (independentStoredParameterProjection (4 * A.children.length) Y)) ρ edge

def actualIndependentCoarseExtendedSliceLiftData (D : OCData) (A : RealChain) (ρ : ℝ) (slot : ℤ)
    (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (χ : Vec (2 + 4 * A.children.length) → ℝ) (a b : ℝ) (Y : Vec (2 + 4 * A.children.length)) :
    LiftOperatorData ι (fun _ => ℝ) Dm :=
  { actualIndependentCoarseSliceLiftData D A ρ slot edge Y with
    G := fun t X => actualIndependentCoarseScaledExtendedMetric D A ρ χ a b t
      (independentIntrinsicSlowEmbedding (4 * A.children.length) X +
        independentIntrinsicSliceOffset (4 * A.children.length) Y) }

def actualIndependentCoarseCarrierCoefficients (D : OCData) (A : RealChain) (bw : ℝ)
    (c : Vec (4 * A.children.length) → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (Y : Vec (2 + 4 * A.children.length)) : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ) :=
  independentCarrierCoefficientExtension (actualIndependentCoarseStoredCarrier D A bw) c
    (independentStoredParameterProjection (4 * A.children.length) Y)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Every inherited weak slice retains unit contrast and the actual normalized path edges. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem actualIndependentCoarseExtendedWeakSliceData_eq
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (A : RealChain) (hweak : D.term < A.ctxLevel) (ρ : ℝ) (slot : ℤ)
    (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (χ : Vec (2 + 4 * A.children.length) → ℝ) (a b : ℝ)
    (Y : Vec (2 + 4 * A.children.length)) :
    actualIndependentCoarseExtendedSliceLiftData D A ρ slot edge χ a b Y =
      ⟨1, (fun t X => actualIndependentCoarseScaledExtendedMetric D A ρ χ a b t
        (independentIntrinsicSlowEmbedding (4 * A.children.length) X +
          independentIntrinsicSliceOffset (4 * A.children.length) Y)),
        ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) slot,
        (actualIndependentCoarseSliceLiftData D A ρ slot edge Y).edge⟩ := by
  have hη : D.kap A.ctxLevel / D.kap (A.ctxLevel - 1) = 1 :=
    weakData_family_contrast (ι := ι) (h := fun _ => ℝ) (Dm := Dm)
      D hΛ hζ hband A.ctxLevel hweak slot A ρ edge
  simp only [actualIndependentCoarseExtendedSliceLiftData, actualIndependentCoarseSliceLiftData,
    familyLiftData, hη]

end AVRegularity.EntryWeakProofs
end
end

section
/-! The produced open metric carrier and literal coefficient extension transfer original family inverses without global boundary smoothness. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem actualIndependentCoarseCarrierInverse_transfer (D : OCData) (A : RealChain) (hA : A.WellSlotted)
    (bw ρ a b : ℝ) (slot : ℤ) (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (χ : Vec (2 + 4 * A.children.length) → ℝ)
    (hχ : ∀ Y, ‖independentFreshCarrierCoordinates A.children.length Y‖ < 1 / 4 → χ =ᶠ[𝓝 Y] fun _ => 1)
    (c : Vec (4 * A.children.length) → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (sX sZ N R hh n : ℕ) (hhh : hh ≤ R) (hn : 1 ≤ n) (hnN : n ≤ N)
    (Y : Vec (2 + 4 * A.children.length)) (hY : Y ∈ actualIndependentCoarseNativeCarrier D A bw)
    (hc : IsLiftSequence (actualIndependentCoarseSliceLiftData D A ρ slot edge Y)
      sX sZ a b N R (c (independentStoredParameterProjection (4 * A.children.length) Y)))
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IsCellFieldInverse
      (fun t => Matrix.of ((actualIndependentCoarseExtendedSliceLiftData D A ρ slot edge χ a b Y).G t
        (independentIntrinsicSlowProjection (4 * A.children.length) Y)))
      (actualIndependentCoarseSliceLiftData D A ρ slot edge Y).v sZ a b 0
      (fun t z => liftCellSource (actualIndependentCoarseExtendedSliceLiftData D A ρ slot edge χ a b Y)
        (actualIndependentCoarseCarrierCoefficients D A bw c Y) (fun _ => f) hh n t
        (independentIntrinsicSlowProjection (4 * A.children.length) Y) z)
      (fun t z => liftApply n (actualIndependentCoarseCarrierCoefficients D A bw c Y hh n) (fun _ => f) t
        (independentIntrinsicSlowProjection (4 * A.children.length) Y) z) := by
  let Q := actualIndependentCoarseSliceLiftData D A ρ slot edge Y
  let U := independentIntrinsicSliceCarrier (4 * A.children.length) (actualIndependentCoarseNativeCarrier D A bw) Y
  have hU : IsOpen U := independentIntrinsicSliceCarrier_isOpen _ _
    (actualIndependentCoarseNativeCarrier_isOpen D A bw) Y
  have hbase : independentIntrinsicSlowProjection (4 * A.children.length) Y ∈ U :=
    independentIntrinsicSliceCarrier_base _ _ Y hY
  have hi := independentCarrierCoefficientExtension_inverse (actualIndependentCoarseStoredCarrier D A bw) c
    (independentStoredParameterProjection (4 * A.children.length) Y) hY.1 Q hc hh n hhh hn hnN f hf
    (independentIntrinsicSlowProjection (4 * A.children.length) Y)
  let G := (actualIndependentCoarseExtendedSliceLiftData D A ρ slot edge χ a b Y).G
  have hG : ∀ t ∈ Icc a b, ∀ X ∈ U, Q.G t X = G t X := by
    intro t ht X hX
    have he := actualIndependentCoarseScaledExtendedMetric_carrier_copy D A bw ρ a b t χ hχ ht
      (independentIntrinsicSlowEmbedding (4 * A.children.length) X +
        independentIntrinsicSliceOffset (4 * A.children.length) Y) hX
    exact (actualIndependentCoarseScaledMetric_slice D A hA ρ slot edge Y t X).symm.trans he.symm
  exact local_lift_inverse_metric_carrier_replacement hU Q G a b hG sZ hh n
    (actualIndependentCoarseCarrierCoefficients D A bw c Y) (fun _ => f)
    (independentIntrinsicSlowProjection (4 * A.children.length) Y) hbase hi

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual weak eddy slice has unit contrast and literally empty source edges. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem actualIndependentCoarseExtendedEmptySliceData_eq (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (A : RealChain) (hweak : D.term < A.ctxLevel) (ρ : ℝ) (slot : ℤ)
    (χ : Vec (2 + 4 * A.children.length) → ℝ) (a b : ℝ) (Y : Vec (2 + 4 * A.children.length)) :
    actualIndependentCoarseExtendedSliceLiftData (ι := ι) (Dm := Dm) D A ρ slot (fun _ _ _ => []) χ a b Y =
      ⟨1, (fun t X => actualIndependentCoarseScaledExtendedMetric D A ρ χ a b t
        (independentIntrinsicSlowEmbedding (4 * A.children.length) X +
          independentIntrinsicSliceOffset (4 * A.children.length) Y)),
        ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) slot, fun _ _ _ => []⟩ := by
  have hη : D.kap A.ctxLevel / D.kap (A.ctxLevel - 1) = 1 :=
    weakData_family_contrast (ι := ι) (h := fun _ => ℝ) (Dm := Dm) D hΛ hζ hband
      A.ctxLevel hweak slot A ρ (fun _ _ _ => [])
  simp only [actualIndependentCoarseExtendedSliceLiftData, actualIndependentCoarseSliceLiftData, familyLiftData,
    hη, liftEdges_empty]

end AVRegularity.EntryWeakProofs
end
end
end
