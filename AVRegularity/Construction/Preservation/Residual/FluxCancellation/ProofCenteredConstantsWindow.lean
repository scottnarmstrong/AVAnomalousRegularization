-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofHilbertLiftArraysSetting
import AVRegularity.CycleComparison.Lift.NormalizedSourceArrayZeroMatrixBound
import AVRegularity.EntryWeakAssembly.StoredSourceCounting
import AVRegularity.Proofs.GenSem.LiftOn.Omega
public import AVRegularity.Proofs.GenSem.ChainMetric
import AVRegularity.Proofs.GenSem.Op.FamChart
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCenteredConstantsLift
import AVRegularity.Proofs.Results.Construction.SuccessorFluxUnique
import AVRegularity.Construction.Uniqueness.SuccessorFluxWindow
import AVRegularity.Proofs.GenSem.Jet.Chart
import AVRegularity.Proofs.Results.Construction.SuccWindowData.Jacobian

section
@[expose] public section
noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLDecomp

/-! The path-sum step at positive grades: the slow flux `liftFluxX` of a path-candidate array on a finite
sum of single-component test fields.

`liftFluxX_cand` computes the slow flux of a path-candidate
array on one field `g₀ e`. A general coarse field is a finite sum of such fields (coordinates in
bases of the fibres), and the slow flux is additive on them:

* `hl_liftApply_field_sum`, `hl_sourceFlux_sum`, `hl_liftFluxX_field_sum`: additivity of
  `liftApply`, `sourceFlux` and `liftFluxX` in the test field, under the regularity that the
  derivatives in them need.
* `hl_liftFluxX_cand_sum`: the slow flux of `cand F T` on `∑ s, g₀ s · e s` is the sum over `s`
  and over the walks from the component of `s` of the scalar `formX` of the profile `g₀ s`.
* `hl_chain_liftFluxX_last_sum`: the same for a chain family, read at the last vertex.
* `hl_dual_sum_walkVec`, `hl_continuous_cand_sum`: reading a component through a functional, and
  continuity in the fast variable. -/

open AVRegularity.Providers.PathDecomp

/-- The context of the explicit formulas of the operator data `Q`, the arrays `T`, the time `t`
and the test profile `g₀`. -/
def hlCtx {ι : Type} {hs : ι → Type} [∀ i, NormedAddCommGroup (hs i)] [∀ i, NormedSpace ℝ (hs i)]
    {Dm : ℕ} (Q : LiftOperatorData ι hs Dm) (T : (g : ℕ) → (Fin g → StepDat) → SArr) (t : ℝ)
    (g₀ : Vec 2 → ℝ) : Ctx :=
  ⟨Q.η, Q.G, Q.v, Dm, g₀, T, t⟩

/-- A list sum of finite sums. -/
theorem hl_list_sum_map_finset_sum {σ β M : Type*} [AddCommMonoid M] (l : List β) (S : Finset σ)
    (f : β → σ → M) :
    (l.map fun x => ∑ s ∈ S, f x s).sum = ∑ s ∈ S, (l.map fun x => f x s).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, Finset.sum_add_distrib]

theorem hl_smul_sum_comm {σ τ M : Type*} [AddCommMonoid M] [Module ℝ M] (J : Finset τ)
    (S : Finset σ) (c : ℝ) (g : τ → ℝ) (B : σ → τ → M) :
    c • ∑ j ∈ J, g j • ∑ s ∈ S, B s j = ∑ s ∈ S, c • ∑ j ∈ J, g j • B s j := by
  simp only [Finset.smul_sum]
  exact Finset.sum_comm

theorem hl_sum_smul_sum_comm {σ τ M : Type*} [AddCommMonoid M] [Module ℝ M] (J : Finset τ)
    (S : Finset σ) (g : τ → ℝ) (B : σ → τ → M) :
    ∑ j ∈ J, g j • ∑ s ∈ S, B s j = ∑ s ∈ S, ∑ j ∈ J, g j • B s j := by
  simp only [Finset.smul_sum]
  exact Finset.sum_comm

variable {ι : Type} [Fintype ι] {hs : ι → Type} [∀ i, NormedAddCommGroup (hs i)]
  [∀ i, NormedSpace ℝ (hs i)] {σ : Type}

/-- `liftApply` is additive in smooth test fields. -/
theorem hl_liftApply_field_sum (S : Finset σ) (k : ℕ) (c : LiftCoeff ι hs)
    (a : σ → Vec 2 → ∀ i, hs i) (ha : ∀ s ∈ S, ContDiff ℝ (⊤ : ℕ∞) (a s)) (t : ℝ) (X z : Vec 2) :
    liftApply k c (fun _ Y => ∑ s ∈ S, a s Y) t X z =
      ∑ s ∈ S, liftApply k c (fun _ => a s) t X z := by
  funext v
  have hd : ∀ (m : ℕ) (α : DerivativeWord2 m),
      orderedDerivative α (fun Y => ∑ s ∈ S, a s Y) =
        fun Y => ∑ s ∈ S, orderedDerivative α (a s) Y := by
    intro m α
    have h := orderedDerivative_clm_sum S (fun _ => ContinuousLinearMap.id ℝ (∀ i, hs i)) α
      (β := a) (fun s hs' => (ha s hs').of_le (by exact_mod_cast le_top))
    simp only [ContinuousLinearMap.id_apply] at h
    exact h
  simp only [liftApply, hd, Finset.sum_apply, map_sum]
  exact (Finset.sum_congr rfl fun m _ =>
    (Finset.sum_congr rfl fun α _ => Finset.sum_comm).trans Finset.sum_comm).trans Finset.sum_comm

/-- The source flux is additive in fields of class `C^{Dm}`. -/
theorem hl_sourceFlux_sum {Dm : ℕ} (edge : ConstituentEdges Dm hs) (η ε t : ℝ) (S : Finset σ)
    {Φ : σ → Vec 2 → Vec 2 → ∀ i, hs i} (hΦ : ∀ s ∈ S, GoodField Dm (Φ s)) (κ : Fin 2)
    (X z : Vec 2) :
    sourceFlux edge η ε t (fun X z => ∑ s ∈ S, Φ s X z) κ X z =
      ∑ s ∈ S, sourceFlux edge η ε t (Φ s) κ X z := by
  funext v
  have hd : ∀ (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1)),
      dEpsWord η ε α (fun X z => ∑ s ∈ S, Φ s X z) =
        fun X z => ∑ s ∈ S, dEpsWord η ε α (Φ s) X z := by
    intro d α
    have h := dEpsWord_clm_sum S (fun _ => ContinuousLinearMap.id ℝ (∀ i, hs i)) α (Φ := Φ)
      (fun s hs' => (hΦ s hs').mono (by have := (Finset.mem_Icc.mp d.2).2; omega)) η ε
    simp only [ContinuousLinearMap.id_apply] at h
    exact h
  simp only [sourceFlux, hd, Finset.sum_apply, map_sum, Finset.smul_sum]
  refine (Finset.sum_congr rfl fun u _ =>
    (Finset.sum_congr rfl fun d _ => ?_).trans Finset.sum_comm).trans Finset.sum_comm
  rw [← hl_list_sum_map_finset_sum]
  congr 1
  exact List.map_congr_left fun γ _ => Finset.sum_comm

/-- **The slow flux is additive in the test field**, when the values `liftApply` of the summands
are good fields and their source fluxes are differentiable in `ε`. -/
theorem hl_liftFluxX_field_sum {Dm : ℕ} (Q : LiftOperatorData ι hs Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι hs) (S : Finset σ) (a : σ → Vec 2 → ∀ i, hs i) (hh n : ℕ) (t : ℝ)
    (X z : Vec 2) (κ : Fin 2)
    (h1 : ∀ k hh', liftApply k (Cc hh' k) (fun _ Y => ∑ s ∈ S, a s Y) t =
      fun X z => ∑ s ∈ S, liftApply k (Cc hh' k) (fun _ => a s) t X z)
    (h2 : ∀ s ∈ S, ∀ k hh', GoodField (Dm + 1) (liftApply k (Cc hh' k) (fun _ => a s) t))
    (h3 : ∀ s ∈ S, ∀ j, ContDiff ℝ ((j - 1 : ℕ) : ℕ∞) (fun ε : ℝ =>
      sourceFlux Q.edge Q.η ε t (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a s) t)
        κ X z)) :
    liftFluxX Q Cc (fun _ Y => ∑ s ∈ S, a s Y) hh n t X z κ =
      ∑ s ∈ S, liftFluxX Q Cc (fun _ => a s) hh n t X z κ := by
  have hF : ∀ k hh' j,
      fastPartial j (fun X z => ∑ s ∈ S, liftApply k (Cc hh' k) (fun _ => a s) t X z) X z =
        ∑ s ∈ S, fastPartial j (liftApply k (Cc hh' k) (fun _ => a s) t) X z := by
    intro k hh' j
    have h := fastPartial_clm_sum S (fun _ => ContinuousLinearMap.id ℝ (∀ i, hs i))
      (Φ := fun s => liftApply k (Cc hh' k) (fun _ => a s) t)
      (fun s hs' => (h2 s hs' k hh').mono (by omega)) j X z
    simp only [ContinuousLinearMap.id_apply] at h
    exact h
  have hS : ∀ k hh' j,
      slowPartial j (fun X z => ∑ s ∈ S, liftApply k (Cc hh' k) (fun _ => a s) t X z) X z =
        ∑ s ∈ S, slowPartial j (liftApply k (Cc hh' k) (fun _ => a s) t) X z := by
    intro k hh' j
    have h := slowPartial_clm_sum S (fun _ => ContinuousLinearMap.id ℝ (∀ i, hs i))
      (Φ := fun s => liftApply k (Cc hh' k) (fun _ => a s) t)
      (fun s hs' => (h2 s hs' k hh').mono (by omega)) j X z
    simp only [ContinuousLinearMap.id_apply] at h
    exact h
  have hE : ∀ j, iteratedDeriv (j - 1) (fun ε : ℝ => sourceFlux Q.edge Q.η ε t
      (fun X z => ∑ s ∈ S, liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a s) t X z) κ X z)
      0 = ∑ s ∈ S, iteratedDeriv (j - 1) (fun ε : ℝ => sourceFlux Q.edge Q.η ε t
        (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a s) t) κ X z) 0 := by
    intro j
    have e1 : (fun ε : ℝ => sourceFlux Q.edge Q.η ε t
        (fun X z => ∑ s ∈ S, liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a s) t X z)
        κ X z) = fun ε => ∑ s ∈ S, sourceFlux Q.edge Q.η ε t
          (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a s) t) κ X z :=
      funext fun ε => hl_sourceFlux_sum Q.edge Q.η ε t S
        (fun s hs' => (h2 s hs' _ _).mono (by omega)) κ X z
    rw [e1]
    have h := iteratedDeriv_clm_sum S (fun _ => ContinuousLinearMap.id ℝ (∀ i, hs i))
      (F := fun s ε => sourceFlux Q.edge Q.η ε t
        (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a s) t) κ X z)
      (fun s hs' => h3 s hs' j) 0
    simp only [ContinuousLinearMap.id_apply] at h
    exact h
  unfold liftFluxX
  simp only [h1, hF, hS, hE]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  congr 1
  · congr 1
    · congr 1
      · exact Finset.smul_sum
      · exact hl_smul_sum_comm _ _ _ _ _
    · split_ifs with h2n
      · rw [Finset.sum_neg_distrib]
        congr 1
        exact hl_smul_sum_comm _ _ _ _ _
      · exact Finset.sum_const_zero.symm
  · split_ifs with hh0
    · exact Finset.sum_const_zero.symm
    · exact hl_sum_smul_sum_comm _ _ _ _

variable [DecidableEq ι]

/-- **The slow flux of a path-candidate array on a finite sum of single-component fields.** -/
theorem hl_liftFluxX_cand_sum {Dm : ℕ} (F : FamData ι hs) (Q : LiftOperatorData ι hs Dm)
    (hQ : HasFamFlux Q F) (T : (g : ℕ) → (Fin g → StepDat) → SArr) (t : ℝ) {r : ℕ}
    (hT : ∀ g (cd : Fin g → StepDat) k m (α : DerivativeWord2 m),
      GoodField (r + 1 + Dm) (fun X z => T g cd k m α t X z))
    (hdat : ∀ v u (γ : F.Γ v u), GoodDat (r + 1 + Dm) t (F.dat v u γ))
    (S : Finset σ) (w : σ → ι) (g₀ : σ → Vec 2 → ℝ) (hg₀ : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (g₀ s))
    (e : ∀ s, hs (w s)) (g n : ℕ) (X z : Vec 2) (κ : Fin 2) :
    liftFluxX Q (cand F T)
        (fun _ Y => ∑ s ∈ S, (Pi.single (w s) (g₀ s Y • e s) : ∀ i, hs i)) g n t X z κ =
      ∑ s ∈ S, ∑ p : WalkFrom F g (w s),
        (hlCtx Q T t (g₀ s)).formX n g (F.walkDat p.2) κ X z • walkVec F (e s) p := by
  have hval : ∀ s k g',
      liftApply k (cand F T g' k) (fun _ Y => Pi.single (w s) (g₀ s Y • e s)) t =
        valField F (hlCtx Q T t (g₀ s)) (e s) k g' := fun s k g' =>
    funext fun X => funext fun z => liftApply_cand F (hlCtx Q T t (g₀ s)) (hg₀ s) (e s) k g' X z
  have hgood : ∀ s k g',
      GoodField (r + 1 + Dm) (valField F (hlCtx Q T t (g₀ s)) (e s) k g') := fun s k g' =>
    goodField_clm_sum Finset.univ (walkL F (e s)) fun p _ =>
      (hlCtx Q T t (g₀ s)).goodField_valF hT (hg₀ s) k g' _
  have h1 : ∀ k hh', liftApply k (cand F T hh' k)
      (fun _ Y => ∑ s ∈ S, (Pi.single (w s) (g₀ s Y • e s) : ∀ i, hs i)) t =
      fun X z => ∑ s ∈ S,
        liftApply k (cand F T hh' k) (fun _ Y => Pi.single (w s) (g₀ s Y • e s)) t X z := by
    intro k hh'
    funext X z
    exact hl_liftApply_field_sum S k _ (fun s Y => (Pi.single (w s) (g₀ s Y • e s) : ∀ i, hs i))
      (fun s _ => contDiff_single_smul (e s) (hg₀ s)) t X z
  have h2 : ∀ s ∈ S, ∀ k hh', GoodField (Dm + 1)
      (liftApply k (cand F T hh' k) (fun _ Y => Pi.single (w s) (g₀ s Y • e s)) t) := by
    intro s _ k hh'
    rw [hval]
    exact (hgood s k hh').mono (by omega)
  have h3 : ∀ s ∈ S, ∀ j, ContDiff ℝ ((j - 1 : ℕ) : ℕ∞) (fun ε : ℝ =>
      sourceFlux Q.edge Q.η ε t (liftApply (n - j) (cand F T (g - 1) (n - j))
        (fun _ Y => Pi.single (w s) (g₀ s Y • e s)) t) κ X z) := by
    intro s _ j
    rw [hval]
    have hflux := sourceFlux_valField F Q hQ (hlCtx Q T t (g₀ s)) rfl (r := r + 1) hT (hg₀ s)
      (e s) (n - j) (g - 1)
    have e1 : (fun ε : ℝ => sourceFlux Q.edge Q.η ε t
        (valField F (hlCtx Q T t (g₀ s)) (e s) (n - j) (g - 1)) κ X z) =
        fun ε => ∑ p : WalkFrom F (g - 1 + 1) (w s),
          (hlCtx Q T t (g₀ s)).fluxS (n - j) (g - 1) (F.walkDat p.2) ε κ X z •
            walkVec F (e s) p :=
      funext fun ε => congrFun (congrFun (hflux ε κ) X) z
    rw [e1]
    exact ContDiff.sum fun p _ => (EpsPoly.contDiff_eps
      ((hlCtx Q T t (g₀ s)).epsPoly_fluxS (r := r) hT (hg₀ s) (n - j) (g - 1) (F.walkDat p.2)
        (goodDat_walkDat F hdat p.2 _) κ) X z _).smul contDiff_const
  exact (hl_liftFluxX_field_sum Q (cand F T) S
    (fun s Y => (Pi.single (w s) (g₀ s Y • e s) : ∀ i, hs i)) g n t X z κ h1 h2 h3).trans
    (Finset.sum_congr rfl fun s _ => liftFluxX_cand F Q hQ (hlCtx Q T t (g₀ s)) rfl rfl rfl rfl
      hT (hg₀ s) hdat (e s) g n X z κ)

/-- The slow flux of the path-candidate array of a chain family at the last vertex, on a sum of
fields in the entry `0`. -/
theorem hl_chain_liftFluxX_last_sum {Dm L : ℕ} (cd : Fin L → StepDat)
    (Q : LiftOperatorData (Fin (L + 1)) (fun _ => ℝ) Dm) (hQ : HasFamFlux Q (chainFam cd))
    (T : (g : ℕ) → (Fin g → StepDat) → SArr) (t : ℝ) {r : ℕ}
    (hT : ∀ g (cd : Fin g → StepDat) k m (α : DerivativeWord2 m),
      GoodField (r + 1 + Dm) (fun X z => T g cd k m α t X z))
    (hcd : ∀ i, GoodDat (r + 1 + Dm) t (cd i)) (S : Finset σ) (g₀ : σ → Vec 2 → ℝ)
    (hg₀ : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (g₀ s)) (c : σ → ℝ) (n : ℕ) (X z : Vec 2) (κ : Fin 2) :
    liftFluxX Q (cand (chainFam cd) T)
        (fun _ Y => ∑ s ∈ S, (Pi.single (0 : Fin (L + 1)) (g₀ s Y • c s) : Fin (L + 1) → ℝ))
        L n t X z κ (Fin.last L) =
      ∑ s ∈ S, (hlCtx Q T t (g₀ s)).formX n L cd κ X z * c s := by
  have hdat : ∀ v u (γ : (chainFam cd).Γ v u),
      GoodDat (r + 1 + Dm) t ((chainFam cd).dat v u γ) := fun v u γ => hcd _
  rw [hl_liftFluxX_cand_sum (chainFam cd) Q hQ T t hT hdat S (w := fun _ => (0 : Fin (L + 1)))
    g₀ hg₀ (e := c) L n X z κ, Finset.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_walkVec_apply, chain_sum_walk]
  have hlast : (Fin.last L).val = (0 : Fin (L + 1)).val + L := by simp
  rw [dite_eq_left_of_eq_true (eq_true hlast), chain_compMap, chain_walkDat]
  simp only [ContinuousLinearMap.id_apply, smul_eq_mul]
  congr 2
  funext j
  congr 1
  ext
  simp

/-- A functional of a sum of walk sums, read at a component. -/
theorem hl_dual_sum_walkVec (F : FamData ι hs) {g : ℕ} (S : Finset σ) (w : σ → ι)
    (e : ∀ s, hs (w s)) (c : ∀ s, WalkFrom F g (w s) → ℝ) (v : ι) (ℓ : hs v →L[ℝ] ℝ) :
    ℓ ((∑ s ∈ S, ∑ p : WalkFrom F g (w s), c s p • walkVec F (e s) p) v) =
      ∑ s ∈ S, ℓ (∑ q : F.Walk g (w s) v, c s ⟨v, q⟩ • F.compMap q (e s)) := by
  rw [Finset.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun s _ => by rw [sum_walkVec_apply]

/-- The walk sums of `formX` are continuous in the fast variable. -/
theorem hl_continuous_cand_sum {Dm : ℕ} (F : FamData ι hs) (Q : LiftOperatorData ι hs Dm)
    (T : (g : ℕ) → (Fin g → StepDat) → SArr) (t : ℝ) {r : ℕ}
    (hT : ∀ g (cd : Fin g → StepDat) k m (α : DerivativeWord2 m),
      GoodField (r + 1 + Dm) (fun X z => T g cd k m α t X z))
    (hdat : ∀ v u (γ : F.Γ v u), GoodDat (r + 1 + Dm) t (F.dat v u γ))
    (hG : ∀ a b, ContDiff ℝ ((r + 2 : ℕ) : ℕ∞) (fun X => Q.G t X a b))
    (hv : ∀ κ, GoodField (r + 2) (fun (_ z : Vec 2) => Q.v t z κ))
    (S : Finset σ) (w : σ → ι) (g₀ : σ → Vec 2 → ℝ) (hg₀ : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (g₀ s))
    (e : ∀ s, hs (w s)) (g n : ℕ) (X : Vec 2) (κ : Fin 2) :
    Continuous fun z => ∑ s ∈ S, ∑ p : WalkFrom F g (w s),
      (hlCtx Q T t (g₀ s)).formX n g (F.walkDat p.2) κ X z • walkVec F (e s) p := by
  refine continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun p _ => ?_
  have hGv : (hlCtx Q T t (g₀ s)).GoodGv (r + 2) := ⟨hG, hv⟩
  exact (((hlCtx Q T t (g₀ s)).goodField_formX hT (hg₀ s) hGv n g _
    (goodDat_walkDat F hdat p.2) κ).continuous_slice X).smul continuous_const

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLDecomp
end
end
end

section
/-! The diagonal candidate is a grade-zero lift sequence of the Hilbert operator data.

The scalar lift sequence `C0` of the one-point family is transported componentwise: a cell
inverse of the scalar source, composed with `ℓ ∘ proj_v`, is the dual of the `v` component of the
Hilbert inverse (`hl_liftCellSource_transfer`), and a vector cell inverse is assembled from its
duals along a basis (`cellFieldInverse_pi_synthesis`, `cellFieldInverse_dependent_pi`). -/

/-! The grade-zero slow flux of the diagonal candidate.

`liftFluxX` at grade zero reads `liftApply` of the arrays of degrees `n - 1` and `n - 2` and
differentiates it once in the fast variable and once in the slow variable. For the diagonal
candidate the `v` component along `ℓ` is the scalar flux of the scalarization. -/

@[expose] public noncomputable section

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLZero

section
open Homogenization AVRegularity.Sobolev AVRegularity
open AVRegularity.CycleComparison.Lift


variable {ι : Type*} [Fintype ι] [DecidableEq ι] {hs : ι → Type*}
  [∀ i, NormedAddCommGroup (hs i)] [∀ i, NormedSpace ℝ (hs i)] {Dm : ℕ}

/-- A vector cell inverse from its duals. -/
theorem isCellFieldInverse_of_dual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (sZ : ℕ) (hsZ : 1 ≤ sZ) (a b : ℝ) (hab : a ≤ b) (g c : ℝ → Vec 2 → E)
    (h : ∀ ℓ : E →L[ℝ] ℝ, IsCellFieldInverse G v sZ a b (fun _ => (0 : ℝ))
      (fun t z => ℓ (g t z)) (fun t z => ℓ (c t z))) :
    IsCellFieldInverse G v sZ a b (fun _ => (0 : E)) g c := by
  let bs := Module.finBasis ℝ E
  let ℓj : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ := fun j =>
    LinearMap.toContinuousLinearMap (bs.coord j)
  let L : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] E :=
    LinearMap.toContinuousLinearMap (bs.equivFun.symm : (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E)
  have key : ∀ x : E, L (fun j => ℓj j x) = x := fun x => by
    have : (fun j => ℓj j x) = bs.equivFun x := by
      funext j; simp [ℓj, Module.Basis.coord_apply]
    rw [this]
    exact bs.equivFun.symm_apply_apply x
  have hs := cellFieldInverse_pi_synthesis L G v sZ hsZ a b hab
    (fun j t z => ℓj j (g t z)) (fun j t z => ℓj j (c t z)) (fun j => h (ℓj j))
  simp only [key] at hs
  exact hs

/-- The scalar-ized cell inverse of the `v` component (one functional, one time window). -/
theorem hlDiag_cellInverse_dual [∀ i, FiniteDimensional ℝ (hs i)] [∀ i, CompleteSpace (hs i)]
    (C0 : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ))
    (Q : LiftOperatorData ι hs Dm) (Q0 : LiftOperatorData (Fin 1) (fun _ : Fin 1 => ℝ) Dm)
    (hη : Q0.η = Q.η) (hG : Q0.G = Q.G) (hv : Q0.v = Q.v) {sX sZ N : ℕ} {t₀ t₁ : ℝ}
    (hC0 : IsLiftSequence Q0 sX sZ t₀ t₁ N 0 C0) (hab : t₀ ≤ t₁) (hsZ : 1 ≤ sZ)
    (hfX : N + 2 ≤ sX) (hfZ : N + 2 ≤ sZ)
    (hGs : ∀ t i j, ContDiff ℝ (⊤ : ℕ∞) (fun X => Q.G t X i j))
    (hvs : ∀ t k, ContDiff ℝ (⊤ : ℕ∞) (fun z => Q.v t z k))
    (hcH : ∀ t ∈ Set.Icc t₀ t₁, ∀ n' m α v' u, IsBoxSmooth sX sZ
      (fun X z => hlDiagCoeff hs C0 0 n' m α t X z v' u))
    {n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) (a₀ : Vec 2 → ∀ i, hs i)
    (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀) (X : Vec 2) {v : ι} (ℓ : hs v →L[ℝ] ℝ) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ t₀ t₁ (fun _ => (0 : ℝ))
      (fun t z => ℓ (liftCellSource Q (hlDiagCoeff hs C0) (fun _ => a₀) 0 n t X z v))
      (fun t z => ℓ (liftApply n (hlDiagCoeff hs C0 0 n) (fun _ => a₀) t X z v)) := by
  let b₀ : Vec 2 → Fin 1 → ℝ := fun Y _ => ℓ (a₀ Y v)
  have hb₀ : ContDiff ℝ (⊤ : ℕ∞) b₀ := hlScal_contDiff ℓ (a := fun _ => a₀) (t := 0) ha₀
  have h7 := hC0.2.2.2.2.2.2 0 le_rfl n hn1 hnN b₀ hb₀ X
  rw [hG, hv] at h7
  have hP := AVRegularity.Providers.PathDecomp.isCellFieldInverse_clm hsZ (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 1 => ℝ) 0) h7
  have hz : (fun x : Vec 2 => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
      ((fun _ : Vec 2 => (0 : Fin 1 → ℝ)) x)) = fun _ => (0 : ℝ) := by
    funext x; simp
  rw [hz] at hP
  have hsc : ∀ t ∈ Set.Icc t₀ t₁, ∀ z,
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
        (liftCellSource Q0 C0 (fun _ => b₀) 0 n t X z) =
      ℓ (liftCellSource Q (hlDiagCoeff hs C0) (fun _ => a₀) 0 n t X z v) := by
    intro t ht z
    have hbox := fun n' m α v' u => (hC0.2.2.2.2.2.1 0 le_rfl n' m α v' u t ht).1
    symm
    exact hl_liftCellSource_transfer C0 Q Q0 hη hG hv ℓ (fun _ => a₀) n t X z
      (hGs t) (hvs t) (ha₀.of_le (by exact_mod_cast le_top))
      (fun n' m α v' u => (hcH t ht n' m α v' u).mono (by omega) (by omega))
      (fun n' m α v' u => (hbox n' m α v' u).mono (by omega) (by omega))
  have hsl : ∀ t ∈ Set.Icc t₀ t₁, ∀ z,
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
        (liftApply n (C0 0 n) (fun _ => b₀) t X z) =
      ℓ (liftApply n (hlDiagCoeff hs C0 0 n) (fun _ => a₀) t X z v) := by
    intro t ht z
    symm
    exact hl_liftApply_transfer C0 n ℓ (fun _ => a₀) t X z (ha₀.of_le (by exact_mod_cast le_top))
  have h1 := CycleComparison.Lift.cellFieldInverse_source_congr_on _ _ sZ t₀ t₁ _
    (fun t z => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
        (liftCellSource Q0 C0 (fun _ => b₀) 0 n t X z))
    (fun t z => ℓ (liftCellSource Q (hlDiagCoeff hs C0) (fun _ => a₀) 0 n t X z v)) _
    (fun t ht => funext (hsc t ht)) hP
  exact AVRegularity.WeakEntryProofs.cellFieldInverse_field_congr_on _ _ sZ t₀ t₁ hab _ _ _ _ h1
    (fun t ht => funext (hsl t ht))

/-- **The diagonal candidate is a grade-zero lift sequence of the Hilbert operator data.** -/
theorem hlDiag_isLiftSequence [∀ i, FiniteDimensional ℝ (hs i)] [∀ i, CompleteSpace (hs i)]
    (C0 : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ))
    (Q : LiftOperatorData ι hs Dm) (Q0 : LiftOperatorData (Fin 1) (fun _ : Fin 1 => ℝ) Dm)
    (hη : Q0.η = Q.η) (hG : Q0.G = Q.G) (hv : Q0.v = Q.v) {sX sZ N : ℕ} {t₀ t₁ : ℝ}
    (hC0 : IsLiftSequence Q0 sX sZ t₀ t₁ N 0 C0) (hab : t₀ ≤ t₁) (hsZ : 1 ≤ sZ)
    (hfX : N + 2 ≤ sX) (hfZ : N + 2 ≤ sZ)
    (hGs : ∀ t i j, ContDiff ℝ (⊤ : ℕ∞) (fun X => Q.G t X i j))
    (hvs : ∀ t k, ContDiff ℝ (⊤ : ℕ∞) (fun z => Q.v t z k)) :
    IsLiftSequence Q sX sZ t₀ t₁ N 0 (hlDiagCoeff hs C0) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hC0
  have hbp : ∀ t ∈ Set.Icc t₀ t₁, ∀ n' m α v' u,
      IsBoxSmooth sX sZ (fun X z => hlDiagCoeff hs C0 0 n' m α t X z v' u) ∧
        ∀ X, AVenhance.IsZ2Periodic (fun z => hlDiagCoeff hs C0 0 n' m α t X z v' u) :=
    fun t ht n' m α v' u => hlDiag_boxSmooth_periodic C0 sX sZ n' m α t v' u
      (h5 0 le_rfl n' m α 0 0 t ht).1 (h5 0 le_rfl n' m α 0 0 t ht).2
  refine ⟨fun a₀ ha₀ t ht X z => hlDiag_clause_one C0 h0 a₀ ht X z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hh h1' hh0
    omega
  · intro hh hhH n hn m α t X z v u
    obtain rfl : hh = 0 := Nat.le_zero.mp hhH
    exact hlDiag_vanish C0 n m α t X z (by rw [h2 0 le_rfl n hn m α t X z 0 0]) v u
  · intro hh hhH n m hnm α t X z v u
    obtain rfl : hh = 0 := Nat.le_zero.mp hhH
    exact hlDiag_vanish C0 n m α t X z (by rw [h3 0 le_rfl n m hnm α t X z 0 0]) v u
  · intro hh hhH n m α σ
    obtain rfl : hh = 0 := Nat.le_zero.mp hhH
    exact hlDiag_symm C0 n m σ α (h4 0 le_rfl n m α σ)
  · intro hh hhH n m α v u t ht
    obtain rfl : hh = 0 := Nat.le_zero.mp hhH
    exact hbp t ht n m α v u
  · intro hh hhH n hn1 hnN a₀ ha₀ X
    obtain rfl : hh = 0 := Nat.le_zero.mp hhH
    refine cellFieldInverse_dependent_pi _ _ sZ hsZ t₀ t₁ hab _ _ fun v => ?_
    exact isCellFieldInverse_of_dual _ _ sZ hsZ t₀ t₁ hab _ _ fun ℓ =>
      hlDiag_cellInverse_dual C0 Q Q0 hη hG hv ⟨h0, h1, h2, h3, h4, h5, h6⟩ hab hsZ hfX hfZ hGs hvs
        (fun t ht n' m α v' u => (hbp t ht n' m α v' u).1) hn1 hnN a₀ ha₀ X ℓ

end

section
open Homogenization AVRegularity.Sobolev AVRegularity
open AVRegularity.CycleComparison.Lift


variable {ι : Type*} [Fintype ι] [DecidableEq ι] {hs : ι → Type*}
  [∀ i, NormedAddCommGroup (hs i)] [∀ i, NormedSpace ℝ (hs i)] {Dm : ℕ}

omit [DecidableEq ι] in
theorem liftFluxX_zero_formula {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (n : ℕ) (t : ℝ) (X z : Vec 2) (k : Fin 2) :
    liftFluxX Q Cc a 0 n t X z k =
      ((Real.sqrt Q.η * Q.v t z k) • liftApply (n - 1) (Cc 0 (n - 1)) a t X z
        - Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k j •
            fastPartial j (liftApply (n - 1) (Cc 0 (n - 1)) a t) X z)
      + (if 2 ≤ n then -(Q.η • ∑ j : Fin 2, Q.G t X k j •
            slowPartial j (liftApply (n - 2) (Cc 0 (n - 2)) a t) X z) else 0) := by
  simp [liftFluxX]

/-- `ℓ` of the `v` component of the grade-zero flux of the diagonal candidate. -/
theorem hl_liftFluxX_transfer (c : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ))
    (Q : LiftOperatorData ι hs Dm) (Q0 : LiftOperatorData (Fin 1) (fun _ : Fin 1 => ℝ) Dm)
    (hη : Q0.η = Q.η) (hG : Q0.G = Q.G) (hv : Q0.v = Q.v)
    {v : ι} (ℓ : hs v →L[ℝ] ℝ) (a : ℝ → Vec 2 → ∀ i, hs i) (n : ℕ) (t : ℝ) (X z : Vec 2)
    (k : Fin 2) (ha : ContDiff ℝ ((n + 2 : ℕ) : ℕ∞) (a t))
    (hcH : ∀ n' m α v' u, IsBoxSmooth 2 1 (fun X z => hlDiagCoeff hs c 0 n' m α t X z v' u))
    (hcS : ∀ n' m α v' u, IsBoxSmooth 2 1 (fun X z => c 0 n' m α t X z v' u)) :
    ℓ (liftFluxX Q (hlDiagCoeff hs c) a 0 n t X z k v) =
      liftFluxX Q0 c (hlScal ℓ a) 0 n t X z k 0 := by
  let Λ : (∀ i, hs i) →L[ℝ] ℝ := ℓ.comp (ContinuousLinearMap.proj (R := ℝ) (φ := hs) v)
  let P0 : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0
  have hrel : ∀ k', k' ≤ n → ∀ Y y, Λ (liftApply k' (hlDiagCoeff hs c 0 k') a t Y y) =
      P0 (liftApply k' (c 0 k') (hlScal ℓ a) t Y y) := fun k' hk Y y =>
    hl_liftApply_transfer c k' ℓ a t Y y (ha.of_le (by exact_mod_cast (by omega)))
  have hF1H : IsBoxSmooth 0 1 (liftApply (n - 1) (hlDiagCoeff hs c 0 (n - 1)) a t) :=
    liftApply_box_reserve (n - 1) 0 1 _ a t (ha.of_le (by exact_mod_cast (by omega)))
      fun m _ α v' u => (hcH (n - 1) m α v' u).mono (by norm_num) le_rfl
  have hF1S : IsBoxSmooth 0 1 (liftApply (n - 1) (c 0 (n - 1)) (hlScal ℓ a) t) :=
    liftApply_box_reserve (n - 1) 0 1 _ (hlScal ℓ a) t
      ((hlScal_contDiff ℓ ha).of_le (by exact_mod_cast (by omega)))
      fun m _ α v' u => (hcS (n - 1) m α v' u).mono (by norm_num) le_rfl
  have hfast : ∀ j' : Fin 2, Λ (fastPartial j' (liftApply (n - 1) (hlDiagCoeff hs c 0 (n - 1)) a t) X z) =
      P0 (fastPartial j' (liftApply (n - 1) (c 0 (n - 1)) (hlScal ℓ a) t) X z) := by
    intro j'
    rw [← fastPartial_postcomposition Λ _ hF1H j' X z,
      ← fastPartial_postcomposition P0 _ hF1S j' X z]
    congr 1
    funext Y y
    exact hrel (n - 1) (by omega) Y y
  rw [liftFluxX_zero_formula, liftFluxX_zero_formula, ← hη, ← hG, ← hv]
  change Λ (_ + _) = _
  rw [map_add, map_sub, map_smul, map_smul, map_sum, hrel (n - 1) (by omega)]
  simp only [map_smul, hfast]
  by_cases h2 : 2 ≤ n
  · have hF2H : IsBoxSmooth 1 0 (liftApply (n - 2) (hlDiagCoeff hs c 0 (n - 2)) a t) :=
      liftApply_box_reserve (n - 2) 1 0 _ a t (ha.of_le (by exact_mod_cast (by omega)))
        fun m _ α v' u => (hcH (n - 2) m α v' u).mono (by norm_num) (by norm_num)
    have hF2S : IsBoxSmooth 1 0 (liftApply (n - 2) (c 0 (n - 2)) (hlScal ℓ a) t) :=
      liftApply_box_reserve (n - 2) 1 0 _ (hlScal ℓ a) t
        ((hlScal_contDiff ℓ ha).of_le (by exact_mod_cast (by omega)))
        fun m _ α v' u => (hcS (n - 2) m α v' u).mono (by norm_num) (by norm_num)
    have hslow : ∀ j' : Fin 2, Λ (slowPartial j' (liftApply (n - 2) (hlDiagCoeff hs c 0 (n - 2)) a t) X z) =
        P0 (slowPartial j' (liftApply (n - 2) (c 0 (n - 2)) (hlScal ℓ a) t) X z) := by
      intro j'
      rw [← slowPartial_postcomposition Λ _ hF2H j' X z,
        ← slowPartial_postcomposition P0 _ hF2S j' X z]
      congr 1
      funext Y y
      exact hrel (n - 2) (by omega) Y y
    simp only [h2, ite_true, map_neg, map_smul, map_sum, hslow]
    rfl
  · simp only [h2, ite_false, map_zero]
    rfl

omit [DecidableEq ι] in
/-- The grade-zero slow flux is box smooth of order `(0, 0)`. -/
theorem liftFluxX_boxSmooth_zero {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (n : ℕ) (t : ℝ) (k : Fin 2)
    (hGs : ∀ i j, ContDiff ℝ (0 : ℕ∞) (fun X => Q.G t X i j))
    (hvs : ∀ k', ContDiff ℝ (0 : ℕ∞) (fun z => Q.v t z k'))
    (ha : ContDiff ℝ ((n + 2 : ℕ) : ℕ∞) (a t))
    (hc : ∀ n' m α v u, IsBoxSmooth 2 1 (fun X z => Cc 0 n' m α t X z v u)) :
    IsBoxSmooth 0 0 (fun X z => liftFluxX Q Cc a 0 n t X z k) := by
  have hF1 : IsBoxSmooth 0 1 (liftApply (n - 1) (Cc 0 (n - 1)) a t) :=
    liftApply_box_reserve (n - 1) 0 1 _ a t (ha.of_le (by exact_mod_cast (by omega)))
      fun m _ α v' u => (hc (n - 1) m α v' u).mono (by norm_num) le_rfl
  have hls : IsBoxSmooth 0 0 (fun (X : Vec 2) (z : Vec 2) => Real.sqrt Q.η * Q.v t z k) :=
    isBoxSmooth_fast_field 0 0 (fun z => Real.sqrt Q.η * Q.v t z k)
      (contDiff_const.mul (hvs k))
  have t1 : IsBoxSmooth 0 0 (fun X z => (Real.sqrt Q.η * Q.v t z k) •
      liftApply (n - 1) (Cc 0 (n - 1)) a t X z) :=
    isBoxSmooth_bilinear hls (hF1.mono le_rfl (by norm_num))
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] _ →L[ℝ] _)
  have t2 : IsBoxSmooth 0 0 (fun X z => Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k j •
      fastPartial j (liftApply (n - 1) (Cc 0 (n - 1)) a t) X z) := by
    apply IsBoxSmooth.const_smul
    apply IsBoxSmooth.sum
    intro j _
    exact isBoxSmooth_bilinear (isBoxSmooth_slow_field 0 0 (fun X => Q.G t X k j) (hGs k j))
      (hF1.fastPartial j) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] _ →L[ℝ] _)
  by_cases h2 : 2 ≤ n
  · have hF2 : IsBoxSmooth 1 0 (liftApply (n - 2) (Cc 0 (n - 2)) a t) :=
      liftApply_box_reserve (n - 2) 1 0 _ a t (ha.of_le (by exact_mod_cast (by omega)))
        fun m _ α v' u => (hc (n - 2) m α v' u).mono (by norm_num) (by norm_num)
    have t3 : IsBoxSmooth 0 0 (fun X z => -(Q.η • ∑ j : Fin 2, Q.G t X k j •
        slowPartial j (liftApply (n - 2) (Cc 0 (n - 2)) a t) X z)) := by
      apply IsBoxSmooth.neg
      apply IsBoxSmooth.const_smul
      apply IsBoxSmooth.sum
      intro j _
      exact isBoxSmooth_bilinear (isBoxSmooth_slow_field 0 0 (fun X => Q.G t X k j) (hGs k j))
        (hF2.slowPartial j) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] _ →L[ℝ] _)
    have e : (fun X z => liftFluxX Q Cc a 0 n t X z k) = fun X z =>
        ((Real.sqrt Q.η * Q.v t z k) • liftApply (n - 1) (Cc 0 (n - 1)) a t X z
          - Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k j •
            fastPartial j (liftApply (n - 1) (Cc 0 (n - 1)) a t) X z)
        + -(Q.η • ∑ j : Fin 2, Q.G t X k j •
            slowPartial j (liftApply (n - 2) (Cc 0 (n - 2)) a t) X z) := by
      funext X z
      rw [liftFluxX_zero_formula]
      simp [h2]
    rw [e]
    exact (t1.sub t2).add t3
  · have e : (fun X z => liftFluxX Q Cc a 0 n t X z k) = fun X z =>
        ((Real.sqrt Q.η * Q.v t z k) • liftApply (n - 1) (Cc 0 (n - 1)) a t X z
          - Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k j •
            fastPartial j (liftApply (n - 1) (Cc 0 (n - 1)) a t) X z) := by
      funext X z
      rw [liftFluxX_zero_formula]
      simp [h2]
    rw [e]
    exact t1.sub t2

omit [DecidableEq ι] in
theorem liftFluxX_continuous_zero {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (n : ℕ) (t : ℝ) (k : Fin 2)
    (hGs : ∀ i j, ContDiff ℝ (0 : ℕ∞) (fun X => Q.G t X i j))
    (hvs : ∀ k', ContDiff ℝ (0 : ℕ∞) (fun z => Q.v t z k'))
    (ha : ContDiff ℝ ((n + 2 : ℕ) : ℕ∞) (a t))
    (hc : ∀ n' m α v u, IsBoxSmooth 2 1 (fun X z => Cc 0 n' m α t X z v u)) (X : Vec 2) :
    Continuous (fun z => liftFluxX Q Cc a 0 n t X z k) :=
  (boxSmooth_continuous (liftFluxX_boxSmooth_zero Q Cc a n t k hGs hvs ha hc)).comp
    (continuous_const.prodMk continuous_id)

/-- The cell mean of the grade-zero flux of the diagonal candidate, along `ℓ` at the component
`v`, is the cell mean of the scalar flux of the scalarization. -/
theorem hl_fluxMean_transfer [∀ i, CompleteSpace (hs i)]
    (c : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ))
    (Q : LiftOperatorData ι hs Dm) (Q0 : LiftOperatorData (Fin 1) (fun _ : Fin 1 => ℝ) Dm)
    (hη : Q0.η = Q.η) (hG : Q0.G = Q.G) (hv : Q0.v = Q.v)
    {v : ι} (ℓ : hs v →L[ℝ] ℝ) (a : ℝ → Vec 2 → ∀ i, hs i) (n : ℕ) (t : ℝ) (X : Vec 2)
    (k : Fin 2) (hGs : ∀ i j, ContDiff ℝ (0 : ℕ∞) (fun X => Q.G t X i j))
    (hvs : ∀ k', ContDiff ℝ (0 : ℕ∞) (fun z => Q.v t z k'))
    (ha : ContDiff ℝ ((n + 2 : ℕ) : ℕ∞) (a t))
    (hcH : ∀ n' m α v' u, IsBoxSmooth 2 1 (fun X z => hlDiagCoeff hs c 0 n' m α t X z v' u))
    (hcS : ∀ n' m α v' u, IsBoxSmooth 2 1 (fun X z => c 0 n' m α t X z v' u)) :
    ℓ (fieldCellMean (fun z => liftFluxX Q (hlDiagCoeff hs c) a 0 n t X z k) v) =
      fieldCellMean (fun z => liftFluxX Q0 c (hlScal ℓ a) 0 n t X z k) 0 := by
  let Λ : (∀ i, hs i) →L[ℝ] ℝ := ℓ.comp (ContinuousLinearMap.proj (R := ℝ) (φ := hs) v)
  let P0 : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0
  have hcH' := liftFluxX_continuous_zero Q (hlDiagCoeff hs c) a n t k hGs hvs ha hcH X
  have hcS' := liftFluxX_continuous_zero Q0 c (hlScal ℓ a) n t k (by rw [hG]; exact hGs)
    (by rw [hv]; exact hvs) (hlScal_contDiff ℓ ha) hcS X
  change Λ (fieldCellMean (fun z => liftFluxX Q (hlDiagCoeff hs c) a 0 n t X z k)) =
    P0 (fieldCellMean (fun z => liftFluxX Q0 c (hlScal ℓ a) 0 n t X z k))
  rw [← fieldCellMean_clm Λ hcH', ← fieldCellMean_clm P0 hcS']
  congr 1
  funext z
  exact hl_liftFluxX_transfer c Q Q0 hη hG hv ℓ a n t X z k ha hcH hcS

end

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLZero
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! The finer-output step of the flux cancellation, clause (i): **recentring covariance of the finer
outputs**. For an admissible family `A` over an odd slot `k` of the stage, a label `y` with
`A^{[y]}` admissible and a time of the pulse window,
`fop(A^{[y]}) (f(y + ·)) (0) = fop(A) f (y)` for every source and every field `f` (no regularity
is used: both sides are the same expression in `fderiv`s of translated functions).

* `FluxRecenterShift G`: the old fluxes of the recentred context are those of the context at the
  shifted slow offset, on the pulse window, admissible or not (`fluxRecenterShift_of_oldCert`: the
  context formula of a certified stage and `recenter_recenter`).
* `ccov_lift_recenter`: the lifts of the scalar path family on `A^{[y]}` are the translates of
  those on `A` (`liftSequence_shift_covariant`; window data of the molecular metric without a
  sign condition on `κ`).
* `ccov_pathMeanFlux_recenter`, `ccov_directFlux_recenter`: the path means and the direct
  transport, at every label `w` with `A^{[y + w]}` admissible.
* `ccov_letter_recenter`: the Eulerian covariance letter (push-forward, powers of the constant
  operator `𝒞`, Piola pullback) for a chart pair and its recentring.
* `ccov_fluxOp_recenter`: the four cases of `SuccSource.fluxOp`. -/

section
open CycleComparison.LiftMeanEntrywise Uniqueness Providers.GenSem

/-! ### Translations -/

section Frame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ccov_orderedDerivative_add_left {m : ℕ} (α : DerivativeWord2 m) (g : Vec 2 → E)
    (y w : Vec 2) :
    orderedDerivative α (fun h' => g (y + h')) w = orderedDerivative α g (y + w) := by
  have h := orderedDerivative_slowShift α g y w
  rw [add_comm y w, ← h]
  congr 1
  funext X
  rw [add_comm]

theorem ccov_covOperator_add_left (H : Matrix (Fin 2) (Fin 2) ℝ) (V : Vec 2 → E) (c : Vec 2) :
    covOperator H (fun w => V (c + w)) = fun w => covOperator H V (c + w) := by
  funext w
  have h1 : ∀ j : Fin 2, (fun y => fderiv ℝ (fun w => V (c + w)) y (basisVec j)) =
      fun y => (fun x => fderiv ℝ V x (basisVec j)) (c + y) := fun j => funext fun y => by
    rw [fderiv_comp_add_left]
  have h2 : ∀ j : Fin 2, fderiv ℝ (fun y => (fun x => fderiv ℝ V x (basisVec j)) (c + y)) w =
      fderiv ℝ (fun x => fderiv ℝ V x (basisVec j)) (c + w) := fun j =>
    fderiv_comp_add_left (𝕜 := ℝ) (f := fun x => fderiv ℝ V x (basisVec j)) c
  show ∑ i : Fin 2, ∑ j : Fin 2,
      H i j • fderiv ℝ (fun y => fderiv ℝ (fun w => V (c + w)) y (basisVec j)) w (basisVec i) =
    ∑ i : Fin 2, ∑ j : Fin 2,
      H i j • fderiv ℝ (fun y => fderiv ℝ V y (basisVec j)) (c + w) (basisVec i)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h1 j, h2 j]

theorem ccov_covOperator_iterate_add_left (H : Matrix (Fin 2) (Fin 2) ℝ) (c : Vec 2) :
    ∀ (a : ℕ) (V : Vec 2 → E),
      (covOperator H)^[a] (fun w => V (c + w)) = fun w => (covOperator H)^[a] V (c + w)
  | 0, _ => rfl
  | a + 1, V => by
      rw [Function.iterate_succ_apply, ccov_covOperator_add_left,
        ccov_covOperator_iterate_add_left H c a (covOperator H V)]
      rfl

end Frame

/-- **The Eulerian covariance letter of a recentred chart pair.** `(Φ', Φi')` is the chart pair
`(Φ, Φi)` recentred at the label `y`, the label operators `M'`, `M` are covariant on a
neighbourhood `U` of the label `0`. -/
theorem ccov_letter_recenter {Φ Φi Φ' Φi' : Vec 2 → Vec 2} {y : Vec 2}
    (h1 : Φ' = fun v => Φ (y + v) - Φ y) (h2 : Φi' = fun w => Φi (Φ y + w) - y)
    (hJ : ∀ w, jacMatrix Φ' w = jacMatrix Φ (y + w)) (hinv : Φi (Φ y) = y)
    (hcont : ContinuousAt Φi (Φ y)) {M M' : (Vec 2 → ℝ) → Vec 2 → Vec 2} {U : Set (Vec 2)}
    (hU : IsOpen U) (h0 : (0 : Vec 2) ∈ U)
    (hM : ∀ (g : Vec 2 → ℝ), ∀ w ∈ U, M' (fun h' => g (y + h')) w = M g (y + w))
    (H : Matrix (Fin 2) (Fin 2) ℝ) (c₀ : ℝ) (a a' : ℕ) (f : Vec 2 → ℝ) :
    pullFlux Φ' Φi' (fun g x => c₀ • (covOperator H)^[a]
        (pushFlux Φ' Φi' M' ((covOperator H)^[a'] g)) x) (fun h' => f (y + h')) 0 =
      pullFlux Φ Φi (fun g x => c₀ • (covOperator H)^[a]
        (pushFlux Φ Φi M ((covOperator H)^[a'] g)) x) f y := by
  have hΦ0 : Φ' 0 = 0 := by rw [h1]; simp
  have hcomp : (fun h' => f (y + h')) ∘ Φi' = fun w => (f ∘ Φi) (Φ y + w) := by
    funext w
    simp only [Function.comp_apply, h2, add_sub_cancel]
  obtain ⟨G₁, hG₁⟩ : ∃ G : Vec 2 → ℝ, G = (covOperator H)^[a'] (f ∘ Φi) := ⟨_, rfl⟩
  have hpush : pushFlux Φ' Φi' M' (fun w => G₁ (Φ y + w)) =ᶠ[𝓝 0]
      fun x' => pushFlux Φ Φi M G₁ (Φ y + x') := by
    have hc : ContinuousAt (fun x' : Vec 2 => Φi (Φ y + x') - y) 0 := by
      have hadd : ContinuousAt (fun x' : Vec 2 => Φ y + x') 0 :=
        (continuous_const.add continuous_id).continuousAt
      have hΦi : ContinuousAt Φi (Φ y + 0) := by rw [add_zero]; exact hcont
      exact (ContinuousAt.comp (f := fun x' : Vec 2 => Φ y + x') hΦi hadd).sub continuousAt_const
    have hmem : (fun x' : Vec 2 => Φi (Φ y + x') - y) ⁻¹' U ∈ 𝓝 (0 : Vec 2) :=
      hc.preimage_mem_nhds (hU.mem_nhds (by rw [add_zero, hinv, sub_self]; exact h0))
    filter_upwards [hmem] with x' hx'
    have hcomp' : (fun w => G₁ (Φ y + w)) ∘ Φ' = fun v => (G₁ ∘ Φ) (y + v) := by
      funext v
      simp only [Function.comp_apply, h1, add_sub_cancel]
    have hw : Φi' x' = Φi (Φ y + x') - y := by rw [h2]
    unfold pushFlux
    rw [hcomp', hw, hJ, hM (G₁ ∘ Φ) _ hx', add_sub_cancel]
  have hiter := (covOperator_iterate_germ H a hpush).eq_of_nhds
  rw [ccov_covOperator_iterate_add_left H (Φ y) a (pushFlux Φ Φi M G₁)] at hiter
  unfold pullFlux
  rw [hΦ0, hJ 0, hcomp]
  beta_reduce
  rw [ccov_covOperator_iterate_add_left H (Φ y) a' (f ∘ Φi), ← hG₁, hiter]
  simp only [add_zero]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-! ### The old fluxes and the chart maps of a recentred family -/

/-- The old fluxes of the recentred context `A^{[y]}` at the slow offset `X` are those of `A` at
`X + y/ε_{m-1}`, at the times of the pulse window (whether or not the recentrings are
admissible). -/
def FluxRecenterShift (G : GenStage D hr Dm b j₀) : Prop :=
  ∀ (p : OddSlot) (A : RealChain) (hA : IsAdmissibleChain D b j₀ G.level p.1 A) (y : Vec 2)
    (hAy : IsAdmissibleChain D b j₀ G.level p.1 (A.recenter D y)) (t : ℝ),
    t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
    ∀ (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1))
      (X z : Vec 2),
      G.fam.flux p ⟨A.recenter D y, hAy⟩ v u γ d I t X z =
        G.fam.flux p ⟨A, hA⟩ v u γ d I t (X + (D.eps (G.level - 1))⁻¹ • y) z

/-- A certified stage has the recentring shift: the context formula and `recenter_recenter`. -/
theorem fluxRecenterShift_of_oldCert (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    {G : GenStage D hr Dm b j₀} {𝒮 : SeedExports} {μ : Comp → ℝ} {L : ℕ} {Cθ : ℝ}
    (hcert : G.OldCert 𝒮 μ L Cθ) : FluxRecenterShift G := by
  intro p A hA y hAy t ht v u γ d I X z
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  funext c
  obtain ⟨θ, -, -, hc⟩ := hcert v u γ
  obtain ⟨f, F, hfF, -⟩ := hc d I c
  obtain ⟨-, -, hval⟩ := hfF p
  have e : (A.recenter D y).recenter D (D.eps (G.level - 1) • X) =
      A.recenter D (D.eps (G.level - 1) • (X + (D.eps (G.level - 1))⁻¹ • y)) := by
    rw [recenter_recenter D hζ, smul_add, smul_inv_smul₀ hε, add_comm]
  have h1 := hval ⟨A.recenter D y, hAy⟩ t ht X z
  have h2 := hval ⟨A, hA⟩ t ht (X + (D.eps (G.level - 1))⁻¹ • y) z
  dsimp only at h1 h2
  rw [e] at h1
  rw [h1, h2]

theorem ccov_famMap_recenter (hζ : IsFastProfile D.ζ) (A : RealChain) (hl : A.WellSlotted)
    (y v : Vec 2) (t : ℝ) :
    (A.recenter D y).famMap D t v = A.famMap D t (y + v) - A.famMap D t y := by
  rw [famMap_recenter D hζ A hl]
  simp only [RealChain.famMap, add_assoc]
  abel

theorem ccov_famMapInv_recenter (hζ : IsFastProfile D.ζ) (A : RealChain) (hl : A.WellSlotted)
    (y w : Vec 2) (t : ℝ) :
    (A.recenter D y).famMapInv D t w = A.famMapInv D t (A.famMap D t y + w) - y := by
  rw [famMapInv_recenter D hζ A hl]
  have e : (A.geom D).1 t (A.geom D).2.1 (A.geom D).2.2 + (A.famMap D t y + w) =
      (A.geom D).1 t ((A.geom D).2.1 + y) (A.geom D).2.2 + w := by
    simp only [RealChain.famMap]
    abel
  simp only [RealChain.famMapInv]
  rw [e]
  abel

/-- The cell time of a time of the pulse window lies in the lift window. -/
theorem ccov_inv_mul_mem_window {m : ℕ} {k : ℤ} (hc : 0 < D.cellScaleSq m) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ m k) :
    (D.cellScaleSq m)⁻¹ * t ∈ Icc (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) := by
  obtain ⟨h1, h2⟩ := ht
  refine ⟨?_, ?_⟩
  · rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hc.le)
  · rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hc.le)

/-- The physical time of a cell time of the lift window lies in the pulse window. -/
theorem ccov_mul_mem_window {m : ℕ} {k : ℤ} (hc : 0 < D.cellScaleSq m) {τ : ℝ}
    (hτ : τ ∈ Icc (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)) :
    D.cellScaleSq m * τ ∈ ocPulseWindow D.α D.q D.Λ m k := by
  obtain ⟨h1, h2⟩ := hτ
  rw [div_le_iff₀ hc] at h1
  rw [le_div_iff₀ hc] at h2
  exact ⟨by unfold OCData.slotStart at h1; linarith, by linarith⟩

/-! ### The lifts of a recentred family -/

/-- The lifted edges of the scalar path family on `A^{[y]}` are those on `A`, translated. -/
theorem ccov_pathEdges_shift (hΛ : 1 ≤ D.Λ) {G : GenStage D hr Dm b j₀}
    (hcov : FluxRecenterShift G) {h : ℕ} (π : StagePath G h) (p : OddSlot) {A : RealChain}
    (hA : IsAdmissibleChain D b j₀ G.level p.1 A) (y : Vec 2)
    (hAy : IsAdmissibleChain D b j₀ G.level p.1 (A.recenter D y)) {ρ : ℝ} (hρ : ρ ≠ 0) {τ : ℝ}
    (hτ : D.cellScaleSq G.level * τ ∈ ocPulseWindow D.α D.q D.Λ G.level p.1) :
    EdgesShiftAt (ρ⁻¹ • y) τ
      (liftEdges (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1))
        (pathEdges G π p ⟨A.recenter D y, hAy⟩))
      (liftEdges (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1))
        (pathEdges G π p ⟨A, hA⟩)) := by
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  intro v u d
  unfold liftEdges pathEdges
  split_ifs with hvu hd
  · simp only [List.map_cons, List.map_nil, List.forall₂_cons, List.forall₂_nil_left_iff,
      and_true]
    refine ⟨trivial, fun α X z => ?_⟩
    have e : (ρ / D.eps (G.level - 1)) • (X + ρ⁻¹ • y) =
        (ρ / D.eps (G.level - 1)) • X + (D.eps (G.level - 1))⁻¹ • y := by
      rw [smul_add, smul_smul]
      congr 2
      field_simp
    rw [e]
    exact hcov p A hA y hAy _ hτ _ _ _ d.1 α _ z
  · exact List.Forall₂.nil
  · exact List.Forall₂.nil

/-- **The lifts of the scalar path family on the recentred family are the translated lifts.** -/
theorem ccov_lift_recenter (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) {G : GenStage D hr Dm b j₀}
    (hcov : FluxRecenterShift G) (hc : 0 < D.cellScaleSq G.level) {h : ℕ} (π : StagePath G h)
    (k : ℤ) (hk : Odd k) {A : RealChain} (hA : IsAdmissibleChain D b j₀ G.level k A) (y : Vec 2)
    (hAy : IsAdmissibleChain D b j₀ G.level k (A.recenter D y)) {ρ : ℝ} (hρ : ρ ≠ 0)
    (sX sZ N : ℕ) (Cc' Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hC' : IsLiftSequenceOn (ladderOmega D b j₀ G.level k (A.recenter D y) ρ)
      (familyLiftData D G.level k (A.recenter D y) ρ
        (pathEdges G π ⟨k, hk⟩ ⟨A.recenter D y, hAy⟩)) sX sZ
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Cc')
    (hC : IsLiftSequenceOn (ladderOmega D b j₀ G.level k A ρ)
      (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)) sX sZ
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Cc) :
    ∀ hh ≤ h, ∀ n m (α : DerivativeWord2 m),
      ∀ τ ∈ Icc (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level),
      ∀ X, X + ρ⁻¹ • y ∈ ladderOmega D b j₀ G.level k A ρ → ∀ z v u,
        Cc' hh n m α τ X z v u = Cc hh n m α τ (X + ρ⁻¹ • y) z v u := by
  have hre : ∀ X : Vec 2,
      (A.recenter D y).recenter D (ρ • X) = A.recenter D (ρ • (X + ρ⁻¹ • y)) := fun X => by
    rw [recenter_recenter D hζ, smul_add, smul_inv_smul₀ hρ, add_comm]
  have hset : ladderOmega D b j₀ G.level k (A.recenter D y) ρ =
      {X | X + ρ⁻¹ • y ∈ ladderOmega D b j₀ G.level k A ρ} := by
    ext X
    show IsAdmissibleChain D b j₀ G.level k ((A.recenter D y).recenter D (ρ • X)) ↔
      IsAdmissibleChain D b j₀ G.level k (A.recenter D (ρ • (X + ρ⁻¹ • y)))
    rw [hre X]
  rw [hset] at hC'
  have hab : D.slotStart G.level k / D.cellScaleSq G.level ≤
      (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level := by
    apply div_le_div_of_nonneg_right _ hc.le
    unfold OCData.slotStart
    exact mul_le_mul_of_nonneg_right (by linarith) (Construction.Stream.ocTau_pos hΛ).le
  refine liftSequence_shift_covariant
    (familyLiftData D G.level k (A.recenter D y) ρ (pathEdges G π ⟨k, hk⟩ ⟨A.recenter D y, hAy⟩))
    (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)) (ρ⁻¹ • y) _ _ hab
    (isOpen_ladderOmega D b j₀ G.level k A ρ) rfl rfl ?_ ?_ ?_ sX sZ N h Cc' Cc hC' hC
  · intro t X i j
    show ((A.recenter D y).recenter D (ρ • X)).famMetric D (D.cellScaleSq G.level * t) i j =
      (A.recenter D (ρ • (X + ρ⁻¹ • y))).famMetric D (D.cellScaleSq G.level * t) i j
    rw [hre X]
  · intro τ hτ
    exact ccov_pathEdges_shift hΛ hcov π ⟨k, hk⟩ hA y hAy hρ (ccov_mul_mem_window hc hτ)
  · intro X _
    obtain ⟨lo, hi, hlo, he⟩ := familyLiftData_pos_window D hζ G.level k (A.recenter D y) ρ
      (pathEdges G π ⟨k, hk⟩ ⟨A.recenter D y, hAy⟩)
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) X
    obtain ⟨Mv, hMv⟩ := familyLiftData_v_bounded D hζ G.level hk (A.recenter D y) ρ
      (pathEdges G π ⟨k, hk⟩ ⟨A.recenter D y, hAy⟩)
    exact ⟨lo, hi, Mv, windowData_of_elliptic _ _ _ _ lo hi Mv
      (fun t => familyLiftData_symm D G.level k (A.recenter D y) ρ
        (pathEdges G π ⟨k, hk⟩ ⟨A.recenter D y, hAy⟩) t X 0 1) hlo he (fun t _ z => hMv t z)⟩

/-- **Recentring covariance of the path mean flux**, at every label `w` with `A^{[y + w]}`
admissible and every time of the pulse window. -/
theorem ccov_pathMeanFlux_recenter (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    {G : GenStage D hr Dm b j₀} (hcov : FluxRecenterShift G) (hc : 0 < D.cellScaleSq G.level)
    {h : ℕ} (π : StagePath G h) (k : ℤ) (hk : Odd k) {A : RealChain}
    (hA : IsAdmissibleChain D b j₀ G.level k A) (y : Vec 2)
    (hAy : IsAdmissibleChain D b j₀ G.level k (A.recenter D y)) {ρ : ℝ} (hρ : ρ ≠ 0)
    (sX sZ N : ℕ) (Cc' Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hC' : IsLiftSequenceOn (ladderOmega D b j₀ G.level k (A.recenter D y) ρ)
      (familyLiftData D G.level k (A.recenter D y) ρ
        (pathEdges G π ⟨k, hk⟩ ⟨A.recenter D y, hAy⟩)) sX sZ
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Cc')
    (hC : IsLiftSequenceOn (ladderOmega D b j₀ G.level k A ρ)
      (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)) sX sZ
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Cc)
    (n : ℕ) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) (f : Vec 2 → ℝ) (w : Vec 2)
    (hw : IsAdmissibleChain D b j₀ G.level k (A.recenter D (y + w))) :
    pathMeanFlux D G.level ρ (familyLiftData D G.level k (A.recenter D y) ρ
        (pathEdges G π ⟨k, hk⟩ ⟨A.recenter D y, hAy⟩)) Cc' n t (fun h' => f (y + h')) w =
      pathMeanFlux D G.level ρ (familyLiftData D G.level k A ρ
        (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)) Cc n t f (y + w) := by
  have hts := ccov_inv_mul_mem_window hc ht
  have hcoef := ccov_lift_recenter hΛ hζ hcov hc π k hk hA y hAy hρ sX sZ N Cc' Cc hC' hC
  have hΩ' : IsOpen {X : Vec 2 | X + ρ⁻¹ • y ∈ ladderOmega D b j₀ G.level k A ρ} :=
    (isOpen_ladderOmega D b j₀ G.level k A ρ).preimage (continuous_id.add continuous_const)
  have hwΩ : ρ⁻¹ • w ∈ {X : Vec 2 | X + ρ⁻¹ • y ∈ ladderOmega D b j₀ G.level k A ρ} := by
    show IsAdmissibleChain D b j₀ G.level k (A.recenter D (ρ • (ρ⁻¹ • w + ρ⁻¹ • y)))
    rw [smul_add, smul_inv_smul₀ hρ, smul_inv_smul₀ hρ, add_comm]
    exact hw
  have hP : ∀ hh' ≤ h, ∀ n' m' (α : DerivativeWord2 m'),
      ∀ X ∈ {X : Vec 2 | X + ρ⁻¹ • y ∈ ladderOmega D b j₀ G.level k A ρ},
      Cc' hh' n' m' α ((D.cellScaleSq G.level)⁻¹ * t) X =
        slowShiftSequence (ρ⁻¹ • y) Cc hh' n' m' α ((D.cellScaleSq G.level)⁻¹ * t) X :=
    fun hh' hh'h n' m' α X hX => funext fun z => funext fun v => funext fun u =>
      hcoef hh' hh'h n' m' α _ hts X hX z v u
  have hG : ∀ X i j, (familyLiftData D G.level k (A.recenter D y) ρ
      (pathEdges G π ⟨k, hk⟩ ⟨A.recenter D y, hAy⟩)).G ((D.cellScaleSq G.level)⁻¹ * t) X i j =
      (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)).G
        ((D.cellScaleSq G.level)⁻¹ * t) (X + ρ⁻¹ • y) i j := by
    intro X i j
    show ((A.recenter D y).recenter D (ρ • X)).famMetric D _ i j =
      (A.recenter D (ρ • (X + ρ⁻¹ • y))).famMetric D _ i j
    rw [recenter_recenter D hζ, smul_add, smul_inv_smul₀ hρ, add_comm]
  have he := ccov_pathEdges_shift hΛ hcov π ⟨k, hk⟩ hA y hAy hρ
    (τ := (D.cellScaleSq G.level)⁻¹ * t) (by rw [mul_inv_cancel_left₀ hc.ne']; exact ht)
  have hab : ∀ Y : Vec 2, (fun (_ : ℝ) (X : Vec 2) =>
      (Pi.single (0 : Fin (h + 1)) (f (y + ρ • X)) : Fin (h + 1) → ℝ))
        ((D.cellScaleSq G.level)⁻¹ * t) Y =
      (fun (_ : ℝ) (X : Vec 2) => (Pi.single (0 : Fin (h + 1)) (f (ρ • X)) : Fin (h + 1) → ℝ))
        ((D.cellScaleSq G.level)⁻¹ * t) (Y + ρ⁻¹ • y) := by
    intro Y
    show (Pi.single (0 : Fin (h + 1)) (f (y + ρ • Y)) : Fin (h + 1) → ℝ) =
      Pi.single (0 : Fin (h + 1)) (f (ρ • (Y + ρ⁻¹ • y)))
    rw [smul_add, smul_inv_smul₀ hρ, add_comm (ρ • Y) y]
  have hz : ∀ z κ, liftFluxX (familyLiftData D G.level k (A.recenter D y) ρ
        (pathEdges G π ⟨k, hk⟩ ⟨A.recenter D y, hAy⟩)) Cc'
        (fun _ X => Pi.single (0 : Fin (h + 1)) (f (y + ρ • X))) h n
        ((D.cellScaleSq G.level)⁻¹ * t) (ρ⁻¹ • w) z κ =
      liftFluxX (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)) Cc
        (fun _ X => Pi.single (0 : Fin (h + 1)) (f (ρ • X))) h n
        ((D.cellScaleSq G.level)⁻¹ * t) (ρ⁻¹ • (y + w)) z κ := by
    intro z κ
    refine (liftFluxX_locEq _ _ h n _ hΩ' hP κ _ hwΩ z).trans ?_
    rw [show ρ⁻¹ • (y + w) = ρ⁻¹ • w + ρ⁻¹ • y from by rw [smul_add, add_comm]]
    exact liftFluxX_shiftRel
      (familyLiftData D G.level k (A.recenter D y) ρ
        (pathEdges G π ⟨k, hk⟩ ⟨A.recenter D y, hAy⟩))
      (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)) Cc
      (fun _ X => (Pi.single (0 : Fin (h + 1)) (f (ρ • X)) : Fin (h + 1) → ℝ))
      (fun _ X => (Pi.single (0 : Fin (h + 1)) (f (y + ρ • X)) : Fin (h + 1) → ℝ))
      (ρ⁻¹ • y) ((D.cellScaleSq G.level)⁻¹ * t) rfl rfl hG he hab h n (ρ⁻¹ • w) z κ
  funext κ
  unfold pathMeanFlux
  simp only [hz]

/-- **Recentring covariance of the direct transport**, at every label and every time of the pulse
window. -/
theorem ccov_directFlux_recenter {G : GenStage D hr Dm b j₀} (hcov : FluxRecenterShift G)
    (p : OddSlot) {A : RealChain} (hA : IsAdmissibleChain D b j₀ G.level p.1 A) (y : Vec 2)
    (hAy : IsAdmissibleChain D b j₀ G.level p.1 (A.recenter D y)) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1) {v u : CompIn G.comps} (γ : G.fam.Γ v u)
    (ords : Finset ℕ) (f : Vec 2 → ℝ) (w : Vec 2) :
    directFlux G p ⟨A.recenter D y, hAy⟩ γ ords t (fun h' => f (y + h')) w =
      directFlux G p ⟨A, hA⟩ γ ords t f (y + w) := by
  unfold directFlux
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun α _ => ?_
  have e2 : (fun z => G.fam.flux p ⟨A.recenter D y, hAy⟩ v u γ d α t
      ((D.eps (G.level - 1))⁻¹ • w) z) =
      fun z => G.fam.flux p ⟨A, hA⟩ v u γ d α t ((D.eps (G.level - 1))⁻¹ • (y + w)) z := by
    funext z
    rw [hcov p A hA y hAy t ht, smul_add, add_comm]
  rw [ccov_orderedDerivative_add_left α f y w, e2]

/-! ### Clause (i) -/

open scoped Classical in
/-- **The finer-output step, clause (i): recentring covariance of the finer output of a source**, for every
field `f`. -/
theorem ccov_fluxOp_recenter (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    {G : GenStage D hr Dm b j₀} (hcov : FluxRecenterShift G) (hc : 0 < D.cellScaleSq G.level)
    (Mn : SuccMenu) (hρ : Mn.lenFactor * liftLength D G.level ≠ 0) (s₀ : ℝ) (s : SuccSource G)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (hLF : s.IsLiftFamily Mn Cc) (k : ℤ) (hk : Odd k) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) {A : RealChain}
    (hA : IsAdmissibleChain D b j₀ G.level k A) (y : Vec 2)
    (hAy : IsAdmissibleChain D b j₀ G.level k (A.recenter D y)) (f : Vec 2 → ℝ) :
    s.fluxOp (Mn.lenFactor * liftLength D G.level) s₀ Cc k t (A.recenter D y)
        (fun h' => f (y + h')) 0 =
      s.fluxOp (Mn.lenFactor * liftLength D G.level) s₀ Cc k t A f y := by
  unfold SuccSource.fluxOp
  rw [dite_eq_left ⟨hAy, hk⟩, dite_eq_left ⟨hA, hk⟩]
  cases s with
  | copyDir t' v u γ =>
    have h := ccov_directFlux_recenter hcov ⟨k, hk⟩ hA y hAy ht γ (Finset.Icc 3 Dm) f 0
    rw [add_zero] at h
    exact h
  | letterDiag t' u => rfl
  | copyQuad t' h π =>
    have hpm := ccov_pathMeanFlux_recenter hΛ hζ hcov hc π k hk hA y hAy hρ Mn.sX Mn.sZ Mn.N
      (Cc k (A.recenter D y)) (Cc k A) (hLF k (A.recenter D y) ⟨hAy, hk⟩) (hLF k A ⟨hA, hk⟩) 2 ht
      f 0 (by rw [add_zero]; exact hAy)
    rw [add_zero] at hpm
    exact hpm
  | letterMean t' n h π =>
    have hpm := ccov_pathMeanFlux_recenter hΛ hζ hcov hc π k hk hA y hAy hρ Mn.sX Mn.sZ Mn.N
      (Cc k (A.recenter D y)) (Cc k A) (hLF k (A.recenter D y) ⟨hAy, hk⟩) (hLF k A ⟨hA, hk⟩) n ht
      f 0 (by rw [add_zero]; exact hAy)
    rw [add_zero] at hpm
    by_cases h1 : h = 1
    · subst h1
      have hd := ccov_directFlux_recenter hcov ⟨k, hk⟩ hA y hAy ht (π.step ⟨0, by omega⟩).2.2
        {n} f 0
      rw [add_zero] at hd
      simp only [↓reduceDIte]
      rw [hpm, hd]
    · simp only [h1, ↓reduceDIte]
      rw [hpm]
  | letterCov t' n h a a' π =>
    have hl : A.WellSlotted := hA.2.2.1
    have hly : (A.recenter D y).WellSlotted := hAy.2.2.1
    have hU : IsOpen {w : Vec 2 | IsAdmissibleChain D b j₀ G.level k (A.recenter D (y + w))} :=
      (isOpen_admissible_recenter D b j₀ G.level k A).preimage
        (continuous_const.add continuous_id)
    refine ccov_letter_recenter (U := {w : Vec 2 |
        IsAdmissibleChain D b j₀ G.level k (A.recenter D (y + w))})
      (funext fun v => ccov_famMap_recenter hζ A hl y v t)
      (funext fun w => ccov_famMapInv_recenter hζ A hl y w t) (fun w => ?_)
      (famMapInv_famMap hζ A t y) (contDiff_famMapInv A t).continuous.continuousAt hU
      (by show IsAdmissibleChain D b j₀ G.level k (A.recenter D (y + 0)); rw [add_zero]; exact hAy)
      (fun g w hw => ?_) _ _ a a' f
    · rw [jacMatrix_famMap hζ _ hly, jacMatrix_famMap hζ _ hl, recenter_recenter D hζ]
    · exact ccov_pathMeanFlux_recenter hΛ hζ hcov hc π k hk hA y hAy hρ Mn.sX Mn.sZ Mn.N
        (Cc k (A.recenter D y)) (Cc k A) (hLF k (A.recenter D y) ⟨hAy, hk⟩) (hLF k A ⟨hA, hk⟩) n
        ht g w hw
end

/-! The finer outputs annihilate constants, the lifts of a family: **the order-`0` entries
of the lifts of the path family of a source vanish**.

`pcc_succ_window_data` is `Providers.succ_window_data` without its unused hypothesis
`∀ i, 0 < D.κ i` (which does not follow from the band chain beyond the terminal level); the body
is that of the original. `pcc_family_order_zero` applies `pcc_order_zero_vanish` to the lift
sequence of a path family on the admissible slow offsets of an admissible chain. -/

section
open Uniqueness Providers Providers.GenSem Providers.SuccWindow

private theorem pcc_entry_le_sum (F : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    |F i j| ≤ |F 0 0| + |F 0 1| + |F 1 0| + |F 1 1| := by
  have h00 := abs_nonneg (F 0 0)
  have h01 := abs_nonneg (F 0 1)
  have h10 := abs_nonneg (F 1 0)
  have h11 := abs_nonneg (F 1 1)
  fin_cases i <;> fin_cases j <;> simp <;> linarith

private theorem pcc_exists_entry_bound {F : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hF : Continuous F)
    (a b : ℝ) : ∃ M : ℝ, ∀ t ∈ Set.Icc a b, ∀ i j, |F t i j| ≤ M := by
  have hc : Continuous (fun t => |F t 0 0| + |F t 0 1| + |F t 1 0| + |F t 1 1|) := by
    have he : ∀ i j : Fin 2, Continuous (fun t => F t i j) := fun i j =>
      (continuous_apply j).comp ((continuous_apply i).comp hF)
    fun_prop
  obtain ⟨M, -, hM⟩ := exists_bound_Icc hc a b
  refine ⟨M, fun t ht i j => (pcc_entry_le_sum (F t) i j).trans ?_⟩
  have := hM t ht
  rwa [abs_of_nonneg (by positivity)] at this

/-- **Window data of the lift operators of a stage** (the statement of `Providers.succ_window_data`, without the
unused hypothesis on the diffusivities). -/
theorem pcc_succ_window_data {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, NormedSpace ℝ (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (hζ : IsFastProfile D.ζ) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) :
    AVRegularity.SuccWindowData D b j₀ Mn G := by
  intro h π k A hA X
  set ch := A.recenter D ((Mn.lenFactor * liftLength D G.level) • X) with hch
  set g := ch.geom D with hg
  have hC : ∀ r : ℝ, ContDiff ℝ 1 (fun p : ℝ × Vec 2 => g.1 p.1 p.2 r) :=
    geomC1_geom D hζ ch
  have hinv : AVRegularity.ChainGeometry.InvLaw g :=
    AVRegularity.ChainGeometry.invLaw_geomAux D _ _ _
      (AVRegularity.ChainGeometry.invLaw_base D _ _ _)
  set c := D.cellScaleSq G.level with hc
  let F : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t => ch.famJac D (c * t)
  have hFc : Continuous F :=
    (jac_continuous (f := fun u y => g.1 u y g.2.2) (hC g.2.2) g.2.1).comp
      (continuous_const.mul continuous_id)
  have hFdet : ∀ t, IsUnit (F t).det := fun t => jac_isUnit_det hinv hC (c * t) g.2.2 g.2.1
  have hAc : Continuous (fun t => (F t)⁻¹) := continuous_inv_of_det hFc hFdet
  set a₀ := D.slotStart G.level k / c
  set b₀ := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / c
  obtain ⟨M, hM⟩ := pcc_exists_entry_bound hFc a₀ b₀
  obtain ⟨N, hN⟩ := pcc_exists_entry_bound hAc a₀ b₀
  obtain ⟨Mv, hMv⟩ := ocPulseCellDrift_bound (α := D.α) (q := D.q) (Λ := D.Λ) hζ G.level
    (D.kap G.level) hA.2
  refine ⟨(4 * M ^ 2 + 1)⁻¹, 2 * N ^ 2, Mv, by positivity, fun t ht ξ => ?_,
    fun t ht i j => ?_, fun t _ z j => hMv t z j⟩
  · exact metric_elliptic (Matrix.nonsing_inv_mul _ (hFdet t)) (hM t ht) ξ
  · exact metric_entry_le (hN t ht) i j

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The order-`0` entries of the lifts of a path family vanish** for `(hh, n) ≠ (0, 0)`. -/
theorem pcc_family_order_zero (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) {G : GenStage D hr Dm b j₀}
    (Mn : SuccMenu) {h : ℕ} (π : StagePath G h) (k : ℤ) (hk : Odd k) {B : RealChain}
    (hB : IsAdmissibleChain D b j₀ G.level k B) {sX sZ N : ℕ}
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hC : IsLiftSequenceOn
      (ladderOmega D b j₀ G.level k B (Mn.lenFactor * liftLength D G.level))
      (familyLiftData D G.level k B (Mn.lenFactor * liftLength D G.level)
        (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)) sX sZ
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Cc) :
    ∀ hh ≤ h, ∀ n, (hh ≠ 0 ∨ n ≠ 0) →
      PccZero (ladderOmega D b j₀ G.level k B (Mn.lenFactor * liftLength D G.level))
        (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Cc hh n := by
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  have hab : D.slotStart G.level k / D.cellScaleSq G.level ≤
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) := by
    unfold OCData.slotStart
    apply div_le_div_of_nonneg_right _ hc.le
    nlinarith [ocTau_nonneg D.α D.q D.Λ G.level]
  have hW := succWindowData_of_target (pcc_succ_window_data hζ Mn G)
  exact pcc_order_zero_vanish _ _ _ hab (isOpen_ladderOmega D b j₀ G.level k B _)
    (fun X _ => hW h π k B ⟨hB, hk⟩ X) sX sZ N h Cc hC
end

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
