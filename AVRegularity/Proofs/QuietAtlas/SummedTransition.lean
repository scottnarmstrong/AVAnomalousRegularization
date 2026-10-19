-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.QuietAtlas.FirstSourceRenewal
public import AVRegularity.CycleComparison.Lift.LeftTermsFieldPostcomposition
import AVRegularity.CycleComparison.Reconstruction.Orders
public import AVRegularity.Proofs.QuietAtlas.PiolaGeom
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleComparison.Reconstruction.InvPiola
import AVRegularity.Families.QuietTransitionBridge
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Providers.QuietAtlas

/-! **The symmetrized renewal identity of a first source.** The coefficient arrays of
the first source are symmetric (`fluxCoeff` tests the operator on monomials), and the Piola
transport of a symmetric array is not symmetric. The exact transfer rule therefore fails for 𝖣,
but its symmetrization holds:
`fluxCoeff D_q (r+1) A 0 = wordSymmetrize (transportedCoeff (Dψ)⁻¹ n (fluxCoeff D_p · · 0) r · Y) A`
(`firstSourceFlux_coeff_renewal_sym`). Route: the operator identity at the centre
(`firstSourceFlux_native_renewal`), the array form of `D_p` with symmetric coefficients
(`arrOp_eq_sum_fluxCoeff`), and the flux identity of the transported coefficients
(`transportedCoeff_flux`) tested on the monomial `∏ (· - Y)(A j)`. -/

section
/-- Ordered derivatives commute with translations. -/
theorem orderedDerivative_comp_add_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (α : DerivativeWord2 m) (V : Vec 2 → E) (c : Vec 2) :
    orderedDerivative α (fun w => V (c + w)) = fun w => orderedDerivative α V (c + w) := by
  unfold orderedDerivative
  generalize List.ofFn α = l
  induction l generalizing V with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [show (fun x => fderiv ℝ (fun w => V (c + w)) x (basisVec i)) =
        fun w => (fun x => fderiv ℝ V x (basisVec i)) (c + w) from
      funext fun x => by rw [fderiv_comp_add_left]]
    exact ih (fun x => fderiv ℝ V x (basisVec i))

/-- **An array operator at the centre is the sum of its symmetric coefficients** against the
ordered derivatives. -/
theorem arrOp_eq_sum_fluxCoeff (K : ℕ) (Arr : Fin 2 → GenSem.CArr)
    (L : (Vec 2 → ℝ) → Vec 2 → Vec 2)
    (hL : ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → ∀ c, L g 0 c = GenSem.applyArr K (Arr c) g 0 0)
    {g : Vec 2 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    L g 0 = ∑ k ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 k,
      orderedDerivative α g 0 • fluxCoeff L (k + 1) α 0 := by
  funext c
  rw [hL g hg c]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold GenSem.applyArr
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkK : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hcoef : ∀ α : DerivativeWord2 k, fluxCoeff L (k + 1) α 0 c =
      ((k.factorial : ℝ))⁻¹ * ∑ σ : Equiv.Perm (Fin k), Arr c k (α ∘ σ) 0 0 := by
    intro α
    unfold fluxCoeff
    simp only [Nat.add_sub_cancel, Pi.smul_apply, smul_eq_mul]
    have h := hL (fun Y : Vec 2 => ∏ j, (Y - 0) (α j)) ((GenSem.contDiff_mono 0 α).of_le le_top) c
    have h2 : GenSem.applyArr K (Arr c) (fun Y : Vec 2 => ∏ j, (Y - 0) (α j)) 0 0 =
        ∑ σ : Equiv.Perm (Fin k), Arr c k (α ∘ σ) 0 0 := GenSem.applyArr_mono K (Arr c) 0 0 α hkK
    exact congrArg _ (h.trans h2)
  simp only [hcoef]
  have hperm : ∀ σ : Equiv.Perm (Fin k), ∑ α : DerivativeWord2 k,
      orderedDerivative α g 0 * Arr c k (α ∘ σ) 0 0 =
        ∑ α : DerivativeWord2 k, Arr c k α 0 0 * orderedDerivative α g 0 := by
    intro σ
    have e : ∀ α : DerivativeWord2 k, orderedDerivative α g 0 * Arr c k (α ∘ σ) 0 0 =
        (fun β : DerivativeWord2 k => Arr c k β 0 0 * orderedDerivative β g 0)
          (CycleComparison.Lift.wordPermutationEquiv σ α) := fun α => by
      change _ = Arr c k (α ∘ σ) 0 0 * orderedDerivative (α ∘ σ) g 0
      rw [CycleComparison.Lift.orderedDerivative_comp_perm α σ g hg, mul_comm]
    simp only [e]
    exact Equiv.sum_comp _ (fun β : DerivativeWord2 k => Arr c k β 0 0 * orderedDerivative β g 0)
  have hk0 : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  calc ∑ α : DerivativeWord2 k, Arr c k α 0 0 * orderedDerivative α g 0
      = ((k.factorial : ℝ))⁻¹ * ∑ _σ : Equiv.Perm (Fin k),
          ∑ α : DerivativeWord2 k, Arr c k α 0 0 * orderedDerivative α g 0 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
          ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]
    _ = ((k.factorial : ℝ))⁻¹ * ∑ σ : Equiv.Perm (Fin k), ∑ α : DerivativeWord2 k,
          orderedDerivative α g 0 * Arr c k (α ∘ σ) 0 0 := by
        simp only [hperm]
    _ = ∑ α : DerivativeWord2 k, orderedDerivative α g 0 *
          (((k.factorial : ℝ))⁻¹ * ∑ σ : Equiv.Perm (Fin k), Arr c k (α ∘ σ) 0 0) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => by ring

/-- Reindexing the orders `1, …, n` by `k + 1`, `k < n`. -/
theorem sum_Icc_one_eq_sum_range {R : Type*} [AddCommMonoid R] (F : ℕ → R) :
    ∀ n : ℕ, ∑ d ∈ Finset.Icc 1 n, F d = ∑ k ∈ Finset.range n, F (k + 1)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, sum_Icc_one_eq_sum_range F n]

/-- The symmetric coefficients of an array operator vanish above its order. -/
theorem fluxCoeff_eq_zero_of_arr (K : ℕ) (Arr : Fin 2 → GenSem.CArr)
    (L : (Vec 2 → ℝ) → Vec 2 → Vec 2)
    (hL : ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → ∀ c, L g 0 c = GenSem.applyArr K (Arr c) g 0 0)
    {d : ℕ} (hd : K < d - 1) (I : DerivativeWord2 (d - 1)) : fluxCoeff L d I 0 = 0 := by
  funext c
  unfold fluxCoeff
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  have h := hL (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) ((GenSem.contDiff_mono 0 I).of_le le_top) c
  have h2 : GenSem.applyArr K (Arr c) (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) 0 0 = 0 := by
    unfold GenSem.applyArr
    refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun α _ => ?_
    have hk' : k ≠ d - 1 := by
      have := Finset.mem_range.mp hk
      omega
    have h0 : orderedDerivative α (GenSem.mono 0 I) 0 = 0 := GenSem.orderedDerivative_mono_of_ne 0 I α hk'
    change Arr c k α 0 0 * orderedDerivative α (GenSem.mono 0 I) 0 = 0
    rw [h0, mul_zero]
  rw [h.trans h2, mul_zero]

variable (D : OCData)

/-- **The symmetrized renewal identity of a first source**, at the centre. On a quiet
overlap, if the first source of the description `p` is an array operator (`hArr`, e.g. by
`firstSourceFlux_applyArr`) whose coefficients vanish above the order `n`, then for `r < n` the
coefficient of the description `q` is the symmetrization of the Piola transport of those of
`p`. -/
theorem firstSourceFlux_coeff_renewal_sym {b : ℝ} {j₀ Dm m : ℕ} {ρ : ℝ} {N pc : ℕ} {s₀ : ℝ}
    {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)} (hm : 1 ≤ m)
    (p q : OddSlot) (Y z : Vec 2) (t : ℝ)
    (hSq : ∀ ch' w, contextStrain D m q.1 t ch' w = ch'.famStrain D t)
    (hSp : ∀ ch' w, contextStrain D m p.1 t ch' w = ch'.famStrain D t)
    (hdiag : ∀ g, (fun x => diagFluxCtx D b j₀ Dm (m + 1) ρ N Cc0 t
        ((nativeChain m q.1).recenter D Y) z g x) =ᶠ[𝓝 0]
      (fun x => diagFluxCtx D b j₀ Dm (m + 1) ρ N Cc0 t
        ((nativeChain m p.1).recenter D (renewalTransition D m p q Y)) z g x))
    (K : ℕ) (Arr : Fin 2 → GenSem.CArr)
    (hArr : ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → ∀ c,
      firstSourceFlux D b j₀ Dm (m + 1) ρ N pc s₀ Cc0 t
        ((nativeChain m p.1).recenter D (renewalTransition D m p q Y)) z g 0 c =
      GenSem.applyArr K (Arr c) g 0 0)
    (n : ℕ) (hvan : ∀ d, n < d → ∀ I : DerivativeWord2 (d - 1),
      fluxCoeff (firstSourceFlux D b j₀ Dm (m + 1) ρ N pc s₀ Cc0 t
        ((nativeChain m p.1).recenter D (renewalTransition D m p q Y)) z) d I 0 = 0)
    {r : ℕ} (hr : r < n) (A : DerivativeWord2 r) :
    fluxCoeff (firstSourceFlux D b j₀ Dm (m + 1) ρ N pc s₀ Cc0 t
        ((nativeChain m q.1).recenter D Y) z) (r + 1) A 0 =
      CycleComparison.Lift.wordSymmetrize (fun A' => transportedCoeff
        (chartInvJacobian (renewalTransition D m p q)) n
        (fun d I => fluxCoeff (firstSourceFlux D b j₀ Dm (m + 1) ρ N pc s₀ Cc0 t
          ((nativeChain m p.1).recenter D (renewalTransition D m p q Y)) z) d I 0) r A' Y) A := by
  set ψ := renewalTransition D m p q with hψ
  set ψi : Vec 2 → Vec 2 := fun y => D.flowOf (m - 1) (D.slotAnchor m q.1) y (D.slotAnchor m p.1)
    with hψi
  set Lq := firstSourceFlux D b j₀ Dm (m + 1) ρ N pc s₀ Cc0 t ((nativeChain m q.1).recenter D Y) z
    with hLq
  set Lp := firstSourceFlux D b j₀ Dm (m + 1) ρ N pc s₀ Cc0 t
    ((nativeChain m p.1).recenter D (ψ Y)) z with hLp
  set B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 := fun d I => fluxCoeff Lp d I 0 with hB
  set V : Vec 2 → ℝ := fun y => GenSem.mono 0 A (ψi y - Y) with hV
  set g : Vec 2 → ℝ := fun w => V (ψ Y + w) with hg
  -- the inverse pair and smoothness
  have hψψi : ∀ y, ψ (ψi y) = y := fun y => by
    simp only [hψ, hψi, renewalTransition]
    rw [flowOf_group, flowOf_self]
  have hψiψ : ∀ x, ψi (ψ x) = x := fun x => by
    simp only [hψ, hψi, renewalTransition]
    rw [flowOf_group, flowOf_self]
  have hψs : ContDiff ℝ (⊤ : ℕ∞) ψ := flowOf_contDiff D (m - 1) _ _
  have hψis : ContDiff ℝ (⊤ : ℕ∞) ψi := flowOf_contDiff D (m - 1) _ _
  have hVs : ContDiff ℝ (⊤ : ℕ∞) V :=
    ((GenSem.contDiff_mono 0 A).of_le le_top).comp (hψis.sub contDiff_const)
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := hVs.comp (contDiff_const.add contDiff_id)
  have hVψ : V ∘ ψ = GenSem.mono Y A := by
    funext x
    simp only [Function.comp_apply, hV, hψiψ, GenSem.mono, sub_zero]
  have hgV : ∀ {k : ℕ} (I : DerivativeWord2 k),
      orderedDerivative I g 0 = orderedDerivative I V (ψ Y) := fun I => by
    rw [hg, orderedDerivative_comp_add_left]
    simp only [add_zero]
  -- the operator identity at the centre
  have hop : Lq (GenSem.mono 0 A) 0 =
      ((jacMatrix (fun h => ψ (Y + h) - ψ Y) 0)⁻¹).mulVec (Lp g 0) :=
    firstSourceFlux_native_renewal D (pc := pc) (s₀ := s₀) hm p q Y z t hSq hSp hdiag
      (GenSem.mono 0 A)
  have hK : (jacMatrix (fun h => ψ (Y + h) - ψ Y) 0)⁻¹ = chartInvJacobian ψ Y := by
    have h := chartInvJacobian_translate ψ Y (ψ Y) 0
    rw [add_zero] at h
    exact h
  -- the array form of `D_p` at `g`, truncated to the orders `≤ n`
  set M := max n (K + 1)
  have htay : ∀ i₀ : Fin 2, Lp g 0 i₀ = ∑ d ∈ Finset.Icc 1 n, ∑ I : DerivativeWord2 (d - 1),
      orderedDerivative I V (ψ Y) * B d I i₀ := by
    intro i₀
    have h := congrFun (arrOp_eq_sum_fluxCoeff K Arr Lp hArr hgs) i₀
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [h]
    set F : ℕ → ℝ := fun d => ∑ I : DerivativeWord2 (d - 1),
      orderedDerivative I V (ψ Y) * B d I i₀ with hF
    have e1 : ∑ k ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 k,
        orderedDerivative α g 0 * fluxCoeff Lp (k + 1) α 0 i₀ =
        ∑ k ∈ Finset.range (K + 1), F (k + 1) :=
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun α _ => by rw [hgV]
    have e2 : ∑ k ∈ Finset.range (K + 1), F (k + 1) = ∑ k ∈ Finset.range M, F (k + 1) := by
      refine Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right _ _)) fun k hk hk' => ?_
      have hkK : K < k + 1 - 1 := by
        simp only [Finset.mem_range, not_lt] at hk hk'
        omega
      refine Finset.sum_eq_zero fun I _ => ?_
      simp only [hB, fluxCoeff_eq_zero_of_arr K Arr Lp hArr hkK I, Pi.zero_apply, mul_zero]
    have e3 : ∑ k ∈ Finset.range n, F (k + 1) = ∑ k ∈ Finset.range M, F (k + 1) := by
      refine Finset.sum_subset (Finset.range_subset_range.mpr (le_max_left _ _)) fun k hk hk' => ?_
      have hkn : n < k + 1 := by
        simp only [Finset.mem_range, not_lt] at hk hk'
        omega
      refine Finset.sum_eq_zero fun I _ => ?_
      simp only [hB, hvan (k + 1) hkn I, Pi.zero_apply, mul_zero]
    rw [e1, e2, ← e3, ← sum_Icc_one_eq_sum_range F n]
  -- the transported flux identity tested on the monomial
  funext a₀
  have tf := CycleComparison.Reconstruction.transportedCoeff_flux hψis hψs hψψi hψiψ hVs n B Y a₀
  rw [hVψ] at tf
  have hleft : ∑ r' ∈ Finset.range n, ∑ A' : DerivativeWord2 r',
      transportedCoeff (chartInvJacobian ψ) n B r' A' Y a₀ •
        orderedDerivative A' (GenSem.mono Y A) Y =
      ∑ σ : Equiv.Perm (Fin r), transportedCoeff (chartInvJacobian ψ) n B r (A ∘ σ) Y a₀ := by
    rw [Finset.sum_eq_single r]
    · have := GenSem.sum_orderedDerivative_mono Y A
        (fun A' => transportedCoeff (chartInvJacobian ψ) n B r A' Y a₀)
      rw [← this]
      exact Finset.sum_congr rfl fun A' _ => by simp only [smul_eq_mul, mul_comm]
    · intro r' _ hr'
      have := GenSem.sum_orderedDerivative_mono_of_ne Y A
        (fun A' => transportedCoeff (chartInvJacobian ψ) n B r' A' Y a₀) hr'
      rw [← this]
      exact Finset.sum_congr rfl fun A' _ => by simp only [smul_eq_mul, mul_comm]
    · intro h
      exact absurd (Finset.mem_range.mpr hr) h
  rw [hleft] at tf
  -- the left side of the claim
  have hfc : fluxCoeff Lq (r + 1) A 0 a₀ = ((r.factorial : ℝ))⁻¹ * Lq (GenSem.mono 0 A) 0 a₀ := by
    unfold fluxCoeff
    rfl
  rw [hfc, hop, hK]
  unfold CycleComparison.Lift.wordSymmetrize
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Fintype.card_perm, Fintype.card_fin]
  congr 1
  rw [tf]
  simp only [Matrix.mulVec, dotProduct, htay, Finset.mul_sum, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun i₀ _ => by ring
end

/-! **The symmetrized quiet Piola rule of a stage.** For a stage
presented by transfers and first sources (`QuietPresentation`), on a history-quiet set with QC2,
the Piola clause of the quiet transition holds after symmetrization in the derivative word
(`quietReanchorSym_of_presentation`):
* transfer edges satisfy the exact rule (`quietReanchor_transfer_edge`);
* first-source edges satisfy the symmetrized rule (`firstSourceFlux_coeff_renewal_sym`), given
  the array form of the first source at the native contexts (`FirstSourceArrayForm`, supplied by
  `firstSourceFlux_applyArr`).
The word-by-word clause is not asserted for 𝖣. -/

section
/-! ### Symmetrization algebra -/

theorem wordSymmetrize_smul {m : ℕ} (c : ℝ) (f : DerivativeWord2 m → Vec 2)
    (α : DerivativeWord2 m) :
    CycleComparison.Lift.wordSymmetrize (fun β => c • f β) α =
      c • CycleComparison.Lift.wordSymmetrize f α := by
  unfold CycleComparison.Lift.wordSymmetrize
  rw [← Finset.smul_sum, smul_comm]

theorem wordSymmetrize_idem {m : ℕ} (f : DerivativeWord2 m → Vec 2) (α : DerivativeWord2 m) :
    CycleComparison.Lift.wordSymmetrize (CycleComparison.Lift.wordSymmetrize f) α =
      CycleComparison.Lift.wordSymmetrize f α := by
  have hc : (Fintype.card (Equiv.Perm (Fin m)) : ℝ) ≠ 0 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    exact_mod_cast (Nat.factorial_pos m).ne'
  show (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ •
      ∑ σ : Equiv.Perm (Fin m), CycleComparison.Lift.wordSymmetrize f (α ∘ σ) = _
  simp only [CycleComparison.Lift.wordSymmetrize_comp_perm, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hc, one_smul]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The flux at a native label is the first-source array of its source. -/
theorem flux_native_first (hΛ : 1 ≤ D.Λ) {G : GenStage D hr Dm b j₀} (P : QuietPresentation G)
    {Mtop : ℕ} (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hnat : G.IsNatural Mtop)
    {v u : CompIn G.comps} {γ : G.fam.Γ v u} {lam ρ s₀ : ℝ} {N pc : ℕ}
    {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}
    (hsrc : P.source v u γ = .first lam ρ s₀ N pc Cc0) (c : OddSlot) (X : Vec 2) (t : ℝ)
    (z : Vec 2) (d : ℕ) (I : DerivativeWord2 (d - 1)) (hd : 2 ≤ d) :
    G.fam.flux c (G.actual c) v u γ d I t ((D.eps (G.level - 1))⁻¹ • X) z =
      (lam * (D.κ G.level * D.eps G.level ^ (d - 2))⁻¹) •
        fluxCoeff (firstSourceFlux D b j₀ Dm (G.level + 1) ρ N pc s₀ Cc0 t
          ((nativeChain G.level c.1).recenter D X) z) d I 0 := by
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  rw [P.represents c (G.actual c) v u γ d I t _ z hd, hsrc, hnat.2.2.1 c, smul_smul,
    mul_inv_cancel₀ hε, one_smul]
  split_ifs with h
  · rfl
  · exact absurd (isAdmissibleChain_nativeChain_recenter hi hj c X) h

/-- **The array form of the first sources** at the native contexts of the quiet times: the
regularity input of the symmetrized rule (supplied by `firstSourceFlux_applyArr`). -/
def FirstSourceArrayForm (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (U : Set ℝ) :
    Prop :=
  ∀ v u (γ : G.fam.Γ v u) (lam ρ s₀ : ℝ) (N pc : ℕ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)),
    P.source v u γ = .first lam ρ s₀ N pc Cc0 →
    ∀ (p : OddSlot) (t : ℝ), t ∈ U → t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
    ∀ X z : Vec 2, ∃ (K : ℕ) (Arr : Fin 2 → GenSem.CArr),
      ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → ∀ c,
        firstSourceFlux D b j₀ Dm (G.level + 1) ρ N pc s₀ Cc0 t
          ((nativeChain G.level p.1).recenter D X) z g 0 c = GenSem.applyArr K (Arr c) g 0 0

/-- **The symmetrized quiet Piola rule** of a stage presented by transfers and first sources:
the Piola clause of the quiet transition after symmetrization in the derivative
word. -/
theorem quietReanchorSym_of_presentation (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hb : 0 < b)
    (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (Mtop : ℕ) (U : Set ℝ)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hnat : G.IsNatural Mtop)
    (hU : IsHistoryQuiet D Mtop G.level U) (hQC2 : QuietReanchors G P U)
    (hArr : FirstSourceArrayForm G P U) :
    ∀ (p q : OddSlot), p ≠ q → ∀ t, t ∈ U →
      t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
      t ∈ ocPulseWindow D.α D.q D.Λ G.level q.1 →
      ∀ Y z : Vec 2, ∀ v u (γ : G.fam.Γ v u) r (A : DerivativeWord2 r),
        CycleComparison.Lift.wordSymmetrize (fun A' =>
          (D.kap G.level * D.eps G.level ^ (r - 1)) •
            G.fam.flux q (G.actual q) v u γ (r + 1) A' t ((D.eps (G.level - 1))⁻¹ • Y) z) A =
        CycleComparison.Lift.wordSymmetrize (fun A' =>
          transportedCoeff (chartInvJacobian (renewalTransition D G.level p q))
            (G.fam.identity v u γ).maxOrder
            (fun d I => G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
              p (G.actual p) v u γ d I t (renewalTransition D G.level p q Y) z) r A' Y) A := by
  intro p q hpq t ht htp htq Y z v u γ r A
  set n := (G.fam.identity v u γ).maxOrder with hn
  have hε : D.eps G.level ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hdim0 : ∀ d (I : DerivativeWord2 (d - 1)), ¬ (2 ≤ d ∧ d ≤ n) →
      G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) p (G.actual p) v u γ
        d I t (renewalTransition D G.level p q Y) z = 0 := by
    intro d I hd
    simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux,
      G.fam.flux_zero p (G.actual p) v u γ d I hd, smul_zero]
  rcases hsrc : P.source v u γ with ⟨lam, order, fop⟩ | ⟨lam, ρ, s₀, N, pc, Cc0⟩
  · -- a transfer: the exact rule
    have e := funext fun A' => quietReanchor_transfer_edge hΛ hζ G P Mtop U hi hj hnat hU hQC2
      hsrc p q hpq t ht htp htq Y z r A'
    exact congrArg (fun f => CycleComparison.Lift.wordSymmetrize f A) e
  -- a first source
  -- the order one
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hL0 : (fun A' : DerivativeWord2 0 => (D.kap G.level * D.eps G.level ^ (0 - 1)) •
        G.fam.flux q (G.actual q) v u γ (0 + 1) A' t ((D.eps (G.level - 1))⁻¹ • Y) z) = 0 := by
      funext A'
      rw [G.fam.flux_zero q (G.actual q) v u γ (0 + 1) A' (by omega), smul_zero, Pi.zero_apply]
    have hR0 : (fun A' : DerivativeWord2 0 => transportedCoeff
        (chartInvJacobian (renewalTransition D G.level p q)) n
        (fun d I => G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
          p (G.actual p) v u γ d I t (renewalTransition D G.level p q Y) z) 0 A' Y) = 0 := by
      funext A' a₀
      exact CycleComparison.Reconstruction.transportedCoeff_low_eq_zero _ _ _ rfl A' Y a₀
        fun I => hdim0 1 I (by omega)
    rw [hL0, hR0]
  set c := lam * D.kap G.level * (D.κ G.level)⁻¹ with hc
  have hscal : ∀ e : ℕ, (D.kap G.level * D.eps G.level ^ e) * (lam * (D.κ G.level * D.eps G.level ^ e)⁻¹) = c := by
    intro e
    rw [mul_inv]
    calc (D.kap G.level * D.eps G.level ^ e) * (lam * ((D.κ G.level)⁻¹ * (D.eps G.level ^ e)⁻¹))
        = lam * D.kap G.level * (D.κ G.level)⁻¹ * (D.eps G.level ^ e * (D.eps G.level ^ e)⁻¹) := by ring
      _ = c := by rw [mul_inv_cancel₀ (pow_ne_zero _ hε), mul_one]
  set Lq := firstSourceFlux D b j₀ Dm (G.level + 1) ρ N pc s₀ Cc0 t ((nativeChain G.level q.1).recenter D Y) z
  set Lp := firstSourceFlux D b j₀ Dm (G.level + 1) ρ N pc s₀ Cc0 t
    ((nativeChain G.level p.1).recenter D (renewalTransition D G.level p q Y)) z
  have hLHS : ∀ A' : DerivativeWord2 r, (D.kap G.level * D.eps G.level ^ (r - 1)) •
      G.fam.flux q (G.actual q) v u γ (r + 1) A' t ((D.eps (G.level - 1))⁻¹ • Y) z =
      c • fluxCoeff Lq (r + 1) A' 0 := by
    intro A'
    rw [flux_native_first hΛ P hi hj hnat hsrc q Y t z (r + 1) A' (by omega), smul_smul,
      show r + 1 - 2 = r - 1 by omega, hscal]
  have hRHS : ∀ A' : DerivativeWord2 r, transportedCoeff
      (chartInvJacobian (renewalTransition D G.level p q)) n
      (fun d I => G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
        p (G.actual p) v u γ d I t (renewalTransition D G.level p q Y) z) r A' Y =
      c • transportedCoeff (chartInvJacobian (renewalTransition D G.level p q)) n
        (fun d I => fluxCoeff Lp d I 0) r A' Y := by
    intro A'
    rw [← transportedCoeff_smul]
    refine transportedCoeff_congr _ _ (fun d hd _ I => ?_) A' Y
    simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux]
    rw [flux_native_first hΛ P hi hj hnat hsrc p (renewalTransition D G.level p q Y) t z d I
      (by omega), smul_smul, hscal]
  refine (congrArg (fun f => CycleComparison.Lift.wordSymmetrize f A) (funext hLHS)).trans
    (Eq.trans ?_ (congrArg (fun f => CycleComparison.Lift.wordSymmetrize f A) (funext hRHS)).symm)
  rw [wordSymmetrize_smul, wordSymmetrize_smul]
  by_cases hc0 : c = 0
  · rw [hc0, zero_smul, zero_smul]
  congr 1
  have hlam : lam ≠ 0 := fun h => hc0 (by rw [hc, h, zero_mul, zero_mul])
  have hκ : D.κ G.level ≠ 0 := fun h => hc0 (by rw [hc, h, inv_zero, mul_zero])
  by_cases hrn : r < n
  swap
  · -- the orders above the identity vanish on both sides
    have hq0 : (fun A' : DerivativeWord2 r => fluxCoeff Lq (r + 1) A' 0) = 0 := by
      funext A'
      have h := hLHS A'
      rw [G.fam.flux_zero q (G.actual q) v u γ (r + 1) A' (by omega), smul_zero] at h
      exact (smul_eq_zero.mp h.symm).resolve_left hc0
    have hp0 : (fun A' : DerivativeWord2 r => transportedCoeff
        (chartInvJacobian (renewalTransition D G.level p q)) n
        (fun d I => fluxCoeff Lp d I 0) r A' Y) = 0 := by
      funext A' a₀
      exact CycleComparison.Reconstruction.transportedCoeff_eq_zero_of_lt _ _ _ A' Y a₀
        (by omega)
    rw [hq0, hp0]
  -- the symmetrized identity of the first source
  have hvan : ∀ d, n < d → ∀ I : DerivativeWord2 (d - 1), fluxCoeff Lp d I 0 = 0 := by
    intro d hd I
    have h := flux_native_first hΛ P hi hj hnat hsrc p (renewalTransition D G.level p q Y) t z d I
      (by omega)
    rw [G.fam.flux_zero p (G.actual p) v u γ d I (by omega)] at h
    exact (smul_eq_zero.mp h.symm).resolve_left
      (mul_ne_zero hlam (inv_ne_zero (mul_ne_zero hκ (pow_ne_zero _ hε))))
  obtain ⟨K, Arr, hK⟩ := hArr v u γ lam ρ s₀ N pc Cc0 hsrc p t ht htp
    (renewalTransition D G.level p q Y) z
  have hSq : ∀ ch' w, contextStrain D G.level q.1 t ch' w = ch'.famStrain D t :=
    fun ch' w => contextStrain_of_labelShear_zero D
      (labelShear_eq_zero_of_quiet D hΛ hζ q.2 (hU.1 ht)) ch' w
  have hSp : ∀ ch' w, contextStrain D G.level p.1 t ch' w = ch'.famStrain D t :=
    fun ch' w => contextStrain_of_labelShear_zero D
      (labelShear_eq_zero_of_quiet D hΛ hζ p.2 (hU.1 ht)) ch' w
  have hrel : ∀ k : ℤ, ocCutoff D.α D.q D.Λ (G.level + 1) k t ≠ 0 →
      (∀ θ, D.relDisp G.level p.1 (D.slotAnchor (G.level + 1) k) t θ = 0) ∧
      (∀ θ, D.relDisp G.level p.1 t (D.slotAnchor (G.level + 1) k) θ = 0) ∧
      (∀ θ, D.relDisp G.level q.1 (D.slotAnchor (G.level + 1) k) t θ = 0) ∧
      (∀ θ, D.relDisp G.level q.1 t (D.slotAnchor (G.level + 1) k) θ = 0) := fun k hkt => by
    have hsk := slotAnchor_mem_availInterval D Mtop (G.level + 1) k
    have htk : t ∈ availInterval D Mtop (G.level + 1) k := mem_availInterval_of_ocCutoff D hΛ hkt
    exact ⟨relDisp_eq_zero_of_historyQuiet D hΛ hζ hU ht hkt p.2 hsk htk,
      relDisp_eq_zero_of_historyQuiet D hΛ hζ hU ht hkt p.2 htk hsk,
      relDisp_eq_zero_of_historyQuiet D hΛ hζ hU ht hkt q.2 hsk htk,
      relDisp_eq_zero_of_historyQuiet D hΛ hζ hU ht hkt q.2 htk hsk⟩
  have hL : ∀ n' ∈ insert 2 (Set.Icc 3 (N + 1)), ∀ k : ℤ, Odd k →
      ocCutoff D.α D.q D.Λ (G.level + 1) k t ≠ 0 → ∀ f,
      diagLabelFlux D Dm (G.level + 1) ρ Cc0 k
          (((nativeChain G.level p.1).recenter D (renewalTransition D G.level p q Y)).appendChild D k t z)
          n' t f =ᶠ[𝓝 0]
      diagLabelFlux D Dm (G.level + 1) ρ Cc0 k
          (((nativeChain G.level q.1).recenter D Y).appendChild D k t z) n' t f := by
    intro n' hn' k hk hkt f
    have h2 := hQC2 v u γ p q hpq t ht htp htq k hk hkt n' (by rw [hsrc]; exact hn') Y z f
    rw [hsrc] at h2
    exact h2
  have hcore := fun A' => firstSourceFlux_coeff_renewal_sym D hi p q Y z t hSq hSp
    (fun g => diagFluxCtx_native_renewal D hΛ hζ hb hi hj p q Y z t htp htq hrel hL g)
    K Arr hK n hvan hrn A'
  rw [show (fun A' : DerivativeWord2 r => fluxCoeff Lq (r + 1) A' 0) = _ from funext hcore,
    wordSymmetrize_idem]
end

end AVRegularity.Providers.QuietAtlas
end

section
open Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.QuietAtlas

/-! **The quiet matching of a transfer stage** (`quietMatching_of_allTransfer`). For a stage
whose identities are all transfers of finer outputs (the weak passages), the quiet matching
clauses hold on every window, with fast independence on any history-quiet set `S`. The inputs are
the natural renewal structure, slot transversality, the carrier start, and the carried
finer-operator invariant (`FinerHistoryInvariant`). The source phase (`quietSourcePhase`), the
Piola leaf for transfers (`quietReanchorTransfer_of_allTransfer`) and the clauses
`QuietPhaseBlind`, `QuietReanchors` from the carried invariant are proved. The structural set is
`ocTrimmedQuiet`.

`quietMatching_of_local` is the assembly with the two algebra facts for the given stage and
presentation, instead of the statements for every stage: the Piola statement for every stage
fails for first sources, while it holds for transfer presentations. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **Quiet matching from the two algebra facts of one stage and presentation.** -/
theorem quietMatching_of_local (G : GenStage D hr Dm b j₀) (Mtop : ℕ) (S Q W : Set ℝ)
    (hΛ : 1 ≤ D.Λ) (hnat : G.IsNatural Mtop) (hQo : outputOverlapTimes D G.level ⊆ Q)
    (phase : ∀ p (ch : StageCtx D b j₀ G.level p) t, t ∈ S ∪ Q →
      t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
      ∀ v u (γ : G.fam.Γ v u) d (I : DerivativeWord2 (d - 1)) (Y z z' : Vec 2),
        G.fam.flux p ch v u γ d I t Y z = G.fam.flux p ch v u γ d I t Y z')
    (piola : ∀ (p q : OddSlot), p ≠ q → ∀ t, t ∈ S ∪ Q →
      t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
      t ∈ ocPulseWindow D.α D.q D.Λ G.level q.1 →
      ∀ Y z : Vec 2, ∀ v u (γ : G.fam.Γ v u) r (A : DerivativeWord2 r),
        (D.kap G.level * D.eps G.level ^ (r - 1)) •
            G.fam.flux q (G.actual q) v u γ (r + 1) A t ((D.eps (G.level - 1))⁻¹ • Y) z =
          transportedCoeff (chartInvJacobian (renewalTransition D G.level p q))
            (G.fam.identity v u γ).maxOrder
            (fun d I => G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
              p (G.actual p) v u γ d I t (renewalTransition D G.level p q Y) z) r A Y)
    (hT : G.IsSlotTransverse) : QuietMatchingOn G S W := by
  have hout (p : OddSlot) :
      (G.fam.piece p).output = ocPulseWindow D.α D.q D.Λ G.level p.1 := (hnat.1 p).2.1
  refine ⟨⟨naturalQuietAtlas G hnat W, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro p q hpq hlabel hmeet
    exact ⟨hpq, hlabel, hmeet⟩
  · intro p q hpq t ht Y
    exact ht
  · intro p q hpq c c' hctx
    rcases hctx with ⟨rfl, rfl⟩
    have hU : ∀ tY ∈ (naturalQuietTransition G hnat W p q).overlap, tY.1 ∈ S ∪ Q := by
      intro tY htY
      exact Or.inr (hQo ⟨p.1, q.1, p.2, q.2, fun h => hpq.1 (Subtype.ext h),
        (hout p) ▸ htY.1.2, (hout q) ▸ htY.2⟩)
    refine ChartedFamily.isQuietTransition_of_wordwise
      (fun tY htY v u γ d I z z' => ?_) (fun tY htY z v u γ r A => ?_)
    · exact ⟨phase p (G.actual p) tY.1 (hU tY htY) ((hout p) ▸ htY.1.2)
        v u γ d I _ z z',
        phase q (G.actual q) tY.1 (hU tY htY) ((hout q) ▸ htY.2)
        v u γ d I _ z z'⟩
    · exact piola p q hpq.1 tY.1 (hU tY htY) ((hout p) ▸ htY.1.2)
        ((hout q) ▸ htY.2) tY.2 z v u γ r A
  · intro p q hpq hmeet
    exact ⟨rfl, rfl⟩
  · intro p q hpq c c' hctx
    exact hctx
  · intro k p c v u γ d I t ht X z s
    by_cases hpk : p = k
    · subst p
      exact hT k c v u γ d I t ((hout k) ▸ ht.2) X z s
    · have hpulse : t ∈ ocPulseWindow D.α D.q D.Λ G.level k.1 := by
        have hτ := Construction.Stream.ocTau_pos hΛ (α := D.α) (q := D.q) (m := G.level)
        constructor <;> linarith only [ht.1.1.1, ht.1.1.2, hτ]
      have htQ : t ∈ Q := hQo ⟨p.1, k.1, p.2, k.2,
        fun h => hpk (Subtype.ext h), (hout p) ▸ ht.2, hpulse⟩
      exact phase p c t (Or.inr htQ) ((hout p) ▸ ht.2) v u γ d I X _ _
  · intro p c v u γ d I t ht X z z'
    exact phase p c t (Or.inl ht.1.1) ((hout p) ▸ ht.2) v u γ d I X z z'

/-- **The quiet matching of a transfer stage.** -/
theorem quietMatching_of_allTransfer (hb : 0 < b) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (hall : P.AllTransfer) (Mtop : ℕ)
    (S W : Set ℝ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (CH Υ : ℝ) (hCH : 1 ≤ CH)
    (hstart : IsCarrierStart D.α D.q D.Λ b CH Υ j₀) (hnat : G.IsNatural Mtop)
    (hS : IsHistoryQuiet D Mtop G.level S) (hF : FinerHistoryInvariant G P Mtop)
    (hT : G.IsSlotTransverse) : QuietMatchingOn G S W := by
  have hQ := isHistoryQuiet_ocTrimmedQuiet hΛ hCH hstart Mtop G.level hj
  have hSQ := hS.union hQ
  have hQC1 := quietPhaseBlind_of_finerHistory hb hΛ hζ G P Mtop _ hSQ hF
  have hQC2 := quietReanchors_of_finerHistory hb hΛ hζ G P Mtop _ hi hj hSQ hF
  exact quietMatching_of_local G Mtop S (ocTrimmedQuiet D G.level) W hΛ hnat
    (outputOverlapTimes_subset_ocTrimmedQuiet hΛ hζ G.level)
    (quietPhaseTransfer_of_source (quietSourcePhase D) G P Mtop _ hΛ hζ hSQ hQC1)
    (quietReanchorTransfer_of_allTransfer hΛ hζ G P Mtop _ hi hj hnat hSQ hQC2 hall) hT

/-- **The atlas clauses of the quiet matching**, from the two algebra facts of one stage and
presentation on the structural set alone (no slot transversality, no fast-independence set). -/
theorem quietAtlas_of_local (G : GenStage D hr Dm b j₀) (Mtop : ℕ) (Q W : Set ℝ)
    (hnat : G.IsNatural Mtop) (hQo : outputOverlapTimes D G.level ⊆ Q)
    (phase : ∀ p (ch : StageCtx D b j₀ G.level p) t, t ∈ Q →
      t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
      ∀ v u (γ : G.fam.Γ v u) d (I : DerivativeWord2 (d - 1)) (Y z z' : Vec 2),
        G.fam.flux p ch v u γ d I t Y z = G.fam.flux p ch v u γ d I t Y z')
    (piola : ∀ (p q : OddSlot), p ≠ q → ∀ t, t ∈ Q →
      t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
      t ∈ ocPulseWindow D.α D.q D.Λ G.level q.1 →
      ∀ Y z : Vec 2, ∀ v u (γ : G.fam.Γ v u) r (A : DerivativeWord2 r),
        (D.kap G.level * D.eps G.level ^ (r - 1)) •
            G.fam.flux q (G.actual q) v u γ (r + 1) A t ((D.eps (G.level - 1))⁻¹ • Y) z =
          transportedCoeff (chartInvJacobian (renewalTransition D G.level p q))
            (G.fam.identity v u γ).maxOrder
            (fun d I => G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
              p (G.actual p) v u γ d I t (renewalTransition D G.level p q Y) z) r A Y) :
    ∃ T : G.fam.Atlas,
      T.IsConsecutiveClosed W ∧
      T.CoversQuiet (ocQuietTimes D.α D.q D.Λ D.ζ G.level) W ∧
      T.IsQuiet (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) ∧
      (∀ p q (hpq : T.adjacent p q),
        ((G.fam.piece p).output ∩ (G.fam.piece q).output ∩ W).Nonempty →
        T.sameCtx p q hpq (G.actual p) (G.actual q)) ∧
      (∀ p q (hpq : T.adjacent p q) c c', T.sameCtx p q hpq c c' →
        c = G.actual p ∧ c' = G.actual q) := by
  have hout (p : OddSlot) :
      (G.fam.piece p).output = ocPulseWindow D.α D.q D.Λ G.level p.1 := (hnat.1 p).2.1
  refine ⟨naturalQuietAtlas G hnat W, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q hpq hlabel hmeet
    exact ⟨hpq, hlabel, hmeet⟩
  · intro p q hpq t ht Y
    exact ht
  · intro p q hpq c c' hctx
    rcases hctx with ⟨rfl, rfl⟩
    have hU : ∀ tY ∈ (naturalQuietTransition G hnat W p q).overlap, tY.1 ∈ Q := by
      intro tY htY
      exact hQo ⟨p.1, q.1, p.2, q.2, fun h => hpq.1 (Subtype.ext h),
        (hout p) ▸ htY.1.2, (hout q) ▸ htY.2⟩
    refine ChartedFamily.isQuietTransition_of_wordwise
      (fun tY htY v u γ d I z z' => ?_) (fun tY htY z v u γ r A => ?_)
    · exact ⟨phase p (G.actual p) tY.1 (hU tY htY) ((hout p) ▸ htY.1.2) v u γ d I _ z z',
        phase q (G.actual q) tY.1 (hU tY htY) ((hout q) ▸ htY.2) v u γ d I _ z z'⟩
    · exact piola p q hpq.1 tY.1 (hU tY htY) ((hout p) ▸ htY.1.2)
        ((hout q) ▸ htY.2) tY.2 z v u γ r A
  · intro p q hpq hmeet
    exact ⟨rfl, rfl⟩
  · intro p q hpq c c' hctx
    exact hctx

/-- **The atlas clauses of the quiet matching of a transfer stage.** -/
theorem quietAtlas_of_allTransfer (hb : 0 < b) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (hall : P.AllTransfer) (Mtop : ℕ)
    (W : Set ℝ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (CH Υ : ℝ) (hCH : 1 ≤ CH)
    (hstart : IsCarrierStart D.α D.q D.Λ b CH Υ j₀) (hnat : G.IsNatural Mtop)
    (hF : FinerHistoryInvariant G P Mtop) :
    ∃ T : G.fam.Atlas,
      T.IsConsecutiveClosed W ∧
      T.CoversQuiet (ocQuietTimes D.α D.q D.Λ D.ζ G.level) W ∧
      T.IsQuiet (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) ∧
      (∀ p q (hpq : T.adjacent p q),
        ((G.fam.piece p).output ∩ (G.fam.piece q).output ∩ W).Nonempty →
        T.sameCtx p q hpq (G.actual p) (G.actual q)) ∧
      (∀ p q (hpq : T.adjacent p q) c c', T.sameCtx p q hpq c c' →
        c = G.actual p ∧ c' = G.actual q) := by
  have hQ := isHistoryQuiet_ocTrimmedQuiet hΛ hCH hstart Mtop G.level hj
  have hQC1 := quietPhaseBlind_of_finerHistory hb hΛ hζ G P Mtop _ hQ hF
  have hQC2 := quietReanchors_of_finerHistory hb hΛ hζ G P Mtop _ hi hj hQ hF
  exact quietAtlas_of_local G Mtop (ocTrimmedQuiet D G.level) W hnat
    (outputOverlapTimes_subset_ocTrimmedQuiet hΛ hζ G.level)
    (quietPhaseTransfer_of_source (quietSourcePhase D) G P Mtop _ hΛ hζ hQ hQC1)
    (quietReanchorTransfer_of_allTransfer hΛ hζ G P Mtop _ hi hj hnat hQ hQC2 hall)

end AVRegularity.Providers.QuietAtlas
end

section
open Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Providers.QuietAtlas

/-! **One-passage preservation of the carried quiet invariant for transfer stages**
(`quietHistoryPreservation_of_allTransfer_core`, for a presentation by transfers). Two
admissible contexts with
the same history geometry give the same flux germs. Near the label `0` both recentered contexts
are admissible (`recenter_eventually`), and recentering keeps the history geometry. In the
transfer array, the parent Jacobians agree on the pulse window, and the appended children of an
active finer slot have the same history geometry on its availability interval, which lies in the
parent's (`histEq_appendChild`, `availInterval_child_subset`). So their Jacobians agree. These
children are admissible (`appendChild_admissible`, from the carrier start), so the carried
finer-operator invariant gives the same finer coefficients (`transferAt_eq_of_histEq`). -/

variable (D : OCData)

theorem invLaw_geom (ch : RealChain) : ChainGeometry.InvLaw (ch.geom D) :=
  ChainGeometry.invLaw_geomAux D _ _ _ (ChainGeometry.invLaw_base D _ _ _)

/-- Appended children inherit the history geometry. -/
theorem histEq_appendChild {C C' : RealChain} (hl : C.WellSlotted) (hl' : C'.WellSlotted)
    (hctx : C.ctxLevel = C'.ctxLevel) (hslot : C.slot = C'.slot) {I J : Set ℝ}
    (hh : HistEq (C.geom D) (C'.geom D) I) (k : ℤ) (t : ℝ) (ζ : Vec 2)
    (hs : D.slotAnchor (C.ctxLevel + 1) k ∈ I) (hJ : J ⊆ I) :
    HistEq ((C.appendChild D k t ζ).geom D) ((C'.appendChild D k t ζ).geom D) J := by
  rw [GenSem.appendChild_geom D C hl, GenSem.appendChild_geom D C' hl', ← hctx, ← hslot]
  exact histEq_childGeom D (invLaw_geom D C) (invLaw_geom D C') hh _ _ _ hs hJ

/-- **Equal history geometry gives equal transfer arrays.** -/
theorem transferAt_eq_of_histEq (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) {b : ℝ} (hb : 0 < b)
    {j₀ : ℕ}
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    {Mtop m : ℕ} (hm : m < Mtop) {p : ℤ} {C C' : RealChain}
    (hC : IsAdmissibleChain D b j₀ m p C) (hC' : IsAdmissibleChain D b j₀ m p C')
    (hh : HistEq (C.geom D) (C'.geom D) (availInterval D Mtop m p)) {fop : FamFluxOp}
    (hF : ∀ k : ℤ, Odd k → ∀ (A A' : RealChain), IsAdmissibleChain D b j₀ (m + 1) k A →
      IsAdmissibleChain D b j₀ (m + 1) k A' → SameHistoryGeometry D Mtop (m + 1) k A A' →
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ (m + 1) k, ∀ f : Vec 2 → ℝ,
        fop k t A f =ᶠ[𝓝 0] fop k t A' f)
    (lam : ℝ) (order : ℕ) {t : ℝ} (htp : t ∈ ocPulseWindow D.α D.q D.Λ m p) (z : Vec 2) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) :
    transferAt D (m + 1) p lam order fop t C z d I =
      transferAt D (m + 1) p lam order fop t C' z d I := by
  have hl : C.WellSlotted := hC.2.2.1
  have hl' : C'.WellSlotted := hC'.2.2.1
  have hctx : C.ctxLevel = m := hC.1
  have hctx' : C'.ctxLevel = m := hC'.1
  have hslot : C.slot = p := hC.2.2.2.1
  have hslot' : C'.slot = p := hC'.2.2.2.1
  have htI : t ∈ availInterval D Mtop m p := ocPulseWindow_subset_availInterval D Mtop m p htp
  unfold transferAt
  refine congrArg (HSMul.hSMul _) (finsum_congr fun k => finsum_congr fun hk => ?_)
  have hsch : IsScheduledIn D m k p := by simpa using hk.2
  by_cases hkt : ocCutoff D.α D.q D.Λ (m + 1) k t = 0
  · rw [hkt, zero_smul, zero_smul]
  have hJ := availInterval_child_subset D hm hk.1 hsch
  have hskJ := slotAnchor_mem_availInterval D Mtop (m + 1) k
  have htJ : t ∈ availInterval D Mtop (m + 1) k := mem_availInterval_of_ocCutoff D hΛ hkt
  have hsI : ∀ C₀ : RealChain, C₀.ctxLevel = m →
      D.slotAnchor (C₀.ctxLevel + 1) k ∈ availInterval D Mtop m p := fun C₀ h0 => by
    rw [h0]; exact hJ hskJ
  -- the transfer Jacobians
  have hK : (fun h => (childTransition D k t (C.recenter D h)
        (z + (D.eps (m + 1 - 1))⁻¹ • h))⁻¹) =
      (fun h => (childTransition D k t (C'.recenter D h)
        (z + (D.eps (m + 1 - 1))⁻¹ • h))⁻¹) := by
    funext h
    have hrh := histEq_recenter D hζ hl hl' hh h
    have hct : (C.recenter D h).ctxLevel = m := by rw [recenter_ctxLevel, hctx]
    have happ := histEq_appendChild D (recenter_wellSlotted D hl h) (recenter_wellSlotted D hl' h)
      (by rw [recenter_ctxLevel, recenter_ctxLevel, hctx, hctx'])
      (by rw [recenter_slot, recenter_slot, hslot, hslot']) hrh k t
      (z + (D.eps (m + 1 - 1))⁻¹ • h) (hsI _ hct) hJ
    unfold childTransition
    rw [famJac_eq_of_histEq D happ htJ, famJac_eq_of_histEq D hrh htI]
  -- the finer coefficients
  have hA := GenSem.appendChild_admissible D hΛ hζ hb hstart m p C hC k hk.1 hsch t hkt z
  have hA' := GenSem.appendChild_admissible D hΛ hζ hb hstart m p C' hC' k hk.1 hsch t hkt z
  have happ := histEq_appendChild D hl hl' (by rw [hctx, hctx']) (by rw [hslot, hslot']) hh k t z
    (hsI _ hctx) hJ
  have hsame := (histEq_iff_sameHistory D _ _ happ.1).mp happ
  have hB : (fun d I => fluxCoeff (fop k t (C.appendChild D k t z)) d I 0) =
      (fun d I => fluxCoeff (fop k t (C'.appendChild D k t z)) d I 0) := by
    funext d' I'
    unfold fluxCoeff
    rw [(hF k hk.1 _ _ hA hA' hsame t (GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero
      (Construction.Stream.ocTau_pos hΛ) hkt) _).eq_of_nhds]
  rw [hK, hB]

variable {D}
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **One-passage preservation of the carried invariant for transfer stages** (minimal
hypotheses: the carrier start bound). -/
theorem quietHistoryPreservation_of_allTransfer_core (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (Mtop : ℕ) (hlt : G.level < Mtop)
    (hall : P.AllTransfer) (hF : FinerHistoryInvariant G P Mtop) :
    StageHistoryInvariant G Mtop := by
  intro p ch ch' hsame t ht v u γ d I z
  by_cases hd : 2 ≤ d ∧ d ≤ (G.fam.identity v u γ).maxOrder
  swap
  · rw [G.fam.flux_zero p ch v u γ d I hd, G.fam.flux_zero p ch' v u γ d I hd]
  obtain ⟨lam, order, fop, hsrc⟩ := hall v u γ
  have hl : ch.1.WellSlotted := ch.2.2.2.1
  have hl' : ch'.1.WellSlotted := ch'.2.2.2.1
  have hanc : (ch.1.geom D).2.2 = (ch'.1.geom D).2.2 := by
    rw [geom_anchor D ch.1 hl, geom_anchor D ch'.1 hl', ch.2.1, ch.2.2.2.2.1, ch'.2.1,
      ch'.2.2.2.2.1]
  have hh := (histEq_iff_sameHistory D ch.1 ch'.1 hanc).mpr hsame
  have htend : Tendsto (fun Y : Vec 2 => D.eps (G.level - 1) • Y) (𝓝 0) (𝓝 0) := by
    have := (continuous_const_smul (D.eps (G.level - 1))).tendsto (0 : Vec 2)
    rwa [smul_zero] at this
  have hev := (htend.eventually (GenSem.recenter_eventually D hζ b j₀ G.level p.1 ch.2)).and
    (htend.eventually (GenSem.recenter_eventually D hζ b j₀ G.level p.1 ch'.2))
  have hF' := hF v u γ 0 (by rw [hsrc]; rfl)
  rw [hsrc] at hF'
  simp only [QuietSource.finer] at hF'
  filter_upwards [hev] with Y hY
  rw [P.represents p ch v u γ d I t Y z hd.1, P.represents p ch' v u γ d I t Y z hd.1]
  split_ifs with h1 h2 h2
  · rw [hsrc]
    simp only [QuietSource.array]
    exact transferAt_eq_of_histEq D hΛ hζ hb hstart hlt hY.1 hY.2
      (histEq_recenter D hζ hl hl' hh _)
      (fun k hk A A' hA hA' hs t' ht' f => hF' ⟨k, hk⟩ ⟨A, hA⟩ ⟨A', hA'⟩ hs t' ht' f)
      lam order ht z d I
  · exact absurd hY.2 h2
  · exact absurd hY.1 h1
  · rfl

end AVRegularity.Providers.QuietAtlas
end

section
open Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.QuietAtlas

/-! **The quiet transition in the summed form for stages with first sources**
(the transport identity summed over the permutations of the word; the first source keeps its
symmetric coefficient).

* `natural_quietTransition_sum_of_presentation`: on every stored transition of the natural quiet
  atlas, with the actual contexts matched, it gives fast independence on the overlap and the
  transport identity summed over `σ : Equiv.Perm (Fin r)` with the word `A ∘ σ` (the two
  conjuncts of `IsQuietTransition`). It is proved from
  `quietReanchorSym_of_presentation` by clearing the factor `1/r!` of `wordSymmetrize`
  (`sum_perm_eq_of_wordSymmetrize_eq`).
* `quietMatching_of_natural_quiet`: the atlas clause `QuietMatchingOn` from any proof that the
  natural quiet atlas is quiet.
* `naturalQuietAtlas_isQuiet_of_presentation`: the natural quiet atlas of a stage with first
  sources is quiet, each transition built by the summed constructor
  `ChartedFamily.isQuietTransition_of_summed`.
* `quietMatching_of_firstSource`: the atlas clause of a stage with first sources. Transfer
  families use `isQuietTransition_of_wordwise`. -/

/-- Clearing the factor of `wordSymmetrize`. -/
theorem sum_perm_eq_of_wordSymmetrize_eq {m : ℕ} (f g : DerivativeWord2 m → Vec 2)
    (A : DerivativeWord2 m)
    (hfg : CycleComparison.Lift.wordSymmetrize f A = CycleComparison.Lift.wordSymmetrize g A) :
    ∑ σ : Equiv.Perm (Fin m), f (A ∘ σ) = ∑ σ : Equiv.Perm (Fin m), g (A ∘ σ) := by
  have hc : (Fintype.card (Equiv.Perm (Fin m)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 Fintype.card_ne_zero
  unfold CycleComparison.Lift.wordSymmetrize at hfg
  exact smul_right_injective _ (inv_ne_zero hc) hfg

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The summed quiet transition of a stage with first sources**, on every stored transition of
the natural quiet atlas: fast independence on the overlap, and the transport identity summed over
the permutations of the word. -/
theorem natural_quietTransition_sum_of_presentation
    (hsource : QuietSourcePhaseStatement (hr := hr) (D := D) (Dm := Dm) (b := b) (j₀ := j₀))
    (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (Mtop : ℕ) (S W : Set ℝ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hb : 0 < b) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (CH Υ : ℝ) (hCH : 1 ≤ CH) (hstart : IsCarrierStart D.α D.q D.Λ b CH Υ j₀)
    (hnat : G.IsNatural Mtop) (hS : IsHistoryQuiet D Mtop G.level S)
    (hQC1 : QuietPhaseBlind G P (S ∪ ocTrimmedQuiet D G.level))
    (hQC2 : QuietReanchors G P (S ∪ ocTrimmedQuiet D G.level))
    (hArr : FirstSourceArrayForm G P (S ∪ ocTrimmedQuiet D G.level)) :
    ∀ p q (hpq : (naturalQuietAtlas G hnat W).adjacent p q) c c',
      (naturalQuietAtlas G hnat W).sameCtx p q hpq c c' →
      (∀ tY ∈ ((naturalQuietAtlas G hnat W).tr p q hpq).overlap, ∀ v u (γ : G.fam.Γ v u) d I,
        ∀ z z' : Vec 2,
          G.fam.flux p c v u γ d I tY.1
              ((D.eps (G.level - 1))⁻¹ • ((naturalQuietAtlas G hnat W).tr p q hpq).Υ tY.2) z =
            G.fam.flux p c v u γ d I tY.1
              ((D.eps (G.level - 1))⁻¹ • ((naturalQuietAtlas G hnat W).tr p q hpq).Υ tY.2) z' ∧
          G.fam.flux q c' v u γ d I tY.1 ((D.eps (G.level - 1))⁻¹ • tY.2) z =
            G.fam.flux q c' v u γ d I tY.1 ((D.eps (G.level - 1))⁻¹ • tY.2) z') ∧
      ∀ tY ∈ ((naturalQuietAtlas G hnat W).tr p q hpq).overlap, ∀ z : Vec 2,
        ∀ v u (γ : G.fam.Γ v u) (r : ℕ) (A : DerivativeWord2 r),
          ∑ σ : Equiv.Perm (Fin r),
              (D.kap G.level * D.eps G.level ^ (r - 1)) •
                G.fam.flux q c' v u γ (r + 1) (A ∘ σ) tY.1 ((D.eps (G.level - 1))⁻¹ • tY.2) z =
            ∑ σ : Equiv.Perm (Fin r),
              transportedCoeff (chartInvJacobian ((naturalQuietAtlas G hnat W).tr p q hpq).Υ)
                (G.fam.identity v u γ).maxOrder
                (fun d I => G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
                  p c v u γ d I tY.1 (((naturalQuietAtlas G hnat W).tr p q hpq).Υ tY.2) z)
                r (A ∘ σ) tY.2 := by
  have hQ := isHistoryQuiet_ocTrimmedQuiet hΛ hCH hstart Mtop G.level hj
  have hQo := outputOverlapTimes_subset_ocTrimmedQuiet hΛ hζ G.level (D := D)
  have phase := quietPhaseTransfer_of_source hsource G P Mtop (S ∪ ocTrimmedQuiet D G.level) hΛ hζ
    (hS.union hQ) hQC1
  have sym := quietReanchorSym_of_presentation hΛ hζ hb G P Mtop (S ∪ ocTrimmedQuiet D G.level)
    hi hj hnat (hS.union hQ) hQC2 hArr
  have hout (p : OddSlot) :
      (G.fam.piece p).output = ocPulseWindow D.α D.q D.Λ G.level p.1 := (hnat.1 p).2.1
  intro p q hpq c c' hctx
  rcases hctx with ⟨rfl, rfl⟩
  have hU : ∀ tY ∈ (naturalQuietTransition G hnat W p q).overlap,
      tY.1 ∈ S ∪ ocTrimmedQuiet D G.level := by
    intro tY htY
    exact Or.inr (hQo ⟨p.1, q.1, p.2, q.2, fun h => hpq.1 (Subtype.ext h),
      (hout p) ▸ htY.1.2, (hout q) ▸ htY.2⟩)
  refine ⟨fun tY htY v u γ d I z z' => ⟨phase p (G.actual p) tY.1 (hU tY htY)
      ((hout p) ▸ htY.1.2) v u γ d I _ z z', phase q (G.actual q) tY.1 (hU tY htY)
      ((hout q) ▸ htY.2) v u γ d I _ z z'⟩, fun tY htY z v u γ r A => ?_⟩
  exact sum_perm_eq_of_wordSymmetrize_eq _ _ A (sym p q hpq.1 tY.1 (hU tY htY)
    ((hout p) ▸ htY.1.2) ((hout q) ▸ htY.2) tY.2 z v u γ r A)

/-- **The atlas clause from a quiet natural atlas.** All clauses of `QuietMatchingOn` except
the quiet transitions are discharged as for transfers. The quiet transitions are the input
`hquiet`. -/
theorem quietMatching_of_natural_quiet
    (hsource : QuietSourcePhaseStatement (hr := hr) (D := D) (Dm := Dm) (b := b) (j₀ := j₀))
    (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (Mtop : ℕ) (S W : Set ℝ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hj : j₀ ≤ G.level)
    (CH Υ : ℝ) (hCH : 1 ≤ CH) (hstart : IsCarrierStart D.α D.q D.Λ b CH Υ j₀)
    (hnat : G.IsNatural Mtop) (hS : IsHistoryQuiet D Mtop G.level S)
    (hQC1 : QuietPhaseBlind G P (S ∪ ocTrimmedQuiet D G.level)) (hT : G.IsSlotTransverse)
    (hquiet : (naturalQuietAtlas G hnat W).IsQuiet (D.kap G.level) (D.eps G.level)
      (D.eps (G.level - 1))) : QuietMatchingOn G S W := by
  have hQ := isHistoryQuiet_ocTrimmedQuiet hΛ hCH hstart Mtop G.level hj
  have hQo := outputOverlapTimes_subset_ocTrimmedQuiet hΛ hζ G.level (D := D)
  have phase := quietPhaseTransfer_of_source hsource G P Mtop (S ∪ ocTrimmedQuiet D G.level) hΛ hζ
    (hS.union hQ) hQC1
  have hout (p : OddSlot) :
      (G.fam.piece p).output = ocPulseWindow D.α D.q D.Λ G.level p.1 := (hnat.1 p).2.1
  refine ⟨⟨naturalQuietAtlas G hnat W, fun p q hpq hlabel hmeet => ⟨hpq, hlabel, hmeet⟩,
    fun p q hpq t ht Y => ht, hquiet, fun p q hpq hmeet => ⟨rfl, rfl⟩,
    fun p q hpq c c' hctx => hctx⟩, ?_, ?_⟩
  · intro k p c v u γ d I t ht X z s
    by_cases hpk : p = k
    · subst p
      exact hT k c v u γ d I t ((hout k) ▸ ht.2) X z s
    · have hpulse : t ∈ ocPulseWindow D.α D.q D.Λ G.level k.1 := by
        have hτ := Construction.Stream.ocTau_pos hΛ (α := D.α) (q := D.q) (m := G.level)
        constructor <;> linarith only [ht.1.1.1, ht.1.1.2, hτ]
      have htQ : t ∈ ocTrimmedQuiet D G.level := hQo ⟨p.1, k.1, p.2, k.2,
        fun h => hpk (Subtype.ext h), (hout p) ▸ ht.2, hpulse⟩
      exact phase p c t (Or.inr htQ) ((hout p) ▸ ht.2) v u γ d I X _ _
  · intro p c v u γ d I t ht X z z'
    exact phase p c t (Or.inl ht.1.1) ((hout p) ▸ ht.2) v u γ d I X z z'

/-- **The natural quiet atlas of a stage with first sources is quiet**: every transition
is built by the summed constructor from `natural_quietTransition_sum_of_presentation`. -/
theorem naturalQuietAtlas_isQuiet_of_presentation
    (hsource : QuietSourcePhaseStatement (hr := hr) (D := D) (Dm := Dm) (b := b) (j₀ := j₀))
    (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (Mtop : ℕ) (S W : Set ℝ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hb : 0 < b) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (CH Υ : ℝ) (hCH : 1 ≤ CH) (hstart : IsCarrierStart D.α D.q D.Λ b CH Υ j₀)
    (hnat : G.IsNatural Mtop) (hS : IsHistoryQuiet D Mtop G.level S)
    (hQC1 : QuietPhaseBlind G P (S ∪ ocTrimmedQuiet D G.level))
    (hQC2 : QuietReanchors G P (S ∪ ocTrimmedQuiet D G.level))
    (hArr : FirstSourceArrayForm G P (S ∪ ocTrimmedQuiet D G.level)) :
    (naturalQuietAtlas G hnat W).IsQuiet (D.kap G.level) (D.eps G.level)
      (D.eps (G.level - 1)) := by
  have h := natural_quietTransition_sum_of_presentation hsource G P Mtop S W hΛ hζ hb hi hj CH Υ
    hCH hstart hnat hS hQC1 hQC2 hArr
  intro p q hpq c c' hc
  exact ChartedFamily.isQuietTransition_of_summed (h p q hpq c c' hc).1 (h p q hpq c c' hc).2

/-- **The atlas clause of a stage with first sources**, its quiet transitions built by the
summed constructor. -/
theorem quietMatching_of_firstSource
    (hsource : QuietSourcePhaseStatement (hr := hr) (D := D) (Dm := Dm) (b := b) (j₀ := j₀))
    (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (Mtop : ℕ) (S W : Set ℝ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hb : 0 < b) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (CH Υ : ℝ) (hCH : 1 ≤ CH) (hstart : IsCarrierStart D.α D.q D.Λ b CH Υ j₀)
    (hnat : G.IsNatural Mtop) (hS : IsHistoryQuiet D Mtop G.level S)
    (hQC1 : QuietPhaseBlind G P (S ∪ ocTrimmedQuiet D G.level))
    (hQC2 : QuietReanchors G P (S ∪ ocTrimmedQuiet D G.level))
    (hArr : FirstSourceArrayForm G P (S ∪ ocTrimmedQuiet D G.level)) (hT : G.IsSlotTransverse) :
    QuietMatchingOn G S W :=
  quietMatching_of_natural_quiet hsource G P Mtop S W hΛ hζ hj CH Υ hCH hstart hnat hS hQC1 hT
    (naturalQuietAtlas_isQuiet_of_presentation hsource G P Mtop S W hΛ hζ hb hi hj CH Υ hCH
      hstart hnat hS hQC1 hQC2 hArr)

end AVRegularity.Providers.QuietAtlas
end
