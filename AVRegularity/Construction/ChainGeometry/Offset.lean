-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Construction.Gen.ParShift
import AVRegularity.CycleReference.SingleModeFlux
import AVenhance.Statements.FlowDefs.FlowIsFlow
import AVenhance.Infra.Flow.Laws

/-! Offset-flow identities of real chains:
the transverse shear is invariant along its own direction, so the relative displacement obeys
the inverse law `d(u; s, θ + d(s; u, θ)) = -d(s; u, θ)`; every family geometry of a chain obeys
the inverse law `𝔛(a, 𝔛(b, w, a), b) = w` of its offset flow; appending a child is one more
`childGeom` step. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.CycleReference

namespace AVRegularity

namespace ChainGeometry

/-- The transverse shear velocity does not change along its own direction. -/
theorem ocShearVel_add_smul_self (α q : ℝ) (Λ m : ℕ) (k : ℤ) (y y' : Vec 2) (c : ℝ) :
    ocShearVel α q Λ m k (y + c • ocShearVel α q Λ m k y') = ocShearVel α q Λ m k y := by
  by_cases h1 : k % 4 = 1
  · simp only [ocShearVel_horizontal h1]
    simp
  · by_cases h3 : k % 4 = 3
    · simp only [ocShearVel_vertical h3]
      simp
    · have h0 : ∀ z, ocShearVel α q Λ m k z = 0 := by
        intro z
        have hψ : ocShear α q Λ m k = fun _ => 0 := by
          funext w
          rw [ocShear_sine_formula]
          simp [h1, h3]
        change AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (ocShear α q Λ m k) z) = 0
        have hg : AVenhance.spaceGrad (fun _ : Vec 2 => (0 : ℝ)) z = 0 := by
          funext i; simp [AVenhance.spaceGrad]
        rw [hψ, hg, Matrix.mulVec_zero]
      simp only [h0, smul_zero, add_zero]

variable (D : OCData)

/-- The inverse law of the relative displacement. -/
theorem relDisp_inverse (i : ℕ) (p : ℤ) (u s : ℝ) (θ : Vec 2) :
    D.relDisp i p u s (θ + D.relDisp i p s u θ) = -D.relDisp i p s u θ := by
  unfold OCData.relDisp
  by_cases he : D.eps i = 0
  · simp [he]
  · have h1 : D.eps i • (D.eps i)⁻¹ • ((∫ v in u..s, ocPulse D.α D.q D.Λ D.ζ i p v) •
        ocShearVel D.α D.q D.Λ i p (D.eps i • θ)) =
        (∫ v in u..s, ocPulse D.α D.q D.Λ D.ζ i p v) •
          ocShearVel D.α D.q D.Λ i p (D.eps i • θ) := by
      rw [smul_smul, mul_inv_cancel₀ he, one_smul]
    rw [smul_add, h1, ocShearVel_add_smul_self, intervalIntegral.integral_symm u s, neg_smul,
      smul_neg]

/-- The inverse law of an offset flow. -/
def InvLaw (g : ChainGeom) : Prop := ∀ a b : ℝ, ∀ w : Vec 2, g.1 a (g.1 b w a) b = w

theorem invLaw_base (k : ℕ) (x : Vec 2) (s : ℝ) : InvLaw (D.flowOf k, x, s) := by
  intro a b w
  have hL := (D.hΦ k).vel_lipschitz
  have hX := AVenhance.flow_isFlow _ (D.hΦ k).vel_continuous hL
  change streamFlow (D.Φ k) (D.hΦ k) a (streamFlow (D.Φ k) (D.hΦ k) b w a) b = w
  unfold streamFlow
  rw [AVenhance.Infra.Flow.flow_group_law _ hL hX w a b a]
  exact hX.1 w a

theorem invLaw_childGeom (k : ℕ) (pk : ℤ) (s' : ℝ) (c : ChainChild) {g : ChainGeom}
    (hg : InvLaw g) : InvLaw (D.childGeom k pk s' c g) := by
  intro a b w
  simp only [OCData.childGeom]
  set γ := c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)
  set y₁ := g.1 g.2.2 w a
  set θ₁ := (D.eps k)⁻¹ • y₁ + γ
  have hz : g.1 g.2.2 (g.1 b (y₁ + D.eps k • D.relDisp k pk b a θ₁) g.2.2) b =
      y₁ + D.eps k • D.relDisp k pk b a θ₁ := hg _ _ _
  rw [hz]
  by_cases he : D.eps k = 0
  · have h0 : ∀ u r θ, D.relDisp k pk u r θ = 0 := by
      intro u r θ; simp [OCData.relDisp, he]
    simp only [h0, smul_zero, add_zero]
    exact hg _ _ _
  · have harg : (D.eps k)⁻¹ • (y₁ + D.eps k • D.relDisp k pk b a θ₁) + γ =
        θ₁ + D.relDisp k pk b a θ₁ := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ he, one_smul]
      simp only [θ₁]; abel
    rw [harg, relDisp_inverse, smul_neg, add_neg_cancel_right]
    exact hg _ _ _

theorem invLaw_geomAux : ∀ (cs : List ChainChild) (k : ℕ) (sl : List ℤ) {g : ChainGeom},
    InvLaw g → InvLaw (D.geomAux k sl cs g)
  | [], k, sl, g, hg => by
    match sl with
    | [] => exact hg
    | [_] => exact hg
    | _ :: _ :: _ => exact hg
  | c :: cs, k, sl, g, hg => by
    match sl with
    | [] => exact hg
    | [_] => exact hg
    | pk :: pk1 :: rest =>
      exact invLaw_geomAux cs (k + 1) (pk1 :: rest) (invLaw_childGeom D k pk _ c hg)

theorem geomAux_append (p' : ℤ) (c : ChainChild) : ∀ (cs : List ChainChild) (k : ℕ)
    (sl : List ℤ) (g : ChainGeom), sl.length = cs.length + 1 →
    D.geomAux k (sl ++ [p']) (cs ++ [c]) g =
      D.childGeom (k + cs.length) (sl.getLastD 0) (D.slotAnchor (k + cs.length + 1) p') c
        (D.geomAux k sl cs g)
  | [], k, sl, g, hl => by
    match sl, hl with
    | [pk], _ => simp [OCData.geomAux]
  | c₀ :: cs, k, sl, g, hl => by
    match sl, hl with
    | pk :: pk1 :: rest, hl =>
      have hl' : (pk1 :: rest).length = cs.length + 1 := by simpa using hl
      have ih := geomAux_append p' c cs (k + 1) (pk1 :: rest)
        (D.childGeom k pk (D.slotAnchor (k + 1) pk1) c₀ g) hl'
      simp only [List.cons_append, OCData.geomAux] at ih ⊢
      rw [ih]
      have e1 : k + 1 + cs.length = k + (cs.length + 1) := by omega
      rw [e1]
      rfl

end ChainGeometry

end AVRegularity
