import Submission.Work.Mixed.Bridge.CoreF3
import Submission.Work.Mixed.Hist2979_HalitZiyaV2_Hc
import Submission.Work.XHostT.HFW2979.GeomInstW
import Submission.Work.XHostT.Inst.S2979_HalitZiyaV2_Hc_Facts
/-!
# afc-cut: the A-fc FULL-cut (#2979Fc) engine theorem on the WARP network (the real #2979 provider words)

aA-data's `HFTest2979HW.lean` (x-inst's `HFTest2979W.lean` with design A's numbers) with fc-engine's FULL cut
(`HFTest3945FW.lean`): the heads of the warp network (x-inst's `XHostTW.xnetGeomW_heads_first`; every head is the
block of the 48 A4 lines `a4Lines` of its frame `a4Base`) are removed entirely, so the cut lines of a head are ALL its
48 lines (`cutSF`), and `bph_cutF` is **the 48-line cut fact**, the `hz` of `MX.cut_heads_full` on #2979's words (by
`MX.bph_cast`: the head directions `zGeom` are those lines, cast to `Fin 48`).  The warp network, its heads-first
certificate, `zGeom`, `cutA`, `a4Lines` and `a4Base` are the same modules design A (L2979H) and design B (L3945F)
use; `bph_cutF` is fc-engine's lemma, restated in this namespace for #2979's 74 replicas.
* `engine2979Fc_geomW`: any head set `hb` (never hosted, remaining climb 48), data facts `hU`, `hcutF`, `hLlen`, `hσ`,
  `hα`;
* `engine2979Fc_geomW_auto`: 74 replicas, classes `Fin 112`, the canonical head set `headBins S`, the head count in
  Finset form (16,576), positive residuals, any unit profile `U` with `hcutF`;
* `engine2979Fc_geomW_unit`: the same with `U = MX.unit2979Fc` (`hcutF2979Fc`).
Seam exponent `1 - 1788704501/10^12` (DFT figure 1.7887045e-3, e-r45m1's convention).
afc-cut (wht45/afc, 20 Oct 2026); prepared with assistance from Claude.  No `sorry`.
-/
-- changed for the head-cut extension (1959540039/1000000000000); see Submission.lean

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace PB
namespace HFTest2979_HalitZiyaV2_Hc_W
open Binary Matrix Finset RAM SS CB RF BR GF GX BC B401 XHost XHostR XHostD XHostT XHostTW

noncomputable section

universe U

variable {H Sl C : Type} [Fintype H] [DecidableEq H] [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}

/-- **The head-cut (#2979_HalitZiyaV2_Hc) engine theorem from the geometric WARP network and the table data.** -/
theorem engine2979_HalitZiyaV2_Hc_geomW (I : GInvW H (Fin 112) Sl C Ok) (Ic : Fin 74 → Fin 9 → GInvW H (Fin 112) Sl C Ok)
    (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv) (base : Fin 112 → OBase H) (l : H) (hbase : ∀ t, I.tv t = (base t).v l)
    (hH : Fintype.card H = 9) (hOk : ∀ (n : ℕ) (d : Orth (BC.LC (Fin 8) H l)), Ok (win401N l hH n d))
    (S : HostSchedT 74 Sl (Fin 112)) (hfit : S.fits (resIcW Ic))
    (hpos : ∀ ρ l' q, 0 < resIcW Ic ρ l' q)
    (h2 : (Finset.univ.filter (fun p : Fin 74 × Bool × Fin 112 => S.hrem p.1 0 p.2 = 16)).card = 16572)
    (h3 : (Finset.univ.filter (fun p : Fin 74 × Bool × Fin 112 => S.hrem p.1 2 p.2 = 32)).card = 16576)
    (h4 : (Finset.univ.filter (fun p : Fin 74 × Bool × Fin 112 => S.hrem p.1 4 p.2 = 48)).card = 12177)
    (hU : ∀ φ, unitPriceTW Ic S φ = listCost φ MX.unit2979_HalitZiyaV2_Hc)
    (m : Bool) (cl : Paint) {ι : Type U} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2 ^ k i * envelope (1 - (195954003901:ℝ)/(10:ℝ)^14) (k i)) := by
  -- the canonical head sets of the three kinds and their sizes
  have e2 : headBinsK S 0 16 = Finset.univ.filter (fun p : Fin 74 × Bool × Fin 112 => S.hrem p.1 0 p.2 = 16) :=
    headBinsK_eq S (resIcW Ic) hfit hpos 0
  have e3 : headBinsK S 2 32 = Finset.univ.filter (fun p : Fin 74 × Bool × Fin 112 => S.hrem p.1 2 p.2 = 32) :=
    headBinsK_eq S (resIcW Ic) hfit hpos 2
  have e4 : headBinsK S 4 48 = Finset.univ.filter (fun p : Fin 74 × Bool × Fin 112 => S.hrem p.1 4 p.2 = 48) :=
    headBinsK_eq S (resIcW Ic) hfit hpos 4
  have c2 : (headBinsK S 0 16).card = 16572 := by rw [e2]; exact h2
  have c3 : (headBinsK S 2 32).card = 16576 := by rw [e3]; exact h3
  have c4 : (headBinsK S 4 48).card = 12177 := by rw [e4]; exact h4
  -- the heads-first certificate of the three kinds
  obtain ⟨body, hP, hc, hk⟩ := xnetGeomW_heads_first3 I Ic hIc base l hbase hH hOk S hfit
    (headBinsK S 0 16) (headBinsK S 2 32) (headBinsK S 4 48)
    (headBinsK_unh S 0 16)
    (headBinsK_unh S 2 32)
    (headBinsK_unh S 4 48)
    (headBinsK_full S 0 16) (headBinsK_full S 2 32)
    (headBinsK_full S 4 48)
  -- the three head lists: duplicate free and pairwise disjoint
  have hd23 := headsLP_disj (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) (p := 2) (q := 3)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num) (headBinsK S 0 16) (headBinsK S 2 32)
  have hd24 := headsLP_disj (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) (p := 2) (q := 4)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num) (headBinsK S 0 16) (headBinsK S 4 48)
  have hd34 := headsLP_disj (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) (p := 3) (q := 4)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num) (headBinsK S 2 32) (headBinsK S 4 48)
  have hL : (headsLP (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) (nR := 74) 2 (headBinsK S 0 16)
      ++ headsLP (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) 3 (headBinsK S 2 32)
      ++ headsLP (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) 4 (headBinsK S 4 48)).Nodup := by
    refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨headsLP_nodup 2 _, headsLP_nodup 3 _, hd23⟩,
      headsLP_nodup 4 _, fun a ha b hb => ?_⟩
    rcases List.mem_append.mp ha with h | h
    · exact hd24 a h b hb
    · exact hd34 a h b hb
  have hG : 1 ≤ Fintype.card (Orth (BC.LC (Fin 8) H l)) := Orth.card_pos
  have hl2 : (headsLP (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) (nR := 74) 2 (headBinsK S 0 16)).length
      = Fintype.card (Orth (BC.LC (Fin 8) H l)) * 16572 := by
    rw [headsLP_length (p := 2) ⟨by norm_num, by norm_num⟩, c2, Nat.mul_comm]
  have hl3 : (headsLP (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) (nR := 74) 3 (headBinsK S 2 32)).length
      = Fintype.card (Orth (BC.LC (Fin 8) H l)) * 16576 := by
    rw [headsLP_length (p := 3) ⟨by norm_num, by norm_num⟩, c3, Nat.mul_comm]
  have hl4 : (headsLP (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) (nR := 74) 4 (headBinsK S 4 48)).length
      = Fintype.card (Orth (BC.LC (Fin 8) H l)) * 12177 := by
    rw [headsLP_length (p := 4) ⟨by norm_num, by norm_num⟩, c4, Nat.mul_comm]
  exact full_engine3 Sum.inl Sum.inl_injective _ _ _ hL (zG2 base l hH) (zG3 base l hH) (zG4 base l hH)
    (zG2_indep base l hH) (zG3_indep base l hH) (zG4_indep base l hH) (cutA3 base l) (cutS3 l)
    (fun r hr x => bph_cut2 base l hH _ r hr x) (fun r hr x => bph_cut3 base l hH _ r hr x)
    (fun r hr x => bph_cut4 base l hH _ r hr x)
    (fun r hr => cutS3_card2 l hH _ r hr) (fun r hr => cutS3_card3 l hH _ r hr) (fun r hr => cutS3_card4 l hH _ r hr)
    body hP hk MX.cut2979_HalitZiyaV2_Hc (fun φ => by rw [hc φ, hU φ]) MX.hcut2979_HalitZiyaV2_Hc hl2 hl3 hl4
    (Inst.card_live2979_HalitZiyaV2_Hc (Orth (BC.LC (Fin 8) H l))) hG (by norm_num) (card_LC401 l hH)
    (fun q hq => (MX.cut2979_HalitZiyaV2_Hc_proper q hq).2) MX.rate2979_HalitZiyaV2_Hc_moment
    (by norm_num [MX.zRate2979_HalitZiyaV2_Hc]) (by norm_num [MX.zRate2979_HalitZiyaV2_Hc]) (by norm_num) m cl k v

end
end HFTest2979_HalitZiyaV2_Hc_W
end PB
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.PB.HFTest2979_HalitZiyaV2_Hc_W.engine2979_HalitZiyaV2_Hc_geomW
