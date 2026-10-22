import Submission.Work.Mixed.Rate2979_HalitZiyaV2_Hc
/-!
# The histogram bookkeeping of the FULL cut of A-fc (suffix 2979Fc): unit -> body -> cut (nothing to split)

afc-cut (wht45/afc, 20 Oct 2026), fc-rate's `Hist3945F.lean` with A-fc's numbers.  A-fc (the hub's word of PR #2979,
T74 clock, with the re-solved fill u1-2979sep of round wht45/fullcut) has the unit profile `unit2979Fc` (its
PROFILE.json, sha256 5df79411...); its 16,576 rank-48 blocks are ALL literal heads (children 8/10), and every other
block has rank at most 23.
* M1's `cut_heads_full` removes the 16,576 heads from `headWord ++ body`: the body has the profile `body2979Fc`
  (`hbody2979Fc`), which has no rank-48 block (`body2979Fc_no48`);
* M1's `splitWord 24 24` therefore has NOTHING to split: by `hist_splitWord 24 24` the histogram is unchanged
  (`hsplit2979Fc`, stated in exactly the shape of the right-hand side of `hist_splitWord` with `a = b = 24` and `w` =
  the body), and the body profile IS R5's cut profile (`body2979Fc_eq_cut`);
* `hcut2979Fc`: unit -> cut in one identity; `mass2979Fc`: the rank mass drops by exactly 48 x 16,576;
* separation: `cut2979Fc_sep` (every paid rank < 25, in fact <= 23), `cut2979Fc_no48`, `cut2979Fc_no24`;
* negatives (`decide`): one head more breaks `hbody2979Fc`; the unit profile is not the cut profile.
Prepared with assistance from Claude.  No `sorry`.
-/
-- changed for the head-cut extension (1959540039/1000000000000); see Submission.lean

namespace OAI.PowerSaving.MX
open BlockAccounting

/-- the ranks that occur in the two profiles, and the split ranks 24, 1 -/
def keys2979_HalitZiyaV2_Hc : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 10, 16, 24, 25, 32, 48]

theorem histFn_eq_zero_of_keys2979_HalitZiyaV2_Hc {l : List (ℕ × ℕ)} {K : List ℕ} (hl : ∀ q ∈ l, q.1 ∈ K) {r : ℕ}
    (hr : r ∉ K) : histFn l r = 0 := by
  by_contra hne
  have := mem_keys_of_histFn_ne_zero l r hne
  unfold keys at this
  rw [List.mem_toFinset, List.mem_map] at this
  obtain ⟨q, hq, rfl⟩ := this
  exact hr (hl q hq)

theorem unit2979_HalitZiyaV2_Hc_keys : ∀ q ∈ unit2979_HalitZiyaV2_Hc, q.1 ∈ keys2979_HalitZiyaV2_Hc := by decide
theorem cut2979_HalitZiyaV2_Hc_keys : ∀ q ∈ cut2979_HalitZiyaV2_Hc, q.1 ∈ keys2979_HalitZiyaV2_Hc := by decide

/-- **Unit -> cut**: the heads go, every block of rank 25 becomes one of rank 24 and one of rank 1. -/
theorem hcut2979_HalitZiyaV2_Hc : ∀ r, histFn cut2979_HalitZiyaV2_Hc r + (if r = 16 then 16572 else 0) + (if r = 32 then 16576 else 0)
    + (if r = 48 then 12177 else 0) + (if r = 25 then histFn unit2979_HalitZiyaV2_Hc 25 else 0)
    = histFn unit2979_HalitZiyaV2_Hc r + (if r = 24 then histFn unit2979_HalitZiyaV2_Hc 25 else 0)
      + (if r = 1 then histFn unit2979_HalitZiyaV2_Hc 25 else 0) := by
  intro r
  by_cases hr : r ∈ keys2979_HalitZiyaV2_Hc
  · have h : ∀ r ∈ keys2979_HalitZiyaV2_Hc, histFn cut2979_HalitZiyaV2_Hc r + (if r = 16 then 16572 else 0) + (if r = 32 then 16576 else 0)
        + (if r = 48 then 12177 else 0) + (if r = 25 then histFn unit2979_HalitZiyaV2_Hc 25 else 0)
        = histFn unit2979_HalitZiyaV2_Hc r + (if r = 24 then histFn unit2979_HalitZiyaV2_Hc 25 else 0)
          + (if r = 1 then histFn unit2979_HalitZiyaV2_Hc 25 else 0) := by
      decide
    exact h r hr
  · have h16 : r ≠ 16 := fun h => hr (by subst h; decide)
    have h32 : r ≠ 32 := fun h => hr (by subst h; decide)
    have h48 : r ≠ 48 := fun h => hr (by subst h; decide)
    have h25 : r ≠ 25 := fun h => hr (by subst h; decide)
    have h24 : r ≠ 24 := fun h => hr (by subst h; decide)
    have h1 : r ≠ 1 := fun h => hr (by subst h; decide)
    rw [histFn_eq_zero_of_keys2979_HalitZiyaV2_Hc cut2979_HalitZiyaV2_Hc_keys hr, histFn_eq_zero_of_keys2979_HalitZiyaV2_Hc unit2979_HalitZiyaV2_Hc_keys hr,
      if_neg h16, if_neg h32, if_neg h48, if_neg h25, if_neg h24, if_neg h1]

/-- The unit's rank mass is unchanged by the table (it is #2979's: 65,088 x 74). -/
theorem unit2979_HalitZiyaV2_Hc_mass : (unit2979_HalitZiyaV2_Hc.map fun b => b.1 * b.2).sum = 65088 * 74 := by decide

/-- Separation of the cut: every paid rank is below the smallest target 25 (at most 24). -/
theorem cut2979_HalitZiyaV2_Hc_sep : ∀ b ∈ cut2979_HalitZiyaV2_Hc, 1 ≤ b.1 ∧ b.1 < 25 := by decide

end OAI.PowerSaving.MX

#print axioms OAI.PowerSaving.MX.hcut2979_HalitZiyaV2_Hc
#print axioms OAI.PowerSaving.MX.unit2979_HalitZiyaV2_Hc_mass
