import Submission.Work.XHostT.KHist
import Submission.Work.XHostT.Data.H2979_HalitZiyaV2_Hc.GlobC0
import Submission.Work.XHostT.Data.H2979_HalitZiyaV2_Hc.GlobC1
import Submission.Work.XHostT.Data.H2979_HalitZiyaV2_Hc.GlobC2
import Submission.Work.XHostT.Data.H2979_HalitZiyaV2_Hc.GlobC3
import Submission.Work.XHostT.Data.H2979_HalitZiyaV2_Hc.GlobC4
import Submission.Work.XHostT.Data.H2979_HalitZiyaV2_Hc.GlobC5
/-! p-hostck mk_parts.py: global facts of H2979_HalitZiyaV2_Hc: remainder histogram {0: 96652, 1: 3893, 3: 3310, 7: 1, 9: 2, 10: 1, 16: 16572, 32: 16576, 48: 12177}, residual sums {0: 3283, 1: 3283} (6 chunks of 111 kinds). -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OAI.PowerSaving.XHostT.K.DH2979_HalitZiyaV2_Hc
open OAI.PowerSaving.XHostT.K
/-- every remainder is one of [0, 1, 3, 7, 9, 10, 16, 32, 48]. -/
theorem rem_in : inR rt [0, 1, 3, 7, 9, 10, 16, 32, 48] 0 NK = true :=
  inR_list rt [0, 1, 3, 7, 9, 10, 16, 32, 48] 111 6 0 (fun j hj => by
    interval_cases j
    exacts [gin0, gin1, gin2, gin3, gin4, gin5])
theorem rem_c0 : cntR rt 0 0 NK = 96652 := by
  have h := cntR_list rt 0 111 [14001, 15669, 16094, 15419, 17348, 18121] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc0_0, gc0_1, gc0_2, gc0_3, gc0_4, gc0_5])
  rw [show ([14001, 15669, 16094, 15419, 17348, 18121] : List ℕ).sum = 96652 by decide] at h
  exact h
theorem rem_c1 : cntR rt 1 0 NK = 3893 := by
  have h := cntR_list rt 1 111 [26, 6, 706, 933, 939, 1283] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc1_0, gc1_1, gc1_2, gc1_3, gc1_4, gc1_5])
  rw [show ([26, 6, 706, 933, 939, 1283] : List ℕ).sum = 3893 by decide] at h
  exact h
theorem rem_c3 : cntR rt 3 0 NK = 3310 := by
  have h := cntR_list rt 3 111 [2325, 901, 0, 0, 0, 84] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc3_0, gc3_1, gc3_2, gc3_3, gc3_4, gc3_5])
  rw [show ([2325, 901, 0, 0, 0, 84] : List ℕ).sum = 3310 by decide] at h
  exact h
theorem rem_c7 : cntR rt 7 0 NK = 1 := by
  have h := cntR_list rt 7 111 [1, 0, 0, 0, 0, 0] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc7_0, gc7_1, gc7_2, gc7_3, gc7_4, gc7_5])
  rw [show ([1, 0, 0, 0, 0, 0] : List ℕ).sum = 1 by decide] at h
  exact h
theorem rem_c9 : cntR rt 9 0 NK = 2 := by
  have h := cntR_list rt 9 111 [2, 0, 0, 0, 0, 0] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc9_0, gc9_1, gc9_2, gc9_3, gc9_4, gc9_5])
  rw [show ([2, 0, 0, 0, 0, 0] : List ℕ).sum = 2 by decide] at h
  exact h
theorem rem_c10 : cntR rt 10 0 NK = 1 := by
  have h := cntR_list rt 10 111 [1, 0, 0, 0, 0, 0] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc10_0, gc10_1, gc10_2, gc10_3, gc10_4, gc10_5])
  rw [show ([1, 0, 0, 0, 0, 0] : List ℕ).sum = 1 by decide] at h
  exact h
theorem rem_c16 : cntR rt 16 0 NK = 16572 := by
  have h := cntR_list rt 16 111 [2908, 2688, 2688, 2912, 2688, 2688] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc16_0, gc16_1, gc16_2, gc16_3, gc16_4, gc16_5])
  rw [show ([2908, 2688, 2688, 2912, 2688, 2688] : List ℕ).sum = 16572 by decide] at h
  exact h
theorem rem_c32 : cntR rt 32 0 NK = 16576 := by
  have h := cntR_list rt 32 111 [2912, 2688, 2688, 2912, 2688, 2688] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc32_0, gc32_1, gc32_2, gc32_3, gc32_4, gc32_5])
  rw [show ([2912, 2688, 2688, 2912, 2688, 2688] : List ℕ).sum = 16576 by decide] at h
  exact h
theorem rem_c48 : cntR rt 48 0 NK = 12177 := by
  have h := cntR_list rt 48 111 [2688, 2912, 2688, 2688, 1201, 0] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc48_0, gc48_1, gc48_2, gc48_3, gc48_4, gc48_5])
  rw [show ([2688, 2912, 2688, 2688, 1201, 0] : List ℕ).sum = 12177 by decide] at h
  exact h
/-- **the remainder histogram** of H2979_HalitZiyaV2_Hc: any function of the remainders summed over all host indices. -/
theorem rem_hist {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ i ∈ Finset.range (224 * NK), f (remAt rt i) = (96652 : ℕ) • f 0 + (3893 : ℕ) • f 1 + (3310 : ℕ) • f 3 + (1 : ℕ) • f 7 + (2 : ℕ) • f 9 + (1 : ℕ) • f 10 + (16572 : ℕ) • f 16 + (16576 : ℕ) • f 32 + (12177 : ℕ) • f 48 := by
  rw [rem_sum rt NK [0, 1, 3, 7, 9, 10, 16, 32, 48] (by decide) rem_in f]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, rem_c0, rem_c1, rem_c3, rem_c7, rem_c9, rem_c10, rem_c16, rem_c32, rem_c48, add_zero, add_assoc]
/-- the residual sum of provider 0. -/
theorem res_sum0 : ∑ q ∈ Finset.range R, resAt resT 0 q = 3283 := by
  rw [← resS_eq]; decide +kernel
/-- the residual sum of provider 1. -/
theorem res_sum1 : ∑ q ∈ Finset.range R, resAt resT 1 q = 3283 := by
  rw [← resS_eq]; decide +kernel
end OAI.PowerSaving.XHostT.K.DH2979_HalitZiyaV2_Hc
#print axioms OAI.PowerSaving.XHostT.K.DH2979_HalitZiyaV2_Hc.rem_hist
#print axioms OAI.PowerSaving.XHostT.K.DH2979_HalitZiyaV2_Hc.res_sum0
#print axioms OAI.PowerSaving.XHostT.K.DH2979_HalitZiyaV2_Hc.res_sum1
